// parse.js — a dependency-free Markdown renderer whose output matches
// marked 18.1.3 (default options: gfm on, breaks off, pedantic off)
// byte for byte, written for speed: plain string scanning, no regexes
// on the hot paths, and a fast lane for plain text.
//
// Structure: a block stage builds a small block tree (containers:
// blockquote / list / item; leaves: paragraph, heading, code, html,
// thematic break, table), collecting link reference definitions on the
// way. An inline stage then renders each leaf's text with a scanner
// plus the CommonMark delimiter-stack treatment of emphasis, and a
// renderer turns the tree into marked's exact HTML.

// ------------------------------------------------------------------
// character helpers
// ------------------------------------------------------------------

const CC_TAB = 9, CC_LF = 10, CC_CR = 13, CC_SPACE = 32;

function isDigit(c) { return c >= 48 && c <= 57; }
function isAlpha(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122); }
function isAlnum(c) { return isAlpha(c) || isDigit(c); }
function isHex(c) { return isDigit(c) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102); }

// ASCII punctuation: !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
function isAsciiPunct(c) {
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) ||
         (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}

const RE_WS_CHAR = /\s/;
const RE_PUNCT_CHAR = /[\p{P}\p{S}]/u;
// Classify the character at a string index for flanking tests.
// Returns 0 = whitespace (or string edge), 1 = punctuation, 2 = other.
function charClass(str, idx) {
  if (idx < 0 || idx >= str.length) return 0;
  const ch = str[idx];
  if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' ||
      ch === '\f' || ch === '\v') return 0;
  const code = str.charCodeAt(idx);
  if (code < 128) return isAsciiPunct(code) ? 1 : 2;
  if (RE_WS_CHAR.test(ch)) return 0;
  return RE_PUNCT_CHAR.test(ch) ? 1 : 2;
}

// ------------------------------------------------------------------
// HTML escaping, in marked's two flavours:
//  - escapeCode: every & < > is escaped (code spans and code blocks)
//  - escapeText: text nodes; an & that begins something shaped like a
//    character reference (&word; or &#123; / &#x1f;) is left alone,
//    and a numeric reference is decoded before escaping.
// ------------------------------------------------------------------

function escapeCode(s) {
  if (!/[&<>"']/.test(s)) return s;
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
          .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}

// Decode the code point of a numeric reference body ("123" or "x1F600"
// without the leading #). Out-of-range, zero and surrogate values map
// to U+FFFD, as does anything above U+10FFFF.
function numericRefChar(body) {
  let cp;
  if (body.charCodeAt(0) === 120 || body.charCodeAt(0) === 88) {
    cp = parseInt(body.slice(1), 16);
  } else {
    cp = parseInt(body, 10);
  }
  if (!(cp > 0) || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)) cp = 0xFFFD;
  return String.fromCodePoint(cp);
}

// Escape one already-decoded character for text output.
function escapeDecodedChar(ch) {
  if (ch === '&') return '&amp;';
  if (ch === '<') return '&lt;';
  if (ch === '>') return '&gt;';
  if (ch === '"') return '&quot;';
  if (ch === "'") return '&#39;';
  return ch;
}

function escapeText(s) {
  // fast lane: nothing escapable at all
  let i = 0;
  const n = s.length;
  let out = null;
  while (i < n) {
    const c = s.charCodeAt(i);
    if (c === 38) { // &
      // numeric character reference? &#123; / &#x1f; (1-7 / 1-6 digits)
      if (s.charCodeAt(i + 1) === 35) {
        let j = i + 2, hex = false, cnt = 0;
        if (s.charCodeAt(j) === 120 || s.charCodeAt(j) === 88) { hex = true; j++; }
        const start = j;
        while (j < n && cnt <= 7) {
          const cc = s.charCodeAt(j);
          if (hex ? isHex(cc) : isDigit(cc)) { j++; cnt++; } else break;
        }
        const maxDigits = hex ? 6 : 7;
        if (cnt >= 1 && cnt <= maxDigits && s.charCodeAt(j) === 59) {
          if (out === null) out = s.slice(0, i);
          out += escapeDecodedChar(numericRefChar(s.slice(i + 2, j)));
          i = j + 1;
          continue;
        }
      }
      // named-reference shape &word; passes through untouched
      let j = i + 1;
      while (j < n && isAlnum(s.charCodeAt(j))) j++;
      if (j > i + 1 && s.charCodeAt(j) === 59) {
        if (out !== null) out += s.slice(i, j + 1);
        i = j + 1;
        continue;
      }
      if (out === null) out = s.slice(0, i);
      out += '&amp;';
      i++;
      continue;
    }
    if (c === 60 || c === 62 || c === 34 || c === 39) { // < > " '
      if (out === null) out = s.slice(0, i);
      out += c === 60 ? '&lt;' : c === 62 ? '&gt;' : c === 34 ? '&quot;' : '&#39;';
      i++;
      continue;
    }
    if (out !== null) out += s[i];
    i++;
  }
  return out === null ? s : out;
}

// Attribute values (href, title, alt): marked escapes &, <, >, " and
// leaves reference-shaped &...; alone, like text.
function escapeAttr(s) { return escapeText(s); }

// ------------------------------------------------------------------
// block stage
// ------------------------------------------------------------------

// Per-line cursor: s = the line's text, off = index of the first
// unconsumed character, col = the column that character sits in.
function newLine(s) { return { s, off: 0, col: 0 }; }

function lineRest(ln) { return ln.s.slice(ln.off); }

function lineBlank(ln) {
  for (let i = ln.off; i < ln.s.length; i++) {
    const c = ln.s.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

// Columns of indentation at the cursor (tab counts to the next stop).
function lineIndent(ln) {
  let col = ln.col, i = ln.off;
  while (i < ln.s.length) {
    const c = ln.s.charCodeAt(i);
    if (c === 32) { col++; i++; }
    else if (c === 9) { col += 4 - (col % 4); i++; }
    else break;
  }
  return col - ln.col;
}

// Consume exactly n columns of whitespace. A tab that straddles the
// boundary is split: the unconsumed part becomes spaces. False when
// there is not enough indentation.
// After a container prefix (quote marker, item indent) has been
// consumed from a line, marked expands the tabs of the remaining
// leading whitespace run to spaces by their column widths.
function expandLeadingTabs(ln) {
  let i = ln.off, col = ln.col, add = '', sawTab = false;
  while (i < ln.s.length) {
    const c = ln.s.charCodeAt(i);
    if (c === 32) { add += ' '; col++; i++; }
    else if (c === 9) {
      const w = 4 - (col % 4);
      add += ' '.repeat(w); col += w; i++; sawTab = true;
    } else break;
  }
  if (sawTab) ln.s = ln.s.slice(0, ln.off) + add + ln.s.slice(i);
}

function eatIndent(ln, n) {
  const sv = snapLine(ln);
  let need = n;
  while (need > 0) {
    const c = ln.s.charCodeAt(ln.off);
    if (c === 32) { ln.off++; ln.col++; need--; }
    else if (c === 9) {
      const w = 4 - (ln.col % 4);
      if (w <= need) { ln.off++; ln.col += w; need -= w; }
      else {
        ln.s = ln.s.slice(0, ln.off) + ' '.repeat(w - need) + ln.s.slice(ln.off + 1);
        ln.col += need;
        need = 0;
      }
    } else { restoreLine(ln, sv); return false; }
  }
  return true;
}

// Consume up to n plain space characters (never tabs); returns count.
function eatSpaces(ln, n) {
  let k = 0;
  while (k < n && ln.s.charCodeAt(ln.off) === 32) { ln.off++; ln.col++; k++; }
  return k;
}

function snapLine(ln) { return { s: ln.s, off: ln.off, col: ln.col }; }
function restoreLine(ln, s) { ln.s = s.s; ln.off = s.off; ln.col = s.col; }

// Blockquote prefix: up to 3 spaces, '>', then one optional space.
// Marked lexes a quote's content as a fresh document: the column
// frame restarts at the remainder, and the remainder's leading tabs
// expand as if the prefix were (leading spaces + "> ") wide.
function matchQuotePrefix(ln) {
  const sv = snapLine(ln);
  const lead = eatSpaces(ln, 3);
  if (ln.s.charCodeAt(ln.off) !== 62) { restoreLine(ln, sv); return false; }
  ln.off++; ln.col++;
  if (ln.s.charCodeAt(ln.off) === 32) { ln.off++; ln.col++; }
  ln.col = lead + 2;
  expandLeadingTabs(ln);
  ln.col = 0;
  return true;
}

// List marker at the cursor (after up to 3 spaces). Returns
// { ordered, start, bullet, delim, relIndent, blankItem } where
// relIndent is the column of the item's content measured from where
// matching began, or null.
function matchListMarker(ln) {
  const sv = snapLine(ln);
  const startCol = ln.col;
  eatSpaces(ln, 3);
  const s = ln.s;
  let i = ln.off;
  let ordered = false, start = 0, bullet = 0, delim = 0;
  const c = s.charCodeAt(i);
  if (c === 45 || c === 43 || c === 42) { bullet = c; i++; }
  else if (isDigit(c)) {
    let n = 0, digits = 0;
    while (i < s.length && digits < 9 && isDigit(s.charCodeAt(i))) {
      n = n * 10 + (s.charCodeAt(i) - 48); i++; digits++;
    }
    const d = s.charCodeAt(i);
    if ((d === 46 || d === 41) && digits >= 1) { ordered = true; start = n; delim = d; i++; }
    else { restoreLine(ln, sv); return null; }
  } else { restoreLine(ln, sv); return null; }
  // what follows the marker decides; the content column is measured
  // from where matching started, so leading spaces before the marker
  // count toward the indentation continuation lines must have
  const after = s.charCodeAt(i);
  const markerCols = (ln.col + (i - ln.off)) - startCol;
  if (i >= s.length) {
    // marker alone on the line: an empty item
    ln.col += i - ln.off; ln.off = i;
    return { ordered, start, bullet, delim, relIndent: markerCols + 1, blankItem: true };
  }
  if (after !== 32 && after !== 9) { restoreLine(ln, sv); return null; }
  // count whitespace columns after the marker
  let col = ln.col + (i - ln.off), j = i, ws = 0;
  while (j < s.length) {
    const cc = s.charCodeAt(j);
    if (cc === 32) { col++; ws++; j++; }
    else if (cc === 9) { const w = 4 - (col % 4); col += w; ws += w; j++; }
    else break;
  }
  ln.col += i - ln.off; ln.off = i;
  if (j >= s.length) {
    // only whitespace after the marker: blank item
    return { ordered, start, bullet, delim, relIndent: markerCols + 1, blankItem: true };
  }
  if (ws >= 5) {
    // content starts one space after the marker; the rest is content
    return { ordered, start, bullet, delim, relIndent: markerCols + 1, blankItem: false };
  }
  return { ordered, start, bullet, delim, relIndent: markerCols + ws, blankItem: false };
}

// After a marker matched, move the cursor to the content start.
// matchListMarker leaves the cursor at the marker's end; from there
// only whitespace remains up to the content column.
function consumeToContent(ln, m, matchStart) {
  eatIndent(ln, m.relIndent - (ln.col - matchStart.col));
  if (ln.col > 0) expandLeadingTabs(ln);
  ln.col = 0; // the item's content is a fresh local frame in marked
}

function matchAtxHeading(ln) {
  const sv = snapLine(ln);
  eatSpaces(ln, 3);
  let i = ln.off, level = 0;
  while (ln.s.charCodeAt(i) === 35 && level <= 6) { i++; level++; }
  if (level === 0 || level > 6) { restoreLine(ln, sv); return null; }
  const c = ln.s.charCodeAt(i);
  if (i < ln.s.length && c !== 32 && c !== 9) { restoreLine(ln, sv); return null; }
  let text = ln.s.slice(i);
  // strip a closing sequence of #s, then trim
  text = text.replace(/[ \t]+#+[ \t]*$/, '').replace(/^[ \t]+|[ \t]+$/g, '');
  if (/^#+$/.test(text)) text = '';
  return { level, text };
}

function matchThematicBreak(ln) {
  const sv = snapLine(ln);
  eatSpaces(ln, 3);
  const s = ln.s;
  let i = ln.off, ch = 0, count = 0;
  // a fourth space, or a tab, in the indentation makes it code, not a break
  if (s.charCodeAt(i) === 32 || s.charCodeAt(i) === 9) { restoreLine(ln, sv); return false; }
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === 42 || c === 45 || c === 95) {
      if (ch === 0) ch = c;
      else if (c !== ch) { restoreLine(ln, sv); return false; }
      count++; i++;
    } else if (c === 32 || c === 9) i++;
    else { restoreLine(ln, sv); return false; }
  }
  if (count < 3) { restoreLine(ln, sv); return false; }
  return true;
}

function matchSetextUnderline(ln) {
  const sv = snapLine(ln);
  eatSpaces(ln, 3);
  const s = ln.s;
  let i = ln.off;
  const c = s.charCodeAt(i);
  if (c !== 61 && c !== 45) { restoreLine(ln, sv); return 0; }
  while (s.charCodeAt(i) === c) i++;
  while (i < s.length) {
    const cc = s.charCodeAt(i);
    if (cc !== 32 && cc !== 9) { restoreLine(ln, sv); return 0; }
    i++;
  }
  return c === 61 ? 1 : 2;
}

function matchFenceStart(ln) {
  const sv = snapLine(ln);
  const indent = eatSpaces(ln, 3);
  const s = ln.s;
  let i = ln.off;
  const c = s.charCodeAt(i);
  if (c !== 96 && c !== 126) { restoreLine(ln, sv); return null; }
  let len = 0;
  while (s.charCodeAt(i) === c) { i++; len++; }
  if (len < 3) { restoreLine(ln, sv); return null; }
  const info = s.slice(i).trim();
  if (c === 96 && info.includes('`')) { restoreLine(ln, sv); return null; }
  return { ch: c, len, info, indent };
}

function matchFenceClose(ln, fence) {
  const sv = snapLine(ln);
  eatSpaces(ln, 3);
  const s = ln.s;
  let i = ln.off, len = 0;
  while (s.charCodeAt(i) === fence.ch) { i++; len++; }
  if (len < fence.len) { restoreLine(ln, sv); return false; }
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c !== 32 && c !== 9) { restoreLine(ln, sv); return false; }
    i++;
  }
  return true;
}

const HTML_BLOCK_TAGS = new Set(('address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol optgroup option p param section source summary table tbody td tfoot th thead title tr track ul').split(' '));

// Try to read a tag name at position i of s; returns {name, end} for a
// plausible tag start "<name" or "</name", else null.
function readTagName(s, i) {
  let j = i + 1, closing = false;
  if (s.charCodeAt(j) === 47) { closing = true; j++; }
  if (!isAlpha(s.charCodeAt(j))) return null;
  const start = j;
  while (j < s.length && (isAlnum(s.charCodeAt(j)) || s.charCodeAt(j) === 45)) j++;
  return { name: s.slice(start, j).toLowerCase(), end: j, closing };
}

// Parse a complete HTML tag starting at s[i] === '<' per the
// CommonMark grammar. Returns the index just past '>', or -1.
function parseHtmlTag(s, i) {
  let j = i + 1;
  if (s.charCodeAt(j) === 47) j++; // closing tag
  if (!isAlpha(s.charCodeAt(j))) return -1;
  j++;
  while (j < s.length && (isAlnum(s.charCodeAt(j)) || s.charCodeAt(j) === 45)) j++;
  if (s.charCodeAt(i + 1) === 47) {
    // closing tag: optional whitespace then >
    while (s[j] === ' ' || s[j] === '\t' || s[j] === '\n') j++;
    return s.charCodeAt(j) === 62 ? j + 1 : -1;
  }
  // open tag: attributes
  for (;;) {
    let ws = 0;
    while (s[j] === ' ' || s[j] === '\t' || s[j] === '\n') { j++; ws++; }
    if (s.charCodeAt(j) === 62) return j + 1;
    if (s.charCodeAt(j) === 47 && s.charCodeAt(j + 1) === 62) return j + 2;
    if (ws === 0) return -1;
    // attribute name
    const ac = s.charCodeAt(j);
    if (!(isAlpha(ac) || ac === 95 || ac === 58)) return -1;
    j++;
    while (j < s.length) {
      const c = s.charCodeAt(j);
      if (isAlnum(c) || c === 95 || c === 46 || c === 58 || c === 45) j++; else break;
    }
    // optional = value
    let k = j;
    while (s[k] === ' ' || s[k] === '\t' || s[k] === '\n') k++;
    if (s.charCodeAt(k) === 61) {
      k++;
      while (s[k] === ' ' || s[k] === '\t' || s[k] === '\n') k++;
      const q = s.charCodeAt(k);
      if (q === 34 || q === 39) {
        const end = s.indexOf(s[k], k + 1);
        if (end === -1) return -1;
        j = end + 1;
      } else {
        let v = k;
        while (v < s.length) {
          const c = s.charCodeAt(v);
          if (c === 32 || c === 9 || c === 10 || c === 34 || c === 39 ||
              c === 61 || c === 60 || c === 62 || c === 96) break;
          v++;
        }
        if (v === k) return -1;
        j = v;
      }
    }
  }
}

// HTML block start at the cursor. Returns { endKind, endStr } where
// endKind is 'blank' (types 6/7), 'str' (ends when a line contains
// endStr), or 'tag' (type 1, ends at the matching close tag).
function matchHtmlBlockStart(ln, canInterrupt) {
  const sv = snapLine(ln);
  eatSpaces(ln, 3);
  const s = ln.s, i = ln.off;
  if (s.charCodeAt(i) !== 60) { restoreLine(ln, sv); return null; }
  if (s.startsWith('<!--', i)) return { endKind: 'str', endStr: '-->' };
  if (s.startsWith('<?', i)) return { endKind: 'str', endStr: '?>' };
  if (s.startsWith('<![CDATA[', i)) return { endKind: 'str', endStr: ']]>' };
  if (s.charCodeAt(i + 1) === 33) {
    const c3 = s.charCodeAt(i + 2);
    if (c3 >= 65 && c3 <= 90) return { endKind: 'str', endStr: '>' };
  }
  const tag = readTagName(s, i);
  if (tag) {
    const after = s.charCodeAt(tag.end);
    const afterOk = tag.end >= s.length || after === 32 || after === 9 ||
                    after === 62 || (after === 47 && s.charCodeAt(tag.end + 1) === 62);
    if (!tag.closing && afterOk &&
        (tag.name === 'script' || tag.name === 'pre' || tag.name === 'style' || tag.name === 'textarea')) {
      return { endKind: 'tag', endStr: tag.name };
    }
    if (afterOk && HTML_BLOCK_TAGS.has(tag.name)) return { endKind: 'blank' };
  }
  if (!canInterrupt) {
    const end = parseHtmlTag(s, i);
    if (end !== -1) {
      let j = end;
      while (j < s.length && (s.charCodeAt(j) === 32 || s.charCodeAt(j) === 9)) j++;
      if (j >= s.length) return { endKind: 'blank' };
    }
  }
  restoreLine(ln, sv);
  return null;
}

// ---------------------------------------------------------------
// link reference definitions
// ---------------------------------------------------------------

function normalizeLabel(raw) {
  // labels match raw (backslashes kept), whitespace-collapsed, with
  // full Unicode case folding (ß folds to ss, ligatures expand)
  return raw.replace(/[ \t\n]+/g, ' ').replace(/^ | $/g, '').toLowerCase()
    .replace(/ß/g, 'ss').replace(/ﬀ/g, 'ff').replace(/ﬁ/g, 'fi')
    .replace(/ﬂ/g, 'fl').replace(/ﬃ/g, 'ffi').replace(/ﬄ/g, 'ffl')
    .replace(/ﬅ/g, 'st').replace(/ﬆ/g, 'st').replace(/ſ/g, 's');
}

// Scan a link destination at T[i]: returns { dest, end } or null.
function scanDest(T, i) {
  if (T.charCodeAt(i) === 60) {
    let j = i + 1;
    while (j < T.length) {
      const c = T.charCodeAt(j);
      if (c === 10) return null; // no newlines inside <...> in marked
      if (c === 92) {
        if (T.charCodeAt(j + 1) === 10) return null;
        j += 2; continue;
      }
      if (c === 62) return { dest: T.slice(i + 1, j), end: j + 1 };
      if (c === 60) return null;
      j++;
    }
    return null;
  }
  let j = i, depth = 0;
  while (j < T.length) {
    const c = T.charCodeAt(j);
    if (c === 92) { j += 2; continue; }
    if (c <= 32) break;
    if (c === 40) depth++;
    else if (c === 41) { if (depth === 0) break; depth--; }
    j++;
  }
  if (j === i) return null;
  return { dest: T.slice(i, j), end: j };
}

// Scan a link title at T[i]: returns { title, end } or null.
function scanTitle(T, i) {
  const open = T.charCodeAt(i);
  let close;
  if (open === 34) close = 34;
  else if (open === 39) close = 39;
  else if (open === 40) close = 41;
  else return null;
  let j = i + 1;
  while (j < T.length) {
    const c = T.charCodeAt(j);
    if (c === 92) { j += 2; continue; }
    if (c === close) return { title: T.slice(i + 1, j), end: j + 1 };
    if (open === 40 && c === 40) return null;
    j++;
  }
  return null;
}

// Unescape backslash-escaped ASCII punctuation.
function unescapeStr(s) {
  if (!s.includes('\\')) return s;
  let out = '';
  for (let i = 0; i < s.length; i++) {
    if (s.charCodeAt(i) === 92 && i + 1 < s.length && isAsciiPunct(s.charCodeAt(i + 1))) {
      out += s[i + 1]; i++;
    } else out += s[i];
  }
  return out;
}

// Try to parse one link reference definition in the virtual text T
// (several lines joined by \n). Returns { label, dest, title,
// newlines } — newlines = how many line boundaries it spans — or null.
function parseOneDef(T) {
  let i = 0;
  while (T.charCodeAt(i) === 32) i++;
  if (i > 3) return null;
  if (T.charCodeAt(i) !== 91) return null;
  // label
  let j = i + 1, labelEnd = -1;
  while (j < T.length && j - i <= 1000) {
    const c = T.charCodeAt(j);
    if (c === 92) { j += 2; continue; }
    if (c === 91) return null;
    if (c === 93) { labelEnd = j; break; }
    j++;
  }
  if (labelEnd === -1) return null;
  const rawLabel = T.slice(i + 1, labelEnd);
  if (!rawLabel.trim()) return null;
  if (T.charCodeAt(labelEnd + 1) !== 58) return null;
  let k = labelEnd + 2;
  const skipWs = (from, newlinesOnly) => {
    let p = from;
    for (;;) {
      const c = T.charCodeAt(p);
      if (c === 32 || c === 9 || c === 10) { p++; continue; }
      break;
    }
    return p;
  };
  k = skipWs(k);
  const d = scanDest(T, k);
  if (!d) return null;
  k = d.end;
  // the end of the destination's own line (dest-only fallback point)
  let eolK = k;
  while (T.charCodeAt(eolK) === 32 || T.charCodeAt(eolK) === 9) eolK++;
  const destLineEnds = eolK >= T.length || T.charCodeAt(eolK) === 10;
  // optional title, but only when whitespace separates it from the
  // destination, and only when nothing but blanks follows it
  let title = null, endK = -1;
  const afterWs = skipWs(k);
  if (afterWs > k) {
    const t = scanTitle(T, afterWs);
    if (t) {
      let m = t.end;
      while (T.charCodeAt(m) === 32 || T.charCodeAt(m) === 9) m++;
      if (m >= T.length || T.charCodeAt(m) === 10) { title = t.title; endK = m; }
    }
  }
  if (endK === -1) {
    if (!destLineEnds) return null;
    endK = eolK;
  }
  let newlines = 0;
  for (let p = 0; p < endK; p++) if (T.charCodeAt(p) === 10) newlines++;
  return {
    label: normalizeLabel(rawLabel),
    dest: unescapeStr(d.dest),
    title: title === null ? null : unescapeStr(title),
    newlines,
  };
}

// ---------------------------------------------------------------
// tables (GFM)
// ---------------------------------------------------------------

function parseDelimiterRow(s) {
  let t = s.trim();
  if (!t.includes('-')) return null;
  if (t.startsWith('|')) t = t.slice(1);
  if (t.endsWith('|') && !t.endsWith('\\|')) t = t.slice(0, -1);
  const cells = t.split('|');
  const aligns = [];
  for (const cell of cells) {
    const c = cell.trim();
    if (!/^:?-+:?$/.test(c)) return null;
    const left = c.startsWith(':'), right = c.endsWith(':');
    aligns.push(left && right ? 'center' : left ? 'left' : right ? 'right' : null);
  }
  return aligns;
}

// Split a table row into raw cell texts: pipes inside code spans or
// escaped as \| do not split.
// In table cells, a \| escape becomes a literal pipe in the cell
// text (even inside code spans); a \\ pair stays a pair.
function unescapePipes(s) {
  if (!s.includes('\\')) return s;
  let out = '', i = 0;
  while (i < s.length) {
    if (s.charCodeAt(i) === 92 && s.charCodeAt(i + 1) === 124) { out += '|'; i += 2; }
    else if (s.charCodeAt(i) === 92 && s.charCodeAt(i + 1) === 92) { out += '\\\\'; i += 2; }
    else { out += s[i]; i++; }
  }
  return out;
}

function splitRowCells(s) {
  // marked splits on pipes that are not backslash-escaped; a
  // backslash escapes whatever follows it for splitting purposes,
  // and code spans do not protect pipes
  let t = s.trim();
  const cells = [];
  let cur = '', i = 0;
  const push = () => { cells.push(cur); cur = ''; };
  while (i < t.length) {
    const c = t.charCodeAt(i);
    if (c === 92 && i + 1 < t.length) { cur += t[i] + t[i + 1]; i += 2; continue; }
    if (c === 124) { push(); i++; continue; }
    cur += t[i]; i++;
  }
  push();
  // drop the empty edge cells produced by leading/trailing pipes
  if (cells.length > 1 && cells[0].trim() === '' && t.startsWith('|')) cells.shift();
  if (cells.length > 1 && cells[cells.length - 1].trim() === '' && t.endsWith('|')) cells.pop();
  return cells.map(c => unescapePipes(c.trim()));
}

// ---------------------------------------------------------------
// the block driver
// ---------------------------------------------------------------

function parse(srcInput) {
  const src = srcInput.replace(/\r\n?/g, '\n');
  const hadNL = src.endsWith('\n');
  const lines = src.split('\n');
  if (hadNL) lines.pop();

  const refs = new Map();
  const doc = { type: 'doc', children: [] };
  const stack = [doc];
  const top = () => stack[stack.length - 1];

  let lineOpened = false;
  function addBlock(node) {
    lineOpened = true;
    const p = top();
    node.parent = p;
    // content added to an item after a blank line makes the blank an
    // in-item separator between two blocks (and consumes it: the
    // blank is no longer "after the item" for the parent list)
    if (p.type === 'item' && p.blankAfter) {
      if (p.children.length >= 1) p.blankSeen = true;
      p.blankAfter = false;
    }
    p.children.push(node);
    if (p.type === 'item' && p.blankSeen && p.children.length > 1 && p.listNode) {
      p.listNode.loose = true;
    }
    return node;
  }

  function finalize(b, parent) {
    if (b.type === 'para') {
      let text = b.parts.join('\n');
      // strip leading link reference definitions into refs
      for (;;) {
        const d = parseOneDef(text);
        if (!d) break;
        if (!refs.has(d.label)) refs.set(d.label, { dest: d.dest, title: d.title });
        let cut = 0, nl = 0;
        while (cut < text.length && nl <= d.newlines) {
          if (text.charCodeAt(cut) === 10) nl++;
          cut++;
        }
        text = text.slice(cut);
        if (!text) break;
      }
      b.text = text;
      if (!text.trim()) {
        b.dead = true;
        const idx = parent.children.indexOf(b);
        if (idx !== -1) parent.children.splice(idx, 1);
      }
    } else if (b.type === 'fence') {
      // marked drops exactly one trailing newline from fenced content
      if (b.lines.length && b.lines[b.lines.length - 1] === '') b.lines.pop();
      b.text = b.lines.map(l => l + '\n').join('');
    } else if (b.type === 'icode') {
      const ls = b.lines;
      while (ls.length && ls[ls.length - 1] === '') ls.pop();
      b.text = ls.length ? ls.join('\n') + '\n' : '';
    } else if (b.type === 'list') {
      // loose when a blank line separates two items, or an item holds
      // two blocks across a blank line
      const items = b.children.filter(c => !c.dead);
      for (let i = 0; i < items.length; i++) {
        if (items[i].blankAfter && i < items.length - 1) b.loose = true;
        if (items[i].blankSeen &&
            items[i].children.filter(c => !c.dead).length > 1) b.loose = true;
      }
      // a blank after the last item's content is a blank after the
      // list itself for the enclosing item's bookkeeping
      if (items.length && items[items.length - 1].blankAfter &&
          parent && parent.type === 'item') parent.blankAfter = true;
    } else if (b.type === 'item' || b.type === 'quote') {
      // a container whose captured text ends with an HTML block loses
      // that block's final newline (marked strips it from the capture)
      for (let i = b.children.length - 1; i >= 0; i--) {
        const last = b.children[i];
        if (last.dead) continue;
        if (last.type === 'html') last.endedByBlank = true;
        break;
      }
    }
  }

  function closeBlocks(fromIdx) {
    while (stack.length > fromIdx) {
      const b = stack.pop();
      finalize(b, stack[stack.length - 1]);
    }
  }

  // An HTML block that a truly empty line follows loses its final
  // newline in marked's output, whether it is still open or already
  // closed. A whitespace-only line does not count (a type-6 block
  // still ends at one, via its own blank termination).
  function flagHtmlBeforeBlank(ln) {
    if (ln && lineRest(ln) !== '') return;
    const b = top();
    if (b.type === 'html') { b.endedByBlank = true; return; }
    if (b.children && b.children.length) {
      const last = b.children[b.children.length - 1];
      if (last.type === 'html') last.endedByBlank = true;
    }
  }

  function noteBlankLine() {
    // the blank belongs to the innermost open item, unless it falls
    // inside a blockquote nested in that item
    for (let i = stack.length - 1; i >= 0; i--) {
      const ty = stack[i].type;
      if (ty === 'item') {
        const it = stack[i];
        it.blankAfter = true;
        if (it.children.length) it.blankSeen = true;
        else it.diedBlank = true;
        return;
      }
      if (ty === 'quote' || ty === 'doc') return;
    }
  }

  // Run the container descent on an arbitrary raw line against the
  // current stack; returns the remainder, or null when some container
  // does not match. Used to peek at the next line (table delimiters).
  function peekRemainder(n) {
    if (n >= lines.length) return null;
    const pln = newLine(lines[n]);
    if (lineBlank(pln)) return '';
    for (let d = 1; d < stack.length; d++) {
      const b = stack[d];
      if (b.type === 'quote') { if (!matchQuotePrefix(pln)) return null; }
      else if (b.type === 'item') { if (!eatIndent(pln, b.relIndent)) return null; }
    }
    return lineRest(pln);
  }

  // Would this line start an item of a list already open? Then it is
  // not a lazy paragraph continuation, even when the item is empty.
  function startsOpenListItem(ln) {
    let hasList = false;
    for (const b of stack) if (b.type === 'list') { hasList = true; break; }
    if (!hasList) return false;
    const sv = snapLine(ln);
    const m = matchListMarker(ln);
    restoreLine(ln, sv);
    if (!m) return false;
    for (const b of stack) {
      if (b.type === 'list' && b.ordered === m.ordered &&
          (m.ordered ? b.delim === m.delim : b.bullet === m.bullet)) return true;
    }
    return false;
  }

  // Would this line start a list item (with content) once the open
  // containers close? Inside a list item that also blocks laziness:
  // the line ends the current list and starts a new one.
  function startsLooseListItem(ln) {
    let hasList = false;
    for (const b of stack) if (b.type === 'list') { hasList = true; break; }
    if (!hasList) return false;
    const sv = snapLine(ln);
    const m = matchListMarker(ln);
    restoreLine(ln, sv);
    return !!m && !m.blankItem;
  }

  // Would this line interrupt an open paragraph? (laziness test)
  function startsInterruptingBlock(ln) {
    const sv = snapLine(ln);
    let yes = false;
    if (matchQuotePrefix(ln)) yes = true;
    restoreLine(ln, sv);
    if (!yes && matchFenceStart(ln)) yes = true;
    restoreLine(ln, sv);
    if (!yes && matchAtxHeading(ln)) yes = true;
    restoreLine(ln, sv);
    if (!yes && matchThematicBreak(ln)) yes = true;
    restoreLine(ln, sv);
    if (!yes && matchHtmlBlockStart(ln, true)) yes = true;
    restoreLine(ln, sv);
    if (!yes) {
      const m = matchListMarker(ln);
      if (m && !m.blankItem && (!m.ordered || m.start === 1)) yes = true;
      restoreLine(ln, sv);
    }
    return yes;
  }

  for (let li = 0; li < lines.length; li++) {
    const raw = lines[li];
    const terminated = li < lines.length - 1 || hadNL;
    const ln = newLine(raw);

    // phase 1: match open containers (list nodes are transparent;
    // the descent stops at the first leaf block)
    let leafDepth = stack.length;
    for (let d = 1; d < stack.length; d++) {
      const ty = stack[d].type;
      if (ty !== 'quote' && ty !== 'item' && ty !== 'list') { leafDepth = d; break; }
    }
    const matchedQuotes = [];
    let matched = 1, itemMatched = false;
    while (matched < leafDepth) {
      const b = stack[matched];
      if (b.type === 'quote') {
        if (!matchQuotePrefix(ln)) break;
        matchedQuotes.push(b); matched++;
      }
      else if (b.type === 'item') {
        // an item that saw a blank line before any content is over:
        // later lines cannot join it (CommonMark example 280)
        if (b.diedBlank) break;
        if (lineBlank(ln)) { matched++; continue; }
        if (!eatIndent(ln, b.relIndent)) break;
        if (ln.col > 0) expandLeadingTabs(ln);
        ln.col = 0; // content frame restarts, as in marked's capture
        itemMatched = true;
        matched++;
      }
      else matched++; // list: transparent
    }
    if (ln.col > 0) expandLeadingTabs(ln);
    let lazyQuote = null, lazyFirst = false;
    // a whitespace-only final line joins an open paragraph in marked
    // (its capture has no trailing newline there), whether it carries
    // a quote marker or the input simply ends without a newline
    const eofSpaceLine = li === lines.length - 1 && lineBlank(ln) &&
      (matchedQuotes.length > 0 || !terminated);
    // a fence open inside list items swallows later content lines
    // that fail the innermost items' indentation, but only once it
    // has real content; with no content yet, such a line ends the
    // fence (and the item). Quotes still end it either way.
    let fenceSwallow = false;
    if (matched < leafDepth && top().type === 'fence' && top().hasContent) {
      fenceSwallow = true;
      for (let d = matched; d < leafDepth; d++) {
        const ty = stack[d].type;
        if (ty !== 'item' && ty !== 'list') { fenceSwallow = false; break; }
      }
    }
    if (matched < leafDepth && !fenceSwallow) {
      if (lineBlank(ln) && !(eofSpaceLine && top().type === 'para') &&
          !(top().type === 'table' && lineRest(ln).includes('\t'))) {
        flagHtmlBeforeBlank(ln);
        closeBlocks(matched);
      } else if ((top().type === 'para' || top().type === 'table') &&
                 !startsInterruptingBlock(ln) && !startsOpenListItem(ln) &&
                 !startsLooseListItem(ln)) {
        // lazy continuation: every container stays open; remember the
        // deepest quote the line slipped into, for marked's quirks
        for (let d = leafDepth - 1; d >= matched; d--) {
          if (stack[d].type === 'quote') { lazyQuote = stack[d]; break; }
        }
        if (lazyQuote) {
          lazyFirst = !lazyQuote.lazyRun;
          lazyQuote.lazyRun = (lazyQuote.lazyRun || 0) + 1;
        }
        for (const q of matchedQuotes) q.lazyRun = 0;
      } else {
        closeBlocks(matched);
      }
    } else {
      for (const q of matchedQuotes) q.lazyRun = 0;
    }

    // phase 2: open containers / start or continue leaves
    let consumed = false;
    lineOpened = false;
    while (!consumed) {
      const t = top();

      // greedy leaves first
      if (t.type === 'fence') {
        const sv = snapLine(ln);
        if (matchFenceClose(ln, t)) { closeBlocks(stack.length - 1); }
        else {
          restoreLine(ln, sv);
          const rest = lineRest(ln);
          // the fence dedent removes up to `indent` leading
          // whitespace characters (a tab counts as one character);
          // marked only dedents backtick fences, never tilde fences
          let k = 0;
          if (t.ch === 96) { // backtick fence
            while (k < t.indent && (rest.charCodeAt(k) === 32 || rest.charCodeAt(k) === 9)) k++;
          }
          t.lines.push(rest.slice(k));
          // only a non-blank line that arrived through the full
          // container descent establishes the fence for swallowing
          if (matched >= leafDepth && rest.trim() !== '') t.hasContent = true;
        }
        consumed = true; break;
      }
      if (t.type === 'html') {
        if (t.endKind === 'blank' && lineBlank(ln)) {
          t.endedByBlank = true;
          closeBlocks(stack.length - 1); continue;
        }
        t.parts.push(lineRest(ln) + (terminated ? '\n' : ''));
        const rest = lineRest(ln);
        const low = t.endKind === 'tag' ? rest.toLowerCase() : rest;
        if ((t.endKind === 'str' && rest.includes(t.endStr)) ||
            (t.endKind === 'tag' && low.includes('</' + t.endStr))) {
          closeBlocks(stack.length - 1);
        }
        consumed = true; break;
      }
      if (t.type === 'icode') {
        if (lineIndent(ln) >= 4) { eatIndent(ln, 4); t.lines.push(lineRest(ln)); consumed = true; break; }
        if (lineBlank(ln)) { t.lines.push(''); consumed = true; break; }
        closeBlocks(stack.length - 1); continue;
      }
      if (t.type === 'table') {
        // a whitespace-only line containing a tab is an (empty) row
        // in marked; a spaces-only line ends the table
        if (lineBlank(ln) && !lineRest(ln).includes('\t')) {
          closeBlocks(stack.length - 1); continue;
        }
        const sv = snapLine(ln);
        if (startsInterruptingBlock(ln)) { restoreLine(ln, sv); closeBlocks(stack.length - 1); continue; }
        restoreLine(ln, sv);
        const cells = splitRowCells(lineRest(ln));
        const row = [];
        for (let c = 0; c < t.header.length; c++) row.push(c < cells.length ? cells[c] : '');
        t.rows.push(row);
        consumed = true; break;
      }

      // a whitespace-only final line joins an open paragraph
      if (eofSpaceLine && t.type === 'para') {
        t.parts.push(lineRest(ln));
        consumed = true; break;
      }

      // blank line (a line whose remainder is blank only because a
      // marker was just consumed does not count as a blank line)
      if (lineBlank(ln)) {
        if (t.type === 'para') closeBlocks(stack.length - 1);
        flagHtmlBeforeBlank(ln);
        if (!lineOpened) noteBlankLine();
        consumed = true; break;
      }

      // an open paragraph: setext, table conversion, interruption, or
      // plain continuation
      if (t.type === 'para') {
        // marked quirk: a setext-shaped line slipped lazily into a
        // blockquote joins the paragraph as text — bare when it is the
        // run's first lazy line, indented by 4 after earlier lazy lines
        if (lazyQuote) {
          const trimmed = lineRest(ln).replace(/^[ \t]+|[ \t]+$/g, '');
          if (/^=+$/.test(trimmed)) {
            t.parts.push(lazyFirst ? trimmed : '    ' + trimmed);
            consumed = true; break;
          }
        }
        const lvl = matchSetextUnderline(ln);
        if (lvl) {
          // strip leading definitions first (marked consumes them as
          // their own tokens before the setext line is considered)
          let text = t.parts.join('\n');
          for (;;) {
            const d = parseOneDef(text);
            if (!d) break;
            if (!refs.has(d.label)) refs.set(d.label, { dest: d.dest, title: d.title });
            let cut = 0, nl = 0;
            while (cut < text.length && nl <= d.newlines) {
              if (text.charCodeAt(cut) === 10) nl++;
              cut++;
            }
            text = text.slice(cut);
            if (!text) break;
          }
          if (!text.trim()) {
            t.dead = true;
            closeBlocks(stack.length - 1);
            const idx = t.parent.children.indexOf(t);
            if (idx !== -1) t.parent.children.splice(idx, 1);
            continue; // the underline line is reprocessed fresh
          }
          t.type = 'heading'; t.level = lvl;
          t.text = text.replace(/^[ \t\n]+/, '').replace(/[ \t\n]+$/, '');
          closeBlocks(stack.length - 1);
          consumed = true; break;
        }
        // table conversion: this line is a delimiter row and the
        // paragraph's last line is the header
        {
          const rest = lineRest(ln);
          const aligns = parseDelimiterRow(rest);
          if (aligns && t.parts.length) {
            const headerLine = t.parts[t.parts.length - 1];
            const cells = splitRowCells(headerLine);
            if (cells.length === aligns.length &&
                (headerLine.includes('|') || rest.includes('|'))) {
              t.parts.pop();
              const table = { type: 'table', header: cells, align: aligns, rows: [] };
              closeBlocks(stack.length - 1); // finalize the paragraph
              addBlock(table);
              stack.push(table);
              consumed = true; break;
            }
          }
        }
        // interruption?
        const sv = snapLine(ln);
        let interrupt = false;
        if (matchQuotePrefix(ln)) interrupt = true;
        restoreLine(ln, sv);
        if (!interrupt && matchFenceStart(ln)) interrupt = true;
        restoreLine(ln, sv);
        if (!interrupt && matchAtxHeading(ln)) interrupt = true;
        restoreLine(ln, sv);
        if (!interrupt && matchThematicBreak(ln)) interrupt = true;
        restoreLine(ln, sv);
        if (!interrupt && matchHtmlBlockStart(ln, true)) interrupt = true;
        restoreLine(ln, sv);
        if (!interrupt) {
          const m = matchListMarker(ln);
          // inside a list item, marked lets any ordered marker
          // interrupt a paragraph; elsewhere only start === 1 does
          if (m && !m.blankItem &&
              (!m.ordered || m.start === 1 || t.parent.type === 'item')) interrupt = true;
          restoreLine(ln, sv);
        }
        if (interrupt) { closeBlocks(stack.length - 1); continue; }
        {
          let rest = lineRest(ln);
          // a deeply indented line slipped lazily into a container
          // loses its indentation in marked's capture
          if (matched < leafDepth && lineIndent(ln) >= 4) rest = rest.replace(/^[ \t]+/, '');
          t.parts.push(rest);
        }
        consumed = true; break;
      }

      // an open list expects a new item (or ends)
      if (t.type === 'list') {
        // a thematic break on the line ends the list instead
        if (matchThematicBreak(ln)) {
          closeBlocks(stack.length - 1);
          addBlock({ type: 'hr' });
          consumed = true; break;
        }
        const sv = snapLine(ln);
        const m = matchListMarker(ln);
        if (m && m.ordered === t.ordered &&
            (m.ordered ? m.delim === t.delim : m.bullet === t.bullet)) {
          const prev = t.children[t.children.length - 1];
          if (prev && prev.blankSeen && prev.children.length) t.loose = true;
          const item = { type: 'item', children: [], relIndent: m.relIndent, blankSeen: false, listNode: t };
          addBlock(item);
          stack.push(item);
          consumeToContent(ln, m, sv);
          continue;
        }
        restoreLine(ln, sv);
        closeBlocks(stack.length - 1);
        continue;
      }

      // fresh block starts at a container (doc / quote / item)
      {
        const sv = snapLine(ln);
        if (matchQuotePrefix(ln)) {
          const q = { type: 'quote', children: [] };
          addBlock(q); stack.push(q);
          if (ln.col > 0) expandLeadingTabs(ln);
          continue;
        }
        restoreLine(ln, sv);
      }
      {
        const f = matchFenceStart(ln);
        if (f) {
          const node = { type: 'fence', ch: f.ch, len: f.len, indent: f.indent,
                         info: f.info, lines: [] };
          addBlock(node); stack.push(node);
          consumed = true; break;
        }
      }
      {
        const h = matchAtxHeading(ln);
        if (h) {
          addBlock({ type: 'heading', level: h.level, text: h.text });
          consumed = true; break;
        }
      }
      if (matchThematicBreak(ln)) {
        addBlock({ type: 'hr' });
        consumed = true; break;
      }
      {
        const sv = snapLine(ln);
        const m = matchListMarker(ln);
        if (m) {
          const list = { type: 'list', ordered: m.ordered, start: m.start, loose: false, children: [], bullet: m.bullet, delim: m.delim };
          addBlock(list); stack.push(list);
          const item = { type: 'item', children: [], relIndent: m.relIndent, blankSeen: false, listNode: list };
          addBlock(item); stack.push(item);
          consumeToContent(ln, m, sv);
          continue;
        }
        restoreLine(ln, sv);
      }
      {
        const rest0 = lineRest(ln);
        const hb = matchHtmlBlockStart(ln, false);
        if (hb) {
          const node = { type: 'html', endKind: hb.endKind, endStr: hb.endStr, parts: [] };
          addBlock(node); stack.push(node);
          node.parts.push(rest0 + (terminated ? '\n' : ''));
          const low = hb.endKind === 'tag' ? rest0.toLowerCase() : rest0;
          if ((hb.endKind === 'str' && rest0.includes(hb.endStr)) ||
              (hb.endKind === 'tag' && low.includes('</' + hb.endStr))) {
            closeBlocks(stack.length - 1);
          }
          consumed = true; break;
        }
      }
      // table start: this line is the header, the next the delimiter
      {
        const rest = lineRest(ln);
        if (rest.includes('|') || true) {
          const next = peekRemainder(li + 1);
          if (next !== null && next !== '') {
            const aligns = parseDelimiterRow(next);
            if (aligns) {
              const cells = splitRowCells(rest);
              if (cells.length === aligns.length &&
                  (rest.includes('|') || next.includes('|'))) {
                const table = { type: 'table', header: cells, align: aligns, rows: [] };
                addBlock(table); stack.push(table);
                li++; // the delimiter line is consumed too
                consumed = true; break;
              }
            }
          }
        }
      }
      // indented code
      if (lineIndent(ln) >= 4) {
        const node = { type: 'icode', lines: [] };
        addBlock(node); stack.push(node);
        eatIndent(ln, 4);
        node.lines.push(lineRest(ln));
        consumed = true; break;
      }
      // a paragraph begins
      {
        const node = { type: 'para', parts: [lineRest(ln)] };
        addBlock(node); stack.push(node);
        consumed = true; break;
      }
    }
  }

  closeBlocks(1);
  refs.inLinkState = { inLink: false };
  return renderDocument(doc, refs);
}

// ---------------------------------------------------------------
// rendering
// ---------------------------------------------------------------

function renderDocument(doc, refs) {
  return renderBlocks(doc.children, refs, false);
}

function renderBlocks(blocks, refs, tight) {
  let out = '';
  for (const b of blocks) out += renderBlock(b, refs, tight);
  return out;
}

function renderBlock(b, refs, tight) {
  switch (b.type) {
    case 'para':
      return tight ? renderInline(b.text, refs)
                   : '<p>' + renderInline(b.text, refs) + '</p>\n';
    case 'heading':
      return '<h' + b.level + '>' + renderInline(b.text, refs) + '</h' + b.level + '>\n';
    case 'hr':
      return '<hr>\n';
    case 'fence': {
      const lang = b.info ? unescapeStr(b.info.split(/[ \t]/)[0]) : '';
      return '<pre><code' + (lang ? ' class="language-' + escapeAttr(lang) + '"' : '') +
             '>' + escapeCode(b.text) + '</code></pre>\n';
    }
    case 'icode':
      return '<pre><code>' + escapeCode(b.text) + '</code></pre>\n';
    case 'html': {
      let text = b.parts.join('');
      // a block a blank line follows (or a container capture that ends
      // with it) drops its last line's newline
      if (b.endedByBlank && text.endsWith('\n')) text = text.slice(0, -1);
      return text;
    }
    case 'quote':
      return '<blockquote>\n' + renderBlocks(b.children, refs, false) + '</blockquote>\n';
    case 'list': {
      const tag = b.ordered ? 'ol' : 'ul';
      let out = '<' + tag +
        (b.ordered && b.start !== 1 ? ' start="' + b.start + '"' : '') + '>\n';
      for (const item of b.children) out += renderItem(item, b, refs);
      return out + '</' + tag + '>\n';
    }
    case 'table': {
      let out = '<table>\n<thead>\n<tr>\n';
      for (let c = 0; c < b.header.length; c++) {
        out += '<th' + (b.align[c] ? ' align="' + b.align[c] + '"' : '') + '>' +
               renderInline(b.header[c], refs) + '</th>\n';
      }
      out += '</tr>\n</thead>\n';
      if (b.rows.length) {
        out += '<tbody>';
        for (const row of b.rows) {
          out += '<tr>\n';
          for (let c = 0; c < b.header.length; c++) {
            out += '<td' + (b.align[c] ? ' align="' + b.align[c] + '"' : '') + '>' +
                   renderInline(row[c], refs) + '</td>\n';
          }
          out += '</tr>\n';
        }
        out += '</tbody>';
      }
      return out + '</table>\n';
    }
  }
  return '';
}

function renderItem(item, list, refs) {
  const tight = !list.loose;
  const kids = item.children;
  let body = '';
  let startAt = 0;
  const first = kids[0];
  if (first && first.type === 'para' && first.text &&
      first.text.charCodeAt(0) === 91 &&
      (first.text[1] === ' ' || first.text[1] === 'x' || first.text[1] === 'X') &&
      first.text.charCodeAt(2) === 93 && first.text.charCodeAt(3) === 32) {
    const checked = first.text[1] !== ' ';
    const input = checked ? '<input checked="" disabled="" type="checkbox">'
                          : '<input disabled="" type="checkbox">';
    const saved = first.text;
    first.text = saved.slice(3);
    // tight: the input prefixes the bare text; loose: it goes
    // inside the paragraph element
    body += tight ? input + renderInline(first.text, refs)
                  : '<p>' + input + renderInline(first.text, refs) + '</p>\n';
    first.text = saved;
    startAt = 1;
  }
  for (let i = startAt; i < kids.length; i++) body += renderBlock(kids[i], refs, tight);
  return '<li>' + body + '</li>\n';
}

// ---------------------------------------------------------------
// inline stage
// ---------------------------------------------------------------

function encodeHref(h) {
  // marked percent-encodes the href but restores existing escapes
  try { return encodeURI(h).replace(/%25/g, '%'); } catch { return h; }
}

function decodeNumericRefs(s) {
  if (!s.includes('&#')) return s;
  return s.replace(/&#(\d{1,7});/g, (_, d) => numericRefChar(d))
          .replace(/&#[xX]([0-9a-fA-F]{1,6});/g, (_, h) => numericRefChar('x' + h));
}

function plainText(nodes) {
  let out = '';
  for (const nd of nodes) {
    switch (nd.k) {
      case 'text': out += decodeNumericRefs(nd.s); break;
      case 'code': out += nd.s; break;
      case 'html': out += nd.s; break;
      case 'br': out += ' '; break;
      case 'open': out += nd.image ? '![' : '['; break;
      case 'delim': out += nd.ch.repeat(nd.n); break;
      case 'em': case 'strong': case 'del': case 'link':
        out += plainText(nd.children); break;
      case 'image': out += nd.alt; break;
      case 'autolink': out += nd.text; break;
    }
  }
  return out;
}

function renderNodes(nodes) {
  let out = '';
  for (const nd of nodes) {
    switch (nd.k) {
      case 'text': out += nd.fin ? nd.s : escapeText(nd.s); break;
      case 'code': out += '<code>' + escapeCode(nd.s) + '</code>'; break;
      case 'html': out += nd.s; break;
      case 'br': out += '<br>'; break;
      case 'open': out += nd.image ? '![' : '['; break;
      case 'delim': out += nd.ch.repeat(nd.n); break;
      case 'em': out += '<em>' + renderNodes(nd.children) + '</em>'; break;
      case 'strong': out += '<strong>' + renderNodes(nd.children) + '</strong>'; break;
      case 'del': out += '<del>' + renderNodes(nd.children) + '</del>'; break;
      case 'link':
        out += '<a href="' + escapeAttr(encodeHref(nd.href)) + '"' +
               (nd.title !== null && nd.title !== undefined
                 ? ' title="' + escapeAttr(nd.title) + '"' : '') +
               '>' + renderNodes(nd.children) + '</a>';
        break;
      case 'image':
        out += '<img src="' + escapeAttr(encodeHref(nd.src)) + '" alt="' +
               escapeAttr(nd.alt) + '"' +
               (nd.title !== null && nd.title !== undefined
                 ? ' title="' + escapeAttr(nd.title) + '"' : '') + '>';
        break;
      case 'autolink':
        out += '<a href="' + escapeAttr(encodeHref(nd.href)) + '">' + escapeText(nd.text) + '</a>';
        break;
    }
  }
  return out;
}

// The delimiter-stack emphasis algorithm over a node list.
function processEmphasis(nodes) {
  let ci = 0;
  while (ci < nodes.length) {
    const d = nodes[ci];
    if (d.k !== 'delim' || !d.canClose || d.n === 0) { ci++; continue; }
    let oi = ci - 1, opener = null;
    while (oi >= 0) {
      const o = nodes[oi];
      if (o.k === 'delim' && o.ch === d.ch && o.canOpen && o.n > 0) {
        // strikethrough pairs must have equal run lengths in marked
        if (d.ch === '~' && o.n !== d.n) { oi--; continue; }
        if ((o.canClose || d.canOpen) &&
            (o.orig + d.orig) % 3 === 0 && !(o.orig % 3 === 0 && d.orig % 3 === 0)) {
          oi--; continue;
        }
        // marked disqualifies a closer when the span still holds an
        // unmatched same-char run that could open or close and is
        // not preceded by a word character (fully inert runs, with
        // whitespace on both sides, do not count)
        let blocked = false, blockedR2 = false;
        for (let j = oi + 1; j < ci; j++) {
          const x = nodes[j];
          if (x.k === 'delim' && x.ch === d.ch && x.n > 0 && x.poison && !x.dead &&
              (x.canOpen || x.canClose)) { blocked = true; break; }
        }
        // ... or when the span ends with a wrap of the other kind
        // (em vs strong) followed only by plain text starting with a
        // word character, and the closer run is short (<= 2). The
        // wrap must not be word-attached on its left: a wrap that
        // directly follows a word character (intraword nesting like
        // *foo**bar**baz*) does not trigger this.
        if (!blocked && d.n <= 2) {
          for (let j = ci - 1; j > oi; j--) {
            const x = nodes[j];
            // the gap between the wrap and the closer may hold text
            // and fully inert runs, but no live delimiter
            if (x.k === 'delim' && !x.dead && (x.canOpen || x.canClose)) break;
            if (x.k === 'em' || x.k === 'strong') {
              if (x.ch === d.ch) {
                const gap = nodes[j + 1];
                const wkind = x.k === 'strong' ? 2 : 1;
                const okind = o.orig >= 2 ? 2 : 1;
                let leftFree = true;
                const before = nodes[j - 1];
                if (before && before.k === 'text' && before.s &&
                    charClass(before.s, before.s.length - 1) === 2) leftFree = false;
                if (leftFree && wkind !== okind &&
                    gap && gap.k === 'text' && gap.s &&
                    charClass(gap.s, 0) === 2) { blocked = true; blockedR2 = true; }
              }
              break;
            }
          }
        }
        // an em (single-char) formation is also disqualified when
        // the span holds an unmatched single-char run of the same
        // delimiter: marked's em match cannot skip over a bare
        // one-char run inside its content. An opener rejected this
        // way can never match a later closer either (any later span
        // would contain the same run), so it dies here and stops
        // poisoning outer matches.
        let blockedR3 = false;
        if (!blocked && d.ch !== '~' &&
            !(o.n >= 2 && d.n >= 2)) {
          for (let j = oi + 1; j < ci; j++) {
            const x = nodes[j];
            if (x.k === 'delim' && x.ch === d.ch && x.n === 1 && !x.dead &&
                (x.canOpen || x.canClose)) { blocked = true; blockedR3 = true; break; }
          }
        }
        // a closer that just formed an em out of its own run cannot
        // close an outer opener when the span also holds an earlier
        // wrap of the other kind (the *b*other *c** pileup)
        if (!blocked && d.justKind === 1) {
          const okind = o.orig >= 2 ? 2 : 1;
          for (let j = oi + 1; j < ci - 1; j++) {
            const x = nodes[j];
            if ((x.k === 'em' || x.k === 'strong') && x.ch === d.ch &&
                (x.k === 'strong' ? 2 : 1) !== okind) {
              const after = nodes[j + 1];
              if (after && after.k === 'text' && after.s &&
                  charClass(after.s, 0) === 2) { blocked = true; break; }
            }
          }
        }
        if (blocked) {
          if (blockedR3) { o.canOpen = false; o.dead = true; }
          oi--; continue;
        }
        opener = o; break;
      }
      oi--;
    }
    if (!opener) { ci++; continue; }
    const use = opener.n >= 2 && d.n >= 2 ? 2 : 1;
    d.justKind = use;
    const inner = nodes.splice(oi + 1, ci - oi - 1);
    // a strong closing into a longer run whose excess cannot close
    // any earlier opener renders the excess inside the wrap, right
    // before the closing tag (marked quirk); when an earlier opener
    // is still live the excess stays a delimiter (piggyback)
    if (use === 2 && d.n > 2 && opener.n === 2) {
      let earlier = false;
      for (let j = 0; j < oi; j++) {
        const x = nodes[j];
        if (x.k === 'delim' && x.ch === d.ch && x.canOpen && x.n > 0 && !x.dead) { earlier = true; break; }
      }
      const hasEm = inner.some(x => x.k === 'em' && x.ch === d.ch);
      if (!earlier && hasEm) {
        inner.push({ k: 'text', s: d.ch.repeat(d.n - 2), fin: true });
        d.n = 2;
      }
    }
    const wrap = {
      k: d.ch === '~' ? 'del' : use === 2 ? 'strong' : 'em',
      ch: d.ch,
      children: inner,
    };
    opener.n -= use; d.n -= use;
    nodes.splice(oi + 1, 0, wrap);
    ci = oi + 2;
    if (d.n === 0) nodes.splice(ci, 1);
    if (opener.n === 0) { nodes.splice(oi, 1); ci--; }
  }
  // drop spent delimiters
  for (let i = nodes.length - 1; i >= 0; i--) {
    if (nodes[i].k === 'delim' && nodes[i].n === 0) nodes.splice(i, 1);
  }
}

// Parse "( destination title )" starting at text[i] === '('.
function parseInlineLink(text, i) {
  let j = i + 1;
  const skipWs = () => {
    while (text[j] === ' ' || text[j] === '\t' || text[j] === '\n') j++;
  };
  skipWs();
  let dest = '', title = null;
  if (text.charCodeAt(j) === 41) return { dest, title, end: j + 1 };
  const d = scanDest(text, j);
  if (!d) return null;
  dest = unescapeStr(d.dest); j = d.end;
  const beforeWs = j;
  skipWs();
  if (text.charCodeAt(j) === 41) return { dest, title, end: j + 1 };
  if (j === beforeWs) return null; // a title must follow whitespace
  const t = scanTitle(text, j);
  if (!t) return null;
  title = unescapeStr(t.title); j = t.end;
  skipWs();
  if (text.charCodeAt(j) === 41) return { dest, title, end: j + 1 };
  return null;
}

const AUTOLINK_SCHEME = /^[a-zA-Z][a-zA-Z0-9+.-]{1,31}:/;
const AUTOLINK_EMAIL = /^[a-zA-Z0-9.!#$%&'*+\/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+/;

// Trim an extended autolink candidate per the GFM rules: trailing
// punctuation, unbalanced closing parens, trailing entity shapes.
function trimAutolink(url) {
  let u = url;
  for (;;) {
    if (!u) break;
    const last = u[u.length - 1];
    if ('?!.,:*_~'.includes(last)) { u = u.slice(0, -1); continue; }
    if (last === ';') {
      // an entity-shaped tail is excluded whole; any other trailing
      // semicolon is plain trailing punctuation
      const m = /&(?:#?[a-zA-Z0-9]+);$/.exec(u);
      if (m) { u = u.slice(0, u.length - m[0].length); continue; }
      u = u.slice(0, -1); continue;
    }
    break;
  }
  return u;
}

// Scan a bare www./http(s) URL starting at i. The path is a sequence
// of units: flat parenthesized groups (no parens inside) and single
// characters other than '('. A '(' that cannot start a flat group
// ends the URL — unless another '(' follows inside, in which case
// the first '(' is a plain character. Trailing ')' characters that
// are not a group's closing paren are dropped, as is trailing
// punctuation (see trimAutolink).
function scanBareUrl(text, i) {
  const n = text.length;
  let j = i;
  const pairClose = new Set(); // indices of ')' closing a flat group
  while (j < n) {
    const cc = text.charCodeAt(j);
    if (cc <= 32 || cc === 60) break;
    if (cc === 40) { // (
      let k = j + 1;
      while (k < n) {
        const c2 = text.charCodeAt(k);
        if (c2 === 40 || c2 === 41 || c2 <= 32 || c2 === 60) break;
        k++;
      }
      if (k < n && text.charCodeAt(k) === 41) { pairClose.add(k); j = k + 1; continue; }
      if (k < n && text.charCodeAt(k) === 40) { j++; continue; }
      break;
    }
    j++;
  }
  let end = j;
  for (;;) {
    // drop trailing ')' that did not close a group
    while (end > i && text.charCodeAt(end - 1) === 41 && !pairClose.has(end - 1)) end--;
    const trimmed = trimAutolink(text.slice(i, end));
    if (trimmed.length === end - i) break;
    end = i + trimmed.length;
  }
  return text.slice(i, end);
}

function renderInline(text, refs) {
  const nodes = parseInlineNodes(text, refs);
  return renderNodes(nodes);
}

// marked's link matcher hunts the closing bracket with a scan that
// skips code spans by exact run pairing. A span whose content
// itself contains a backtick ("dirty") is only tolerated when it
// ends the label; an unmatched backtick run is fatal only after a
// real span was skipped. Returns { close, ds, de }: the index of
// the ']' the scan picks (or -1), and the dirty span's extent.
function sloppyClose(text, from) {
  // the scan's universe is the raw label extent: up to the first
  // ']' at raw nesting depth 0 (span searches may not cross it)
  let limit = text.length, d0 = 1;
  for (let k = from; k < text.length; k++) {
    const c = text.charCodeAt(k);
    if (c === 92) { k++; continue; }
    if (c === 91) d0++;
    else if (c === 93) { d0--; if (d0 === 0) { limit = k; break; } }
  }
  let depth = 1, i = from;
  const n = text.length;
  let dirtyEnd = -1, dirtyStart = -1, seenSpan = false, sloppy = false;
  while (i < n) {
    if (i > limit) return { close: -1, ds: dirtyStart, de: dirtyEnd, sloppy };
    const c = text.charCodeAt(i);
    if (c === 92) { i += 2; continue; }
    if (c === 96) {
      let run = 0;
      while (text.charCodeAt(i + run) === 96) run++;
      // pair with the next run of the same length if one exists,
      // else with the next run of any length; a run with no partner
      // at all inside the label kills the link
      let j = i + run, closeAt = -1, closeLen = 0;
      while (j < limit) {
        const idx = text.indexOf('`', j);
        if (idx === -1) break;
        let r2 = 0;
        while (text.charCodeAt(idx + r2) === 96) r2++;
        if (r2 === run) { closeAt = idx; closeLen = r2; break; }
        j = idx + r2;
      }
      if (closeAt === -1) {
        j = text.indexOf('`', i + run);
        if (j === -1 || j >= limit) return { close: -1, ds: dirtyStart, de: dirtyEnd, sloppy };
        closeAt = j; closeLen = 0; sloppy = true;
        while (text.charCodeAt(closeAt + closeLen) === 96) closeLen++;
      }
      seenSpan = true;
      if (text.indexOf('`', i + run) < closeAt) { dirtyStart = i; dirtyEnd = closeAt + closeLen; }
      i = closeAt + closeLen; continue;
    }
    if (c === 91) depth++;
    else if (c === 93) {
      depth--;
      if (depth === 0) {
        return (dirtyEnd === -1 || dirtyEnd === i)
          ? { close: i, ds: -1, de: -1, sloppy }
          : { close: -1, ds: dirtyStart, de: dirtyEnd, sloppy };
      }
    }
    i++;
  }
  return { close: -1, ds: dirtyStart, de: dirtyEnd, sloppy };
}

function parseInlineNodes(text, refs) {
  const nodes = [];
  const brackets = [];
  const spanBlocks = []; // labels killed by a dirty code span
  const formedAt = [];   // srcEnd of every bracket that formed a link/image
  const sloppyLinks = []; // end positions of links whose label paired backticks sloppily
  let bdepth = 0; // raw [ ] nesting depth, as marked's scanner sees it
  // extended autolinks do not form inside link text in marked, nor
  // anywhere after an unclosed inline <a> tag (document-wide state)
  const linkState = refs.inLinkState;
  // extended autolinks are only suppressed by the document-wide
  // in-link state; inside brackets they form provisionally and are
  // unwound if the enclosing link actually forms (see tryFormLink)
  const insideLinkText = () => !!(linkState && linkState.inLink);
  const n = text.length;
  let buf = '';
  let i = 0;

  const flushText = () => {
    if (buf) { nodes.push({ k: 'text', s: buf }); buf = ''; }
  };

  // --- link formation at a ']' (index closeIdx) ---
  function tryFormLink(op, closeIdx) {
    const after = closeIdx + 1;
    let dest = null, title = null, end = -1;
    if (text.charCodeAt(after) === 40) {
      const p = parseInlineLink(text, after);
      if (p) { dest = p.dest; title = p.title; end = p.end; }
    }
    if (end === -1 && text.charCodeAt(after) === 91) {
      // full or collapsed reference
      let j = after + 1, labEnd = -1;
      while (j < n) {
        const c = text.charCodeAt(j);
        if (c === 92) { j += 2; continue; }
        if (c === 91) break;
        if (c === 93) { labEnd = j; break; }
        j++;
      }
      if (labEnd !== -1) {
        const lab = text.slice(after + 1, labEnd);
        if (lab === '') {
          const ref = refs.get(normalizeLabel(text.slice(op.srcEnd, closeIdx)));
          if (ref) { dest = ref.dest; title = ref.title; end = labEnd + 1; }
        } else {
          const ref = refs.get(normalizeLabel(lab));
          if (ref) { dest = ref.dest; title = ref.title; end = labEnd + 1; }
          else return false; // a label was given and missed: no shortcut
        }
      }
    }
    if (end === -1) {
      const ref = refs.get(normalizeLabel(text.slice(op.srcEnd, closeIdx)));
      if (ref) { dest = ref.dest; title = ref.title; end = after; }
    }
    if (end === -1) return false;

    flushText();
    const opIdx = nodes.indexOf(op.node);
    // links may not contain links (images may): an outer link whose
    // text already holds a link does not form
    if (!op.image) {
      for (let k = opIdx + 1; k < nodes.length; k++) {
        if (nodes[k].k === 'link') return false;
      }
    }
    const children = nodes.splice(opIdx + 1);
    // extended autolinks do not exist inside a formed link's text:
    // unwind them back to plain text (angle autolinks stay)
    for (let k = 0; k < children.length; k++) {
      const nd = children[k];
      if (nd.k === 'autolink' && nd.ext) children[k] = { k: 'text', s: nd.text };
    }
    processEmphasis(children);
    let node;
    if (op.image) {
      node = { k: 'image', src: dest, title, alt: plainText(children) };
    } else {
      node = { k: 'link', href: dest, title, children };
    }
    nodes.splice(opIdx, 1);
    nodes.push(node);
    // a formed link deactivates every earlier link opener
    if (!op.image) {
      for (const b of brackets) if (!b.image) b.active = false;
    }
    const bi = brackets.indexOf(op);
    if (bi !== -1) brackets.length = bi;
    formedAt.push(op.srcEnd);
    if (op.sloppyFlag) sloppyLinks.push(end);
    i = end;
    return true;
  }

  while (i < n) {
    const c = text.charCodeAt(i);

    if (c === 92) { // backslash
      const d = text.charCodeAt(i + 1);
      if (d === 10) {
        flushText(); nodes.push({ k: 'br' }); i += 2;
        // marked drops the next line's indentation after a hard break
        while (text.charCodeAt(i) === 32 || text.charCodeAt(i) === 9) i++;
        continue;
      }
      if (isAsciiPunct(d)) {
        if (d === 38 || d === 60 || d === 62 || d === 34 || d === 39) {
          flushText();
          nodes.push({ k: 'text', s: escapeDecodedChar(text[i + 1]), fin: true });
        } else buf += text[i + 1];
        i += 2; continue;
      }
      buf += '\\'; i++; continue;
    }

    if (c === 96) { // code span
      let run = 0;
      while (text.charCodeAt(i + run) === 96) run++;
      // inside a viable label the span may not cross the label's
      // closing bracket (marked matches the link before tokenizing
      // the label's interior)
      let searchEnd = n;
      if (brackets.length) {
        const op = brackets[brackets.length - 1];
        if (op.active) {
          const sc = sloppyClose(text, op.srcEnd);
          if (sc.close !== -1) searchEnd = sc.close;
        }
      }
      let j = i + run, closeAt = -1;
      while (j < searchEnd) {
        const idx = text.indexOf('`', j);
        if (idx === -1 || idx >= searchEnd) break;
        let r2 = 0;
        while (text.charCodeAt(idx + r2) === 96) r2++;
        if (r2 === run) { closeAt = idx; break; }
        j = idx + r2;
      }
      if (closeAt === -1) { buf += text.slice(i, i + run); i += run; continue; }
      flushText();
      let content = text.slice(i + run, closeAt).replace(/\n/g, ' ');
      if (content.length > 1 && content.charCodeAt(0) === 32 &&
          content.charCodeAt(content.length - 1) === 32 && /[^ ]/.test(content)) {
        content = content.slice(1, -1);
      }
      nodes.push({ k: 'code', s: content });
      i = closeAt + run; continue;
    }

    if (c === 60) { // '<': comment / cdata / pi / declaration / autolink / tag
      let done = false;
      if (text.startsWith('<!--', i)) {
        if (text.startsWith('<!-->', i) || text.startsWith('<!--->', i)) {
          flushText();
          nodes.push({ k: 'html', s: text.startsWith('<!-->', i) ? '<!-->' : '<!--->' });
          i += text.startsWith('<!-->', i) ? 5 : 6; done = true;
        } else {
          const e = text.indexOf('-->', i + 4);
          if (e !== -1) { flushText(); nodes.push({ k: 'html', s: text.slice(i, e + 3) }); i = e + 3; done = true; }
        }
      } else if (text.startsWith('<![CDATA[', i)) {
        const e = text.indexOf(']]>', i + 9);
        if (e !== -1) { flushText(); nodes.push({ k: 'html', s: text.slice(i, e + 3) }); i = e + 3; done = true; }
      } else if (text.startsWith('<?', i)) {
        const e = text.indexOf('?>', i + 2);
        if (e !== -1) { flushText(); nodes.push({ k: 'html', s: text.slice(i, e + 2) }); i = e + 2; done = true; }
      } else if (text.charCodeAt(i + 1) === 33 && isAlpha(text.charCodeAt(i + 2))) {
        const e = text.indexOf('>', i + 2);
        if (e !== -1) { flushText(); nodes.push({ k: 'html', s: text.slice(i, e + 1) }); i = e + 1; done = true; }
      }
      if (!done) {
        // autolink <scheme:...> or <email>
        const gt = text.indexOf('>', i + 1);
        if (gt !== -1 && gt - i < 200) {
          const inner = text.slice(i + 1, gt);
          if (!/[\s<>]/.test(inner)) {
            if (AUTOLINK_SCHEME.test(inner)) {
              flushText();
              nodes.push({ k: 'autolink', href: inner, text: inner });
              i = gt + 1; done = true;
            } else if (AUTOLINK_EMAIL.test(inner) && AUTOLINK_EMAIL.exec(inner)[0] === inner) {
              flushText();
              nodes.push({ k: 'autolink', href: 'mailto:' + inner, text: inner });
              i = gt + 1; done = true;
            }
          }
        }
      }
      if (!done) {
        const e = parseHtmlTag(text, i);
        if (e !== -1) {
          flushText();
          const tagText = text.slice(i, e);
          nodes.push({ k: 'html', s: tagText });
          // an inline <a> tag switches marked's in-link state for
          // the rest of the document (and </a> switches it off);
          // while it is on, extended autolinks do not form
          if (linkState && brackets.length === 0) {
            const tm = /^<(\/?)([a-zA-Z][a-zA-Z0-9-]*)/.exec(tagText);
            if (tm && tm[2].toLowerCase() === 'a') {
              if (tm[1] === '/') linkState.inLink = false;
              // an <a> switches the state on only when a space
              // follows the tag name (an attribute area, even an
              // empty one); <a>, <a/> and <a\t/> do not
              else if (tagText.charCodeAt(tm[0].length) === 32) linkState.inLink = true;
            }
          }
          i = e; done = true;
        }
      }
      if (!done) { buf += '<'; i++; }
      continue;
    }

    if (c === 33 && text.charCodeAt(i + 1) === 91) { // ![
      flushText();
      const nd = { k: 'open', image: true };
      nodes.push(nd);
      brackets.push({ node: nd, image: true, active: true, srcEnd: i + 2, depth: ++bdepth });
      i += 2; continue;
    }
    if (c === 91) { // [
      flushText();
      const nd = { k: 'open', image: false };
      nodes.push(nd);
      brackets.push({ node: nd, image: false, active: true, srcEnd: i + 1, depth: ++bdepth });
      i++; continue;
    }
    if (c === 93) { // ]
      // only an opener at the current raw nesting depth can close
      let formed = false;
      for (let oi = brackets.length - 1; oi >= 0; oi--) {
        const op = brackets[oi];
        if (op.depth !== bdepth) continue;
        if (!op.active) break;
        // when the text holds backticks, marked's own bracket scan
        // must pick this very ']' or the link cannot form here
        const tick = text.indexOf('`', op.srcEnd);
        if (tick !== -1 && tick < i) {
          const sc = sloppyClose(text, op.srcEnd);
          if (sc.close !== i) {
            // the emphasis suppression applies only to the
            // inline-link form '](...)', not to shortcut or
            // reference brackets
            if (sc.ds !== -1 && text.charCodeAt(i + 1) === 40) {
              spanBlocks.push({ from: op.srcEnd, to: i, ds: sc.ds, de: sc.de });
            }
            if (sc.close === -1) op.active = false; // marked gives up on it
            break;
          }
          op.sloppyFlag = sc.sloppy;
        }
        if (tryFormLink(op, i)) formed = true;
        else op.active = false;
        break;
      }
      bdepth--;
      if (!formed) { buf += ']'; i++; }
      continue;
    }

    if (c === 42 || c === 95 || c === 126) { // * _ ~
      let run = 0;
      while (text.charCodeAt(i + run) === c) run++;
      // marked: tilde runs of 3+ never form strikethrough
      if (c === 126 && run >= 3) { buf += text.slice(i, i + run); i += run; continue; }
      const prevCls = charClass(text, i - 1);
      const nextCls = charClass(text, i + run);
      const leftFl = nextCls !== 0 && (nextCls !== 1 || prevCls !== 2);
      const rightFl = prevCls !== 0 && (prevCls !== 1 || nextCls !== 2);
      let canOpen, canClose;
      if (c === 95) {
        canOpen = leftFl && (!rightFl || prevCls === 1);
        canClose = rightFl && (!leftFl || nextCls === 1);
      } else {
        canOpen = leftFl; canClose = rightFl;
      }
      flushText();
      nodes.push({ k: 'delim', ch: text[i], n: run, orig: run, canOpen, canClose,
                   poison: prevCls !== 2, pos: i });
      i += run; continue;
    }

    if (c === 10) { // newline: hard break on 2+ trailing spaces
      let sp = 0;
      while (buf.charCodeAt(buf.length - 1 - sp) === 32) sp++;
      if (sp >= 2) {
        buf = buf.slice(0, buf.length - sp);
        flushText();
        nodes.push({ k: 'br' });
        i++;
        // marked drops the next line's indentation after a hard break
        while (text.charCodeAt(i) === 32 || text.charCodeAt(i) === 9) i++;
      } else { buf += '\n'; i++; }
      continue;
    }

    // extended autolinks starting here (www. / http:// / https://);
    // the scheme matches case-insensitively, www. does not
    if ((c === 119 || c === 104 || c === 72) && !insideLinkText() &&
        (i === 0 || charClass(text, i - 1) !== 2)) {
      const isWww = text.startsWith('www.', i);
      const head8 = text.slice(i, i + 8).toLowerCase();
      const isHttp = head8.startsWith('http://') || head8.startsWith('https://');
      if (isWww || isHttp) {
        let url = scanBareUrl(text, i);
        // inside a still-viable label the autolink must stop at the
        // label's closing bracket (it is unwound when the link
        // forms); in a label already doomed by a dirty code span it
        // may swallow the bracket, as marked's does
        if (url && brackets.length) {
          const op = brackets[brackets.length - 1];
          if (op.active) {
            const sc = sloppyClose(text, op.srcEnd);
            if (sc.close !== -1) {
              if (i + url.length > sc.close) url = text.slice(i, sc.close);
              // nor may it cross an inline-structural character:
              // the label's own tokenization still applies there
              const cut = url.search(/[*_~`[]/);
              if (cut !== -1) {
                url = url.slice(0, cut);
                for (;;) {
                  const t2 = trimAutolink(url);
                  if (t2.length === url.length) break;
                  url = t2;
                }
              }
            }
          }
        }
        // the part after www. must contain a dot to be a domain
        if (url && (!isWww || url.slice(4).includes('.'))) {
          flushText();
          nodes.push({ k: 'autolink', href: isWww ? 'http://' + url : url, text: url, ext: true });
          i += url.length; continue;
        }
      }
    }

    // plain run (extended email / mailto: / xmpp: autolinks are
    // attempted at their starting position inside the run)
    {
      let j = i;
      while (j < n) {
        const cc = text.charCodeAt(j);
        if (cc === 92 || cc === 96 || cc === 60 || cc === 91 || cc === 93 ||
            cc === 42 || cc === 95 || cc === 126 || cc === 10) break;
        if (cc === 33 && text.charCodeAt(j + 1) === 91) break;
        if (j > i && !insideLinkText() &&
            ((cc === 119 && text.startsWith('www.', j)) ||
             ((cc === 104 || cc === 72) &&
              /https?:\/\//i.test(text.slice(j, j + 8))))) break;
        // an autolink can only start where the previous character is
        // not part of an email local part (and not an '@')
        if ((isEmailLocal(cc) || cc === 109 || cc === 120) && !insideLinkText() &&
            (j === i || (!isEmailLocal(text.charCodeAt(j - 1)) &&
                         text.charCodeAt(j - 1) !== 64))) {
          // unmatched '_' openers so far (for the trailing-underscore
          // emphasis-closer exception in email domains)
          let uAvail = 0;
          for (const nd of nodes) {
            if (nd.k !== 'delim' || nd.ch !== '_' || nd.pos === undefined || nd.pos >= j) continue;
            if (nd.canOpen && !nd.canClose) uAvail += nd.n;
            else if (nd.canClose && !nd.canOpen) uAvail -= nd.n;
          }
          const m = matchExtendedAutolink(text, j, Math.max(0, uAvail));
          if (m) {
            buf += text.slice(i, j);
            flushText();
            nodes.push({ k: 'autolink', href: m.href, text: m.text, ext: true });
            i = m.end;
            j = -1; // signal: handled
            break;
          }
        }
        j++;
      }
      if (j === -1) continue; // email autolink emitted
      if (j === i) { buf += text[i]; i++; }
      else { buf += text.slice(i, j); i = j; }
      continue;
    }
  }

  flushText();
  // a label killed by a dirty code span also loses any emphasis
  // that straddles the span (unless an inner link formed, which
  // rescues the label's emphasis wholesale)
  for (const b of spanBlocks) {
    if (formedAt.some(p => p > b.from && p <= b.to)) continue;
    for (const nd of nodes) {
      if (nd.k !== 'delim' || nd.pos === undefined) continue;
      if (nd.pos >= b.from && nd.pos <= b.to) { nd.canOpen = false; nd.canClose = false; }
    }
  }
  // after a link whose label paired its backticks sloppily, every
  // later delimiter run that still has a backtick after it in the
  // same inline text is inert in marked
  if (sloppyLinks.length) {
    const from = Math.min(...sloppyLinks);
    for (const nd of nodes) {
      if (nd.k !== 'delim' || nd.pos === undefined) continue;
      if (nd.pos >= from && text.indexOf('`', nd.pos) !== -1) {
        nd.canOpen = false; nd.canClose = false;
      }
    }
  }
  processEmphasis(nodes);
  return nodes;
}

function isEmailLocal(c) {
  return isAlnum(c) || c === 46 || c === 33 || c === 35 || c === 36 ||
    c === 37 || c === 38 || c === 39 || c === 42 || c === 43 || c === 47 ||
    c === 61 || c === 63 || c === 94 || c === 95 || c === 96 || c === 123 ||
    c === 124 || c === 125 || c === 126 || c === 45;
}

// Match an extended email address starting at text[i] (the first
// local-part character). Returns { email, end } or null. The domain
// needs at least one dot and well-formed labels; trailing dots are
// left outside the link, while a following '_' kills the match.
function scanEmailAt(text, i, underscoreAvail = 0) {
  let j = i;
  while (j < text.length && isEmailLocal(text.charCodeAt(j))) j++;
  if (j === i || text.charCodeAt(j) !== 64) return null;
  const local = text.slice(i, j);
  let k = j + 1;
  const dStart = k;
  while (k < text.length) {
    const c = text.charCodeAt(k);
    if (isAlnum(c) || c === 45 || c === 46 || c === 95) k++; else break;
  }
  let dEnd = k;
  while (dEnd > dStart && text.charCodeAt(dEnd - 1) === 46) dEnd--;
  // a domain ending in '-' never links; one ending in '_' links
  // only when those underscores are an emphasis closer (an earlier
  // unmatched '_' opener exists), and they stay outside the link
  const last = text.charCodeAt(dEnd - 1);
  if (last === 45) return null;
  if (last === 95) {
    let runStart = dEnd;
    while (runStart > dStart && text.charCodeAt(runStart - 1) === 95) runStart--;
    if (dEnd - runStart > underscoreAvail) return null;
    dEnd = runStart;
  }
  const domain = text.slice(dStart, dEnd);
  if (!/^[a-zA-Z0-9_-]+(?:\.[a-zA-Z0-9_-]+)+$/.test(domain)) return null;
  return { email: local + '@' + domain, end: dEnd };
}

// Extended autolinks: a bare email, or mailto:/xmpp: followed by an
// email and an optional one-segment path.
function matchExtendedAutolink(text, i, underscoreAvail = 0) {
  let scheme = 0;
  if (text.startsWith('mailto:', i)) scheme = 7;
  else if (text.startsWith('xmpp:', i)) scheme = 5;
  if (scheme) {
    const em = scanEmailAt(text, i + scheme, underscoreAvail);
    if (!em) return null;
    let end = em.end;
    // only xmpp: links may carry one non-empty path segment
    if (scheme === 5 && text.charCodeAt(end) === 47) {
      let k = end + 1;
      while (k < text.length) {
        const c = text.charCodeAt(k);
        if (c <= 32 || c === 47 || c === 60) break;
        k++;
      }
      if (k > end + 1) end = k;
    }
    const t = text.slice(i, end);
    return { href: t, text: t, end };
  }
  const em = scanEmailAt(text, i, underscoreAvail);
  if (em) return { href: 'mailto:' + em.email, text: em.email, end: em.end };
  return null;
}

export { parse };
