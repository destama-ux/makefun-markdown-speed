// main.ts — the harness driver for markdown-render-speed-02.
// Reads every case from the input folder's cases.json, renders each
// with parse() from ./parse.js, and writes the HTML strings, in the
// cases' order, to the output folder's html.json.
//
// The input folder is /input (or $MAKEFUN_INPUT_DIR when set) and the
// output folder is /output (or $MAKEFUN_OUTPUT_DIR when set).

import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR || '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR || '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8'));
const out = new Array(cases.length);
for (let i = 0; i < cases.length; i++) {
  out[i] = parse(cases[i].markdown);
}
mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(out));
