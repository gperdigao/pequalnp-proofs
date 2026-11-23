// L-meta-906. Run with Node as described by the usage message.
// The default bound for each shard is the proposed optimum minus one.
// CaDiCaL 2.1.2 can emit a binary LRAT certificate using
// cadical -q --lrat --checkproof=0 INPUT.cnf OUTPUT.lratb
// The Lean LRAT checker used for these results is available at:
// https://github.com/gperdigao/pequalnp-proofs/blob/efdc360d610762129ca05fc490a68eb7f39ad163/experiments/CheckPrismLrat.lean
// The encoded model follows PEqualNP.Defs.AndCountCircuit and covers the
// maximal independent sets and their one-vertex extensions. The CNF
// reductions are described here for review, rather than embedded in Lean.

import { writeFileSync } from 'node:fs';

const shards = [
  { vertices: 6, bound: 3, edges: [[0, 1], [1, 2], [0, 2], [3, 4], [4, 5], [3, 5]] },
  { vertices: 5, bound: 2, edges: [[0, 1], [1, 2], [2, 3], [3, 4], [4, 0]] },
  { vertices: 7, bound: 2, edges: [[0, 2], [0, 3], [1, 3], [1, 4], [2, 4], [2, 5], [3, 5], [3, 6], [4, 6], [4, 0], [5, 0], [5, 1], [6, 1], [6, 2]] },
];

const arg = process.argv[2];
if (!/^[0-2]$/.test(arg ?? '')) throw new Error('Usage: node generate-and-count-shard.mjs <0|1|2> [path] [bound]');
const { vertices, edges, bound } = shards[Number(arg)];
const gates = process.argv[4] === undefined ? bound : Number(process.argv[4]);
if (!Number.isInteger(gates) || gates < 0 || gates > 4) throw new Error('Expected an AND budget between 0 and 4');

const masks = edges.map(([a, b]) => (1 << a) | (1 << b));
const independent = row => masks.every(mask => (mask & row) !== mask);
const rows = new Map();
for (let row = 0; row < 1 << vertices; row++) {
  if (!independent(row)) continue;
  const extensions = [];
  for (let v = 0; v < vertices; v++) {
    if ((row & (1 << v)) === 0) extensions.push(row | (1 << v));
  }
  if (extensions.some(independent)) continue;
  rows.set(row, false);
  for (const extended of extensions) rows.set(extended, true);
}

let variableCount = 0;
const clauses = [];
const fresh = () => ++variableCount;
const add = (...literals) => clauses.push(literals);
const allocateSide = available => Array.from({ length: available }, fresh);
// Smaller circuits can be padded using unused gates with two empty sides.
const circuits = Array.from({ length: gates }, (_, gate) =>
  [allocateSide(vertices + gate), allocateSide(vertices + gate)]);
const outputChoices = allocateSide(vertices + gates);

function encodeSide(choices, row, earlier) {
  const value = fresh();
  const terms = [];
  for (const [wire, choice] of choices.entries()) {
    if (wire < vertices) {
      if (row & (1 << wire)) terms.push(choice);
      continue;
    }
    const source = earlier[wire - vertices];
    const enabled = fresh();
    add(-enabled, choice);
    add(-enabled, source);
    add(-choice, -source, enabled);
    terms.push(enabled);
  }
  for (const term of terms) add(-term, value);
  add(-value, ...terms);
  return value;
}

for (const [row, target] of rows) {
  const gateValues = [];
  for (const [left, right] of circuits) {
    const a = encodeSide(left, row, gateValues);
    const b = encodeSide(right, row, gateValues);
    const value = fresh();
    add(-value, a);
    add(-value, b);
    add(-a, -b, value);
    gateValues.push(value);
  }
  const value = encodeSide(outputChoices, row, gateValues);
  add(target ? value : -value);
}

const path = process.argv[3] ?? `and-count-${arg}-${gates}.cnf`;
writeFileSync(path, `p cnf ${variableCount} ${clauses.length}\n${clauses.map(clause => `${clause.join(' ')} 0`).join('\n')}\n`);
console.log(JSON.stringify({ shard: Number(arg), gates, rows: rows.size, variables: variableCount, clauses: clauses.length }));
