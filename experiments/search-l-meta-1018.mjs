// L-meta-1018: regenerates the checked 166-row instance.
// node search-l-meta-1018.mjs --emit
// cadical -q --lrat --checkproof=0 line-and-1018.cnf line-and-1018.lratb
// lean --run CheckPrismLrat.lean line-and-1018.cnf line-and-1018.lratb
// Checker: https://github.com/gperdigao/pequalnp-proofs/blob/efdc360d610762129ca05fc490a68eb7f39ad163/experiments/CheckPrismLrat.lean
// CNF SHA-256: fea81e04380ff68458d1f1f7d44987b84a56b1518bdb2fad3b722c34b793c6fa
// Local verification: 68,387 clauses, 238,451 LRAT actions.
// This certificate checks the encoded CNF. The reduction from the posted
// Lean theorem to this encoding is described below and is not formalized.

import { spawnSync } from 'node:child_process';
import { writeFileSync } from 'node:fs';

// Use --emit to generate the first instance without starting a solver.
const generateOnly = process.argv.includes('--emit');

const vertices = 13;
const gateCount = 8;
const lines = [[0, 1, 3, 9], [1, 2, 4, 10], [2, 3, 5, 11]];
const masks = lines.map(line => line.reduce((mask, vertex) => mask | (1 << vertex), 0));
const membership = Array.from({ length: vertices }, (_, vertex) =>
  masks.reduce((key, mask, i) => key | ((mask >> vertex) & 1) << i, 0));
function popcount(value) {
  let count = 0;
  while (value) {
    value &= value - 1;
    count++;
  }
  return count;
}
const rows = Array.from({ length: 1 << vertices }, (_, mask) => mask)
  .filter(mask => popcount(mask) === 6 || popcount(mask) === 7);
const samples = new Set();
for (const line of masks) {
  const positive = rows.filter(row => popcount(row) === 7 && (row & line) === line);
  for (let i = 0; i < positive.length; i += 7) {
    samples.add(positive[i]);
    for (let bits = line; bits; bits &= bits - 1) samples.add(positive[i] ^ (bits & -bits));
  }
}

function encode(sample) {
  let count = 0;
  const clauses = [];
  const next = () => ++count;
  const add = (...literals) => clauses.push(literals);
  const one = choices => {
    add(...choices);
    for (let i = 0; i < choices.length; i++) {
      for (let j = 0; j < i; j++) add(-choices[i], -choices[j]);
    }
  };
  const gateChoices = Array.from({ length: gateCount }, (_, i) => ({
    or: next(), left: Array.from({ length: vertices + i }, next), right: Array.from({ length: vertices + i }, next),
  }));
  const outputs = masks.map(() => gateChoices.map(next));
  for (const { left, right } of gateChoices) {
    one(left);
    one(right);
    for (let i = 0; i < left.length; i++) {
      for (let j = 0; j < i; j++) add(-left[i], -right[j]);
    }
  }
  for (const choices of outputs) one(choices);
  // The three lines are symmetric. Keep only circuits whose last gate is
  // output zero, padding a shorter circuit on that output with identities.
  add(outputs[0].at(-1));
  for (const selection of outputs) {
    // Each of the four line points is essential even on the two layers.
    add(-selection[0]);
    add(-selection[1]);
  }
  for (let i = 0; i + 1 < gateCount; i++) {
    const wire = vertices + i;
    add(...outputs.map(selection => selection[i]),
      ...gateChoices.slice(i + 1).flatMap(({ left, right }) => [left[wire], right[wire]]));
  }
  // Permuting points with the same membership preserves every output.
  // A minimum nonconstant circuit starts with two distinct inputs.
  for (let a = 0; a < vertices; a++) {
    const firstOfA = membership.indexOf(membership[a]);
    for (let b = a; b < vertices; b++) {
      const firstOfB = membership.indexOf(membership[b]);
      const chosenB = membership[a] === membership[b] ? membership.indexOf(membership[b], a + 1) : firstOfB;
      if (a === b || a !== firstOfA || b !== chosenB) add(-gateChoices[0].left[a], -gateChoices[0].right[b]);
    }
  }

  for (const mask of sample) {
    const values = gateChoices.map(next);
    for (const [i, gate] of gateChoices.entries()) {
      const a = next();
      const b = next();
      for (const [selectors, operand] of [[gate.left, a], [gate.right, b]]) {
        for (const [wire, selector] of selectors.entries()) {
          if (wire < vertices) add(-selector, mask & (1 << wire) ? operand : -operand);
          else {
            const value = values[wire - vertices];
            add(-selector, -value, operand);
            add(-selector, value, -operand);
          }
        }
      }
      const value = values[i];
      add(gate.or, -a, -b, value);
      add(gate.or, a, -value);
      add(gate.or, b, -value);
      add(-gate.or, a, b, -value);
      add(-gate.or, -a, value);
      add(-gate.or, -b, value);
    }
    for (const [i, selectors] of outputs.entries()) {
      const expected = (mask & masks[i]) === masks[i];
      for (const [g, selector] of selectors.entries()) add(-selector, expected ? values[g] : -values[g]);
    }
  }
  const dimacs = `p cnf ${count} ${clauses.length}\n${clauses.map(clause => `${clause.join(' ')} 0`).join('\n')}\n`;
  return { dimacs, gateChoices, outputs, count, clauses: clauses.length };
}

for (let round = 0; round < 2; round++) {
  const model = encode(samples);
  writeFileSync('line-and-1018.cnf', model.dimacs);
  if (generateOnly) {
    console.log(JSON.stringify({ rows: samples.size, variables: model.count, clauses: model.clauses }));
    break;
  }
  const run = spawnSync('./lean-4.36.0-windows/bin/cadical.exe', ['-q', '-c', '300000', 'line-and-1018.cnf'],
    { timeout: 42000, encoding: 'utf8' });
  if (run.error && run.error.code !== 'ETIMEDOUT') throw run.error;
  console.log(JSON.stringify({ round, rows: samples.size, variables: model.count, clauses: model.clauses,
    result: run.stdout?.split(/\r?\n/)[0], timeout: run.error?.code === 'ETIMEDOUT' }));
  if (run.status !== 10) break;
  const enabled = new Set(run.stdout.split(/\r?\n/).filter(line => line.startsWith('v '))
    .flatMap(line => line.slice(2).split(/\s+/).map(Number)).filter(literal => literal > 0));
  const gates = model.gateChoices.map(({ or, left, right }) => ({
    or: enabled.has(or), a: left.findIndex(lit => enabled.has(lit)), b: right.findIndex(lit => enabled.has(lit)),
  }));
  const outputs = model.outputs.map(selectors => vertices + selectors.findIndex(lit => enabled.has(lit)));
  const failures = rows.filter(mask => {
    const values = Array.from({ length: vertices }, (_, i) => Boolean(mask & (1 << i)));
    for (const { or, a, b } of gates) values.push(or ? values[a] || values[b] : values[a] && values[b]);
    return outputs.some((wire, i) => values[wire] !== ((mask & masks[i]) === masks[i]));
  });
  if (failures.length === 0) {
    console.log(JSON.stringify({ gates, outputs, checked: rows.length }));
    break;
  }
  for (let i = 0; i < failures.length; i += Math.max(1, Math.floor(failures.length / 20))) samples.add(failures[i]);
}
