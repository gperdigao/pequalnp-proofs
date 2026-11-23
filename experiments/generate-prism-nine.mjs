// Reproduce with Node.js, CaDiCaL 2.1.2 and Lean 4.36.0:
// node generate-prism-nine.mjs prism-nine.cnf
// cadical -q --lrat --checkproof=0 prism-nine.cnf prism-nine.lratb
// lean --run CheckPrismLrat.lean prism-nine.cnf prism-nine.lratb
// CaDiCaL exits with status 20 for UNSAT. The checker validates the
// certificate for this CNF. The reduction from circuits to the CNF is
// explained by the constraints below and is not formalized in Lean here.

import { writeFileSync } from 'node:fs';

// A DIMACS encoding for nine-gate AND/OR circuits computing the edge
// function of the triangular prism. Input wires are numbered 0 through 5.
// The encoding is for minimal circuits. The separate Lean lower bound of
// nine gates means any circuit with at most nine gates must be minimal.
const inputCount = 6;
const gateCount = 9;
const edges = [[0, 1], [1, 2], [0, 2], [3, 4], [4, 5], [3, 5], [0, 3], [1, 4], [2, 5]];
const inputMasks = Array.from({ length: inputCount }, (_, input) => 1 << input);
const edgeMasks = edges.map(([a, b]) => inputMasks[a] | inputMasks[b]);
const target = mask => edgeMasks.some(edge => (mask & edge) === edge);
const boundary = [...edgeMasks];
for (let mask = 0; mask < 1 << inputCount; mask++) {
  if (!target(mask) && inputMasks.every(bit => (mask & bit) !== 0 || target(mask | bit))) {
    boundary.push(mask);
  }
}

let variableCount = 0;
const clauses = [];
const fresh = () => ++variableCount;
const add = (...literals) => clauses.push(literals);
function exactlyOne(choices) {
  add(...choices);
  for (let i = 0; i < choices.length; i++) {
    for (let j = i + 1; j < choices.length; j++) add(-choices[i], -choices[j]);
  }
}

const gates = Array.from({ length: gateCount }, (_, index) => {
  const available = inputCount + index;
  return { or: fresh(), left: Array.from({ length: available }, fresh), right: Array.from({ length: available }, fresh) };
});
for (const { left, right } of gates) {
  exactlyOne(left);
  exactlyOne(right);
  // A repeated operand gives a redundant gate. Operand order is immaterial.
  for (let a = 0; a < left.length; a++) {
    for (let b = 0; b <= a; b++) add(-left[a], -right[b]);
  }
}

// Equality in the verified L-meta-614 branching count leaves at most two
// readers per wire. Track whether at least one or two readers have been seen.
const hasTwoReaders = [];
for (let wire = 0; wire < inputCount + gateCount - 1; wire++) {
  const readers = gates.flatMap(({ left, right }) => wire < left.length ? [left[wire], right[wire]] : []);
  let one;
  let two;
  for (const reader of readers) {
    const nextOne = fresh();
    const nextTwo = fresh();
    add(-reader, nextOne);
    if (one === undefined) {
      add(-nextOne, reader);
      add(-nextTwo);
    } else {
      add(-one, nextOne);
      add(-nextOne, one, reader);
      add(-one, -reader, nextTwo);
      add(-two, nextTwo);
      add(-nextTwo, two, one);
      add(-nextTwo, two, reader);
      add(-two, -reader);
    }
    one = nextOne;
    two = nextTwo;
  }
  hasTwoReaders.push(two);
}

// If a primary input has one reader, that gate cannot read a second primary
// input. AND would block all other neighbors. OR would imply neighborhood
// containment outside the pair, which never occurs in the triangular prism.
for (const { left, right } of gates) {
  for (let a = 0; a < inputCount; a++) {
    for (let b = a + 1; b < inputCount; b++) {
      add(-left[a], -right[b], hasTwoReaders[a]);
      add(-left[a], -right[b], hasTwoReaders[b]);
    }
  }
}

// Choose the lexicographically first list of sorted operands over all
// topological orders and input relabelings preserving the graph.
for (let i = 0; i + 1 < gates.length; i++) {
  const a = gates[i];
  const b = gates[i + 1];
  const dependsOnA = b.right[inputCount + i];
  for (let u = 1; u < a.left.length; u++) {
    for (let v = 0; v < u; v++) add(-a.left[u], -b.left[v], dependsOnA);
  }
}
for (let i = 0; i < gateCount - 1; i++) {
  const wire = inputCount + i;
  add(...gates.slice(i + 1).flatMap(({ left, right }) => [left[wire], right[wire]]));
}
for (let wire = 0; wire < inputCount; wire++) {
  add(...gates.flatMap(({ left, right }) => [left[wire], right[wire]]));
}
const firstPairs = new Set(['0,0', '0,1', '0,3', '0,4']);
for (let a = 0; a < inputCount; a++) {
  for (let b = a; b < inputCount; b++) {
    if (!firstPairs.has(`${a},${b}`)) add(-gates[0].left[a], -gates[0].right[b]);
  }
}

// For a monotone function, the minimal true and maximal false assignments
// determine the entire truth table. Encode wire values on just these rows.
const boundaryOutputs = [];
for (const mask of boundary) {
  const outputs = gates.map(fresh);
  boundaryOutputs.push(outputs);
  for (const [i, gate] of gates.entries()) {
    const leftValue = fresh();
    const rightValue = fresh();
    for (const [choices, value] of [[gate.left, leftValue], [gate.right, rightValue]]) {
      for (const [wire, choice] of choices.entries()) {
        if (wire < inputCount) {
          add(-choice, (mask & inputMasks[wire]) !== 0 ? value : -value);
        } else {
          const earlier = outputs[wire - inputCount];
          add(-choice, -value, earlier);
          add(-choice, value, -earlier);
        }
      }
    }
    const output = outputs[i];
    add(gate.or, -leftValue, -rightValue, output);
    add(gate.or, leftValue, -output);
    add(gate.or, rightValue, -output);
    add(-gate.or, leftValue, rightValue, -output);
    add(-gate.or, -leftValue, output);
    add(-gate.or, -rightValue, output);
  }
  add(target(mask) ? outputs.at(-1) : -outputs.at(-1));
}

// Substitution by a constant is safe if it preserves the relevant boundary
// rows and only changes outputs in the safe direction. Equal boundary values
// also allow substitution by an earlier wire. All these gates are redundant.
for (let gate = 0; gate < gateCount; gate++) {
  const values = boundaryOutputs.map(row => row[gate]);
  add(...values.filter((_, i) => target(boundary[i])));
  add(...values.filter((_, i) => !target(boundary[i])).map(value => -value));
  for (let wire = 0; wire < inputCount; wire++) {
    add(...values.map((value, i) => boundary[i] & inputMasks[wire] ? -value : value));
  }
  for (let earlier = 0; earlier < gate; earlier++) {
    const differences = boundaryOutputs.map((row, i) => {
      const difference = fresh();
      add(-difference, values[i], row[earlier]);
      add(-difference, -values[i], -row[earlier]);
      return difference;
    });
    add(...differences);
  }
}

const path = process.argv[2] ?? 'prism-nine.cnf';
const dimacs = `p cnf ${variableCount} ${clauses.length}\n${clauses.map(clause => `${clause.join(' ')} 0`).join('\n')}\n`;
writeFileSync(path, dimacs);
console.log(`${boundary.length} boundary inputs, ${variableCount} variables, ${clauses.length} clauses.`);
