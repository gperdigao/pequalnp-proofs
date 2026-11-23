// Reproduce shard 14 of L-meta-984:
// node generate-atlas-984-shard-14.mjs atlas-984-bowtie-7.cnf --reduced --sensitive
// cadical -q --lrat --checkproof=0 atlas-984-bowtie-7.cnf atlas-984-bowtie-7.lratb
// lean --run CheckPrismLrat.lean atlas-984-bowtie-7.cnf atlas-984-bowtie-7.lratb
// The Lean checker validated 12,415 clauses and 52,173 LRAT actions.
// CNF SHA-256: 43e99f2a0bc742c112e8170de3a0135c36c0c8d2a2adc315cc863fa9971bc7c2
// Certificate SHA-256 (CaDiCaL 2.1.2): 01c7b8a2b4c8c06136bdd4f6a2aae3e798577107388f6142d12268e5cd398b20
// Checker: https://github.com/gperdigao/pequalnp-proofs/blob/efdc360d610762129ca05fc490a68eb7f39ad163/experiments/CheckPrismLrat.lean
// Branching-count theorem: https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_614.lean
// The certificate is for the CNF. The reduction to this instance is described below.

import { writeFileSync } from 'node:fs';

// L-meta-984, desk shard 14 (n7-056). In --reduced mode set input 5 and
// then input 6 to false, obtaining the bowtie on inputs 0 through 4.
// Each restriction removes at least one gate: the input being fixed is
// essential at that stage, and the first gate reading it becomes a constant
// or an alias. Thus a nine-gate circuit would yield a seven-gate bowtie.
// L-meta-614 excludes smaller circuits in both cases by a branching count.
const reduced = process.argv.includes('--reduced');
const inputCount = reduced ? 5 : 7;
const gateCount = reduced ? 7 : 9;
const bowtie = [[0,1],[0,2],[0,3],[0,4],[1,2],[3,4]];
const edges = reduced ? bowtie : [...bowtie, [1,5], [3,6]];
const vertices = Array.from({ length: inputCount }, (_, v) => v);
const adjacent = (a, b) => edges.some(([u, v]) => (a === u && b === v) || (a === v && b === u));
const neighbors = vertices.map(v => vertices.filter(w => adjacent(v, w)));
const eligible = v => neighbors[v].length >= 2;
if (neighbors.some(row => row.length === 0)) throw new Error('Isolated vertex');
for (const v of vertices.filter(eligible)) {
  for (const w of vertices.filter(eligible)) {
    if (v === w) continue;
    if (adjacent(v, w)) {
      if (!neighbors[v].some(a => a !== w && neighbors[w].some(b => b !== v && !adjacent(a, b)))) {
        throw new Error('Missing adjacency witness for the branching bound');
      }
    } else if (!vertices.some(u => adjacent(v, u) !== adjacent(w, u))) {
      throw new Error('Unexpected nonadjacent twins');
    }
  }
}
const relevantEdges = edges.filter(([a, b]) => eligible(a) && eligible(b));
const covers = Array.from({ length: 1 << inputCount }, (_, mask) => mask)
  .filter(mask => relevantEdges.every(([a, b]) => mask & ((1 << a) | (1 << b))));
const coverNumber = Math.min(...covers.map(mask => vertices.filter(v => mask & (1 << v)).length));
if (inputCount + coverNumber !== gateCount + 1) throw new Error('Bound is not tight at nine gates');

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

// A sole AND reader with another primary would block the remaining
// neighbors of that input. A sole OR reader implies containment of
// its neighborhood outside the pair in the other input's neighborhood.
for (const { left, right, or } of gates) {
  for (let a = 0; a < inputCount; a++) {
    for (let b = a + 1; b < inputCount; b++) {
      if (neighbors[a].some(w => w !== b)) add(or, -left[a], -right[b], hasTwoReaders[a]);
      if (neighbors[b].some(w => w !== a)) add(or, -left[a], -right[b], hasTwoReaders[b]);
      if (neighbors[a].some(w => w !== b && !adjacent(b, w))) {
        add(-or, -left[a], -right[b], hasTwoReaders[a]);
      }
      if (neighbors[b].some(w => w !== a && !adjacent(a, w))) {
        add(-or, -left[a], -right[b], hasTwoReaders[b]);
      }
    }
  }
}

// Choose the lexicographically first list of sorted operands over all
// topological orders.
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
// Fix the unordered first pair to its least representative under every
// automorphism of the graph. Swapping operands does not change a gate.
const symmetries = [];
function buildSymmetries(partial) {
  if (partial.length === inputCount) {
    symmetries.push(partial);
    return;
  }
  const v = partial.length;
  for (const candidate of vertices) {
    if (partial.includes(candidate) || neighbors[v].length !== neighbors[candidate].length) continue;
    if (partial.every((image, w) => adjacent(v, w) === adjacent(candidate, image))) {
      buildSymmetries([...partial, candidate]);
    }
  }
}
buildSymmetries([]);
for (let a = 0; a < inputCount; a++) {
  for (let b = a + 1; b < inputCount; b++) {
    if (symmetries.some(p => Math.min(p[a], p[b]) * inputCount + Math.max(p[a], p[b]) < a * inputCount + b)) {
      add(-gates[0].left[a], -gates[0].right[b]);
    }
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

if (process.argv.includes('--sensitive')) {
  // Every gate of a minimum circuit is needed at both boundary values.
  // Otherwise substituting a constant at that gate preserves the whole
  // monotone function after constants and aliases have been propagated.
  for (let removed = 0; removed < gateCount - 1; removed++) {
    const positiveChanges = [];
    const negativeChanges = [];
    for (const [row, mask] of boundary.entries()) {
      const expected = target(mask);
      const values = boundaryOutputs[row].slice(0, removed);
      const forced = fresh();
      add(expected ? -forced : forced);
      values.push(forced);
      for (let i = removed + 1; i < gateCount; i++) {
        const gate = gates[i];
        const a = fresh();
        const b = fresh();
        for (const [selectors, operand] of [[gate.left, a], [gate.right, b]]) {
          for (const [wire, select] of selectors.entries()) {
            if (wire < inputCount) add(-select, (mask & inputMasks[wire]) !== 0 ? operand : -operand);
            else {
              const earlier = values[wire - inputCount];
              add(-select, -operand, earlier);
              add(-select, operand, -earlier);
            }
          }
        }
        const out = fresh();
        add(gate.or, -a, -b, out);
        add(gate.or, a, -out);
        add(gate.or, b, -out);
        add(-gate.or, a, b, -out);
        add(-gate.or, -a, out);
        add(-gate.or, -b, out);
        values.push(out);
      }
      if (expected) positiveChanges.push(-values.at(-1));
      else negativeChanges.push(values.at(-1));
    }
    add(...positiveChanges);
    add(...negativeChanges);
  }
}

const path = process.argv.slice(2).find(arg => !arg.startsWith('--')) ?? 'atlas-984-shard-14.cnf';
const dimacs = `p cnf ${variableCount} ${clauses.length}\n${clauses.map(clause => `${clause.join(' ')} 0`).join('\n')}\n`;
writeFileSync(path, dimacs);
console.log(`${boundary.length} boundary inputs, ${variableCount} variables, ${clauses.length} clauses.`);
