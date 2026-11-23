import { performance } from 'node:perf_hooks';

// L-meta-904, in the exact edge order listed by the public desk.
const shards = [
  { vertices: 12, edges: '2-3 1-4 0-5 4-6 5-6 3-7 5-7 6-7 2-8 4-8 6-8 1-9 3-9 7-9 0-10 2-10 8-10 0-11 1-11 9-11 10-11' },
  { vertices: 13, edges: '3-5 4-5 2-6 4-6 1-7 3-7 6-7 1-8 2-8 5-8 0-9 2-9 3-9 0-10 1-10 4-10 0-11 6-11 7-11 0-12 5-12 8-12 11-12' },
  { vertices: 13, edges: '2-4 3-4 1-5 3-5 0-6 2-6 0-7 3-7 6-7 0-8 2-8 5-8 0-9 1-9 4-9 6-9 5-10 6-10 0-11 1-11 7-11 9-11 2-12 3-12' },
];

const input = process.argv[2];
if (!/^[0-2]$/.test(input ?? '')) throw new Error('Usage: node verify-orientation-shard.mjs <0|1|2>');
const shard = Number(input);
const { vertices, edges: encodedEdges } = shards[shard];
const edges = encodedEdges.split(' ').map(edge => edge.split('-').map(Number));
const edgeMasks = edges.map(([a, b]) => (1 << a) | (1 << b));
const candidates = [];

for (let set = 0; set < 1 << vertices; set++) {
  if (edgeMasks.some(edge => (set & edge) === edge)) continue;
  const towardSetWhenOne = new Int32Array(vertices);
  const towardSetWhenZero = new Int32Array(vertices);
  for (const [index, [a, b]] of edges.entries()) {
    // A one orients edge a -> b. A zero orients it in the other direction.
    if (set & (1 << b)) towardSetWhenOne[a] |= 1 << index;
    if (set & (1 << a)) towardSetWhenZero[b] |= 1 << index;
  }

  const edgeTests = new Map();
  for (const [index, [a, b]] of edges.entries()) {
    if (set & edgeMasks[index]) continue;
    const whenOne = towardSetWhenOne[a] | towardSetWhenOne[b];
    const whenZero = towardSetWhenZero[a] | towardSetWhenZero[b];
    // One endpoint must have an outgoing edge towards the set.
    edgeTests.set(`${whenOne},${whenZero}`, [whenOne, whenZero]);
  }
  if (edgeTests.has('0,0')) continue;
  candidates.push({ set, tests: Int32Array.from([...edgeTests.values()].flat()) });
}
candidates.sort((a, b) => a.tests.length - b.tests.length);

function works(orientation, tests) {
  for (let i = 0; i < tests.length; i += 2) {
    if (((orientation & tests[i]) | (~orientation & tests[i + 1])) === 0) return false;
  }
  return true;
}

function directWorks(orientation, set) {
  const absorbed = new Set();
  for (const [index, [a, b]] of edges.entries()) {
    const [source, target] = orientation & (1 << index) ? [a, b] : [b, a];
    if (set & (1 << target)) absorbed.add(source);
  }
  return edges.every(([a, b], index) =>
    (set & edgeMasks[index]) !== edgeMasks[index] &&
    ((set & edgeMasks[index]) !== 0 || absorbed.has(a) || absorbed.has(b)));
}

const started = performance.now();
const total = 1 << edges.length;
let previous = 0;
for (let index = 0; index < total; index++) {
  // Gray order visits each orientation once and usually preserves its witness.
  const orientation = index ^ (index >>> 1);
  if (!works(orientation, candidates[previous].tests)) {
    previous = candidates.findIndex(({ tests }) => works(orientation, tests));
    if (previous < 0) {
      console.log(JSON.stringify({ shard, checked: index + 1, counterexample: orientation }));
      process.exit(1);
    }
  }
  if ((index & 0xffff) === 0 && !directWorks(orientation, candidates[previous].set)) {
    throw new Error(`Independent check failed for orientation ${orientation}`);
  }
}
console.log(JSON.stringify({ shard, checked: total, counterexamples: 0, candidates: candidates.length,
  seconds: (performance.now() - started) / 1000 }));
