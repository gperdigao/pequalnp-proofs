// Independent results for atlas cases 9, 10 and 12, plus a replay of case 14.
// The inputs were compared with the 31 public L-meta-984 records.
// Cases 9, 10 and 12 were examined independently of a desk assignment.

// Reproduce with: node verify-atlas-984-leaf-reductions.mjs
// Input: the 31 graph records in the public L-meta-984 atlas (23 Nov 2026).
// Base bowtie bound: certificate independently replayed with Lean's LRAT checker.
// https://github.com/gperdigao/pequalnp-proofs/commit/1d46911ef8669b06d46b1b455f5d8f312028e4c0
//
// If x is essential in a monotone circuit, fix x to false and simplify the
// first gate that reads it. This gate becomes false or a copy of an existing
// wire, so the restriction costs at least one gate in any size-minimal
// circuit. Deleting a graph leaf preserves the remaining edge function
// under that restriction. We test every sequence that preserves the cover
// number, and keep a short witness when a certified core is reached.

const rows = `
n6-025 10 0-1 0-2 0-3 1-2 3-4 3-5 4-5
n7-032 10 0-1 0-2 0-3 0-4 1-2 3-4 5-6
n7-034 10 0-1 0-2 0-3 0-4 1-2 3-5 4-6
n7-040 10 0-1 0-2 0-3 1-2 1-4 3-5 4-6
n7-042 10 0-1 0-2 0-3 1-2 3-4 3-5 4-6
n7-044 10 0-1 0-2 0-3 1-2 3-4 4-5 5-6
n7-045 10 0-1 0-2 0-3 1-2 4-5 4-6 5-6
n7-047 10 0-1 0-2 0-3 1-4 2-5 3-6 4-5
n7-050 10 0-1 0-2 1-3 2-4 3-5 4-6 5-6
n7-051 10 0-1 0-2 0-3 0-4 0-5 0-6 1-2 3-4
n7-052 10 0-1 0-2 0-3 0-4 0-5 1-2 1-6 3-4
n7-053 11 0-1 0-2 0-3 0-4 0-5 1-2 3-4 5-6
n7-054 10 0-1 0-2 0-3 0-4 1-2 1-5 1-6 3-4
n7-055 11 0-1 0-2 0-3 0-4 1-2 1-5 2-6 3-4
n7-056 10 0-1 0-2 0-3 0-4 1-2 1-5 3-4 3-6
n7-057 11 0-1 0-2 0-3 0-4 1-2 1-5 3-4 5-6
n7-058 10 0-1 0-2 0-3 0-4 1-2 1-5 3-6 5-6
n7-059 11 0-1 0-2 0-3 0-4 1-2 3-5 3-6 5-6
n7-060 11 0-1 0-2 0-3 0-4 1-2 3-5 4-6 5-6
n7-061 11 0-1 0-2 0-3 1-2 1-4 2-5 3-6 4-6
n7-062 11 0-1 0-2 0-3 1-2 1-4 3-5 3-6 4-5
n7-063 11 0-1 0-2 0-3 1-2 1-4 3-5 3-6 5-6
n7-064 10 0-1 0-2 0-3 1-2 1-4 3-5 4-5 5-6
n7-065 11 0-1 0-2 0-3 1-2 1-4 3-5 4-6 5-6
n7-066 11 0-1 0-2 0-3 1-2 3-4 4-5 4-6 5-6
n7-067 11 0-1 0-2 0-3 1-4 2-5 3-6 4-5 4-6
n7-068 12 0-1 0-2 0-3 0-4 0-5 0-6 1-2 3-4 5-6
n7-069 12 0-1 0-2 0-3 0-4 1-2 1-5 1-6 3-4 5-6
n7-070 12 0-1 0-2 0-3 0-4 1-2 1-5 3-4 3-6 5-6
n7-071 12 0-1 0-2 0-3 1-2 1-4 2-5 3-6 4-6 5-6
n7-072 12 0-1 0-2 0-3 1-2 1-4 3-5 3-6 4-5 5-6
`.trim().split('\n');

const graphs = rows.map((line, shard) => {
  const [id, bound, ...pairs] = line.split(' ');
  const n = Number(id[1]);
  return {
    shard,
    id,
    bound: Number(bound),
    vertices: Array.from({ length: n }, (_, index) => index),
    edges: pairs.map(pair => pair.split('-').map(Number)),
  };
});

function popcount(mask) {
  let count = 0;
  while (mask !== 0) {
    mask &= mask - 1;
    count++;
  }
  return count;
}

function minCover({ vertices, edges }) {
  const n = vertices.length;
  const index = new Map(vertices.map((v, i) => [v, i]));
  let best = (1 << n) - 1;
  const edgeMasks = edges.map(([a, b]) => (1 << index.get(a)) | (1 << index.get(b)));
  for (let mask = 0; mask < 1 << n; mask++) {
    if (popcount(mask) < popcount(best) && edgeMasks.every(edge => edge & mask)) best = mask;
  }
  return vertices.filter((_, i) => best & (1 << i));
}

function degree({ edges }, v) {
  return edges.filter(edge => edge.includes(v)).length;
}

function triangleLowerBound() {
  const target = 0b11101000;
  // Free 0/1 inputs overapproximate all gates with arity less than two
  // and all references to wires not yet available.
  const inputs = [0b10101010, 0b11001100, 0b11110000, 0, 255];
  let programs = 0;
  function search(wires, remaining) {
    if (wires.includes(target)) throw Error('Found a triangle circuit with at most 3 gates');
    if (remaining === 0) {
      programs++;
      return;
    }
    for (let a = 0; a < wires.length; a++) {
      for (let b = a; b < wires.length; b++) {
        search([...wires, wires[a] & wires[b]], remaining - 1);
        search([...wires, wires[a] | wires[b]], remaining - 1);
      }
    }
  }
  search(inputs, 3);
  return programs;
}

function coreBound(graph) {
  const { vertices, edges } = graph;
  if (vertices.length === 3 && edges.length === 3) return { name: 'triangle', gates: 4 };
  // These degrees force a universal center and exactly two disjoint edges
  // between the four other vertices, which is the certified bowtie.
  if (vertices.length === 5 && vertices.map(v => degree(graph, v)).sort().join(',') === '2,2,2,2,4') {
    return { name: 'bowtie', gates: 8 };
  }
  return undefined;
}

function search(graph, coverNumber, deleted, hits) {
  const core = coreBound(graph);
  if (core) hits.push({ core: core.name, deleted, lower: core.gates + deleted.length });
  for (const v of graph.vertices) {
    if (degree(graph, v) !== 1) continue;
    const reduced = {
      vertices: graph.vertices.filter(w => w !== v),
      edges: graph.edges.filter(edge => !edge.includes(v)),
    };
    if (minCover(reduced).length === coverNumber) {
      search(reduced, coverNumber, [...deleted, v], hits);
    }
  }
}

function verifyUpper({ vertices, edges }, cover) {
  const centers = new Map(cover.map(v => [v, []]));
  for (const [a, b] of edges) {
    if (centers.has(a)) centers.get(a).push(b);
    else if (centers.has(b)) centers.get(b).push(a);
    else throw Error('Invalid cover');
  }

  const gates = [];
  const append = (op, a, b) => {
    const wire = vertices.length + gates.length;
    gates.push([op, a, b]);
    return wire;
  };
  const starOutputs = [];
  for (const [center, leaves] of centers) {
    if (leaves.length === 0) continue;
    const rest = leaves.reduce((a, b) => append('or', a, b));
    starOutputs.push(append('and', center, rest));
  }
  const output = starOutputs.reduce((a, b) => append('or', a, b));
  for (let mask = 0; mask < 1 << vertices.length; mask++) {
    const wires = vertices.map(v => Boolean(mask & (1 << v)));
    for (const [op, a, b] of gates) {
      wires.push(op === 'and' ? wires[a] && wires[b] : wires[a] || wires[b]);
    }
    if (wires[output] !== edges.some(([a, b]) => wires[a] && wires[b])) {
      throw Error('Verification failed on assignment ' + mask);
    }
  }
  return gates.length;
}

console.log(JSON.stringify({ graphRows: graphs.length, triangleProgramsChecked: triangleLowerBound() }));
let certified = 0;
for (const graph of graphs) {
  const cover = minCover(graph);
  const hits = [];
  search(graph, cover.length, [], hits);
  const exact = hits.filter(hit => hit.lower === graph.bound);
  if (!exact.length) continue;
  const upper = verifyUpper(graph, cover);
  if (upper !== graph.bound) throw Error('Star upper bound does not match ' + graph.id);
  certified++;
  console.log(JSON.stringify({
    shard: graph.shard,
    graph: graph.id,
    cover,
    core: exact[0].core,
    leafOrders: exact.map(hit => hit.deleted),
    minimumANDORGates: upper,
  }));
}
console.log(JSON.stringify({ certified }));
