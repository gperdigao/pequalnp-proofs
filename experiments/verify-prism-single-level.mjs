// Exact search for circuits with OR gates below a single layer of AND gates,
// and an OR of the AND outputs. Inputs are free and each gate has fan-in two.
const vertices = 6;
const edges = [[0, 1], [0, 2], [1, 2], [3, 4], [3, 5], [4, 5], [0, 3], [1, 4], [2, 5]];
const edgePosition = new Map(edges.map(([u, v], index) => [`${u},${v}`, index]));
const vertexSets = Array.from({ length: 1 << vertices }, (_, mask) =>
  Array.from({ length: vertices }, (_, vertex) => vertex).filter(vertex => mask & (1 << vertex)));
const allEdges = (1 << edges.length) - 1;

// Each AND joins two disjoint sets. Every crossed pair must be an edge.
const products = [];
for (let a = 1; a < vertexSets.length; a++) {
  for (let b = a + 1; b < vertexSets.length; b++) {
    if (a & b) continue;
    const crossedPairs = vertexSets[a].flatMap(u => vertexSets[b].map(v =>
      edgePosition.get(`${Math.min(u, v)},${Math.max(u, v)}`)));
    if (crossedPairs.some(index => index === undefined)) continue;
    products.push({ a, b, edges: crossedPairs.reduce((mask, index) => mask | (1 << index), 0) });
  }
}

function pairChoices(triple) {
  return vertexSets[triple].map(vertex => triple ^ (1 << vertex));
}

function cheapestOrPlan(required, budget) {
  // Every requested pair uses an OR, and every requested triple uses one
  // additional OR together with at least one of its three constituent pairs.
  if (required.size > budget) return null;
  const triples = [...required].filter(mask => vertexSets[mask].length === 3);
  let best = null;
  const extraPairs = new Set();
  function choose(index) {
    const cost = required.size + extraPairs.size;
    if (cost > budget || (best && cost >= best.cost)) return;
    if (index === triples.length) {
      best = { cost, extraPairs: [...extraPairs] };
      return;
    }
    const choices = pairChoices(triples[index]);
    if (choices.some(pair => required.has(pair) || extraPairs.has(pair))) {
      choose(index + 1);
      return;
    }
    for (const pair of choices) {
      extraPairs.add(pair);
      choose(index + 1);
      extraPairs.delete(pair);
    }
  }
  choose(0);
  return best;
}

if (products.some(({ a, b }) => vertexSets[a].length > 3 || vertexSets[b].length > 3)) {
  throw new Error('The OR cost calculation is only valid for operands of at most three vertices.');
}

let best = null;
let gateLimit = 10;
const maxEdgeCount = Math.max(...products.map(product => product.edges.toString(2).replaceAll('0', '').length));
for (let count = Math.ceil(edges.length / maxEdgeCount); 2 * count - 1 <= gateLimit; count++) {
  const chosen = [];
  function search(start, covered, required) {
    const orPlan = cheapestOrPlan(required, gateLimit - (2 * count - 1));
    if (!orPlan) return;
    if (chosen.length === count) {
      if (covered === allEdges) {
        const gates = 2 * count - 1 + orPlan.cost;
        best = { gates, products: [...chosen], required: [...required], extraPairs: orPlan.extraPairs };
        gateLimit = gates - 1;
      }
      return;
    }
    for (let i = start; i < products.length; i++) {
      const product = products[i];
      if ((covered | product.edges) === covered) continue;
      const next = new Set(required);
      for (const operand of [product.a, product.b]) {
        if (vertexSets[operand].length > 1) next.add(operand);
      }
      chosen.push(product);
      search(i + 1, covered | product.edges, next);
      chosen.pop();
    }
  }
  search(0, 0, new Set());
}

if (!best) throw new Error('No witness found within the initial gate limit.');

const gates = [];
const emit = (op, a, b) => vertices + gates.push({ op, inputs: [a, b] }) - 1;
const wires = new Map(Array.from({ length: vertices }, (_, i) => [1 << i, i]));
for (const pair of new Set([...best.required.filter(mask => vertexSets[mask].length === 2), ...best.extraPairs])) {
  wires.set(pair, emit('or', ...vertexSets[pair]));
}
for (const triple of best.required.filter(mask => vertexSets[mask].length === 3)) {
  const pair = pairChoices(triple).find(mask => wires.has(mask));
  if (pair === undefined) throw new Error('The selected triple has no pair to reuse.');
  wires.set(triple, emit('or', wires.get(pair), wires.get(triple ^ pair)));
}
const terms = best.products.map(({ a, b }) => emit('and', wires.get(a), wires.get(b)));
const output = terms.reduce((first, next) => emit('or', first, next));
for (let input = 0; input < 1 << vertices; input++) {
  const values = Array.from({ length: vertices }, (_, i) => Boolean(input & (1 << i)));
  for (const { op, inputs: [a, b] } of gates) {
    values.push(op === 'or' ? values[a] || values[b] : values[a] && values[b]);
  }
  const expected = edges.some(([a, b]) => values[a] && values[b]);
  if (values[output] !== expected) throw new Error(`Witness failed on input ${input}.`);
}
if (gates.length !== best.gates) throw new Error('The circuit and the cost calculation disagree.');

console.log(JSON.stringify({ minimum: best.gates, bicliqueCount: products.length,
  inputsVerified: 1 << vertices, gates, output }, null, 2));
