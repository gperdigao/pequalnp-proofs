// Verified locally through order 11: 32,025 graph representatives, no
// counterexamples in the one-AND-layer class. Run with argument 11 to reproduce.
// AND gates that read earlier AND gates are outside this check.

// L-meta-1006, one layer of AND gates, all graphs through 11 vertices.
// Usage: node verify-depth-one-and-count.mjs [max vertices, 1 to 11]
const maxVertices = Number(process.argv[2] ?? 10);
if (!Number.isInteger(maxVertices) || maxVertices < 1 || maxVertices > 11) {
  throw new Error('Expected a vertex limit between 1 and 11');
}

function bitCount(mask) {
  let count = 0;
  while (mask !== 0) {
    mask &= mask - 1;
    count++;
  }
  return count;
}

function vertexKeys(adj) {
  const degrees = adj.map(bitCount);
  return adj.map((neighbors, v) => {
    const neighborDegrees = degrees.filter((_, u) => (neighbors & (1 << u)) !== 0).sort((a, b) => a - b);
    let triangles = 0;
    for (let u = 0; u < adj.length; u++) {
      if (neighbors & (1 << u)) triangles += bitCount(neighbors & adj[u]);
    }
    return `${degrees[v]}:${triangles / 2}:${neighborDegrees.join(',')}`;
  });
}

function countMappings(a, b, aKeys, bKeys, stopAfterOne) {
  const compatible = aKeys.map(key => bKeys.flatMap((other, v) => key === other ? [v] : []));
  const order = aKeys.map((_, v) => v).sort((u, v) => compatible[u].length - compatible[v].length);
  const image = new Int32Array(a.length);

  function visit(depth, used) {
    if (depth === order.length) return 1;
    const v = order[depth];
    let count = 0;
    for (const w of compatible[v]) {
      if (used & (1 << w)) continue;
      let consistent = true;
      for (let i = 0; i < depth; i++) {
        const u = order[i];
        if (((a[v] >> u) & 1) !== ((b[w] >> image[u]) & 1)) {
          consistent = false;
          break;
        }
      }
      if (!consistent) continue;
      image[v] = w;
      count += visit(depth + 1, used | (1 << w));
      if (stopAfterOne && count) return 1;
    }
    return count;
  }

  return visit(0, 0);
}

function nextGraphs(smaller) {
  const groups = new Map();
  for (const previous of smaller) {
    const n = previous.adj.length;
    const forbiddenPairs = [];
    for (let a = 0; a < n; a++) {
      for (let b = a + 1; b < n; b++) {
        if ((previous.adj[a] & previous.adj[b]) !== 0) forbiddenPairs.push((1 << a) | (1 << b));
      }
    }
    for (let neighbors = 0; neighbors < 1 << n; neighbors++) {
      // A new four-cycle would use the new vertex and two neighbors with a common old neighbor.
      if (forbiddenPairs.some(pair => (neighbors & pair) === pair)) continue;
      const adj = previous.adj.map((row, v) => row | ((neighbors & (1 << v)) ? 1 << n : 0));
      adj.push(neighbors);
      const keys = vertexKeys(adj);
      const signature = [...keys].sort().join(';');
      let group = groups.get(signature);
      if (!group) {
        group = [];
        groups.set(signature, group);
      }
      if (!group.some(other => countMappings(adj, other.adj, keys, other.keys, true))) {
        group.push({ adj, keys });
      }
    }
  }
  return [...groups.values()].flat();
}

function findSmallerCenterSet(adj) {
  const all = (1 << adj.length) - 1;
  const independent = new Uint8Array(all + 1);
  const maximal = [];
  let largestIndependent = 0;
  independent[0] = 1;
  for (let set = 1; set <= all; set++) {
    const bit = set & -set;
    const vertex = 31 - Math.clz32(bit);
    const rest = set ^ bit;
    if (!independent[rest] || (adj[vertex] & rest)) continue;
    independent[set] = 1;
    largestIndependent = Math.max(largestIndependent, bitCount(set));
    let closed = set;
    for (let vertices = set; vertices; vertices &= vertices - 1) {
      closed |= adj[31 - Math.clz32(vertices & -vertices)];
    }
    if (closed === all) maximal.push(set);
  }
  const coverNumber = adj.length - largestIndependent;
  if (coverNumber === 0) return null;

  // Falsity on all maximal independent sets makes each nonempty output AND
  // of two ORs a biclique, hence a star in a four-cycle-free graph. Enlarging
  // that star to the full neighborhood preserves all required false rows.
  // For I + u, the center set must meet u or an I-neighbor of u.
  const requirements = new Set();
  for (const set of maximal) {
    for (let outside = all ^ set; outside; outside &= outside - 1) {
      const bit = outside & -outside;
      const vertex = 31 - Math.clz32(bit);
      requirements.add(bit | (set & adj[vertex]));
    }
  }
  const sorted = [...requirements].sort((a, b) => bitCount(a) - bitCount(b));
  const minimal = [];
  for (const mask of sorted) {
    if (!minimal.some(other => (mask & other) === other)) minimal.push(mask);
  }

  const explored = new Set();
  function visit(centers, remaining) {
    if (explored.has(centers)) return null;
    explored.add(centers);
    const missed = minimal.find(mask => !(mask & centers));
    if (missed === undefined) return centers;
    if (remaining === 0) return null;
    for (let choices = missed; choices; choices &= choices - 1) {
      const result = visit(centers | (choices & -choices), remaining - 1);
      if (result !== null) return result;
    }
    return null;
  }

  const centers = visit(0, coverNumber - 1);
  return centers === null ? null : { centers, coverNumber, adj };
}

let graphs = [{ adj: [], keys: [] }];
for (let n = 1; n <= maxVertices; n++) {
  graphs = nextGraphs(graphs);
  for (const { adj } of graphs) {
    const counterexample = findSmallerCenterSet(adj);
    if (counterexample) {
      console.log(JSON.stringify({ n, counterexample }));
      process.exit(1);
    }
  }
  console.log(JSON.stringify({ n, graphs: graphs.length, counterexamples: 0 }));
}
