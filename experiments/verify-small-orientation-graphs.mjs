// The recorded run at maxVertices=11 completed in about 35 seconds.
// Orders 7 through 11 cover 31,948 graph representatives and 359,780,783 orientations.
// The lower orders also recover the reported counts of 8,597 labelled graphs
// and 403,068 labelled orientations through order six. These counts are a
// cross-check on the enumeration. The result applies to the orders tested.
// The desk's original three L-meta-904 ranges are recorded separately.

// Independently extend the small-graph check described by L-meta-904.
// Usage: node verify-small-orientation-graphs.mjs [max vertices, 1 to 11]
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

function orientations(adj) {
  const edges = [];
  for (let a = 0; a < adj.length; a++) {
    for (let b = a + 1; b < adj.length; b++) {
      if (adj[a] & (1 << b)) edges.push([a, b, (1 << a) | (1 << b)]);
    }
  }

  const candidateTests = [];
  for (let set = 0; set < 1 << adj.length; set++) {
    if (edges.some(([, , pair]) => (set & pair) === pair)) continue;
    const towardsWhenOne = new Int32Array(adj.length);
    const towardsWhenZero = new Int32Array(adj.length);
    for (const [i, [a, b]] of edges.entries()) {
      if (set & (1 << b)) towardsWhenOne[a] |= 1 << i;
      if (set & (1 << a)) towardsWhenZero[b] |= 1 << i;
    }

    const constraints = [];
    let viable = true;
    for (const [a, b, pair] of edges) {
      if (set & pair) continue;
      const acceptOne = towardsWhenOne[a] | towardsWhenOne[b];
      const acceptZero = towardsWhenZero[a] | towardsWhenZero[b];
      if ((acceptOne | acceptZero) === 0) {
        viable = false;
        break;
      }
      constraints.push(acceptOne, acceptZero);
    }
    if (viable) candidateTests.push(Int32Array.from(constraints));
  }

  function qualifies(code, tests) {
    for (let i = 0; i < tests.length; i += 2) {
      if (((code & tests[i]) | (~code & tests[i + 1])) === 0) return false;
    }
    return true;
  }

  candidateTests.sort((a, b) => a.length - b.length);
  let previous = 0;
  const count = 1 << edges.length;
  for (let i = 0; i < count; i++) {
    const code = i ^ (i >>> 1);
    if (candidateTests.length && qualifies(code, candidateTests[previous])) continue;
    previous = candidateTests.findIndex(tests => qualifies(code, tests));
    if (previous < 0) return { edges, orientation: code };
  }
  return { count };
}

let graphs = [{ adj: [], keys: [] }];
let factorial = 1;
for (let n = 1; n <= maxVertices; n++) {
  factorial *= n;
  graphs = nextGraphs(graphs);
  let orientationsChecked = 0;
  let labeledGraphs = 0;
  let labeledOrientations = 0;
  for (const { adj, keys } of graphs) {
    const result = orientations(adj);
    if (result.count === undefined) {
      console.log(JSON.stringify({ n, counterexample: result }));
      process.exit(1);
    }
    orientationsChecked += result.count;
    if (n <= 6) {
      const labelings = factorial / countMappings(adj, adj, keys, keys, false);
      labeledGraphs += labelings;
      labeledOrientations += labelings * result.count;
    }
  }
  console.log(JSON.stringify({ n, graphs: graphs.length, orientationsChecked, counterexamples: 0,
    ...(n <= 6 ? { labeledGraphs, labeledOrientations } : {}) }));
}
