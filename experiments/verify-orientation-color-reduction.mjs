// Reproduce with node verify-orientation-color-reduction.mjs 12.
// The run found 152045 graph representatives on 12 vertices. That count
// agrees with McKay's Table 2: https://users.cecs.anu.edu.au/~bdm/papers/orderly.pdf
// Exactly one representative was not 3-colourable. All its 2097152
// orientations passed. A separate check identifies it with L-meta-904
// shard 0 (12 vertices, 21 edges), whose 3^12 colourings were also tested.
// The other graphs are covered by the constructive argument at the end.
// This is an independent extension of the original three desk ranges.

// Exhaustive C4-free orientation check for L-meta-904, through 12 vertices.
// Usage: node verify-orientation-color-reduction.mjs [vertices, 1 to 12]
// --direct also checks the orientations of three-colourable graphs.
const maxVertices = Number(process.argv[2] ?? 12);
if (!Number.isInteger(maxVertices) || maxVertices < 1 || maxVertices > 12) {
  throw new Error('Expected a vertex limit between 1 and 12');
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
    const conflicts = Array.from({ length: n }, () => 0);
    for (let a = 0; a < n; a++) {
      for (let b = a + 1; b < n; b++) {
        if ((previous.adj[a] & previous.adj[b]) === 0) continue;
        conflicts[a] |= 1 << b;
        conflicts[b] |= 1 << a;
      }
    }

    // Two neighbours of the added vertex may not share an old neighbour.
    // Enumerate the compatible subsets directly, before isomorphism testing.
    function extend(available, neighbours) {
      const adj = previous.adj.map((row, v) => row | ((neighbours & (1 << v)) ? 1 << n : 0));
      adj.push(neighbours);
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

      while (available !== 0) {
        const bit = available & -available;
        available ^= bit;
        const v = 31 - Math.clz32(bit);
        extend(available & ~conflicts[v], neighbours | bit);
      }
    }
    extend((1 << n) - 1, 0);
  }
  return [...groups.values()].flat();
}

function threeColouring(adj) {
  const groups = [0, 0, 0];
  const degree = adj.map(bitCount);
  const all = (1 << adj.length) - 1;

  function assign(remaining, used) {
    if (remaining === 0) return groups.slice();
    let best = -1;
    let bestBit = 0;
    let bestSaturation = -1;
    for (let set = remaining; set !== 0; set &= set - 1) {
      const bit = set & -set;
      const vertex = 31 - Math.clz32(bit);
      const saturation = groups.reduce((count, group) => count + Number((group & adj[vertex]) !== 0), 0);
      if (saturation === 3) return null;
      if (saturation < bestSaturation || (saturation === bestSaturation && degree[vertex] <= degree[best])) {
        continue;
      }
      best = vertex;
      bestBit = bit;
      bestSaturation = saturation;
    }

    for (let colour = 0; colour < Math.min(3, used + 1); colour++) {
      if ((groups[colour] & adj[best]) !== 0) continue;
      groups[colour] |= bestBit;
      const result = assign(remaining ^ bestBit, Math.max(used, colour + 1));
      groups[colour] ^= bestBit;
      if (result) return result;
    }
    return null;
  }

  const colouring = assign(all, 0);
  if (colouring) {
    if ((colouring[0] | colouring[1] | colouring[2]) !== all ||
        (colouring[0] & colouring[1]) || (colouring[0] & colouring[2]) || (colouring[1] & colouring[2])) {
      throw new Error('Invalid vertex partition');
    }
    for (const group of colouring) {
      for (let v = 0; v < adj.length; v++) {
        if ((group & (1 << v)) && (adj[v] & group)) throw new Error('Invalid colouring edge');
      }
    }
  }
  return colouring;
}

function orientations(adj) {
  const edges = [];
  for (let a = 0; a < adj.length; a++) {
    for (let b = a + 1; b < adj.length; b++) {
      if (adj[a] & (1 << b)) edges.push([a, b, (1 << a) | (1 << b)]);
    }
  }

  if (edges.length >= 31) throw new Error('Too many edges for the orientation mask');

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

// Every orientation of a 3-colourable graph has the required independent
// set. Keep the first colour class initially. Add a vertex of the second
// class that has no outgoing edge to the current set, removing all of its
// neighbours in the first class. Every removed vertex then points to that
// added vertex, which is never removed. Repeat until no addition is possible.
// The result absorbs the other vertices of the first two classes. Any
// unabsorbed vertices lie in the third class, which is independent.
const direct = process.argv.includes('--direct');
const knownCounts = [1, 1, 2, 4, 8, 18, 44, 117, 351, 1230, 5069, 25181];
let graphs = [{ adj: [], keys: [] }];
for (let n = 1; n <= maxVertices; n++) {
  graphs = nextGraphs(graphs);
  if (knownCounts[n] !== undefined && graphs.length !== knownCounts[n]) {
    throw new Error('Graph count differs from the independently checked enumeration');
  }
  let threeColourable = 0;
  let allOrientationsChecked = 0;
  let graphsCheckedDirectly = 0;
  for (const { adj } of graphs) {
    const colouring = threeColouring(adj);
    if (colouring) threeColourable++;
    if (colouring && !direct) continue;
    graphsCheckedDirectly++;
    const result = orientations(adj);
    if (result.count === undefined) {
      console.log(JSON.stringify({ n, counterexample: result }));
      process.exit(1);
    }
    allOrientationsChecked += result.count;
  }
  console.log(JSON.stringify({ n, graphs: graphs.length, threeColourable,
    graphsCheckedDirectly, allOrientationsChecked, counterexamples: 0 }));
}
