

// An applicative expression
export type Exp =
  | { t: 'app', f: Exp, a: Exp }
  | { t: 'var' };


export type ExpInfo = {
  e: Exp,
  ix: number,
  leafId: { [k: string]: number }, // takes variable index, returns node id
  info: {
    [k: string]: { // takes node id
      parent: number, // parent id
      min: number, // minimum variable id below this node
      max: number,// maximum  variable id below this node
      minmax: string, // string repn
    },
  },
  minmaxs: { [k: string]: boolean },
}

function convert(e: Exp, ix: number): ExpInfo {
  let nodeId = 0;
  let varId = 0;
  const ei: ExpInfo = { e, ix, leafId: {}, info: {}, minmaxs: {} };
  function descend(e: Exp): number {
    const id = nodeId++;
    switch (e.t) {
      case 'app': {
        const f = descend(e.f);
        const a = descend(e.a);
        ei.info[f].parent = id;
        ei.info[a].parent = id;
        const min = ei.info[f].min;
        const max = ei.info[a].max;
        const minmax = `${min}/${max}`;
        ei.info[id] = { parent: -1, min, max, minmax };
        ei.minmaxs[minmax] = true;
      } break;
      case 'var': {
        const vid = varId++;
        ei.leafId[vid] = id;
        const min = vid;
        const max = vid;
        const minmax = `${min}/${max}`;
        ei.info[id] = { parent: -1, min, max, minmax };
      } break;
    }
    return id;
  }
  descend(e);
  return ei;
}

// Print it out in prefix form
function stringify(x: Exp): string {
  switch (x.t) {
    case 'var': return '*';
    case 'app': return '(' + stringify(x.f) + ' ' + stringify(x.a) + ')';
  }
}


// Cartesian product of two lists
function cartprod<T, U, V>(ts: T[], us: U[], k: (t: T, u: U) => V): V[] {
  const rv: V[] = [];
  ts.forEach(t => {
    us.forEach(u => {
      rv.push(k(t, u));
    });
  });
  return rv;
}

const cache: { [k: string]: Exp[] } = {};

// Enumerate lambda terms
function terms(vars: number): Exp[] {
  const cacheKey = `${vars}`;
  if (!cache[cacheKey]) {
    let rv: Exp[] = [];

    if (vars == 1) {
      rv.push({ t: 'var' });
    }

    if (vars > 1) {
      for (let i = 1; i <= vars - 1; i++) {
        const f = terms(i);
        const a = terms(vars - i);
        rv = rv.concat(cartprod(f, a, (f, a) => ({ t: 'app', f, a })));
      }
    }
    cache[cacheKey] = rv;
  }
  return cache[cacheKey];
}

function compat(N: number, e1: ExpInfo, e2: ExpInfo): string {
  // If two joined trees have a triangle, their colorability arises from smaller trees
  for (let i = 0; i < N - 1; i++) {
    if (
      e1.info[e1.leafId[i]].parent == e1.info[e1.leafId[i + 1]].parent &&
      e2.info[e2.leafId[i]].parent == e2.info[e2.info[e2.leafId[i + 1]].parent].parent
      ||
      e1.info[e1.leafId[i]].parent == e1.info[e1.leafId[i + 1]].parent &&
      e2.info[e2.leafId[i + 1]].parent == e2.info[e2.info[e2.leafId[i]].parent].parent
      ||
      e2.info[e2.leafId[i]].parent == e2.info[e2.leafId[i + 1]].parent &&
      e1.info[e1.leafId[i]].parent == e1.info[e1.info[e1.leafId[i + 1]].parent].parent
      ||
      e2.info[e2.leafId[i]].parent == e2.info[e2.leafId[i + 1]].parent &&
      e1.info[e1.leafId[i + 1]].parent == e1.info[e1.info[e1.leafId[i]].parent].parent
    ) {
      return '!';
    }
  }

  // If two trees have any subtree spans in common, that means there is
  // a subterm with one free variable, so the colorability of the
  // overall expression folows from the colorability of smaller maps.
  for (const k of Object.keys(e1.info)) {
    const i = e1.info[k].minmax;
    if (i != `0/${N - 1}` && e2.minmaxs[i]) {
      return '#';
    }
  }

  return '.';
}


for (let N = 1; N < 9; N++) {
  let count = 0;
  const trees = terms(N).map(convert);

  const print = (s: string) => { }; // process.stdout.write.bind(process.stdout);;

  trees.forEach(t2 => {
    print('\t');
    print(stringify(t2.e));
  });
  print('\n');

  trees.forEach(t1 => {
    print(stringify(t1.e));
    trees.forEach(t2 => {
      print('\t');
      const c = compat(N, t1, t2);
      if (c == '.') count++;
      print(c);
    });
    print('\n');
  });


  console.log(count);
}



// console.log(trees[5].leafId);
// console.log(trees[5].info);

// trees.forEach((tree, i) => {
//   console.log(i, stringify(tree.e), tree.minmaxs);
// });
