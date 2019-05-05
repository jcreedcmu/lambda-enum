// A lambda expression
type Exp =
  | { t: 'lam', b: Exp }
  | { t: 'app', f: Exp, a: Exp }
  | { t: 'var' };

// Print it out in prefix form
function stringify(x: Exp): string {
  switch (x.t) {
    case 'lam': return '/' + stringify(x.b);
    case 'app': return '(' + stringify(x.f) + ' ' + stringify(x.a) + ')';
    case 'var': return '*';
  }
}



/////////////////////////////////
//// Constraint Computations ////
/////////////////////////////////

// One constraint, as a string, looks like a '/'-delimited list of paths, e.g.
//     BBBF/BBBAF/BBBAA
// which means that the klein-4-group-sum of the variable color
// choices at those three paths BBF, BBBAF, BBBAA is nonzero.

// Remove the rightmost element of a constraint. This is the correct
// way to account for the bound variable since we're working in
// ordered logic.
function trimRight(c: string): string {
  const items = c.split('/');
  items.pop();
  return items.join('/');
}

type ConstraintResult = {
  chere: string, // the constraint arising from having to color the current expression
  clist: string[] // the constraints arising from all subexpressions
};

// return a path that traverses into and out of e
function fullTraverse(e: Exp): string {
  switch (e.t) {
    case 'lam': return fullTraverseThru(e.b, 'B');
    case 'app': return fullTraverseThru(e.f, 'F') + fullTraverseThru(e.a, 'A');
    case 'var': return '';
  }
}
// return a path that traverses through all of e, starting with d
function fullTraverseThru(e: Exp, d: 'B' | 'F' | 'A'): string {
  return d + fullTraverse(e) + 'U';
}

// Return all constraints arising from expression `e`, assuming
// `partial` is the path we took to arrive at `e`.
function _constraints(e: Exp, partial: string): ConstraintResult {
  switch (e.t) {
    case 'lam': {
      const prev = _constraints(e.b, partial + 'B');
      const chere = trimRight(prev.chere);
      return { chere, clist: prev.clist.concat([chere]) };
    }
    case 'app': {
      const ft = fullTraverseThru(e.f, 'F');
      const prevF = _constraints(e.f, partial + 'F');
      const prevA = _constraints(e.a, partial + ft + 'A');
      const chere = prevF.chere + '/' + prevA.chere;
      return { chere, clist: prevF.clist.concat(prevA.clist, [chere]) };
    }
    case 'var': return { chere: partial, clist: [partial] };
  }
}

// Return all constraints arising from expression `e`.
function constraints(e: Exp): string[] {
  return _constraints(e, '').clist;
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
function terms(vars: number, apps: number, deep?: boolean): Exp[] {
  const cacheKey = `${vars}/${apps}/${deep}`;
  if (!cache[cacheKey]) {
    let rv: Exp[] = [];

    if (deep && vars == 0) // forbid bridges
      return [];

    if (vars > apps + 1)
      return [];

    if (apps == 0 && vars == 1) {
      rv.push({ t: 'var' });
    }

    rv = rv.concat(terms(vars + 1, apps, true).map(b => ({ t: 'lam', b })));

    if (apps > 0) {
      for (let i = 0; i <= vars; i++) {
        for (let j = 0; j <= apps - 1; j++) {
          const f = terms(i, j, true);
          const a = terms(vars - i, apps - j - 1, true);
          rv = rv.concat(cartprod(f, a, (f, a) => ({ t: 'app', f, a })));
        }
      }
    }
    cache[cacheKey] = rv;
  }
  return cache[cacheKey];
}

// Maximum size of lambda term to consider, measured in number of application nodes
const N = 5;

const DEBUG = false;
if (DEBUG) {
  for (let i = 0; i <= N; i++) {

    terms(0, i).forEach(e => {
      console.log(stringify(e));
      console.log(constraints(e));
    });
  }
  process.exit(0);
}

// All coloring constraints that arise from lambda terms. The value in
// the map is some arbitrary example term the constraint arose in.
const allConsts: { [k: string]: string } = {};


// Accumulate all the constraints we find
for (let i = 0; i <= N; i++) {
  terms(0, i).forEach(e => {
    const c = constraints(e).forEach(cc => {
      if (cc != '')
        allConsts[cc] = stringify(e);
    });
  });
}

function z3OfConstraintList(cs: [string, string][]): string {
  let rv: string = '';
  const singletons = cs.map(x => x[0]).filter(x => !x.match(/\//));
  singletons.forEach(s => {
    // Each variable has to have a color
    rv += `(declare-const ${s} (_ BitVec 2))\n`;
  });

  cs.forEach(c => {
    // Each constraint must be satisfied
    rv += `(assert (not (= #b00 (bvxor ${c[0].split('/').join(' ')})))) ; ${c[1]}\n`;
  })
  rv += '(check-sat)\n';
  rv += '(get-model)\n';
  return rv;
}

process.stdout.write(z3OfConstraintList(Object.entries(allConsts)));
