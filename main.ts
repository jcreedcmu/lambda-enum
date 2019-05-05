type Exp =
  | { t: 'lam', b: Exp }
  | { t: 'app', f: Exp, a: Exp }
  | { t: 'var' };

function stringifyLam(x: Exp): string {
  switch (x.t) {
    case 'lam': return '/' + stringifyLam(x.b);
    case 'app': return '@' + stringifyLam(x.f) + stringifyLam(x.a);
    case 'var': return '*';
  }
}

function _paths(e: Exp, partial: string): string[] {
  switch (e.t) {
    case 'lam': return _paths(e.b, partial + 'B');
    case 'app': return _paths(e.f, partial + 'F').concat(_paths(e.a, partial + 'A'));
    case 'var': return [partial];
  }
}

function paths(e: Exp): string[] {
  return _paths(e, '');
}

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

for (let i = 0; i < 4; i++) {
  //console.log(terms(0, i).length);
  console.log(terms(0, i).map(x => [stringifyLam(x), paths(x)]));
}
