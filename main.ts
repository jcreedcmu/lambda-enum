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

function terms(vars: number, apps: number): Exp[] {
  const cacheKey = `${vars}/${apps}`;
  if (!cache[cacheKey]) {
    let rv: Exp[] = [];

    if (vars > apps + 1)
      return [];

    if (apps == 0 && vars == 1) {
      rv.push({ t: 'var' });
    }

    rv = rv.concat(terms(vars + 1, apps).map(b => ({ t: 'lam', b })));

    if (apps > 0) {
      for (let i = 0; i <= vars; i++) {
        for (let j = 0; j <= apps - 1; j++) {
          const f = terms(i, j);
          const a = terms(vars - i, apps - j - 1);
          rv = rv.concat(cartprod(f, a, (f, a) => ({ t: 'app', f, a })));
        }
      }
    }
    cache[cacheKey] = rv;
  }
  return cache[cacheKey];
}

for (let i = 0; i < 7; i++) {
  //  console.log(terms(0, 2 * i + 1, true).length);
  console.log(terms(0, i).map(x => stringifyLam(x)).length);
}
