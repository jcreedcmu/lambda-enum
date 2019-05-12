import { Color, Coloring, opp } from './common';

function transpose(x: 1 | 2, y: Color): Color {
  if (y == x)
    return 0;
  else if (y == 0)
    return x;
  else
    return y;
}

function applyLam(c: Coloring): Coloring[] {
  const k: Color = c[0];
  if (k == 0)
    return [];
  else {
    return [c.slice(1).map(x => transpose(opp(k), x))];
  }
}

function applyLamMany(cc: Coloring[]): Coloring[] {
  let rv: Coloring[] = [];
  cc.forEach(c => {
    rv = rv.concat(applyLam(c));
  });
  return rv;
}

// console.log(applyLam([0, 1, 2, 0, 1, 2]).length == 0);
// console.log(JSON.stringify(applyLam([1, 2, 0, 1, 2, 0])) == "[[0,2,1,0,2]]");

function t1(c: Coloring): Coloring {
  return c.map(x => transpose(1, x));
}

function t2(c: Coloring): Coloring {
  return c.map(x => transpose(2, x));
}

function applyApp(c: Coloring, d: Coloring): Coloring[] {
  return [t1(c).concat(t2(d)), t2(c).concat(t1(d))];
}

function applyAppMany(cc: Coloring[], dd: Coloring[]): Coloring[] {
  let rv: Coloring[] = [];
  cc.forEach(c => {
    dd.forEach(d => {
      rv = rv.concat(applyApp(c, d));
    });
  });
  return rv;
}

//console.log(JSON.stringify(applyApp([0, 1, 2], [1, 1, 1])) == "[[1,0,2,1,1,1],[2,1,0,0,0,0]]")

type Row = { [k: string]: boolean };
type State = { total: number, counts: number[], rows: Row[] };


function emptyState(N: number): State {
  return {
    total: 0,
    counts: Array.from({ length: N }, x => 0),
    rows: Array.from({ length: N }, (x, i) => ({}))
  };
}

function makeKey(c: Coloring[]): string {
  const colorings: { [k: string]: boolean } = {}
  c.forEach(x => colorings[x.join('')] = true);
  const cc = Object.keys(colorings);
  cc.sort();
  return cc.join('-');
}

function parseKey(s: string): Coloring[] {
  return s.split('-').map(x => (x.split('').map(x => parseInt(x) as Color)));
}

// let state = emptyState(N);
// state.rows[0][makeKey([[2, 1, 0], [0, 1, 2]])] = true;
// console.log(state);

function iter1(s: State, N: number): State {
  const rv = emptyState(N);
  for (let i = 0; i < N; i++) {
    Object.keys(s.rows[i]).forEach(k => {
      rv.rows[i][k] = s.rows[i][k];
    });
  }

  // Lambdas
  for (let i = 0; i < N - 1; i++) {
    Object.keys(s.rows[i + 1]).forEach(k => {
      rv.rows[i][makeKey(applyLamMany(parseKey(k)))] = true;
    });
  }

  // Applications
  for (let i = 1; i < N; i++) {
    for (let j = 1; j <= N - i; j++) {
      Object.keys(s.rows[i - 1]).forEach(k1 => {
        Object.keys(s.rows[j - 1]).forEach(k2 => {
          rv.rows[i + j - 1][makeKey(applyAppMany(parseKey(k1), parseKey(k2)))] = true;
        });
      });
    }
  }

  // Count
  for (let i = 0; i < N; i++) {
    Object.keys(rv.rows[i]).forEach(k => {
      rv.total++;
      rv.counts[i]++;
    });
  }
  return rv;
}

function uniq(x: string[]): string[] {
  const map: { [k: string]: boolean } = {};
  x.forEach(t => map[t] = true);
  const rv = Object.keys(map);
  rv.sort();
  return rv;
}

function experiment1() {
  const N = 6;

  let state = emptyState(N);
  state.rows[0][makeKey([[0]])] = true;

  while (1) {
    const old = state.total;
    state = iter1(state, N);
    if (state.total == old) break;
  }

  console.log('total', state.total);
  console.log('counts', state.counts);
}

function iter2(cc: Coloring[]): Coloring[] {
  let rv: Coloring[] = [];
  cc.forEach(c => {
    const more = applyApp(c, [0]);
    rv = rv.concat(more);
  });
  return rv;
}

function flip(x: string): string {
  let cs = x.split('');
  cs.reverse();
  cs = cs.map(x => x == '2' ? '1' : x == '1' ? '2' : '0');
  return cs.join('');
}

function experiment2() {
  for (let N = 0; N < 18; N++) {
    let cc: Coloring[] = [[0]];
    for (let i = 0; i < N; i++)
      cc = iter2(cc);
    cc = applyLamMany(cc);
    let s = uniq(cc.map(c => c.join('')));
    s = s.filter(c => c != flip(c));
    console.log(s.length);
    if (s.length <= 36) console.log(s);
  }
}

experiment2();
