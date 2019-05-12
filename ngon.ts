import { Color, Coloring, oppo as opp, third, transpose } from './common';


// Returns a list of all the ways you can color the
// edges *of* the n-gon (as opposed to the edges coming out of it)
// assuming the first color is 0 and the last is 1.
function enumColorsOnNgon(N: number, nonstd?: boolean): Coloring[] {
  if (nonstd) {
    if (N == 2) return [];
    if (N == 3) return [];
    if (N == 4) return [[0, 1, 0, 1]];
  }
  else {
    if (N == 2) return [[0, 1]];
    if (N == 3) return [[0, 2, 1]];
    if (N == 4) return [[0, 2, 0, 1], [0, 1, 2, 1]];
  }

  const pprev1 = enumColorsOnNgon(N - 2, nonstd).map(c => c.concat([0, 1]));
  const pprev2 = enumColorsOnNgon(N - 2, nonstd).map(c => c.map(opp).concat([0, 1]));
  const prev = enumColorsOnNgon(N - 1, nonstd).map(c => c.map(opp).concat([1]));

  return pprev1.concat(pprev2, prev);
}

// Take a coloring of the edges *of* the n-gon and return
// a coloring of the free variables.
function convert(c: Coloring): Coloring {
  return c.map((x, i) => transpose(1, third(x, c[(i + 1) % c.length]))).slice(0, c.length - 1);
}

for (let i = 3; i < 8; i++) {
  console.log(i, enumColorsOnNgon(i, true).map(convert).map(c => c.join('')));
}
