export type Color = 0 | 1 | 2;
export type Coloring = Color[];

function wtf<T>(x: T, n: T): T {
  return n;
}

export function oppo(x: Color): Color {
  switch (x) {
    case 0: return 0;
    case 1: return 2;
    case 2: return 1;
  }
}

export function opp(x: 1 | 2): 1 | 2 {
  switch (x) {
    case 1: return 2;
    case 2: return 1;
  }
}

export function third(x: Color, y: Color): Color {
  if (x == y) throw new Error('domain');
  return (((x + 1) ^ (y + 1)) - 1) as Color;
}

export function transpose(x: Color, y: Color): Color {
  if (x == y) return x;
  return (((x + 1) ^ (y + 1)) - 1) as Color;
}
