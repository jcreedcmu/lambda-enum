// The following code, by outputting nothing, refutes the hypothesis
// that there exists four ternary linear combinations over three
// variables that take the values {1,2} that produce 8 distinct colorings
// that all fit inside the pentagon's coloring set.

//// The following is a tree, and produces valid output if substituted for the pentagon:
// const _shape = "0102 1002 1222 2122 1211 2111 2001 0201";

// The following is the colorings the pentagon admits:
const _shape = "1112 2221 2111 1222 0120 0210 1200 2100 0012 0021";

const pentagon: { [k: string]: boolean } = {};
_shape.split(' ').forEach(k => pentagon[k] = true);

function parse(n: number): number[] {
  const a = n % 3;
  const b = ((n - a) / 3) % 3;
  const c = ((n - a) / 3 - b) / 3;
  return [a, b, c];
}

function attempt(i: number[], j: number[], k: number[], l: number[]) {
  const accum: { [k: string]: boolean } = {};
  for (let a = 1; a < 3; a++) {
    for (let b = 1; b < 3; b++) {
      for (let c = 1; c < 3; c++) {
        const ii = (a * i[0] + b * i[1] + c * i[2]) % 3;
        const jj = (a * j[0] + b * j[1] + c * j[2]) % 3;
        const kk = (a * k[0] + b * k[1] + c * k[2]) % 3;
        const ll = (a * l[0] + b * l[1] + c * l[2]) % 3;
        const s = `${ii}${jj}${kk}${ll}`;
        if (!pentagon[s]) return false;
        accum[s] = true;
      }
    }
  }
  return Object.keys(accum).length == 8;
}

function main() {
  for (let i = 1; i < 27; i++) {
    for (let j = 1; j < 27; j++) {
      for (let k = 1; k < 27; k++) {
        for (let l = 1; l < 27; l++) {
          if (attempt(parse(i), parse(j), parse(k), parse(l)))
            console.log(parse(i), parse(j), parse(k), parse(l));
        }
      }
    }
  }
}


main();
