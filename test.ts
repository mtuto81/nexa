// test.ts — basic feature coverage for the TS -> Cranelift -> native compiler
// Keep this to the supported subset: let, numbers, strings, functions,
// if/else, while/for loops, recursion, basic arithmetic and comparisons.

function add(a: number, b: number): number {
  return a + b;
}

function sub(a: number, b: number): number {
  return a - b;
}

function isEven(n: number): boolean {
  return n % 2 === 0;
}

function factorial(n: number): number {
  if (n <= 1) {
    return 1;
  }
  return n * factorial(n - 1);
}

function fib(n: number): number {
  if (n < 2) {
    return n;
  }
  return fib(n - 1) + fib(n - 2);
}

function sumLoop(n: number): number {
  let total: number = 0;
  let i: number = 0;
  while (i < n) {
    total = total + i;
    i = i + 1;
  }
  return total;
}

function sumForLoop(n: number): number {
  let total: number = 0;
  for (let i: number = 0; i < n; i = i + 1) {
    total = total + i;
  }
  return total;
}

function classify(n: number): string {
  if (n < 0) {
    return "negative";
  } else if (n === 0) {
    return "zero";
  } else {
    return "positive";
  }
}
extern "C"{
  function malloc(size: number): Pointer;
  function free(ptr: Pointer): void;
}
function main(): number {
  let a: number = add(3, 4);
  let b: number = sub(10, 4);
  let f: number = factorial(5);
  let fb: number = fib(10);
  let s1: number = sumLoop(100);
  let s2: number = sumForLoop(100);
  let even: boolean = isEven(42);
  let label: string = classify(-5);
  let input: string = std.in();
  console.log(a);       // 7
  console.log(b);       // 6
  console.log(f);       // 120
  console.log(fb);      // 55
  console.log(s1);      // 4950
  console.log(s2);      // 4950
  console.log(even);    // true
  console.log(label);   // "negative"
  std.log(input);   // input string

  return 0;
}

main();
