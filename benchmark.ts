// benchmark.ts — compute-heavy workloads for measuring native codegen
// performance (compare against ts-node / Node.js / Deno / a JS engine).
// Each function is intentionally simple arithmetic/recursion/loops so it
// stays within the supported compiler subset while still stressing
// codegen: recursion depth, tight loops, and array/memory access.

// 1. Naive recursive fibonacci — stresses function call overhead and
// recursion, no memoization on purpose.
function fib(n: number): number {
  if (n < 2) {
    return n;
  }
  return fib(n - 1) + fib(n - 2);
}

// 2. Tight loop summation — stresses basic loop codegen and integer ops.
function sumTo(n: number): number {
  let total: number = 0;
  for (let i: number = 0; i < n; i = i + 1) {
    total = total + i;
  }
  return total;
}

// 3. Primality test via trial division, run over a range — stresses
// nested loops and branching.
function isPrime(n: number): boolean {
  if (n < 2) {
    return false;
  }
  for (let i: number = 2; i * i <= n; i = i + 1) {
    if (n % i === 0) {
      return false;
    }
  }
  return true;
}

function countPrimes(limit: number): number {
  let count: number = 0;
  for (let n: number = 2; n < limit; n = n + 1) {
    if (isPrime(n)) {
      count = count + 1;
    }
  }
  return count;
}

// 4. Array-heavy workload — stresses memory allocation and load/store.
function sumOfSquaresArray(n: number): number {
  let arr: number[] = new Array<number>(n);
  for (let i: number = 0; i < n; i = i + 1) {
    arr[i] = i * i;
  }
  let total: number = 0;
  for (let i: number = 0; i < n; i = i + 1) {
    total = total + arr[i];
  }
  return total;
}

// 5. Bubble sort — stresses nested loops, comparisons, and swapping via
// array writes (no built-in sort allowed).
function bubbleSort(n: number): number {
  let arr: number[] = new Array<number>(n);
  for (let i: number = 0; i < n; i = i + 1) {
    arr[i] = n - i; // reverse order, worst case for bubble sort
  }
  for (let i: number = 0; i < n; i = i + 1) {
    for (let j: number = 0; j < n - i - 1; j = j + 1) {
      if (arr[j] > arr[j + 1]) {
        let tmp: number = arr[j];
        arr[j] = arr[j + 1];
        arr[j + 1] = tmp;
      }
    }
  }
  return arr[0]; // should be the smallest element
}

function main(): number {
  const fibN: number = 32;
  const sumN: number = 100000000;
  const primeLimit: number = 200000;
  const arrN: number = 1000000;
  const sortN: number = 2000;

  let r1: number = fib(fibN);
  console.log(r1);

  let r2: number = sumTo(sumN);
  console.log(r2);

  let r3: number = countPrimes(primeLimit);
  console.log(r3);

  let r4: number = sumOfSquaresArray(arrN);
  console.log(r4);

  let r5: number = bubbleSort(sortN);
  console.log(r5);

  return 0;
}

main();
