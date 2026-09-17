// The Node.js counterpart to classic_algorithms.ts and classic_algorithms.rs.
// Inputs and output order intentionally match both native benchmarks.

function fibonacci(n) {
  let a = 0;
  let b = 1;
  for (let i = 0; i < n; i++) {
    const next = a + b;
    a = b;
    b = next;
  }
  return a;
}

function gcd(a, b) {
  while (b !== 0) {
    const r = a % b;
    a = b;
    b = r;
  }
  return a;
}

function binarySearch(values, target) {
  let low = 0;
  let high = values.length - 1;
  while (low <= high) {
    const middle = Math.floor((low + high) / 2);
    const value = values[middle];
    if (value === target) return middle;
    if (value < target) low = middle + 1;
    else high = middle - 1;
  }
  return -1;
}

function insertionSort(values) {
  for (let i = 1; i < values.length; i++) {
    const item = values[i];
    let j = i;
    while (j > 0 && values[j - 1] > item) {
      values[j] = values[j - 1];
      j--;
    }
    values[j] = item;
  }
  return values[0] + values[values.length - 1];
}

function sieve(limit) {
  const composite = new Uint8Array(limit);
  for (let p = 2; p * p < limit; p++) {
    if (composite[p] === 0) {
      for (let multiple = p * p; multiple < limit; multiple += p) {
        composite[multiple] = 1;
      }
    }
  }
  let count = 0;
  for (let i = 2; i < limit; i++) {
    if (composite[i] === 0) count++;
  }
  return count;
}

function main() {
  const sorted = new Array(100000);
  for (let i = 0; i < 100000; i++) sorted[i] = i * 2;
  const unsorted = new Array(3000);
  for (let i = 0; i < 3000; i++) unsorted[i] = 3000 - i;

  console.log(fibonacci(45));
  console.log(gcd(1234567890, 987654321));
  console.log(binarySearch(sorted, 199998));
  console.log(insertionSort(unsorted));
  console.log(sieve(200000));
}

main();
