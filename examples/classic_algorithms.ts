// Classic integer algorithms for Nexa benchmarking.
// The program prints deterministic results for correctness and timing checks.

function fibonacci(n: number): number {
  let a: number = 0;
  let b: number = 1;
  for (let i: number = 0; i < n; i = i + 1) {
    let next: number = a + b;
    a = b;
    b = next;
  }
  return a;
}

function gcd(a: number, b: number): number {
  while (b != 0) {
    let r: number = a % b;
    a = b;
    b = r;
  }
  return a;
}

function binarySearch(values: number[], target: number): number {
  let low: number = 0;
  let high: number = 99999;
  while (low <= high) {
    let middle: number = (low + high) / 2;
    if (values[middle] == target) { return middle; }
    if (values[middle] < target) {
      low = middle + 1;
    } else {
      high = middle - 1;
    }
  }
  return -1;
}

function insertionSort(values: number[], n: number): number {
  for (let i: number = 1; i < n; i = i + 1) {
    let item: number = values[i];
    let j: number = i - 1;
    while (j >= 0 && values[j] > item) {
      values[j + 1] = values[j];
      j = j - 1;
    }
    values[j + 1] = item;
  }
  return values[0] + values[n - 1];
}

function sieve(limit: number): number {
  let composite: number[] = new Array<number>(limit);
  for (let i: number = 0; i < limit; i = i + 1) {
    composite[i] = 0;
  }
  for (let p: number = 2; p * p < limit; p = p + 1) {
    if (composite[p] == 0) {
      for (let multiple: number = p * p; multiple < limit; multiple = multiple + p) {
        composite[multiple] = 1;
      }
    }
  }
  let count: number = 0;
  for (let i: number = 2; i < limit; i = i + 1) {
    if (composite[i] == 0) { count = count + 1; }
  }
  return count;
}

function main(): number {
  let sorted: number[] = new Array<number>(100000);
  for (let i: number = 0; i < 100000; i = i + 1) {
    sorted[i] = i * 2;
  }
  let unsorted: number[] = new Array<number>(3000);
  for (let i: number = 0; i < 3000; i = i + 1) {
    unsorted[i] = 3000 - i;
  }

  console.log(fibonacci(45));
  console.log(gcd(1234567890, 987654321));
  console.log(binarySearch(sorted, 199998));
  console.log(insertionSort(unsorted, 3000));
  console.log(sieve(200000));
  return 0;
}

main();
