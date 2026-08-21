// stats.ts — a small stats calculator compiled by Nexa to a native binary

function isPrime(n: number): boolean {
  if (n < 2) {
    return false;
  }
  let i: number = 2;
  while (i * i <= n) {
    if (n % i === 0) {
      return false;
    }
    i = i + 1;
  }
  return true;
}

function countPrimes(limit: number): number {
  let count: number = 0;
  for (let n: number = 2; n <= limit; n = n + 1) {
    if (isPrime(n)) {
      count = count + 1;
    }
  }
  return count;
}

function sumOfDigits(n: number): number {
  let sum: number = 0;
  let x: number = n;
  while (x > 0) {
    sum = sum + (x % 10);
    x = x / 10;
  }
  return sum;
}

function factorial(n: number): number {
  if (n <= 1) {
    return 1;
  }
  return n * factorial(n - 1);
}

function main(): number {
  let primes: number = countPrimes(100);
  console.log("primes below 100");
  console.log(primes);

  let fact10: number = factorial(10);
  console.log("10!");
  console.log(fact10);

  let ds: number = sumOfDigits(9876);
  console.log("digit sum of 9876");
  console.log(ds);

  let total: number = 0;
  for (let i: number = 1; i <= 20; i = i + 1) {
    if (i % 3 === 0) {
      total = total + i;
    }
  }
  console.log("sum of multiples of 3 up to 20");
  console.log(total);

  return 0;
}

main();
