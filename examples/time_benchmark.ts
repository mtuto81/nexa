import * as time from "std/time";

function sumTo(n: number): number {
  let total: number = 0;
  for (let i: number = 0; i < n; i = i + 1) {
    total = total + i;
  }
  return total;
}

function main(): number {
  let start: number = time.nowMs();
  let result: number = sumTo(100000000);
  let elapsed: number = time.nowMs() - start;
  std.log(result);
  std.log(elapsed);
  return 0;
}

main();
