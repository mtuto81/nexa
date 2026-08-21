class Counter {
  count: number;

  constructor() {
    this.count = 0;
  }

  increment(): number {
    this.count = this.count + 1;
    return this.count;
  }
}

function main(): number {
  let a = new Counter();
  let b = new Counter();
  console.log(a.increment());
  console.log(a.increment());
  console.log(b.increment());
  console.log(a.increment());
  return 0;
}

main();
