class Person {
  name: string;

  constructor(n: string) {
    this.name = n;
  }

  greet(): string {
    return "hello, " + this.name;
  }
}

function main(): number {
  let p = new Person("nexa");
  let q = new Person("codex");
  console.log(p.greet());  // "hello, nexa"
  console.log(q.greet());  // "hello, codex"
  console.log(p.name);     // "nexa"
  return 0;
}

main();
