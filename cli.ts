// cli.ts — a small CLI-shaped program to validate Nexa on its main
// target use case: fast-starting native command-line tools.
//
// Assumption: argv access isn't wired into the runtime yet (no process.argv
// binding in the type checker/runtime as of this build), so this stays
// within the confirmed-working subset (functions, control flow, strings,
// numbers, console.log) and simulates a CLI by hard-coding "input" at the
// top of main(). Swap the hard-coded values for real argv reads once
// arg-parsing is wired into the runtime.

function parseIntSafe(s: string): number {
  // Placeholder until real string->number parsing exists in the runtime.
  // For now this just demonstrates the shape of a CLI arg-handling function.
  return 0;
}

function usage(): string {
  return "usage: nexa-cli <command> [args]";
}

function add(a: number, b: number): number {
  return a + b;
}

function sub(a: number, b: number): number {
  return a - b;
}

function mul(a: number, b: number): number {
  return a * b;
}

function runCommand(cmd: string, a: number, b: number): number {
  if (cmd === "add") {
    return add(a, b);
  } else if (cmd === "sub") {
    return sub(a, b);
  } else if (cmd === "mul") {
    return mul(a, b);
  } else {
    console.log(usage());
    return -1;
  }
}

function greet(name: string): string {
  return "hello, " + name;
}

function repeat(n: number): number {
  let count: number = 0;
  for (let i: number = 0; i < n; i = i + 1) {
    console.log(i);
    count = count + 1;
  }
  return count;
}

function main(): number {
  // Simulated CLI input — replace with real argv reads once supported.
  const command: string = "add";
  const argA: number = 7;
  const argB: number = 5;
  const userName: string = "nexa";

  console.log(usage());

  let result: number = runCommand(command, argA, argB);
  console.log(result); // 12

  console.log(greet(userName)); // "hello, nexa"

  let printed: number = repeat(5); // prints 0..4
  console.log(printed); // 5

  return 0;
}

main();
