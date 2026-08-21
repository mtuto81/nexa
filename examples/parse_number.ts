function main(): number {
  std.log("enter a number:");
  let raw: string = std.in();
  let n: number = std.parseNumber(raw);
  std.log(n + 1);
  return 0;
}

main();
