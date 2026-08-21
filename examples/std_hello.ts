// std_hello.ts — std namespace acceptance test
// Run: echo "nexa" | ./std_hello

function main(): number {
  std.log("enter your name:");
  let name: string = std.in();
  std.log("hello, " + name);
  return 0;
}
