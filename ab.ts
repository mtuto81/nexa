function main(): number {
  let a: string = "Hello, " + "World!";
  let b: string = "Hello, Tiold!";
  if (a == b) {
    std.log("BUG: different content reported equal");
  } else {
    std.log("correctly distinguished");
  }
  return 0;
}