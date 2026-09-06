let string1: string = "Hello, World!";
let string2: string = "Hello,"+ " World!";
let string3: string = "Hello, Tiold!";
let float: f32 = 3.14;
function main(): number {
  if (string1 == string2) {
    std.log("equal (same content, should match)");
  } else {
    std.log("BUG: same content reported unequal");
  }

  if (string1 == string3) {
    std.log("BUG: different content reported equal");
  } else {
    std.log("not equal (different content, correctly distinguished)");
  }
  std.log(float);
  return 0;

}
main();