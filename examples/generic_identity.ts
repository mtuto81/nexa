function identity<T>(x: T): T {
  return x;
}

function main(): number {
  std.log(identity<number>(5));
  std.log(identity<string>("hello"));
  std.log(identity<boolean>(true));
  return 0;
}

main();
