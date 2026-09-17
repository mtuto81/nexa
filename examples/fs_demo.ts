import * as fs from "std/fs";

function main(): number {
  let path: string = "/tmp/nexa-fs-demo.txt";
  fs.writeTextFile(path, "hello from nexa\n");
  fs.appendTextFile(path, "filesystem works\n");
  


  std.log(fs.exists(""));
  
 // Bundled module types are flattened into the program, so the exported
  // Buffer type is named directly in annotations.
  let contents: Buffer = fs.readFile(path);
  std.log(contents.length);
  std.log(fs.readTextFile(path));
  fs.freeBuffer(contents);
  return 0;
}

main();
