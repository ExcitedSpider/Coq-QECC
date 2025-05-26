#!/usr/bin/env zx

let [file, startLine, endLine] = argv._;
startLine = Number(startLine);
endLine = Number(endLine);

if (!file || isNaN(startLine) || isNaN(endLine)) {
  console.error("Usage: count_proof <file> <startLine> <endLine>");
  process.exit(1);
}

const lines = (await fs.readFile(file, "utf8")).split("\n");

// Slice the target range
const sliced = lines.slice(startLine - 1, endLine); // lines are 1-indexed
let inProof = false;
let count = 0;

for (const line of sliced) {
  if(line.trim().startsWith("Proof") &&line.trim().startsWith("Qed")) {
    count ++;
    continue;
  }
  if (line.trim().startsWith("Proof")) {
    inProof = true;
    continue;
  }
  if (line.trim().startsWith("Qed")) {
    inProof = false;
    continue;
  }
  if (inProof) count++;
}

console.log(`Proof lines between line ${startLine} and ${endLine}: ${count} in ${endLine - startLine} lines`);
