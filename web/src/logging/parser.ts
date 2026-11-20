// Parses human-friendly schedule text into Operation instances and serializes
// Operation lists back into editable text.
//
// Supported formats (one operation per line, or semicolon-separated):
//   START T1
//   READ T1 X          (or R(T1, X))
//   WRITE T1 X 12      (or W(T1, X, 12))
//   COMMIT T1          (or C(T1))
//   ABORT T1           (or A(T1))
//   CHECKPOINT         (or CKPT)

import {
  AbortOp,
  CheckpointOp,
  CommitOp,
  ReadOp,
  StartOp,
  WriteOp,
  type Operation
} from "./dispatch";

export interface ParseResult {
  operations: Operation[];
  parseErrors: string[];
}

export function parseScheduleText(input: string): ParseResult {
  const operations: Operation[] = [];
  const parseErrors: string[] = [];

  const rawLines = input
    .split(/[\n;]+/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0 && !line.startsWith("//") && !line.startsWith("#"));

  rawLines.forEach((line, idx) => {
    const lineNum = idx + 1;
    const tokens = line
      .replace(/[(),]/g, " ")
      .split(/\s+/)
      .filter(Boolean);

    if (tokens.length === 0) return;

    const cmd = tokens[0].toUpperCase();
    switch (cmd) {
      case "START":
      case "S":
      case "BEGIN": {
        if (tokens.length !== 2) {
          parseErrors.push(`Line ${lineNum}: expected "START <Tx>" (got "${line}").`);
          return;
        }
        operations.push(new StartOp(tokens[1]));
        break;
      }
      case "READ":
      case "R": {
        if (tokens.length !== 3) {
          parseErrors.push(`Line ${lineNum}: expected "READ <Tx> <Element>" (got "${line}").`);
          return;
        }
        operations.push(new ReadOp(tokens[1], tokens[2]));
        break;
      }
      case "WRITE":
      case "W": {
        if (tokens.length !== 4) {
          parseErrors.push(
            `Line ${lineNum}: expected "WRITE <Tx> <Element> <Integer>" (got "${line}").`
          );
          return;
        }
        const num = Number(tokens[3]);
        if (!Number.isInteger(num)) {
          parseErrors.push(
            `Line ${lineNum}: WRITE value must be an integer (got "${tokens[3]}").`
          );
          return;
        }
        operations.push(new WriteOp(tokens[1], tokens[2], num));
        break;
      }
      case "COMMIT":
      case "C": {
        if (tokens.length !== 2) {
          parseErrors.push(`Line ${lineNum}: expected "COMMIT <Tx>" (got "${line}").`);
          return;
        }
        operations.push(new CommitOp(tokens[1]));
        break;
      }
      case "ABORT":
      case "A":
      case "ROLLBACK": {
        if (tokens.length !== 2) {
          parseErrors.push(`Line ${lineNum}: expected "ABORT <Tx>" (got "${line}").`);
          return;
        }
        operations.push(new AbortOp(tokens[1]));
        break;
      }
      case "CHECKPOINT":
      case "CKPT": {
        if (tokens.length !== 1) {
          parseErrors.push(`Line ${lineNum}: expected "CHECKPOINT" with no arguments (got "${line}").`);
          return;
        }
        operations.push(new CheckpointOp());
        break;
      }
      default:
        parseErrors.push(
          `Line ${lineNum}: unknown operation "${tokens[0]}". Use START, READ, WRITE, COMMIT, ABORT, or CHECKPOINT.`
        );
    }
  });

  return { operations, parseErrors };
}

export function serializeSchedule(ops: readonly Operation[]): string {
  return ops.map((op) => op.format()).join("\n");
}
