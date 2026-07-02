#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# Usage: run_tests.sh [file1.wlt file2.wlt ...]
# Defaults to Tests.wlt when no arguments are given.
FILES=("${@:-Tests.wlt}")

total_passed=0
total_failed=0

run_suite() {
  local file="$1"
  echo "=== $file ==="
  wolframscript -code "
    r = TestReport[\"$file\"];
    results = r[\"TestResults\"];
    passed = 0; failed = 0;
    KeyValueMap[Function[{id, res},
      name = ToString[res[\"TestID\"]];
      If[res[\"Outcome\"] === \"Success\",
        passed++;
        Print[\"\033[32m  PASS\033[0m  \" <> name],
        failed++;
        Print[\"\033[31m  FAIL\033[0m  \" <> name];
        Print[\"         Input    : \" <> ToString[res[\"TestInput\"][[1]],    InputForm]];
        Print[\"         Expected : \" <> ToString[res[\"ExpectedOutput\"][[1]], InputForm]];
        Print[\"         Got      : \" <> ToString[res[\"ActualOutput\"][[1]],  InputForm]]
      ]
    ], results];
    Print[\"\"];
    Print[ToString[passed] <> \" passed, \" <> ToString[failed] <> \" failed\"];
    If[failed > 0, Exit[1], Exit[0]]
  "
}

overall_exit=0
for f in "${FILES[@]}"; do
  if run_suite "$f"; then
    :
  else
    overall_exit=1
  fi
done

exit $overall_exit
