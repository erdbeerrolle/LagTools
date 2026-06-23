#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

wolframscript -code '
  r = TestReport["Tests.wlt"];
  results = r["TestResults"];
  passed = 0; failed = 0;
  KeyValueMap[Function[{id, res},
    name = ToString[res["TestID"]];
    If[res["Outcome"] === "Success",
      passed++;
      Print["\033[32m  PASS\033[0m  " <> name],
      failed++;
      Print["\033[31m  FAIL\033[0m  " <> name];
      Print["         Input    : " <> ToString[res["TestInput"], InputForm]];
      Print["         Expected : " <> ToString[res["ExpectedOutput"], InputForm]];
      Print["         Got      : " <> ToString[res["ActualOutput"], InputForm]]
    ]
  ], results];
  Print[""];
  Print[ToString[passed] <> " passed, " <> ToString[failed] <> " failed"];
  If[failed > 0, Exit[1], Exit[0]]
'
