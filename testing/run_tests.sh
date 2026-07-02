#!/usr/bin/env bash
set -uo pipefail

cd "$(dirname "$0")/.."

# Usage: run_tests.sh [file1.wlt file2.wlt ...]
# Defaults to Tests.wlt when no arguments are given.
#
# With a tty, shows a live progress bar (one block per test: green = passed,
# red = failed, grey = pending) plus elapsed time and a done/total counter.
# The exact total -- even for suites that generate their tests at runtime --
# comes from a second, concurrent kernel that stubs out VerificationTest
# with a counting no-op and Gets the file (test bodies stay unevaluated
# because VerificationTest is HoldAllComplete). The tests themselves run in
# a plain TestReport kernel.
#
# After the run only failures are printed (TestID, input, expected, got).
FILES=("${@:-testing/Tests.wlt}")

WORK=$(mktemp -d)
IS_TTY=0
[[ -t 1 ]] && IS_TTY=1

runner_pid=""
counter_pid=""

cleanup() {
  [[ -n $runner_pid ]] && kill "$runner_pid" 2>/dev/null
  [[ -n $counter_pid ]] && kill "$counter_pid" 2>/dev/null
  (( IS_TTY )) && printf '\033[?25h'   # restore cursor
  rm -rf "$WORK"
}
trap cleanup EXIT
trap 'exit 130' INT TERM

# ---- Wolfram drivers -------------------------------------------------------

cat > "$WORK/count.wl" <<'EOF'
(* count.wl <testfile> <outfile>: count VerificationTest calls without
   evaluating them.  The built-in is shadowed by a counting rule prepended
   to its DownValues; HoldAllComplete keeps the test bodies unevaluated
   while Get runs the file's top-level code (fixtures, generating loops). *)
file = $ScriptCommandLine[[2]];
out  = $ScriptCommandLine[[3]];
VerificationTest[True];              (* trigger autoload before Unprotect *)
Unprotect[VerificationTest];
$vtCount = 0;
DownValues[VerificationTest] =
  Prepend[DownValues[VerificationTest],
    HoldPattern[VerificationTest[___]] :> ($vtCount++; Null)];
Unprotect[$TestFileName];
$TestFileName = ExpandFileName[file];   (* files use DirectoryName[$TestFileName] *)
Get[file];
s = OpenWrite[out];
WriteString[s, "@TOTAL ", ToString[$vtCount], "\n"];
Close[s];
Exit[0]
EOF

cat > "$WORK/run.wl" <<'EOF'
(* run.wl <testfile> <outfile>: plain TestReport run; streams one
   "@RES P|F" line per test (open/append/close so bash sees it at once),
   then failure details and "@DONE".  Exit code 1 iff any test failed. *)
file = $ScriptCommandLine[[2]];
out  = $ScriptCommandLine[[3]];
emit[lines___] := Module[{s = OpenAppend[out]},
  Scan[WriteString[s, #, "\n"] &, {lines}]; Close[s]];
report = TestReport[file,
  HandlerFunctions -> <|"TestEvaluated" ->
    (emit["@RES " <> If[#["Outcome"] === "Success", "P", "F"]] &)|>];
strip[h_] := StringTake[ToString[h, InputForm], {10, -2}];  (* drop HoldForm[ ] *)
failures = Select[Values[report["TestResults"]], #["Outcome"] =!= "Success" &];
Scan[emit[
    "@ID "  <> ToString[#["TestID"]],
    "@IN "  <> strip[#["Input"]],
    "@EXP " <> strip[#["ExpectedOutput"]],
    "@GOT " <> strip[#["ActualOutput"]]] &,
  failures];
emit["@DONE"];
Exit[If[Length[failures] > 0, 1, 0]]
EOF

# ---- live display ----------------------------------------------------------

BLOCKS_PER_LINE=50
lines_drawn=0

draw() {
  local done=${#results} elapsed=$SECONDS buf="" nlines=0 i col c
  (( lines_drawn > 0 )) && printf '\033[%dA\r' "$lines_drawn"
  if [[ -n $total ]]; then
    for ((i = 0; i < total; i++)); do
      if (( i < done )); then
        c=${results:i:1}
        [[ $c == P ]] && col=$'\033[32m' || col=$'\033[31m'
      else
        col=$'\033[90m'
      fi
      buf+="${col}█"
      if (( (i + 1) % BLOCKS_PER_LINE == 0 || i + 1 == total )); then
        buf+=$'\033[0m\033[K\n'
        (( nlines++ ))
      fi
    done
    buf+=$(printf '%02d:%02d  %d/%d' $((elapsed / 60)) $((elapsed % 60)) "$done" "$total")
  else
    buf+=$(printf '%02d:%02d  Loading dependencies...' $((elapsed / 60)) $((elapsed % 60)))
  fi
  buf+=$'\033[K\n'
  (( nlines++ ))
  printf '%s\033[J' "$buf"
  lines_drawn=$nlines
}

print_failures() {
  local stream="$1" red="" off=""
  if (( IS_TTY )); then red=$'\033[31m'; off=$'\033[0m'; fi
  awk -v red="$red" -v off="$off" '
    /^@ID /  { print red "FAIL" off "  " substr($0, 5); next }
    /^@IN /  { print "  Input    : " substr($0, 5); next }
    /^@EXP / { print "  Expected : " substr($0, 6); next }
    /^@GOT / { print "  Got      : " substr($0, 6); next }
  ' "$stream"
}

# ---- run suites ------------------------------------------------------------

overall_exit=0
n=0

for f in "${FILES[@]}"; do
  n=$((n + 1))
  stream="$WORK/$n.stream"
  totalfile="$WORK/$n.total"
  : > "$stream"
  total=""
  results=""
  SECONDS=0

  if (( IS_TTY )); then
    printf '\033[?25l'
    wolframscript -file "$WORK/count.wl" "$f" "$totalfile" >/dev/null 2>&1 &
    counter_pid=$!
  fi

  wolframscript -file "$WORK/run.wl" "$f" "$stream" >/dev/null 2>&1 &
  runner_pid=$!

  if (( IS_TTY )); then
    lines_drawn=0
    while :; do
      [[ -z $total && -s $totalfile ]] && total=$(sed -n 's/^@TOTAL //p' "$totalfile")
      results=$(sed -n 's/^@RES //p' "$stream" | tr -d '\n')
      draw
      kill -0 "$runner_pid" 2>/dev/null || break
      sleep 0.2
    done
    # final state (all results are in once the runner exited)
    results=$(sed -n 's/^@RES //p' "$stream" | tr -d '\n')
    [[ -z $total ]] && total=${#results}
    draw
    printf '\033[?25h'
  fi

  wait "$runner_pid"
  rc=$?
  runner_pid=""
  if [[ -n $counter_pid ]]; then
    kill "$counter_pid" 2>/dev/null
    wait "$counter_pid" 2>/dev/null
    counter_pid=""
  fi

  if ! grep -q '^@DONE$' "$stream"; then
    echo "run_tests.sh: test kernel for $f exited without completing" >&2
    overall_exit=1
    continue
  fi

  print_failures "$stream"
  (( rc != 0 )) && overall_exit=1
done

exit $overall_exit
