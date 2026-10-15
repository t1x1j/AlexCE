#!/bin/bash
# Host tests of the steps (steps.cc): builds tools/hostgiac (worktree), prints the steps of
# tests/host/steps_cases.txt and checks their labels. Usage (WSL): run_steps_tests.sh
set -e
T=$(cd "$(dirname "$0")" && pwd); R=$(cd "$T/../.." && pwd)
export HG_BUILD=${HG_BUILD:-$HOME/flowce-build/hostgiac}
bash "$R/tools/hostgiac/build.sh" worktree > /tmp/steps_build.log 2>&1 || { tail -30 /tmp/steps_build.log; exit 1; }
cut -d: -f1 "$T/steps_cases.txt" | sed 's/ *$//' | grep -v '^#' | grep -v '^$' > /tmp/steps_inputs.txt
"$HG_BUILD/bin/hostgiac-worktree" -k -S -p -f /tmp/steps_inputs.txt > /tmp/steps_out.txt 2>&1
cat /tmp/steps_out.txt
python3 "$T/check_steps.py" "$T/steps_cases.txt" /tmp/steps_out.txt
