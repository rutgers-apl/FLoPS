#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
harness="$root/tools/p3109-table-check"
work=$(mktemp -d "${TMPDIR:-/tmp}/p3109-table-check.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM

"${CC:-cc}" -std=c11 -Wall -Wextra -Werror -pedantic \
  "$harness/p3109_table_reference.c" -o "$work/p3109_table_reference"
"$work/p3109_table_reference" > "$work/c.txt"

(
  cd "$root"
  lake env lean --run tools/p3109-table-check/LeanTableDump.lean
) > "$work/lean.txt"

diff -u "$harness/k4-expected.txt" "$work/c.txt"
diff -u "$harness/k4-expected.txt" "$work/lean.txt"

printf '%s\n' \
  'P3109 K=4 table check passed: 224 code points across 14 formats.'
