# P3109 K=4 Table Comparison

This harness checks all 224 code points in the 14 complete `K = 4`
format tables in Annex B of P3109/D1 (Tables 4-7).

It compares three independently maintained views of those tables:

- `k4-expected.txt` is an exact dyadic transcription of the published
  tables;
- `p3109_table_reference.c` decodes code points directly from the P3109
  bit-field equations, without using Lean or FLoPS code; and
- `LeanTableDump.lean` obtains values from the executable FLoPS kernel's
  `fromBits` function.

Finite tokens have the form `finite:m:e` and denote `m * 2^e`. Zero is
normalized to `zero`, independently of its internal exponent, and the
special tokens are `+inf`, `-inf`, and `nan`.

Run the check from the repository root:

```sh
./tools/p3109-table-check/check.sh
```

The command requires a C11 compiler, Lake, and the repository's pinned
Lean toolchain.
