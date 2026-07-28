# Semantics, Operations, and Properties of P3109 Floating-Point Representations in Lean

by [Tung-Che Chang](https://farmerzhang1.github.io/), [Sehyeok
Park](https://people.cs.rutgers.edu/~santosh.nagarakatte/rapl/index.html),
[Jay P Lim](https://dongura.me/), and [Santosh
Nagarakatte](https://people.cs.rutgers.edu/~santosh.nagarakatte/)

FLoPS formalizes the IEEE P3109 standard for low-precision
floating-point arithmetic in Lean. This repository is the artifact for
the FMCAD 2026 paper of the same title.

Unlike the fixed types of IEEE 754, P3109 introduces a parametric
framework defined by bit width, precision, signedness, and domain. It
includes formats with as little as one bit of precision, stochastic
rounding, and saturation arithmetic. FLoPS provides a machine-checked
semantic model, proves foundational properties and algorithmic results,
and connects the mathematical model to an executable bit-level kernel.

The preprint is available as [FLoPS: Semantics, Operations, and
Properties of P3109 Floating-Point Representations in
Lean](https://arxiv.org/pdf/2602.15965), Rutgers Department of Computer
Science Technical Report DCS-TR-762, February 2026.

## Project Structure

- `Flops/Core` contains the abstract floating-point model and reusable
  arithmetic results.
- `Flops/P3109` contains the mathematical P3109 semantics, including
  definitions, rounding, projection, saturation, and arithmetic
  properties.
- `Flops/P3109/Exec` contains the executable bit-level model, refinement
  proofs for the representation, projection pipeline, and operations,
  together with executable regression tests.
- `Flops/AccSum` is retained from the reviewed artifact for the
  ExtractScalar case study. It is not part of the P3109 semantic model
  and is unchanged by the camera-ready artifact update.

The P3109 development includes:

- definitions from the standard in `Defs.lean`, `Rounding.lean`, and
  `Projection.lean`;
- rounding results in `RtoProperty.lean`, `StochasticProperties.lean`,
  and `RoundingProjection.lean`;
- representation results in `Emax.lean`, `Bijection.lean`, and
  `RoundTrip.lean`;
- arithmetic results in `Sterbenz.lean`, `Fast2Sum.lean`,
  `Fast2SumSat.lean`, and `ExtractScalar.lean`.

## Executable Semantics

`Flops/P3109/Exec.lean` is the entry point for the executable artifact.
It includes bit-level format descriptions, encoding and decoding,
classification, rounding, saturation, projection, and core operations.
The files under `Flops/P3109/Exec/Refinement` prove that encoding,
decoding, canonicalization, rounding, saturation, projection, arithmetic,
comparisons, and extrema correspond to the mathematical semantics,
including NaN propagation. `Tests.lean` checks these refinement results,
the executable operations, and P3109's exceptional-value rules. It is
elaborated when the entry point is built.

## Building

The artifact uses Lean `v4.28.0` and Mathlib `v4.28.0`, pinned by
`lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`. Install Lean
through [elan](https://lean-lang.org/install/), then run from the
repository root:

```sh
lake build
```

To check only the executable semantics and its refinement proofs:

```sh
lake build +Flops.P3109.Exec
```

To compare the executable decoder and an independent C decoder with all
224 entries in the standard's complete `K = 4` tables:

```sh
./tools/p3109-table-check/check.sh
```

Both commands elaborate the regression examples imported by
`Flops.P3109.Exec`. A successful command exits with status 0.
