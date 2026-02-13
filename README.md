# Semantics, Operations, and Properties of P3109 Floating-Point Representations in Lean
This repository is the accompanying Lean source code of formalizing the P3109 standard in Lean.

The upcoming IEEE-P3109 standard for low-precision floating-point arithmetic is poised to become the foundation of future machine learning hardware and software. Unlike the fixed types of IEEE-754, P3109 introduces a parametric framework defined by bitwidth, precision, signedness, and domain. This flexibility results in a vast combinatorial space of formats — some with as little as one bit of precision — alongside novel features such as stochastic rounding and saturation arithmetic. These deviations create a unique verification gap that this paper intends to address.

This paper presents **FLoPS**, **F**ormalization in **L**ean **o**f the **P**3109 **S**tandard, which is the first formal model of P3109 in Lean. Our work serves as a rigorous, machine-checked specification
that facilitates deep analysis of the standard. We demonstrate the model's utility by verifying foundational properties and analyzing key algorithms within the P3109 context.
Specifically, we reveal that FastTwoSum exhibits a novel property of computing exact "overflow error" under saturation using any rounding mode, whereas previously established properties of the ExtractScalar algorithm fail for formats with one bit of precision. This work provides a verified foundation for reasoning about P3109 and enables formal verification of future numerical software.

## Project Structure
The outer directory, Flops/, contains the general definition of the abstract model (formats with subnormals and no exponent upper bound) and foundational properties of floating-point arithmetic. The directory Flops/P3109 is the actual formalization of the P3109 standard. The directory can be roughly grouped in three parts:
- Formalization of definitions from the standard: `Defs.lean`, `Rounding.lean`, `Projection.lean`, `KApproximate.lean`. `Defs.lean` contains the P3109 algebraic data type.
- Correctness guarantees: `Emax.lean`, `Bijection.lean`, `RoundTrip.lean`.
- Properties of P3109 arithmetic: `Sterbenz.lean`, `Fast2Sum.lean`, `Fast2SumSat.lean`, `Scalar.lean`.

## Compiling Instructions
The formalization has been developed in `Lean 4` and its math library `Mathlib`. For detailed instructions to install Lean, Mathlib, and build system, visit the [Lean Community website](https://lean-lang.org/install/).

After the repo is cloned to your local computer, you can open VSCode and run the extension, or enter `lake build` in the root directory using command line.
