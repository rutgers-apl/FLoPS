import Flops.Core.Defs

/-!
# Shared executable binary rounding kernel

The Core and P3109 executable rounders use the same quotient/remainder
decision for their deterministic IEEE-style modes.  This module deliberately
knows nothing about either format record or their enclosing value types: each
caller supplies its precision, bias, quotient, residue, and sign.
-/

namespace Flops.Exec.RoundKernel

/-- Deterministic rounding modes supported by the common residue kernel. -/
inductive Mode where
  | RD | RU | RZ | RNE | RNA | RTO
  deriving Repr, BEq, DecidableEq

/-- Whether a nonnegative quotient/remainder should be increased by one. -/
@[simp] def roundAway (precision : Nat) (bias : Int) (mode : Mode)
    (q r d : Nat) (exponent sign : Int) : Bool :=
  let qInt : Int := q
  match mode with
  | .RD => decide (sign < 0 ∧ r ≠ 0)
  | .RU => decide (0 < sign ∧ r ≠ 0)
  | .RZ => false
  | .RNE =>
    decide
      (2 * r > d ∨
        (2 * r = d ∧
          if 1 < precision then Even (qInt + 1)
          else Even (exponent + bias + 1) ∧ q ≠ 0))
  | .RNA => decide (2 * r ≥ d)
  | .RTO =>
    decide (r ≠ 0 ∧
      (if 1 < precision then Even qInt else q = 0 ∨ Even (exponent + bias)))

end Flops.Exec.RoundKernel
