import Mathlib.Data.Nat.Basic

/-! Executable P3109 rounding and saturation mode tags. -/

inductive RoundingMode where
  | RD | RU | RZ | RNE | RNA | RTO
  | StochasticA (N : ℕ) (R : ℕ) (h : 0 ≤ R ∧ R < 2 ^ N)
  | StochasticB (N : ℕ) (R : ℕ) (h : 0 ≤ R ∧ R < 2 ^ N)
  | StochasticC (N : ℕ) (R : ℕ) (h : 0 ≤ R ∧ R < 2 ^ N)

inductive SaturationMode where
  | SatFinite | SatPropagate | SatNone
