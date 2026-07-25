import Flops.P3109.Rounding
import Flops.Core.RoundingError

lemma rounding_error_p3109_lt_ulp  (r : ℝ) (rnd : RoundingMode) :
  |r - @round_to_fp f rnd r| < @ulp f.to_format (@round_to_fp f rnd r) (@round_to_fp_canonical f rnd r)
  := by
  simp only [round_to_fp]
  split
  repeat apply rounding_error_lt_ulp

lemma epsilon_p3109_lt_ulp (r : ℝ) (rnd : RoundingMode) :
  ∃ε, @round_to_fp f rnd r = r + ε ∧ |ε| < @ulp f.to_format (@round_to_fp f rnd r) (@round_to_fp_canonical f rnd r) := by
  exists (@round_to_fp f rnd r - r)
  simp only [add_sub_cancel, true_and]
  rw [abs_sub_comm]; apply rounding_error_p3109_lt_ulp
