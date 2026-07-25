/-
  RTO (Round-To-Odd) Property for P3109 Projection

  The RTO property states: when a real value x is not exactly representable
  in the target format, the projected result has an odd significand (fnum).

  This file proves the RTO property for `project` when the input is in the
  representable range, where saturation is inactive. Overflow behavior is
  mode-, domain-, and saturation-dependent and is characterized in
  `Projection.lean` without collapsing NaN to an extended-real value.

  The parity characterizations are proved in `RtoParity.lean`.
  The core RTO property for `round_fp` is proved in `RtoCore.lean`.
-/
import Flops.P3109.Projection
import Flops.P3109.RtoCore
import Flops.P3109.RtoParity

variable {f : p3109_format}

set_option maxHeartbeats 800000

namespace p3109_format
namespace p3109

/-! ### Main theorem: RTO property for projection (in-range case) -/

/-- Helper: project_in_bound fnum equals round_to_fp fnum -/
lemma project_in_range_fnum_eq_round_fnum (x : ℝ) (sat : SaturationMode)
    (h : @min_finite f ≤ x ∧ x ≤ @max_finite f) :
    (@project f x .RTO sat).fnum = (@round_to_fp f .RTO x).fnum := by
  rw [project_in_bound_eq_round' x .RTO sat h]
  simp only [fnum, to_p3109]

/-- Helper: round_to_fp .RTO x = round_fp to_odd x -/
lemma round_to_fp_RTO_eq (x : ℝ) :
    @round_to_fp f .RTO x = @round_fp f.to_format (@to_odd f.to_format) x := by
  simp only [round_to_fp]

/-- Helper: if round_to_fp .RTO x = (x : ℝ), then project returns x. -/
lemma project_eq_x_of_round_eq (x : ℝ) (sat : SaturationMode)
    (h : @min_finite f ≤ x ∧ x ≤ @max_finite f)
    (hrnd : (@round_to_fp f .RTO x : ℝ) = x) :
    (@project f x .RTO sat : ℝ) = x := by
  rw [project_real_in_bound_eq_round x .RTO sat h]
  rw [round_to_fp_eq, round_to_fp_RTO_eq]
  exact hrnd

/-- **Main RTO theorem (in-range)**: When x is in the representable range
    [min_finite, max_finite] and x is not exactly representable,
    the projected value has odd significand. -/
theorem project_rto_odd_in_range (x : ℝ) (sat : SaturationMode) :
    @min_finite f ≤ x →
    x ≤ @max_finite f →
    (x : ℝ) ≠ (@project f x .RTO sat : ℝ) →
    Odd (@project f x .RTO sat).fnum := by
  intro hmin hmax hne
  have hbound : @min_finite f ≤ x ∧ x ≤ @max_finite f := ⟨hmin, hmax⟩
  rw [project_in_range_fnum_eq_round_fnum x sat hbound]
  rw [round_to_fp_RTO_eq]
  -- Now we need: Odd (round_fp to_odd x).fnum
  apply round_fp_to_odd_fnum_odd
  -- x ≠ 0
  · intro heq
    exfalso; apply hne
    have hbound0 : @min_finite f ≤ (0:ℝ) ∧ (0:ℝ) ≤ @max_finite f := by
      subst heq; exact hbound
    have : (0:ℝ) = (@project f (0:ℝ) .RTO sat : ℝ) :=
      (project_eq_x_of_round_eq 0 sat hbound0 (by
        rw [round_to_fp_RTO_eq]; simp only [round_fp_0_0])).symm
    subst heq; exact this
  -- round ≠ x
  · intro hrnd
    exfalso; apply hne
    exact (project_eq_x_of_round_eq x sat hbound (by
      rw [round_to_fp_RTO_eq]
      exact hrnd)).symm

end p3109
end p3109_format
