/-
  Mode-specific properties of precision rounding.

  This file proves mode-specific correctness properties of
  `round_to_precision` (RD, RU, RZ, RNE, RNA).

  ## Main results

  These hold for ALL extended real inputs with no conditions:

  - `round_to_precision_RD_le`: RD never rounds up: `round_to_precision x .RD ≤ x`
  - `round_to_precision_RU_ge`: RU never rounds down: `x ≤ round_to_precision x .RU`
  - `round_to_precision_RZ_le_of_nonneg`: RZ rounds toward zero for nonneg
  - `round_to_precision_RZ_ge_of_nonpos`: RZ rounds toward zero for nonpos
  - `round_to_precision_RNE_nearest`: RNE is nearest for real inputs
  - `round_to_precision_RNA_nearest`: RNA is nearest for real inputs

-/

import Mathlib.Tactic
import Flops.P3109.Projection

variable {f : p3109_format}

set_option maxHeartbeats 800000

namespace p3109_format
namespace p3109

/-! ### Properties of `round_to_precision` for all EReal -/

/-- RD never rounds up: for any extended real `x`,
  `round_to_precision x .RD ≤ x`. -/
lemma round_to_precision_RD_le (x : EReal) :
  @round_to_precision f x .RD ≤ x := by
  cases x with
  | bot => simp only [round_to_precision, le_refl]
  | top => simp only [round_to_precision, le_refl]
  | coe r =>
    rw [round_to_precision_eq_simp, EReal.coe_le_coe_iff, round_to_precision_eq]
    simp only [round_to_precision_generic]
    exact (@rounddown_real_rounddown (format := f.to_format) r).2.1

/-- RU never rounds down: for any extended real `x`,
  `x ≤ round_to_precision x .RU`. -/
lemma round_to_precision_RU_ge (x : EReal) :
  x ≤ @round_to_precision f x .RU := by
  cases x with
  | bot => simp only [round_to_precision, le_refl]
  | top => simp only [round_to_precision, le_refl]
  | coe r =>
    rw [round_to_precision_eq_simp, EReal.coe_le_coe_iff, round_to_precision_eq]
    simp only [round_to_precision_generic]
    exact (@roundup_real_roundup (format := f.to_format) r).2.1

/-- RZ rounds toward zero for nonnegative inputs. -/
lemma round_to_precision_RZ_le_of_nonneg (x : EReal) :
  0 ≤ x → @round_to_precision f x .RZ ≤ x := by
  cases x with
  | bot => simp only [le_bot_iff, EReal.zero_ne_bot, IsEmpty.forall_iff]
  | top => simp only [le_top, round_to_precision, le_refl, imp_self]
  | coe r =>
    intro hr; simp only [EReal.coe_nonneg] at hr
    rw [round_to_precision_eq_simp, EReal.coe_le_coe_iff, round_to_precision_eq]
    simp only [round_to_precision_generic]
    have h := @roundzero_roundzero (format := f.to_format) r
    simp only at h; split at h
    · exact h.2.1
    · linarith

/-- RZ rounds toward zero for nonpositive inputs. -/
lemma round_to_precision_RZ_ge_of_nonpos (x : EReal) :
  x ≤ 0 → x ≤ @round_to_precision f x .RZ := by
  cases x with
  | bot => simp only [bot_le, round_to_precision, le_refl, imp_self]
  | top => simp only [top_le_iff, EReal.zero_ne_top, IsEmpty.forall_iff]
  | coe r =>
    intro hr; simp only [EReal.coe_nonpos] at hr
    rw [round_to_precision_eq_simp, EReal.coe_le_coe_iff, round_to_precision_eq]
    simp only [round_to_precision_generic]
    have h := @roundzero_roundzero (format := f.to_format) r
    simp only at h; split at h
    · have : r = 0 := le_antisymm hr (by assumption)
      rw [this]; simp only [round_to_zero_all, round_fp_0_0, le_refl]
    · exact h.2.1

/-- RNE is nearest for real inputs: among all bounded floats, `round_to_fp .RNE x`
  minimizes the distance to `x`. -/
lemma round_to_precision_RNE_nearest (x : ℝ) :
  @nearest 2 f.to_format x (@round_to_fp f .RNE x) := by
  simp only [round_to_fp]
  exact (@rne_abs_correct (format := f.to_format) x).1

/-- RNA is nearest for real inputs: among all bounded floats, `round_to_fp .RNA x`
  minimizes the distance to `x`. -/
lemma round_to_precision_RNA_nearest (x : ℝ) :
  @nearest 2 f.to_format x (@round_to_fp f .RNA x) := by
  simp only [round_to_fp, rna_float, round_nearest_all]
  exact (@rna_round_rne (format := f.to_format) x).1

end p3109
end p3109_format
