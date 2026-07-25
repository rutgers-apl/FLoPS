import Flops.P3109.Exec.Refinement.Project

namespace p3109_format
namespace Exec

lemma isLess_refines (x y : Bits f) :
    isLess (f := f) x y = decide ((toEReal (fromBits x)) < (toEReal (fromBits y))) := by
  unfold isLess
  simpa using valueLT_refines (f := f) (fromBits x) (fromBits y)

lemma isGreater_refines (x y : Bits f) :
    isGreater (f := f) x y = decide ((toEReal (fromBits y)) < (toEReal (fromBits x))) := by
  unfold isGreater
  simpa using valueLT_refines (f := f) (fromBits y) (fromBits x)

lemma isEqual_refines (x y : Bits f) :
    isEqual (f := f) x y = decide (x = y) := by
  rfl

lemma minimum_refines (x y : Bits f) :
    toEReal (fromBits (minimum (f := f) x y)) =
      (if (toEReal (fromBits x)) < (toEReal (fromBits y))
        then toEReal (fromBits x) else toEReal (fromBits y)) := by
  unfold minimum
  rw [isLess_refines]
  by_cases h : (toEReal (fromBits x)) < (toEReal (fromBits y))
  · simp [h]
  · simp [h]

lemma maximum_refines (x y : Bits f) :
    toEReal (fromBits (maximum (f := f) x y)) =
      (if (toEReal (fromBits y)) < (toEReal (fromBits x))
        then toEReal (fromBits x) else toEReal (fromBits y)) := by
  unfold maximum
  rw [isGreater_refines]
  by_cases h : (toEReal (fromBits y)) < (toEReal (fromBits x))
  · simp [h]
  · simp [h]

lemma add_refines
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (add x y rnd sat)) =
      (@p3109_format.p3109.project f
        (toEReal (fromBits x) + toEReal (fromBits y)) rnd sat) := by
  unfold add
  simpa [toEReal_addExact] using
    (project_value_refines (f := f)
      (x := addExact (f := f) (fromBits x) (fromBits y)) rnd sat)

lemma sub_refines
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (subtract x y rnd sat)) =
      (@p3109_format.p3109.project f
        (toEReal (fromBits x) - toEReal (fromBits y)) rnd sat) := by
  unfold subtract
  simpa [toEReal_subExact] using
    (project_value_refines (f := f)
      (x := subExact (f := f) (fromBits x) (fromBits y)) rnd sat)

lemma subtract_refines
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (subtract x y rnd sat)) =
      (@p3109_format.p3109.project f
        (toEReal (fromBits x) - toEReal (fromBits y)) rnd sat) :=
  sub_refines (f := f) x y rnd sat

lemma mul_refines
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (multiply x y rnd sat)) =
      (@p3109_format.p3109.project f
        (toEReal (fromBits x) * toEReal (fromBits y)) rnd sat) := by
  unfold multiply
  simpa [toEReal_mulExact] using
    (project_value_refines (f := f)
      (x := mulExact (f := f) (fromBits x) (fromBits y)) rnd sat)

lemma multiply_refines
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (multiply x y rnd sat)) =
      (@p3109_format.p3109.project f
        (toEReal (fromBits x) * toEReal (fromBits y)) rnd sat) :=
  mul_refines (f := f) x y rnd sat

lemma fma_refines
    (x y z : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (fma x y z rnd sat)) =
      (@p3109_format.p3109.project f
        (toEReal (fromBits x) * toEReal (fromBits y) +
          toEReal (fromBits z)) rnd sat) := by
  unfold fma
  simpa [toEReal_addExact, toEReal_mulExact] using
    (project_value_refines (f := f)
      (x := addExact (f := f)
        (mulExact (f := f) (fromBits x) (fromBits y))
        (fromBits z)) rnd sat)

lemma faa_refines
    (x y z : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (faa x y z rnd sat)) =
      (@p3109_format.p3109.project f
        ((toEReal (fromBits x) + toEReal (fromBits y)) +
          toEReal (fromBits z)) rnd sat) := by
  unfold faa
  simpa [toEReal_addExact] using
    (project_value_refines (f := f)
      (x := addExact (f := f)
        (addExact (f := f) (fromBits x) (fromBits y))
        (fromBits z)) rnd sat)

lemma divRoundedValue_refines
    (x y : Value f)
    (rnd : RoundingMode) :
    toEReal (divRoundedValue (f := f) x y rnd) =
      @round_to_precision f (toEReal x / toEReal y) rnd := by
  cases x with
  | nan =>
      cases y <;> simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
  | posInf =>
      cases y with
      | nan =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | posInf =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | negInf =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | finite m e =>
          by_cases hm0 : m = 0
          · simp [divRoundedValue, hm0, toEReal, round_to_precision, round_to_precision_real]
          · by_cases hmneg : m < 0
            · have hreal : (m : ℝ) * (2 : ℝ) ^ e < 0 :=
                  mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (by positivity)
              have hden_neg :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) < (0 : EReal) := by
                simpa [EReal.coe_mul] using (EReal.coe_neg'.mpr hreal)
              have hden_ne_bot :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) ≠ (⊥ : EReal) := by
                simpa [EReal.coe_mul] using
                  (EReal.coe_ne_bot ((m : ℝ) * (2 : ℝ) ^ e))
              have hdiv :
                  (⊤ : EReal) /
                    (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) = ⊥ :=
                EReal.top_div_of_neg_ne_bot hden_neg hden_ne_bot
              simp [divRoundedValue, hm0, hmneg, toEReal]
              rw [hdiv]
              simp [round_to_precision]
            · have hmpos : 0 < m := by
                have hnonneg : 0 ≤ m := le_of_not_gt hmneg
                exact lt_of_le_of_ne hnonneg (Ne.symm hm0)
              have hreal : 0 < (m : ℝ) * (2 : ℝ) ^ e :=
                  mul_pos (by exact_mod_cast hmpos) (by positivity)
              have hden_pos :
                  (0 : EReal) < (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) := by
                simpa [EReal.coe_mul] using (EReal.coe_pos.mpr hreal)
              have hden_ne_top :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) ≠ (⊤ : EReal) := by
                simpa [EReal.coe_mul] using
                  (EReal.coe_ne_top ((m : ℝ) * (2 : ℝ) ^ e))
              have hdiv :
                  (⊤ : EReal) /
                    (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) = ⊤ :=
                EReal.top_div_of_pos_ne_top hden_pos hden_ne_top
              simp [divRoundedValue, hm0, hmneg, toEReal]
              rw [hdiv]
              simp [round_to_precision]
  | negInf =>
      cases y with
      | nan =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | posInf =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | negInf =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | finite m e =>
          by_cases hm0 : m = 0
          · simp [divRoundedValue, hm0, toEReal, round_to_precision, round_to_precision_real]
          · by_cases hmneg : m < 0
            · have hreal : (m : ℝ) * (2 : ℝ) ^ e < 0 :=
                  mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (by positivity)
              have hden_neg :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) < (0 : EReal) := by
                simpa [EReal.coe_mul] using (EReal.coe_neg'.mpr hreal)
              have hden_ne_bot :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) ≠ (⊥ : EReal) := by
                simpa [EReal.coe_mul] using
                  (EReal.coe_ne_bot ((m : ℝ) * (2 : ℝ) ^ e))
              have hdiv :
                  (⊥ : EReal) /
                    (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) = ⊤ :=
                EReal.bot_div_of_neg_ne_bot hden_neg hden_ne_bot
              simp [divRoundedValue, hm0, hmneg, toEReal]
              rw [hdiv]
              simp [round_to_precision]
            · have hmpos : 0 < m := by
                have hnonneg : 0 ≤ m := le_of_not_gt hmneg
                exact lt_of_le_of_ne hnonneg (Ne.symm hm0)
              have hreal : 0 < (m : ℝ) * (2 : ℝ) ^ e :=
                  mul_pos (by exact_mod_cast hmpos) (by positivity)
              have hden_pos :
                  (0 : EReal) < (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) := by
                simpa [EReal.coe_mul] using (EReal.coe_pos.mpr hreal)
              have hden_ne_top :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) ≠ (⊤ : EReal) := by
                simpa [EReal.coe_mul] using
                  (EReal.coe_ne_top ((m : ℝ) * (2 : ℝ) ^ e))
              have hdiv :
                  (⊥ : EReal) /
                    (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) = ⊥ :=
                EReal.bot_div_of_pos_ne_top hden_pos hden_ne_top
              simp [divRoundedValue, hm0, hmneg, toEReal]
              rw [hdiv]
              simp [round_to_precision]
  | finite m₁ e₁ =>
      cases y with
      | nan =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | posInf =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | negInf =>
          simp [divRoundedValue, toEReal, round_to_precision, round_to_precision_real]
      | finite m₂ e₂ =>
          by_cases hm₂ : m₂ = 0
          · simp [divRoundedValue, hm₂, toEReal, round_to_precision, round_to_precision_real]
          · by_cases hm₁ : m₁ = 0
            · simp [divRoundedValue, hm₁, hm₂, toEReal, round_to_precision, round_to_precision_real]
            · -- Finite, nonzero division is the exact rational-rounding case.
              have hnum : Int.natAbs m₁ ≠ 0 := by
                simpa using Int.natAbs_ne_zero.mpr hm₁
              have hden : Int.natAbs m₂ ≠ 0 := by
                simpa using Int.natAbs_ne_zero.mpr hm₂
              let neg : Bool := decide ((m₁ < 0) ≠ (m₂ < 0))
              have hround :=
                roundFiniteRat_refines (f := f)
                  (Int.natAbs m₁) (Int.natAbs m₂) (e₁ - e₂)
                  neg rnd hnum hden
              have htarget :
                  ((if neg then
                      -((((Int.natAbs m₁ : Nat) : ℝ) /
                          ((Int.natAbs m₂ : Nat) : ℝ)) * (2 : ℝ) ^ (e₁ - e₂))
                    else
                      (((Int.natAbs m₁ : Nat) : ℝ) /
                          ((Int.natAbs m₂ : Nat) : ℝ)) * (2 : ℝ) ^ (e₁ - e₂)) : ℝ) =
                    ((m₁ : ℝ) * (2 : ℝ) ^ e₁) /
                      ((m₂ : ℝ) * (2 : ℝ) ^ e₂) := by
                have hm₂R : (m₂ : ℝ) ≠ 0 := by exact_mod_cast hm₂
                have hp₂ : (2 : ℝ) ^ e₂ ≠ 0 := by positivity
                have hpow :
                    (2 : ℝ) ^ (e₁ - e₂) =
                      (2 : ℝ) ^ e₁ / (2 : ℝ) ^ e₂ := by
                  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
                by_cases h₁ : m₁ < 0 <;> by_cases h₂ : m₂ < 0
                · have hm₁abs :
                      ((Int.natAbs m₁ : Nat) : ℝ) = -(m₁ : ℝ) := by
                    rw [intNatAbs_cast_real, abs_of_neg (by exact_mod_cast h₁)]
                  have hm₂abs :
                      ((Int.natAbs m₂ : Nat) : ℝ) = -(m₂ : ℝ) := by
                    rw [intNatAbs_cast_real, abs_of_neg (by exact_mod_cast h₂)]
                  simp [neg, h₁, h₂, hm₁abs, hm₂abs, hpow]
                  field_simp [hm₂R, hp₂]
                · have hm₁abs :
                      ((Int.natAbs m₁ : Nat) : ℝ) = -(m₁ : ℝ) := by
                    rw [intNatAbs_cast_real, abs_of_neg (by exact_mod_cast h₁)]
                  have hm₂pos : 0 < m₂ := by
                    have hnonneg : 0 ≤ m₂ := le_of_not_gt h₂
                    exact lt_of_le_of_ne hnonneg (Ne.symm hm₂)
                  have hm₂abs :
                      ((Int.natAbs m₂ : Nat) : ℝ) = (m₂ : ℝ) := by
                    rw [intNatAbs_cast_real, abs_of_pos (by exact_mod_cast hm₂pos)]
                  simp [neg, h₁, h₂, hm₁abs, hm₂abs, hpow]
                  field_simp [hm₂R, hp₂]
                · have hm₁pos : 0 < m₁ := by
                    have hnonneg : 0 ≤ m₁ := le_of_not_gt h₁
                    exact lt_of_le_of_ne hnonneg (Ne.symm hm₁)
                  have hm₁abs :
                      ((Int.natAbs m₁ : Nat) : ℝ) = (m₁ : ℝ) := by
                    rw [intNatAbs_cast_real, abs_of_pos (by exact_mod_cast hm₁pos)]
                  have hm₂abs :
                      ((Int.natAbs m₂ : Nat) : ℝ) = -(m₂ : ℝ) := by
                    rw [intNatAbs_cast_real, abs_of_neg (by exact_mod_cast h₂)]
                  simp [neg, h₁, h₂, hm₁abs, hm₂abs, hpow]
                  field_simp [hm₂R, hp₂]
                · have hm₁pos : 0 < m₁ := by
                    have hnonneg : 0 ≤ m₁ := le_of_not_gt h₁
                    exact lt_of_le_of_ne hnonneg (Ne.symm hm₁)
                  have hm₂pos : 0 < m₂ := by
                    have hnonneg : 0 ≤ m₂ := le_of_not_gt h₂
                    exact lt_of_le_of_ne hnonneg (Ne.symm hm₂)
                  have hm₁abs :
                      ((Int.natAbs m₁ : Nat) : ℝ) = (m₁ : ℝ) := by
                    rw [intNatAbs_cast_real, abs_of_pos (by exact_mod_cast hm₁pos)]
                  have hm₂abs :
                      ((Int.natAbs m₂ : Nat) : ℝ) = (m₂ : ℝ) := by
                    rw [intNatAbs_cast_real, abs_of_pos (by exact_mod_cast hm₂pos)]
                  simp [neg, h₁, h₂, hm₁abs, hm₂abs, hpow]
                  field_simp [hm₂R, hp₂]
              have htargetE :
                  (((if neg then
                      -((((Int.natAbs m₁ : Nat) : ℝ) /
                          ((Int.natAbs m₂ : Nat) : ℝ)) * (2 : ℝ) ^ (e₁ - e₂))
                    else
                      (((Int.natAbs m₁ : Nat) : ℝ) /
                          ((Int.natAbs m₂ : Nat) : ℝ)) * (2 : ℝ) ^ (e₁ - e₂)) : ℝ) : EReal) =
                    ((m₁ : ℝ) : EReal) * (((2 : ℝ) ^ e₁ : ℝ) : EReal) /
                      (((m₂ : ℝ) : EReal) * (((2 : ℝ) ^ e₂ : ℝ) : EReal)) := by
                rw [htarget]
                simp only [div_eq_mul_inv]
                rw [← EReal.coe_mul ((m₁ : ℝ)) ((2 : ℝ) ^ e₁)]
                rw [← EReal.coe_mul ((m₂ : ℝ)) ((2 : ℝ) ^ e₂)]
                rw [← EReal.coe_inv ((m₂ : ℝ) * (2 : ℝ) ^ e₂)]
                rw [← EReal.coe_mul]
              calc
                toEReal (divRoundedValue (f := f)
                    (Value.finite (f := f) m₁ e₁)
                    (Value.finite (f := f) m₂ e₂) rnd)
                    = toEReal
                        (roundFiniteRat f (Int.natAbs m₁) (Int.natAbs m₂)
                          (e₁ - e₂) neg rnd) := by
                        simp [divRoundedValue, hm₁, hm₂, neg]
                _ = @round_to_precision f
                      (((if neg then
                          -((((Int.natAbs m₁ : Nat) : ℝ) /
                              ((Int.natAbs m₂ : Nat) : ℝ)) * (2 : ℝ) ^ (e₁ - e₂))
                        else
                          (((Int.natAbs m₁ : Nat) : ℝ) /
                              ((Int.natAbs m₂ : Nat) : ℝ)) * (2 : ℝ) ^ (e₁ - e₂)) : ℝ) : EReal)
                      rnd := hround
                _ = @round_to_precision f
                      (((m₁ : ℝ) : EReal) * (((2 : ℝ) ^ e₁ : ℝ) : EReal) /
                        (((m₂ : ℝ) : EReal) * (((2 : ℝ) ^ e₂ : ℝ) : EReal)))
                      rnd := by rw [htargetE]
                _ = @round_to_precision f
                      (toEReal (Value.finite (f := f) m₁ e₁) /
                        toEReal (Value.finite (f := f) m₂ e₂))
                      rnd := by simp [toEReal]

lemma semantic_project_round_idempotent
    (target rounded : EReal)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hr : rounded = @round_to_precision f target rnd) :
    ((@p3109_format.p3109.project f rounded rnd sat : p3109 f) : EReal) =
      (@p3109_format.p3109.project f target rnd sat : p3109 f) := by
  unfold p3109_format.p3109.project
  simp [p3109_format.p3109.encode_to_ereal_local, hr,
    round_to_precision_idempotent]

lemma div_refines
    (x y : Bits f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (divide x y rnd sat)) =
      (@p3109_format.p3109.project f (toEReal (fromBits x) / toEReal (fromBits y)) rnd sat) := by
  unfold divide
  let r := divRoundedValue (f := f) (fromBits x) (fromBits y) rnd
  have hproj :
      toEReal (fromBits (project (f := f) r rnd sat)) =
        (@p3109_format.p3109.project f (toEReal r) rnd sat) := by
    exact project_value_refines (f := f) r rnd sat
  have hr :
      toEReal r =
        @round_to_precision f (toEReal (fromBits x) / toEReal (fromBits y)) rnd := by
    exact divRoundedValue_refines (f := f) (fromBits x) (fromBits y) rnd
  calc
    toEReal (fromBits (project (f := f) r rnd sat))
        = (@p3109_format.p3109.project f (toEReal r) rnd sat) := hproj
    _ = (@p3109_format.p3109.project f
          (toEReal (fromBits x) / toEReal (fromBits y)) rnd sat) := by
          exact semantic_project_round_idempotent
            (f := f)
            (target := toEReal (fromBits x) / toEReal (fromBits y))
            (rounded := toEReal r) rnd sat hr


/-!
# NaN-faithful saturation / projection specs (P3109 §4.7.3 / §4.7.5)

The `toEReal` bridge used throughout `Exec.Refinement` collapses `NaN` to `0`,
so the existing refinement lemmas (`saturate_refines`, `project_value_refines`,
...) can only speak about the *lossy* `toEReal` picture and cannot witness the
P3109 rules

* `ωProject(NaN) → NaN`  (§4.7.3), and
* `ωSaturate(*, *, NaN, *, *) → NaN`  (§4.7.5).

This module adds the **NaN-faithful** specification layer, stated against the
closed extended reals `EReal ⊕ Unit` (`toCereal`, where `Sum.inr ()` denotes
`NaN`):

* semantic `saturateC` / `projectCereal` on `EReal ⊕ Unit`;
* ordinary executable `round` / `project` propagation of `NaN`;
* refinement lemmas relating the two through `toCereal`.
-/

set_option maxHeartbeats 1600000

variable {f : p3109_format}

/-! ## Semantic NaN-faithful operators on `EReal ⊕ Unit` -/

/-- NaN-faithful semantic saturation on the closed extended reals.
`Sum.inr ()` (NaN) is propagated unchanged (`ωSaturate(*, *, NaN, *, *) → NaN`),
while finite/infinite inputs delegate to the existing semantic `saturate`. -/
noncomputable def saturateC (x : EReal ⊕ Unit) (sat : SaturationMode)
    (rnd : RoundingMode) : EReal ⊕ Unit :=
  match x with
  | Sum.inr () => Sum.inr ()
  | Sum.inl e => @p3109_format.saturate f e sat rnd

@[simp] lemma saturateC_nan (sat : SaturationMode) (rnd : RoundingMode) :
    saturateC (f := f) (Sum.inr ()) sat rnd = Sum.inr () := rfl

@[simp] lemma saturateC_inl (e : EReal) (sat : SaturationMode) (rnd : RoundingMode) :
    saturateC (f := f) (Sum.inl e) sat rnd = @p3109_format.saturate f e sat rnd := rfl

/-- NaN-faithful semantic projection on the closed extended reals.
`Sum.inr ()` (NaN) is propagated unchanged (`ωProject(NaN) → NaN`), while
finite/infinite inputs delegate to the existing semantic `p3109.project` and are
read back through `to_cereal`. -/
noncomputable def projectCereal (x : EReal ⊕ Unit) (rnd : RoundingMode)
    (sat : SaturationMode) : EReal ⊕ Unit :=
  match x with
  | Sum.inr () => Sum.inr ()
  | Sum.inl e => (@p3109_format.p3109.project f e rnd sat).to_cereal

@[simp] lemma projectCereal_nan (rnd : RoundingMode) (sat : SaturationMode) :
    projectCereal (f := f) (Sum.inr ()) rnd sat = Sum.inr () := rfl

@[simp] lemma projectCereal_inl (e : EReal) (rnd : RoundingMode) (sat : SaturationMode) :
    projectCereal (f := f) (Sum.inl e) rnd sat =
      (@p3109_format.p3109.project f e rnd sat).to_cereal := rfl

/-! ## `NaN` propagation facts -/

/-- Executable `saturate` propagates `NaN` (`Value.nan` is always in the finite
range because `toEReal Value.nan = 0`). -/
@[simp] lemma saturate_nan (sat : SaturationMode) (rnd : RoundingMode) :
    saturate f Value.nan sat rnd = Value.nan := by
  unfold saturate
  simp [inFiniteRange_nan]

/-! ## NaN-faithful refinement lemmas -/

/-- Bridging lemma: a `Value` `w` and a closed-extended-real `S` that agree
under the lossy `toEReal`/`cerealToEReal` bridge and agree on being `NaN`
actually agree under the NaN-faithful `toCereal`. -/
lemma toCereal_eq_of_toEReal_of_nan_iff {w : Value f} {S : EReal ⊕ Unit}
    (h1 : toEReal w = cerealToEReal S)
    (h2 : w = Value.nan ↔ S = Sum.inr ()) :
    toCereal w = S := by
  cases S with
  | inr u =>
      cases u
      have hw : w = Value.nan := h2.2 rfl
      simp [hw, toCereal]
  | inl e =>
      have hw : w ≠ Value.nan := by
        intro hc
        have := h2.1 hc
        exact (by simp at this)
      rw [toCereal_eq_inl_toEReal hw]
      simpa using h1

/-- Characterization of when the executable `saturate` produces `NaN` on a
non-`NaN` input:  it matches exactly the situation where the semantic
`p3109_format.saturate` produces `Sum.inr ()`. -/
lemma saturate_nan_iff_semantic_inr {x : Value f} (hx : x ≠ Value.nan)
    (sat : SaturationMode) (rnd : RoundingMode) :
    saturate f x sat rnd = Value.nan ↔
      @p3109_format.saturate f (toEReal x) sat rnd = Sum.inr () := by
  unfold saturate
  rw [inFiniteRange_semantic_refines]
  by_cases hr : toEReal x ≤ (p3109_format.max_finite (f := f) : EReal) ∧
      (p3109_format.min_finite (f := f) : EReal) ≤ toEReal x
  · rw [p3109_format.p3109.saturate_in_range (toEReal x) sat rnd hr.2 hr.1]
    simp [hr, hx]
  · simp only [hr, decide_false, Bool.false_eq_true, if_false]
    cases sat with
    | SatFinite =>
        constructor
        · intro h
          split_ifs at h <;>
            simp_all [minFiniteValue_ne_nan, maxFiniteValue_ne_nan]
        · intro h
          have hmode := (p3109_format.p3109.saturate_nan_implies_satNone h).1
          contradiction
    | SatPropagate =>
        constructor
        · intro h
          cases x <;> simp_all [minFiniteValue_ne_nan, maxFiniteValue_ne_nan,
            negOverflowValue_ne_nan]
          all_goals split_ifs at h <;>
            simp_all [minFiniteValue_ne_nan, maxFiniteValue_ne_nan]
        · intro h
          have hmode := (p3109_format.p3109.saturate_nan_implies_satNone h).1
          contradiction
    | SatNone =>
        cases x with
        | nan => contradiction
        | posInf =>
            unfold p3109_format.saturate
            cases f.s <;> cases f.d <;> simp_all +decide [maxFiniteValue_ne_nan]
        | negInf =>
            unfold p3109_format.saturate
            cases f.s <;> cases f.d <;> simp_all +decide [minFiniteValue_ne_nan]
        | finite m e =>
            rw [valueLT_minFinite_refines]
            let v : ℝ := (m : ℝ) * (2 ^ e : ℝ)
            change
              ((if decide ((v : EReal) < (p3109_format.min_finite (f := f) : EReal)) then
                  match rnd with
                  | .RZ | .RU => minFiniteValue f
                  | _ =>
                    match f.s, f.d with
                    | .signed, .extended => .negInf
                    | _, _ => .nan
                else
                  match rnd, f.s, f.d with
                  | .RZ, _, _ | .RD, _, _ => maxFiniteValue f
                  | .RTO, .unsigned, .extended => maxFiniteValue f
                  | _, _, .finite => .nan
                  | _, _, .extended => .posInf) = Value.nan ↔
                @p3109_format.saturate f (v : EReal) .SatNone rnd = Sum.inr ())
            have hrv : ¬ ((v : EReal) ≤ (p3109_format.max_finite (f := f) : EReal) ∧
                (p3109_format.min_finite (f := f) : EReal) ≤ (v : EReal)) := by
              simpa [v] using hr
            rw [← lift_real_some_some v] at hrv ⊢
            unfold p3109_format.saturate
            cases rnd <;> cases f.s <;> cases f.d
            all_goals split_ifs <;>
              simp_all +decide [minFiniteValue_ne_nan, maxFiniteValue_ne_nan]

/- Forward direction of the `NaN` characterization. -/
lemma semantic_inr_of_saturate_nan {x : Value f} (hx : x ≠ Value.nan)
    (sat : SaturationMode) (rnd : RoundingMode)
    (h : saturate f x sat rnd = Value.nan) :
    @p3109_format.saturate f (toEReal x) sat rnd = Sum.inr () :=
  (saturate_nan_iff_semantic_inr hx sat rnd).mp h

/- Backward direction of the `NaN` characterization. -/
lemma saturate_nan_of_semantic_inr {x : Value f} (hx : x ≠ Value.nan)
    (sat : SaturationMode) (rnd : RoundingMode)
    (h : @p3109_format.saturate f (toEReal x) sat rnd = Sum.inr ()) :
    saturate f x sat rnd = Value.nan :=
  (saturate_nan_iff_semantic_inr hx sat rnd).mpr h

/-- **NaN-faithful saturation refinement.**  The executable `saturate` on
`Value`s matches the NaN-faithful semantic `saturateC` through `toCereal`.
Unlike `saturate_refines`, this preserves the `NaN` case. -/
lemma saturate_toCereal_refines (x : Value f) (sat : SaturationMode) (rnd : RoundingMode) :
    toCereal (saturate f x sat rnd) = saturateC (f := f) (toCereal x) sat rnd := by
  by_cases hx : x = Value.nan
  · subst hx
    simp [saturate_nan, toCereal, saturateC]
  · rw [toCereal_eq_inl_toEReal hx, saturateC_inl]
    apply toCereal_eq_of_toEReal_of_nan_iff
    · exact saturate_refines x sat rnd
    · exact saturate_nan_iff_semantic_inr hx sat rnd

/-- For a non-`NaN` value, `toCereal (project e rnd sat) = (p3109.project e rnd sat).to_cereal`
recovered semantically.  Auxiliary reformulation of the semantic projection at
the closed-extended-real level. -/
lemma project_semantic_to_cereal (e : EReal) (rnd : RoundingMode) (sat : SaturationMode) :
    (@p3109_format.p3109.project f e rnd sat).to_cereal =
      @p3109_format.saturate f (@round_to_precision f e rnd) sat rnd := by
  unfold p3109_format.p3109.project
  exact p3109_format.p3109.encode_to_cereal_local _ _

/-- On non-`NaN` inputs, executable rounding never returns `NaN`. -/
lemma round_ne_nan_of_ne_nan {x : Value f} (h : x ≠ Value.nan) (rnd : RoundingMode) :
    round x rnd ≠ Value.nan := by
  cases x with
  | nan => contradiction
  | posInf => simp [round]
  | negInf => simp [round]
  | finite m e =>
      simp only [round, roundFinite]
      split_ifs <;> simp

/-- **NaN-faithful projection refinement.**  The ordinary executable projection
pipeline (`round` followed by `saturate`) matches the semantic `projectCereal`
through `toCereal`.  In particular `NaN` projects to `NaN`. -/
lemma saturate_round_toCereal_refines (x : Value f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (saturate f (round x rnd) sat rnd) =
      projectCereal (f := f) (toCereal x) rnd sat := by
  by_cases hx : x = Value.nan
  · subst hx
    simp [round, saturate_nan, toCereal, projectCereal]
  · rw [toCereal_eq_inl_toEReal hx, projectCereal_inl,
      saturate_toCereal_refines,
      toCereal_eq_inl_toEReal (round_ne_nan_of_ne_nan hx rnd), saturateC_inl, round_refines,
      project_semantic_to_cereal]

/-- Encoding `Value.nan` and decoding it back recovers `Value.nan`. -/
lemma fromBits_encodeValue_nan :
    fromBits (encodeValue (f := f) Value.nan) = Value.nan := by
  have hK : 1 ≤ f.K := le_of_lt (lt_trans (by decide) f.h_K)
  cases hs : f.s
  · have hmod : 2 ^ (f.K - 1) % 2 ^ f.K = 2 ^ (f.K - 1) := by
      refine Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) ?_)
      exact Nat.sub_lt (lt_of_lt_of_le (by decide) hK) (by decide)
    simp [encodeValue, encodeValueNat, fromBits, encodeNat, encodeSpecial, nanCode,
      signBase, p3109.n_to_p3109, hs, hmod]
  · have hpos : 0 < 2 ^ f.K := pow_pos (by decide : 0 < 2) f.K
    have hmod : (2 ^ f.K - 1) % 2 ^ f.K = 2 ^ f.K - 1 := by
      exact Nat.mod_eq_of_lt (Nat.sub_lt hpos (by decide))
    simp [encodeValue, encodeValueNat, fromBits, encodeNat, encodeSpecial, nanCode,
      maxCode, p3109.n_to_p3109, hs, hmod]

/-- The ordinary bit projection sends `NaN` to a bit pattern that decodes back
to `NaN` (`ωProject(NaN) → NaN`). -/
lemma project_nan (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (project (f := f) Value.nan rnd sat)) = Sum.inr () := by
  unfold project
  rw [show round (f := f) Value.nan rnd = Value.nan by rfl, saturate_nan,
    fromBits_encodeValue_nan]
  rfl

end Exec
end p3109_format
