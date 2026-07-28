import Flops.P3109.Exec.Refinement.Project

namespace p3109_format
namespace Exec

/-!
# Total saturation / projection refinement (P3109 §4.7.3 / §4.7.5)

The `toEReal` bridge used throughout `Exec.Refinement` collapses `NaN` to `0`,
so the existing refinement lemmas (`saturate_refines`, `project_value_refines`,
...) can only speak about the *lossy* `toEReal` picture and cannot witness the
P3109 rules

* `ωProject(NaN) → NaN`  (§4.7.3), and
* `ωSaturate(*, *, NaN, *, *) → NaN`  (§4.7.5).

The core algebraic layer now provides total specifications on the closed
extended reals `EReal ⊕ Unit` (`Sum.inr ()` denotes `NaN`). This module relates
the executable operations to those specifications:

* core semantic saturation and projection on `EReal ⊕ Unit`;
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
  @p3109_format.saturate_total f x sat rnd

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
  (@p3109_format.p3109.project_total f x rnd sat).to_cereal

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
    simp [round, saturate_nan, toCereal, projectCereal, p3109.to_cereal]
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
