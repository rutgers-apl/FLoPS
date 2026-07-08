/-
  Lifting rounding mode properties to `project` for all extended real values.

  This file proves that the mode-specific correctness properties of
  `round_to_precision` (RD, RU, RZ, RNE, RNA) extend to the full `project`
  function, which includes saturation and encoding.

  ## Main results

  ### Properties of `round_to_precision` (EReal → EReal, no saturation):

  These hold for ALL extended real inputs with no conditions:

  - `round_to_precision_RD_le`: RD never rounds up: `round_to_precision x .RD ≤ x`
  - `round_to_precision_RU_ge`: RU never rounds down: `x ≤ round_to_precision x .RU`
  - `round_to_precision_RZ_le_of_nonneg`: RZ rounds toward zero for nonneg
  - `round_to_precision_RZ_ge_of_nonpos`: RZ rounds toward zero for nonpos
  - `round_to_precision_RNE_nearest`: RNE is nearest for real inputs
  - `round_to_precision_RNA_nearest`: RNA is nearest for real inputs

  ### Properties of `project` (EReal → p3109, with saturation):

  For `project`, saturation may clip values at the boundary of the representable
  range. The mode-specific ordering properties hold under mild conditions:

  - `project_RD_le`: RD projection ≤ x when x ≥ min_finite
  - `project_RU_ge`: x ≤ RU projection when x ≤ max_finite
  - `project_RZ_le_of_nonneg`: RZ projection ≤ x for nonneg real x
  - `project_RZ_ge_of_nonpos`: x ≤ RZ projection for nonpos real x
  - `project_RNE_nearest_finite`: RNE gives nearest among bounded floats (when finite)
  - `project_RNA_nearest_finite`: RNA gives nearest among bounded floats (when finite)
-/

import Mathlib
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
  | bot => simp [round_to_precision]
  | top => simp [round_to_precision]
  | coe r =>
    rw [round_to_precision_eq_simp, EReal.coe_le_coe_iff, round_to_precision_eq]
    simp [round_to_precision_generic]
    exact (@rounddown_real_rounddown (format := f.to_format) r).2.1

/-- RU never rounds down: for any extended real `x`,
  `x ≤ round_to_precision x .RU`. -/
lemma round_to_precision_RU_ge (x : EReal) :
  x ≤ @round_to_precision f x .RU := by
  cases x with
  | bot => simp [round_to_precision]
  | top => simp [round_to_precision]
  | coe r =>
    rw [round_to_precision_eq_simp, EReal.coe_le_coe_iff, round_to_precision_eq]
    simp [round_to_precision_generic]
    exact (@roundup_real_roundup (format := f.to_format) r).2.1

/-- RZ rounds toward zero for nonnegative inputs. -/
lemma round_to_precision_RZ_le_of_nonneg (x : EReal) :
  0 ≤ x → @round_to_precision f x .RZ ≤ x := by
  cases x with
  | bot => simp
  | top => simp [round_to_precision]
  | coe r =>
    intro hr; simp at hr
    rw [round_to_precision_eq_simp, EReal.coe_le_coe_iff, round_to_precision_eq]
    simp [round_to_precision_generic]
    have h := @roundzero_roundzero (format := f.to_format) r
    simp at h; split at h
    · exact h.2.1
    · linarith

/-- RZ rounds toward zero for nonpositive inputs. -/
lemma round_to_precision_RZ_ge_of_nonpos (x : EReal) :
  x ≤ 0 → x ≤ @round_to_precision f x .RZ := by
  cases x with
  | bot => simp [round_to_precision]
  | top => simp
  | coe r =>
    intro hr; simp at hr
    rw [round_to_precision_eq_simp, EReal.coe_le_coe_iff, round_to_precision_eq]
    simp [round_to_precision_generic]
    have h := @roundzero_roundzero (format := f.to_format) r
    simp at h; split at h
    · have : r = 0 := le_antisymm hr (by assumption)
      rw [this]; simp [round_to_zero_all, round_fp_0_0]
    · exact h.2.1

/-- RNE is nearest for real inputs: among all bounded floats, `round_to_fp .RNE x`
  minimizes the distance to `x`. -/
lemma round_to_precision_RNE_nearest (x : ℝ) :
  @nearest 2 f.to_format x (@round_to_fp f .RNE x) := by
  simp [round_to_fp]
  exact (@rne_abs_correct (format := f.to_format) x).1

/-- RNA is nearest for real inputs: among all bounded floats, `round_to_fp .RNA x`
  minimizes the distance to `x`. -/
lemma round_to_precision_RNA_nearest (x : ℝ) :
  @nearest 2 f.to_format x (@round_to_fp f .RNA x) := by
  simp [round_to_fp, rna_float, round_nearest_all]
  exact (@rna_round_rne (format := f.to_format) x).1

/-! ### Saturate helpers for specific rounding modes -/

/-- When the rounded value > max_finite, saturate with RD clips to max_finite
  (never produces ⊤). -/
lemma saturate_overflow_RD (v : ℝ) (sat : SaturationMode)
  (hv : @max_finite f < (v : EReal)) :
  @saturateEReal f v sat .RD = @max_finite f := by
    unfold saturateEReal;
    split_ifs <;> norm_cast at *;
    · grind;
    · have h_min_le_max : ∀ x : p3109 f, x.is_finite → (x : ℝ) ≤ @max_finite f := by
        intro x hx_finite
        apply all_le_max_finite x hx_finite;
      exact absurd ‹_› ( not_lt_of_ge <| le_trans ( show min_finite.to_ereal ≤ max_finite.to_ereal from by exact (by
        convert h_min_le_max _ _
        rotate_left
        exact @min_finite f
        · grind +suggestions
        · simp +decide [ to_ereal ]
          rw [ ← EReal.coe_le_coe_iff ]
          rw [ min_finite, max_finite ]
          split_ifs <;> norm_num [ to_real ]) ) hv.le );
    · cases sat <;> cases f.s <;> cases f.d <;> tauto

/-- When the rounded value < min_finite, saturate with RU clips to min_finite
  (never produces ⊥). -/
lemma saturate_underflow_RU (v : ℝ) (sat : SaturationMode)
  (hv : (v : EReal) < @min_finite f) :
  @saturateEReal f v sat .RU = @min_finite f := by
    contrapose! hv
    apply Classical.byContradiction
    intro h_contra
    unfold saturateEReal at hv
    split_ifs at hv
    · tauto
    · cases sat <;> cases f.s <;> cases f.d <;> tauto
    · exact h_contra ( le_of_not_gt ‹_› )

/-- Saturate with RZ clips overflow to max_finite. -/
lemma saturate_overflow_RZ (v : ℝ) (sat : SaturationMode)
  (hv : @max_finite f < (v : EReal)) :
  @saturateEReal f v sat .RZ = @max_finite f := by
    contrapose! hv
    unfold saturateEReal at hv
    split_ifs at hv <;> norm_cast at hv
    · tauto
    · refine' le_trans _ ( show ( min_finite.to_ereal : EReal ) ≤ max_finite.to_ereal from _ )
      exact le_of_lt ‹_›
      have h_min_le_max : ∀ x : p3109 f, x.is_finite → (x : ℝ) ≤ @max_finite f := by
        intro x hx; exact (by
        convert all_le_max_finite x hx using 1)
      convert h_min_le_max _ _
      rotate_left
      exact @min_finite f
      · grind +suggestions
      · simp +decide [ to_ereal ]
        rw [ ← EReal.coe_le_coe_iff ]
        rw [ min_finite, max_finite ]
        split_ifs <;> norm_num [ to_real ]
    · cases sat <;> cases f.s <;> cases f.d <;> tauto

/-- Saturate with RZ clips underflow to min_finite. -/
lemma saturate_underflow_RZ (v : ℝ) (sat : SaturationMode)
  (hv : (v : EReal) < @min_finite f) :
  @saturateEReal f v sat .RZ = @min_finite f := by
    unfold saturateEReal
    cases sat <;> cases f.s <;> cases f.d <;> simp +decide [ hv ]
    all_goals split_ifs <;> try exact absurd ‹_› ( not_and_of_not_right _ hv.not_ge )
    all_goals cases v ; trivial

/-! ### Saturate-level ordering helpers -/

/-- For x ≥ min_finite, the saturated RD result is ≤ x. -/
lemma saturate_round_RD_le (x : ℝ) (sat : SaturationMode)
  (hx : @min_finite f ≤ x) :
  @saturateEReal f (@round_to_precision f x .RD) sat .RD ≤ (x : EReal) := by
  have hrd_le : @round_to_precision_real f x .RD ≤ x := by
    simp [round_to_precision_eq, round_to_precision_generic]
    exact (@rounddown_real_rounddown (format := f.to_format) x).2.1
  have hrd_ge_min : @min_finite f ≤ @round_to_precision_real f x .RD := by
    simp [round_to_precision_eq, round_to_fp_eq]
    rw [← min_fp_eq_min]
    exact weakly_monotone_le_round_to_fp .RD _ _ (by apply min_fp_bounded) (by rw [min_fp_eq_min]; exact hx)
  rw [round_to_precision_eq_simp]
  by_cases hle_max : @round_to_precision_real f x .RD ≤ @max_finite f
  · have hin1 : (@min_finite f : EReal) ≤ ↑(@round_to_precision_real f x .RD) := by
      rw [finite_to_ereal_eq _ min_is_finite]; exact EReal.coe_le_coe_iff.mpr hrd_ge_min
    have hin2 : (↑(@round_to_precision_real f x .RD) : EReal) ≤ @max_finite f := by
      rw [finite_to_ereal_eq _ max_is_finite]; exact EReal.coe_le_coe_iff.mpr hle_max
    rw [(@saturate_eq f _ sat .RD).1 hin1 hin2]
    exact EReal.coe_le_coe_iff.mpr hrd_le
  · push_neg at hle_max
    have hov : (@max_finite f : EReal) < ↑(@round_to_precision_real f x .RD) := by
      rw [finite_to_ereal_eq _ max_is_finite]; exact EReal.coe_lt_coe_iff.mpr hle_max
    rw [saturate_overflow_RD _ sat hov]
    rw [finite_to_ereal_eq _ max_is_finite]; exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- For x ≤ max_finite, the saturated RU result is ≥ x. -/
lemma saturate_round_RU_ge (x : ℝ) (sat : SaturationMode)
  (hx : x ≤ @max_finite f) :
  (x : EReal) ≤ @saturateEReal f (@round_to_precision f x .RU) sat .RU := by
  have hru_ge : x ≤ @round_to_precision_real f x .RU := by
    simp [round_to_precision_eq, round_to_precision_generic]
    exact (@roundup_real_roundup (format := f.to_format) x).2.1
  have hru_le_max : @round_to_precision_real f x .RU ≤ @max_finite f := by
    simp [round_to_precision_eq, round_to_fp_eq]
    rw [← max_fp_eq_max]
    exact weakly_monotone_round_to_fp_le .RU _ _ (by apply max_fp_bounded) (by rw [max_fp_eq_max]; exact hx)
  rw [round_to_precision_eq_simp]
  by_cases hge_min : @min_finite f ≤ @round_to_precision_real f x .RU
  · have hin1 : (@min_finite f : EReal) ≤ ↑(@round_to_precision_real f x .RU) := by
      rw [finite_to_ereal_eq _ min_is_finite]; exact EReal.coe_le_coe_iff.mpr hge_min
    have hin2 : (↑(@round_to_precision_real f x .RU) : EReal) ≤ @max_finite f := by
      rw [finite_to_ereal_eq _ max_is_finite]; exact EReal.coe_le_coe_iff.mpr hru_le_max
    rw [(@saturate_eq f _ sat .RU).1 hin1 hin2]
    exact EReal.coe_le_coe_iff.mpr hru_ge
  · push_neg at hge_min
    have huv : (↑(@round_to_precision_real f x .RU) : EReal) < @min_finite f := by
      rw [finite_to_ereal_eq _ min_is_finite]; exact EReal.coe_lt_coe_iff.mpr hge_min
    rw [saturate_underflow_RU _ sat huv]
    rw [finite_to_ereal_eq _ min_is_finite]; exact EReal.coe_le_coe_iff.mpr (by linarith)

/-
For nonneg x, the saturated RZ result is ≤ x.
-/
lemma saturate_round_RZ_le_of_nonneg (x : ℝ) (sat : SaturationMode)
  (hx : 0 ≤ x) :
    @saturateEReal f (@round_to_precision f x .RZ) sat .RZ ≤ (x : EReal) := by
      -- By definition of saturation, we know that if the round result is within the bounds, then the saturate function returns the round result.
      by_cases h_bounds : @min_finite f ≤ @round_to_precision f x RoundingMode.RZ ∧ @round_to_precision f x RoundingMode.RZ ≤ @max_finite f;
      · convert round_to_precision_RZ_le_of_nonneg ( x : EReal ) ( by aesop ) using 1;
        exact saturate_eq _ _ _ |>.1 h_bounds.1 h_bounds.2;
      · by_cases h_max : @max_finite f < @round_to_precision f x RoundingMode.RZ;
        · have h_max_finite : @saturateEReal f (@round_to_precision f x RoundingMode.RZ) sat RoundingMode.RZ = @max_finite f := by
            apply saturate_overflow_RZ; assumption;
          have h_max_finite_le_x : @round_to_precision f x RoundingMode.RZ ≤ x := by
            apply round_to_precision_RZ_le_of_nonneg;
            exact EReal.coe_le_coe_iff.mpr hx;
          exact h_max_finite.symm ▸ le_trans ( le_of_lt h_max ) h_max_finite_le_x;
        · by_cases h_min : @round_to_precision f x RoundingMode.RZ < @min_finite f;
          · have h_round_nonneg : 0 ≤ @round_to_precision f x RoundingMode.RZ := by
              have h_round_nonneg : 0 ≤ @round_to_precision_real f x RoundingMode.RZ := by
                unfold round_to_precision_real; simp +decide [ hx ] ;
                split_ifs <;> simp_all +decide [ Real.sign_of_pos, abs_of_nonneg ];
                rw [ Real.sign_of_pos ( lt_of_le_of_ne hx ( Ne.symm ‹_› ) ) ] ; norm_num;
                positivity;
              convert h_round_nonneg using 1;
              simp +decide [ round_to_precision_eq_simp ];
            contrapose! h_min;
            cases h : f.s <;> simp_all +decide [ min_finite ];
            · cases h : max_finite <;> simp_all +decide [ min_finite ];
              · unfold max_finite at h; simp_all +decide [ min_finite ] ;
                split_ifs at h;
              · finiteness;
              · cases h : round_to_precision ( x : EReal ) RoundingMode.RZ <;> simp_all +decide [ to_ereal ];
                norm_cast at *;
                linarith;
            · convert h_round_nonneg using 1;
              exact EReal.coe_eq_coe_iff.mpr ( by simp +decide [ to_real, _root_.to_real ] );
          · exact False.elim <| h_bounds ⟨ le_of_not_gt h_min, le_of_not_gt h_max ⟩

/-
For nonpos x, the saturated RZ result is ≥ x.
-/
lemma saturate_round_RZ_ge_of_nonpos (x : ℝ) (sat : SaturationMode)
  (hx : x ≤ 0) :
    (x : EReal) ≤ @saturateEReal f (@round_to_precision f x .RZ) sat .RZ := by
      have h_round_le : @round_to_precision f x RoundingMode.RZ ≥ (x : EReal) := by
        -- Apply the lemma that states the round_to_precision of x with RoundingMode.RZ is greater than or equal to x when x is non-positive.
        apply round_to_precision_RZ_ge_of_nonpos; exact_mod_cast hx
      generalize_proofs at *; (
      by_cases h_bounds : @min_finite f ≤ @round_to_precision f x RoundingMode.RZ ∧ @round_to_precision f x RoundingMode.RZ ≤ @max_finite f;
      · exact le_trans h_round_le ( by rw [ saturate_eq _ _ _ |>.1 h_bounds.1 h_bounds.2 ] );
      · by_cases h_max : @max_finite f < @round_to_precision f x RoundingMode.RZ;
        · have h_contra : @max_finite f ≥ (0 : ℝ) := by
            unfold max_finite
            generalize_proofs at *; (
            split_ifs <;> simp +decide [ *, to_real ] at *;
            · positivity;
            · exact mul_nonneg ( mod_cast by solve_by_elim ) ( by positivity ))
          generalize_proofs at *; (
          have h_contra : @round_to_precision f x RoundingMode.RZ ≤ (0 : ℝ) := by
            have h_contra : @round_to_precision f x RoundingMode.RZ = @round_to_precision_real f x RoundingMode.RZ := by
              exact?
            generalize_proofs at *; (
            simp_all +decide [ round_to_precision_real ];
            split_ifs <;> simp_all +decide [ Real.sign_of_neg, Real.sign_of_pos ];
            rw [ Real.sign_of_neg ( lt_of_le_of_ne hx ‹_› ) ] ; norm_num;
            positivity)
          generalize_proofs at *; (
          have h_contra : @max_finite f < (0 : ℝ) := by
            convert h_max.trans_le h_contra using 1
            generalize_proofs at *; (
            simp +decide [ max_finite, to_ereal ];
            split_ifs <;> norm_cast;
            · simp +decide [ p3109_finite, to_real ];
            · exact?)
          generalize_proofs at *; (
          linarith!)));
        · grind +suggestions)

/-! ### encode preserves EReal values -/

/-
Encoding an EReal value in the value set and converting back to EReal
  gives the original value. This is the key bridge between the saturate-level
  and project-level properties.
-/
lemma encode_to_ereal (v : EReal) (h : Sum.inl v ∈ value_set f) :
    (@encode f (Sum.inl v) h : EReal) = v := by
      rcases v with ( _ | _ | v );
      · obtain ⟨ x, hx ⟩ := h;
        cases x <;> tauto;
      · tauto;
      · by_cases hv : v = 0
        · subst hv
          unfold encode
          simp +decide [to_ereal]; rfl
        · exact @encode_real_to_ereal_eq f v h hv

/-! ### Properties of `project` for real values -/

variable (domain_sat_consistent : ∀ (sat : SaturationMode), f.d = .finite → ¬sat = .SatFinite → False)
include domain_sat_consistent

/-- The EReal value of `project x rnd sat` equals the saturate result. -/
lemma project_ereal_eq_saturate (x : ℝ) (rnd : RoundingMode) (sat : SaturationMode) :
    (@project f domain_sat_consistent (↑x) rnd sat : EReal) =
    @saturateEReal f (@round_to_precision f (↑x) rnd) sat rnd := by
  simp only [project]
  exact encode_to_ereal _ _

/-- RD projection ≤ x for all real x with x ≥ min_finite. -/
lemma project_RD_le (x : ℝ) (sat : SaturationMode)
  (hx : @min_finite f ≤ x) :
  (@project f domain_sat_consistent x .RD sat : EReal) ≤ x := by
  rw [project_ereal_eq_saturate]
  exact saturate_round_RD_le x sat hx

/-- x ≤ RU projection for all real x with x ≤ max_finite. -/
lemma project_RU_ge (x : ℝ) (sat : SaturationMode)
  (hx : x ≤ @max_finite f) :
  (x : EReal) ≤ @project f domain_sat_consistent x .RU sat := by
  rw [project_ereal_eq_saturate]
  exact saturate_round_RU_ge x sat hx

/-- RZ projection ≤ x for nonneg real x. -/
lemma project_RZ_le_of_nonneg (x : ℝ) (sat : SaturationMode) (hx : 0 ≤ x) :
  (@project f domain_sat_consistent x .RZ sat : EReal) ≤ x := by
  rw [project_ereal_eq_saturate]
  exact saturate_round_RZ_le_of_nonneg x sat hx

/-- x ≤ RZ projection for nonpos real x. -/
lemma project_RZ_ge_of_nonpos (x : ℝ) (sat : SaturationMode) (hx : x ≤ 0) :
  (x : EReal) ≤ @project f domain_sat_consistent x .RZ sat := by
  rw [project_ereal_eq_saturate]
  exact saturate_round_RZ_ge_of_nonpos x sat hx

/-- When p = project x rnd sat is finite and x is in bounds,
    (p : ℝ) = round_to_fp rnd x. -/
lemma project_finite_in_bound_to_real (x : ℝ) (rnd : RoundingMode) (sat : SaturationMode)
    (hbound : @min_finite f ≤ x ∧ x ≤ @max_finite f) :
    (@project f domain_sat_consistent (↑x) rnd sat : ℝ) =
      @round_to_fp f rnd x := by
  have := project_real_in_bound_eq_round domain_sat_consistent x rnd sat hbound
  rw [this, round_to_fp_eq]

/-
When p.is_finite and x > max_finite, (p : ℝ) = max_finite.
-/
lemma project_finite_overflow_real {rnd : RoundingMode} {sat : SaturationMode}
    {x : ℝ} (hx : @max_finite f < x)
    (hfin : (@project f domain_sat_consistent (↑x) rnd sat).is_finite) :
    (@project f domain_sat_consistent (↑x) rnd sat : ℝ) = @max_finite f := by
      convert @x_overflow_project_max_or_top f _ _ _ _ _ using 1;
      any_goals exact hx;
      rotate_left;
      exact?;
      exact rnd;
      exact sat;
      constructor <;> intro h <;> simp_all +decide [ EReal.coe_eq_coe_iff ];
      · exact?;
      · cases h <;> simp_all +decide [ p3109_format.p3109.max_is_finite, p3109_format.p3109.finite_to_ereal_eq ]

/-
When p.is_finite and x < min_finite, (p : ℝ) = min_finite.
-/
lemma project_finite_underflow_real {rnd : RoundingMode} {sat : SaturationMode}
    {x : ℝ} (hx : x < @min_finite f)
    (hfin : (@project f domain_sat_consistent (↑x) rnd sat).is_finite) :
    (@project f domain_sat_consistent (↑x) rnd sat : ℝ) = @min_finite f := by
      have h_saturate : @saturateEReal f (@round_to_precision f (↑x) rnd) sat rnd = @min_finite f := by
        have h_saturate : @round_to_precision f (↑x) rnd ≤ @min_finite f := by
          have h_round_le : (@round_to_fp f rnd x : ℝ) ≤ @min_finite f := by
            have h_round_le : (@round_to_fp f rnd x : ℝ) ≤ @min_fp f := by
              apply weakly_monotone_round_to_fp_le rnd x (@min_fp f) (min_fp_bounded);
              exact hx.le.trans ( by simp +decide [ min_fp_eq_min ] );
            exact h_round_le.trans ( by rw [ min_fp_eq_min ] );
          have h_round_le : (@round_to_precision f x rnd : EReal) = (@round_to_fp f rnd x : ℝ) := by
            -- By definition of round_to_precision, we have round_to_precision x rnd = round_to_fp rnd x.
            rw [round_to_precision_eq_simp];
            rw [ round_to_precision_eq, round_to_fp_eq ]
          generalize_proofs at *; (
          convert EReal.coe_le_coe_iff.mpr ‹_› using 1
          generalize_proofs at *; (
          grind +suggestions));
        have := @saturate_eq f (@round_to_precision f (↑x) rnd) sat rnd;
        cases lt_or_eq_of_le h_saturate <;> simp_all +decide;
        · cases this.1 <;> simp_all +decide [ project ];
          cases hfin;
        · exact this.1 (by
            have h := @all_le_max_finite f min_finite min_is_finite
            have hfin1 := @min_is_finite f
            rw [finite_to_ereal_eq _ hfin1, finite_to_ereal_eq _ max_is_finite]
            exact EReal.coe_le_coe_iff.mpr h)
      have h_project : @project f domain_sat_consistent (↑x) rnd sat = @saturateEReal f (@round_to_precision f (↑x) rnd) sat rnd := by
        apply_rules [ project_ereal_eq_saturate ];
      grind +suggestions

/-- RNE projection is nearest among representable (p3109 finite) values
    when the result is finite.

    Note: The original formulation quantified over `bounded_float` (Format-level),
    but `bounded_float` does not bound the exponent from above, so bounded floats
    can exceed `max_finite`. After saturation, the projected value is clipped to
    the representable range and may not be nearest among all bounded floats.
    The correct quantifier is over finite p3109 values (which have bounded exponents
    via `canonical_p3109`). -/
lemma project_RNE_nearest_finite (x : ℝ) (sat : SaturationMode) :
  let p := @project f domain_sat_consistent x .RNE sat;
  p.is_finite →
  ∀ (g : p3109 f), g.is_finite →
    |(p : ℝ) - x| ≤ |(g : ℝ) - x| := by
  intro p hp g hg
  by_cases hle_max : x ≤ @max_finite f
  · by_cases hge_min : @min_finite f ≤ x
    · rw [project_finite_in_bound_to_real domain_sat_consistent x RoundingMode.RNE sat ⟨hge_min, hle_max⟩]
      have hbf : @bounded_float 2 f.to_format g.to_float := by
        rcases g with _|_|⟨m, e, hm, hcan⟩ <;> simp [is_finite] at hg
        exact canonical_bounded (canonical_fp_of_canonical_p3109 _ hcan)
      have := (round_to_precision_RNE_nearest x).2 g.to_float hbf
      rwa [to_float_eq] at this
    · push_neg at hge_min
      rw [project_finite_underflow_real (domain_sat_consistent := domain_sat_consistent) hge_min hp]
      have hg_ge := min_finite_le_all g hg
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · push_neg at hle_max
    rw [project_finite_overflow_real (domain_sat_consistent := domain_sat_consistent) hle_max hp]
    have hg_le := all_le_max_finite g hg
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-- RNA projection is nearest among representable (p3109 finite) values
    when the result is finite. See `project_RNE_nearest_finite` for
    discussion of the quantifier choice. -/
lemma project_RNA_nearest_finite (x : ℝ) (sat : SaturationMode) :
  let p := @project f domain_sat_consistent x .RNA sat;
  p.is_finite →
  ∀ (g : p3109 f), g.is_finite →
    |(p : ℝ) - x| ≤ |(g : ℝ) - x| := by
  intro p hp g hg
  by_cases hle_max : x ≤ @max_finite f
  · by_cases hge_min : @min_finite f ≤ x
    · rw [project_finite_in_bound_to_real domain_sat_consistent x RoundingMode.RNA sat ⟨hge_min, hle_max⟩]
      have hbf : @bounded_float 2 f.to_format g.to_float := by
        rcases g with _|_|⟨m, e, hm, hcan⟩ <;> simp [is_finite] at hg
        exact canonical_bounded (canonical_fp_of_canonical_p3109 _ hcan)
      have := (round_to_precision_RNA_nearest x).2 g.to_float hbf
      rwa [to_float_eq] at this
    · push_neg at hge_min
      rw [project_finite_underflow_real (domain_sat_consistent := domain_sat_consistent) hge_min hp]
      have hg_ge := min_finite_le_all g hg
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · push_neg at hle_max
    rw [project_finite_overflow_real (domain_sat_consistent := domain_sat_consistent) hle_max hp]
    have hg_le := all_le_max_finite g hg
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

end p3109
end p3109_format
