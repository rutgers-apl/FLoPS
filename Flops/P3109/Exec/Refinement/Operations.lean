import Flops.P3109.Exec.Refinement.Ops
import Flops.P3109.RoundTrip

namespace p3109_format
namespace Exec

variable {f : p3109_format}

/-!
# Executable operation refinement

The operation specifications below use `EReal ⊕ Unit`, with `Sum.inr ()`
representing NaN.  This keeps the exceptional-value rules visible while the
ordinary finite and infinite cases continue to use `EReal` arithmetic.
-/

@[simp] lemma two_zpow_ne_zero (e : Int) : (2 : ℝ) ^ e ≠ 0 := by
  positivity

@[simp] lemma finiteEReal_ne_top (m e : Int) :
    ((((m : ℝ) * (2 : ℝ) ^ e : ℝ) : EReal)) ≠ ⊤ :=
  EReal.coe_ne_top _

@[simp] lemma finiteEReal_ne_bot (m e : Int) :
    ((((m : ℝ) * (2 : ℝ) ^ e : ℝ) : EReal)) ≠ ⊥ :=
  EReal.coe_ne_bot _

@[simp] lemma finiteEReal_eq_zero_iff (m e : Int) :
    ((((m : ℝ) * (2 : ℝ) ^ e : ℝ) : EReal)) = 0 ↔ m = 0 := by
  simp [two_zpow_ne_zero]

@[simp] lemma finiteERealMul_ne_top (m e : Int) :
    ((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal) ≠ ⊤ := by
  rw [← EReal.coe_mul]
  exact EReal.coe_ne_top _

@[simp] lemma finiteERealMul_ne_bot (m e : Int) :
    ((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal) ≠ ⊥ := by
  rw [← EReal.coe_mul]
  exact EReal.coe_ne_bot _

@[simp] lemma finiteERealMul_eq_zero_iff (m e : Int) :
    ((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal) = 0 ↔ m = 0 := by
  rw [← EReal.coe_mul]
  simp [two_zpow_ne_zero]

noncomputable def cerealNeg (x : EReal ⊕ Unit) : EReal ⊕ Unit :=
  match x with
  | Sum.inr () => Sum.inr ()
  | Sum.inl a => Sum.inl (-a)

noncomputable def cerealAdd (x y : EReal ⊕ Unit) : EReal ⊕ Unit :=
  match x, y with
  | Sum.inr (), _ | _, Sum.inr () => Sum.inr ()
  | Sum.inl a, Sum.inl b =>
      if (a = ⊤ ∧ b = ⊥) ∨ (a = ⊥ ∧ b = ⊤) then Sum.inr ()
      else Sum.inl (a + b)

noncomputable def cerealMul (x y : EReal ⊕ Unit) : EReal ⊕ Unit :=
  match x, y with
  | Sum.inr (), _ | _, Sum.inr () => Sum.inr ()
  | Sum.inl a, Sum.inl b =>
      if (a = 0 ∧ (b = ⊤ ∨ b = ⊥)) ∨ (b = 0 ∧ (a = ⊤ ∨ a = ⊥)) then
        Sum.inr ()
      else
        Sum.inl (a * b)

lemma neg_toCereal_refines (x : Value f) :
    toCereal (neg x) = cerealNeg (toCereal x) := by
  cases x <;> simp [neg, cerealNeg, toCereal, EReal.coe_neg]

lemma addExact_toCereal_refines (x y : Value f) :
    toCereal (addExact x y) = cerealAdd (toCereal x) (toCereal y) := by
  cases x with
  | nan => cases y <;> simp [addExact, cerealAdd, toCereal]
  | posInf => cases y <;> simp [addExact, cerealAdd, toCereal]
  | negInf => cases y <;> simp [addExact, cerealAdd, toCereal]
  | finite m1 e1 =>
      cases y with
      | nan => simp [addExact, cerealAdd, toCereal]
      | posInf => simp [addExact, cerealAdd, toCereal]
      | negInf => simp [addExact, cerealAdd, toCereal]
      | finite m2 e2 =>
          have hnot :
              addExact (f := f) (Value.finite m1 e1) (Value.finite m2 e2) ≠
                Value.nan := by
            simp [addExact]
            split <;> simp
          rw [toCereal_eq_inl_toEReal hnot]
          simp only [cerealAdd, toCereal]
          congr 1
          exact toEReal_addExact_finite f m1 m2 e1 e2

lemma mulExact_toCereal_refines (x y : Value f) :
    toCereal (mulExact x y) = cerealMul (toCereal x) (toCereal y) := by
  cases x with
  | nan => cases y <;> simp [mulExact, cerealMul, toCereal]
  | posInf =>
      cases y with
      | nan => simp [mulExact, cerealMul, toCereal]
      | posInf => simp [mulExact, cerealMul, toCereal]
      | negInf => simp [mulExact, cerealMul, toCereal]
      | finite m e =>
          by_cases hm : m = 0
          · subst m; simp [mulExact, cerealMul, toCereal]
          · have hnot :
                mulExact (f := f) Value.posInf (Value.finite m e) ≠ Value.nan := by
                simp [mulExact, hm]
                split <;> simp
            rw [toCereal_eq_inl_toEReal hnot]
            rw [toEReal_mulExact_posInf_finite]
            simp [cerealMul, toCereal, hm]
  | negInf =>
      cases y with
      | nan => simp [mulExact, cerealMul, toCereal]
      | posInf => simp [mulExact, cerealMul, toCereal]
      | negInf => simp [mulExact, cerealMul, toCereal]
      | finite m e =>
          by_cases hm : m = 0
          · subst m; simp [mulExact, cerealMul, toCereal]
          · have hnot :
                mulExact (f := f) Value.negInf (Value.finite m e) ≠ Value.nan := by
                simp [mulExact, hm]
                split <;> simp
            rw [toCereal_eq_inl_toEReal hnot]
            rw [toEReal_mulExact_negInf_finite]
            simp [cerealMul, toCereal, hm]
  | finite m e =>
      cases y with
      | nan => simp [mulExact, cerealMul, toCereal]
      | posInf =>
          by_cases hm : m = 0
          · subst m; simp [mulExact, cerealMul, toCereal]
          · have hnot :
                mulExact (f := f) (Value.finite m e) Value.posInf ≠ Value.nan := by
                simp [mulExact, hm]
                split <;> simp
            rw [toCereal_eq_inl_toEReal hnot]
            rw [toEReal_mulExact_finite_posInf]
            simp [cerealMul, toCereal, hm]
      | negInf =>
          by_cases hm : m = 0
          · subst m; simp [mulExact, cerealMul, toCereal]
          · have hnot :
                mulExact (f := f) (Value.finite m e) Value.negInf ≠ Value.nan := by
                simp [mulExact, hm]
                split <;> simp
            rw [toCereal_eq_inl_toEReal hnot]
            rw [toEReal_mulExact_finite_negInf]
            simp [cerealMul, toCereal, hm]
      | finite m2 e2 =>
          rw [toCereal_eq_inl_toEReal (by simp [mulExact])]
          rw [toEReal_mulExact_finite]
          simp [cerealMul, toCereal]

lemma fromBits_encodeValue_zero_ne_nan (e : Int) :
    fromBits (encodeValue (f := f) (.finite 0 e)) ≠ Value.nan := by
  cases hs : f.s
  · have hneNan : ¬ 0 = 2 ^ (f.K - 1) :=
      ne_of_lt (zero_lt_pow_pred f)
    have hnePosInf : ¬ (0 = 2 ^ (f.K - 1) - 1 ∧ f.d = Domain.extended) := by
      intro h
      have htwo : 2 ≤ 2 ^ (f.K - 1) := by
        rw [← pow_one 2]
        apply pow_le_pow_right₀ (by decide : 1 ≤ 2)
        exact Nat.succ_le_of_lt
          (Nat.sub_pos_of_lt (Nat.lt_trans (by decide : 1 < 2) f.h_K))
      omega
    have hneNegInf : ¬ (0 = 2 ^ f.K - 1 ∧ f.d = Domain.extended) := by
      intro h
      have hpow : 2 ≤ 2 ^ f.K := two_le_pow_K f
      omega
    simp [encodeValue, encodeValueNat, finiteValueCode, fromBits,
      p3109.n_to_p3109, p3109.n_to_p3109_finite, hs, hneNan, hnePosInf,
      hneNegInf]
  · have hneNan : ¬ 0 = 2 ^ f.K - 1 := by
      have hpow : 2 ≤ 2 ^ f.K := two_le_pow_K f
      omega
    have hnePosInf : ¬ (0 = 2 ^ f.K - 2 ∧ f.d = Domain.extended) := by
      intro h
      have hge : 4 ≤ 2 ^ f.K := four_le_pow_K f
      omega
    simp [encodeValue, encodeValueNat, finiteValueCode, fromBits,
      p3109.n_to_p3109, p3109.n_to_p3109_finite, hs, hneNan, hnePosInf]

lemma encodeValue_toCereal_refines_of_canonical
    (x : Value f)
    (hpos : x = Value.posInf (f := f) → f.d = Domain.extended)
    (hneg : x = Value.negInf (f := f) →
      f.s = Signedness.signed ∧ f.d = Domain.extended)
    (hfin : ∀ m e, x = Value.finite (f := f) m e →
      (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩) :
    toCereal (fromBits (encodeValue (f := f) x)) = toCereal x := by
  cases x with
  | nan => simp [fromBits_encodeValue_nan]
  | posInf =>
      have hreal := encodeValue_posInf_refines (f := f) (hpos rfl)
      have hnot : fromBits (encodeValue (f := f) Value.posInf) ≠ Value.nan := by
        intro hnan
        rw [hnan] at hreal
        exact EReal.zero_ne_top hreal
      apply toCereal_eq_of_toEReal_of_nan_iff hreal
      simp [hnot]
  | negInf =>
      have hf := hneg rfl
      have hreal := encodeValue_negInf_refines (f := f) hf.1 hf.2
      have hnot : fromBits (encodeValue (f := f) Value.negInf) ≠ Value.nan := by
        intro hnan
        rw [hnan] at hreal
        exact EReal.zero_ne_bot hreal
      apply toCereal_eq_of_toEReal_of_nan_iff hreal
      simp [hnot]
  | finite m e =>
      have hf := hfin m e rfl
      by_cases hm : m = 0
      · subst m
        apply toCereal_eq_of_toEReal_of_nan_iff
          (encodeValue_zero_refines (f := f) e)
        simp [fromBits_encodeValue_zero_ne_nan]
      · have hreal := encodeValue_finite_canonical_refines
          (f := f) hf.1 hf.2
        have hnot :
            fromBits (encodeValue (f := f) (Value.finite m e)) ≠ Value.nan := by
          intro hnan
          have hz : toEReal (Value.finite (f := f) m e) = 0 := by
            rw [← hreal, hnan]
            rfl
          simp [toEReal, hm] at hz
        apply toCereal_eq_of_toEReal_of_nan_iff hreal
        simp [hnot, toCereal]

lemma round_finite_safe_canonical
    (x : Value f) (rnd : RoundingMode) {m e : Int}
    (hrange : inFiniteRange f (round (f := f) x rnd) = true)
    (h : round (f := f) x rnd = Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  apply round_finite_safe_canonical_of_finite_nonzero (f := f) rnd ?_ x hrange h
  intro m0 e0 hm0 m' e' hrange' hfin'
  apply roundFinite_output_canonical_of_branch_obligations
    (f := f) m0 e0 rnd hm0 hfin'
  · intro hcarry hm' he'
    exact roundFinite_carry_canonical_of_inFiniteRange
      (f := f) m0 e0 rnd hrange' hfin' hcarry hm' he'
  · intro hcore hm' he'
    exact roundFinite_core_canonical_of_mag_split
      (f := f) m0 e0 rnd hm0 hrange' hfin' hcore hm' he'
      (fun hlow => roundFinite_core_low_mag_exp_eq_emin_lsb
        (f := f) m0 e0 rnd hm0 hm' he' hlow)

lemma project_toCereal_refines
    (x : Value f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (project (f := f) x rnd sat)) =
      projectCereal (f := f) (toCereal x) rnd sat := by
  let s : Value f := saturate f (round (f := f) x rnd) sat rnd
  have henc :
      toCereal (fromBits (encodeValue (f := f) s)) = toCereal s := by
    apply encodeValue_toCereal_refines_of_canonical (f := f) s
    · intro hpos
      dsimp [s] at hpos
      have hcereal :
          cerealToEReal (@p3109_format.saturate f
            (@round_to_precision f (toEReal x) rnd) sat rnd) = (⊤ : EReal) := by
        have hs := saturate_refines (f := f) (round (f := f) x rnd) sat rnd
        rw [round_refines (f := f) x rnd] at hs
        rw [← hs, hpos]
        rfl
      have hsem :
          @p3109_format.saturate f
            (@round_to_precision f (toEReal x) rnd) sat rnd = Sum.inl ⊤ :=
        cerealToEReal_eq_top hcereal
      exact p3109.saturate_ext_domain_ext (f := f)
        (@round_to_precision f (toEReal x) rnd) rnd sat (Or.inr hsem)
    · intro hneg
      dsimp [s] at hneg
      have hcereal :
          cerealToEReal (@p3109_format.saturate f
            (@round_to_precision f (toEReal x) rnd) sat rnd) = (⊥ : EReal) := by
        have hs := saturate_refines (f := f) (round (f := f) x rnd) sat rnd
        rw [round_refines (f := f) x rnd] at hs
        rw [← hs, hneg]
        rfl
      have hsem :
          @p3109_format.saturate f
            (@round_to_precision f (toEReal x) rnd) sat rnd = Sum.inl ⊥ :=
        cerealToEReal_eq_bot hcereal
      exact ⟨
        p3109.saturate_bot_signed (f := f)
          (@round_to_precision f (toEReal x) rnd) rnd sat hsem,
        p3109.saturate_ext_domain_ext (f := f)
          (@round_to_precision f (toEReal x) rnd) rnd sat (Or.inl hsem)⟩
    · intro m e hfin
      dsimp [s] at hfin
      exact saturate_round_finite_safe_canonical_of_round
        (f := f) x rnd sat
        (fun m' e' hrange hround =>
          (round_finite_safe_canonical (f := f) x rnd hrange hround).2)
        hfin
  calc
    toCereal (fromBits (project (f := f) x rnd sat)) =
        toCereal (fromBits (encodeValue (f := f) s)) := by
          rfl
    _ = toCereal s := henc
    _ = projectCereal (f := f) (toCereal x) rnd sat := by
      exact saturate_round_toCereal_refines (f := f) x rnd sat

noncomputable def cerealSub (x y : EReal ⊕ Unit) : EReal ⊕ Unit :=
  cerealAdd x (cerealNeg y)

lemma subExact_toCereal_refines (x y : Value f) :
    toCereal (subExact x y) = cerealSub (toCereal x) (toCereal y) := by
  unfold subExact cerealSub
  rw [addExact_toCereal_refines, neg_toCereal_refines]

lemma negate_refines
    (x : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (negate x rnd sat)) =
      projectCereal (f := f) (cerealNeg (toCereal (fromBits x))) rnd sat := by
  unfold negate
  rw [project_toCereal_refines, neg_toCereal_refines]

lemma add_refines
    (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (add x y rnd sat)) =
      projectCereal (f := f)
        (cerealAdd (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat := by
  unfold add
  rw [project_toCereal_refines, addExact_toCereal_refines]

lemma sub_refines
    (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (subtract x y rnd sat)) =
      projectCereal (f := f)
        (cerealSub (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat := by
  unfold subtract
  rw [project_toCereal_refines, subExact_toCereal_refines]

lemma subtract_refines
    (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (subtract x y rnd sat)) =
      projectCereal (f := f)
        (cerealSub (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat :=
  sub_refines x y rnd sat

lemma mul_refines
    (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (multiply x y rnd sat)) =
      projectCereal (f := f)
        (cerealMul (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat := by
  unfold multiply
  rw [project_toCereal_refines, mulExact_toCereal_refines]

lemma multiply_refines
    (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (multiply x y rnd sat)) =
      projectCereal (f := f)
        (cerealMul (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat :=
  mul_refines x y rnd sat

lemma fma_refines
    (x y z : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (fma x y z rnd sat)) =
      projectCereal (f := f)
        (cerealAdd
          (cerealMul (toCereal (fromBits x)) (toCereal (fromBits y)))
          (toCereal (fromBits z))) rnd sat := by
  unfold fma
  rw [project_toCereal_refines, addExact_toCereal_refines,
    mulExact_toCereal_refines]

lemma faa_refines
    (x y z : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (faa x y z rnd sat)) =
      projectCereal (f := f)
        (cerealAdd
          (cerealAdd (toCereal (fromBits x)) (toCereal (fromBits y)))
          (toCereal (fromBits z))) rnd sat := by
  unfold faa
  rw [project_toCereal_refines, addExact_toCereal_refines,
    addExact_toCereal_refines]

noncomputable def cerealLT (x y : EReal ⊕ Unit) : Bool :=
  match x, y with
  | Sum.inl a, Sum.inl b => decide (a < b)
  | _, _ => false

noncomputable def cerealEq (x y : EReal ⊕ Unit) : Bool :=
  match x, y with
  | Sum.inl a, Sum.inl b => decide (a = b)
  | _, _ => false

noncomputable def cerealMin (x y : EReal ⊕ Unit) : EReal ⊕ Unit :=
  match x, y with
  | Sum.inr (), _ | _, Sum.inr () => Sum.inr ()
  | Sum.inl _, Sum.inl _ => if cerealLT x y then x else y

noncomputable def cerealMax (x y : EReal ⊕ Unit) : EReal ⊕ Unit :=
  match x, y with
  | Sum.inr (), _ | _, Sum.inr () => Sum.inr ()
  | Sum.inl _, Sum.inl _ => if cerealLT y x then x else y

lemma isLess_refines (x y : Bits f) :
    isLess x y = cerealLT (toCereal (fromBits x)) (toCereal (fromBits y)) := by
  unfold isLess
  generalize hx : fromBits x = a
  generalize hy : fromBits y = b
  cases a <;> cases b <;> simp [cerealLT, toCereal, valueLT_refines]

lemma isGreater_refines (x y : Bits f) :
    isGreater x y = cerealLT (toCereal (fromBits y)) (toCereal (fromBits x)) := by
  unfold isGreater
  exact isLess_refines y x

lemma toCereal_fromBits (x : Bits f) :
    toCereal (fromBits x) = p3109.to_cereal (p3109.n_to_p3109 x) := by
  cases h : p3109.n_to_p3109 x with
  | p3109_nan => simp [fromBits, toCereal, p3109.to_cereal, h]
  | p3109_infinity hdom sign hsign =>
      cases sign <;> simp [fromBits, toCereal, p3109.to_cereal, h]
  | p3109_finite m e hm hcan =>
      simp [fromBits, toCereal, p3109.to_cereal, h]

lemma toCereal_fromBits_injective :
    Function.Injective (fun x : Bits f => toCereal (fromBits x)) := by
  intro x y hxy
  apply p3109.bi_inj
  apply (p3109.bi2 (f := f)).1
  apply Subtype.ext
  change toCereal (fromBits x) = toCereal (fromBits y) at hxy
  rw [toCereal_fromBits, toCereal_fromBits] at hxy
  simpa [p3109.to_cereal'] using hxy

lemma isEqual_refines (x y : Bits f) :
    isEqual x y = cerealEq (toCereal (fromBits x)) (toCereal (fromBits y)) := by
  by_cases hxy : x = y
  · subst y
    cases h : fromBits x <;> simp [isEqual, cerealEq, toCereal, h]
  · have hsem : toCereal (fromBits x) ≠ toCereal (fromBits y) := by
      intro h
      exact hxy (toCereal_fromBits_injective h)
    generalize hx : fromBits x = a at hsem ⊢
    generalize hy : fromBits y = b at hsem ⊢
    cases a <;> cases b <;>
      simp [isEqual, cerealEq, toCereal, hx, hy, hxy] at hsem ⊢
    all_goals
      change decide (x = y) = _
      simp [hxy, hsem]

lemma minimum_refines (x y : Bits f) :
    toCereal (fromBits (minimum x y)) =
      cerealMin (toCereal (fromBits x)) (toCereal (fromBits y)) := by
  generalize hx : fromBits x = a
  generalize hy : fromBits y = b
  cases a <;> cases b <;>
    simp [minimum, cerealMin, cerealLT, toCereal, hx, hy,
      fromBits_encodeValue_nan, isLess_refines]
  all_goals split_ifs <;> simp_all

lemma maximum_refines (x y : Bits f) :
    toCereal (fromBits (maximum x y)) =
      cerealMax (toCereal (fromBits x)) (toCereal (fromBits y)) := by
  generalize hx : fromBits x = a
  generalize hy : fromBits y = b
  cases a <;> cases b <;>
    simp [maximum, cerealMax, cerealLT, toCereal, hx, hy,
      fromBits_encodeValue_nan, isGreater_refines]
  all_goals split_ifs <;> simp_all

noncomputable def cerealRound (x : EReal ⊕ Unit) (rnd : RoundingMode) :
    EReal ⊕ Unit :=
  match x with
  | Sum.inr () => Sum.inr ()
  | Sum.inl a => Sum.inl (@round_to_precision f a rnd)

noncomputable def cerealDiv (x y : EReal ⊕ Unit) : EReal ⊕ Unit :=
  match x, y with
  | Sum.inr (), _ | _, Sum.inr () => Sum.inr ()
  | Sum.inl a, Sum.inl b =>
      if ((a = ⊤ ∨ a = ⊥) ∧ (b = ⊤ ∨ b = ⊥)) ∨ b = 0 then
        Sum.inr ()
      else
        Sum.inl (a / b)

lemma roundFiniteRat_ne_nan
    (num den : Nat) (e : Int) (neg : Bool) (rnd : RoundingMode) :
    roundFiniteRat f num den e neg rnd ≠ Value.nan := by
  simp only [roundFiniteRat]
  split <;> simp
  split <;> simp

lemma projectCereal_round_idempotent
    (x : EReal ⊕ Unit) (rnd : RoundingMode) (sat : SaturationMode) :
    projectCereal (f := f) (cerealRound (f := f) x rnd) rnd sat =
      projectCereal (f := f) x rnd sat := by
  cases x with
  | inr u => cases u; rfl
  | inl e =>
      simp only [cerealRound, projectCereal_inl]
      unfold p3109_format.p3109.project
      simp [p3109_format.p3109.encode_to_cereal_local,
        round_to_precision_idempotent]

lemma divRoundedValue_toEReal_refines
    (x y : Value f) (rnd : RoundingMode) :
    toEReal (divRoundedValue (f := f) x y rnd) =
      @round_to_precision f (toEReal x / toEReal y) rnd := by
  cases x with
  | nan =>
      cases y <;> simp [divRoundedValue, toEReal, round_to_precision,
        round_to_precision_real]
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
          · simp [divRoundedValue, hm0, toEReal, round_to_precision,
              round_to_precision_real]
          · by_cases hmneg : m < 0
            · have hreal : (m : ℝ) * (2 : ℝ) ^ e < 0 :=
                  mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (by positivity)
              have hden_neg :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) < (0 : EReal) := by
                simpa [EReal.coe_mul] using (EReal.coe_neg'.mpr hreal)
              have hden_ne_bot :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) ≠ (⊥ : EReal) := by
                exact finiteERealMul_ne_bot m e
              have hdiv :
                  (⊤ : EReal) /
                    (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) = ⊥ :=
                EReal.top_div_of_neg_ne_bot hden_neg hden_ne_bot
              simp [divRoundedValue, hmneg, toEReal]
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
                exact finiteERealMul_ne_top m e
              have hdiv :
                  (⊤ : EReal) /
                    (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) = ⊤ :=
                EReal.top_div_of_pos_ne_top hden_pos hden_ne_top
              simp [divRoundedValue, hmneg, toEReal]
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
          · simp [divRoundedValue, hm0, toEReal, round_to_precision,
              round_to_precision_real]
          · by_cases hmneg : m < 0
            · have hreal : (m : ℝ) * (2 : ℝ) ^ e < 0 :=
                  mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (by positivity)
              have hden_neg :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) < (0 : EReal) := by
                simpa [EReal.coe_mul] using (EReal.coe_neg'.mpr hreal)
              have hden_ne_bot :
                  (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) ≠ (⊥ : EReal) := by
                exact finiteERealMul_ne_bot m e
              have hdiv :
                  (⊥ : EReal) /
                    (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) = ⊤ :=
                EReal.bot_div_of_neg_ne_bot hden_neg hden_ne_bot
              simp [divRoundedValue, hmneg, toEReal]
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
                exact finiteERealMul_ne_top m e
              have hdiv :
                  (⊥ : EReal) /
                    (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) = ⊥ :=
                EReal.bot_div_of_pos_ne_top hden_pos hden_ne_top
              simp [divRoundedValue, hmneg, toEReal]
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
          · simp [divRoundedValue, hm₂, toEReal, round_to_precision,
              round_to_precision_real]
          · by_cases hm₁ : m₁ = 0
            · simp [divRoundedValue, hm₁, hm₂, toEReal, round_to_precision,
                round_to_precision_real]
            · have hnum : Int.natAbs m₁ ≠ 0 := by
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
                    (Value.finite (f := f) m₂ e₂) rnd) =
                    toEReal (roundFiniteRat f (Int.natAbs m₁) (Int.natAbs m₂)
                      (e₁ - e₂) neg rnd) := by
                        simp [divRoundedValue, neg]
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

lemma divRoundedValue_toCereal_refines
    (x y : Value f) (rnd : RoundingMode) :
    toCereal (divRoundedValue (f := f) x y rnd) =
      cerealRound (f := f) (cerealDiv (toCereal x) (toCereal y)) rnd := by
  apply toCereal_eq_of_toEReal_of_nan_iff
  · rw [divRoundedValue_toEReal_refines]
    cases x with
    | nan =>
        cases y <;> simp [cerealRound, cerealDiv, toCereal,
          round_to_precision, round_to_precision_real]
    | posInf =>
        cases y with
        | nan =>
            simp [cerealRound, cerealDiv, toCereal, round_to_precision,
              round_to_precision_real]
        | posInf | negInf =>
            simp [cerealRound, cerealDiv, toCereal, round_to_precision,
              round_to_precision_real]
        | finite m e =>
            by_cases hm : m = 0 <;>
              simp [cerealRound, cerealDiv, toCereal, hm, round_to_precision,
                round_to_precision_real]
    | negInf =>
        cases y with
        | nan =>
            simp [cerealRound, cerealDiv, toCereal, round_to_precision,
              round_to_precision_real]
        | posInf | negInf =>
            simp [cerealRound, cerealDiv, toCereal, round_to_precision,
              round_to_precision_real]
        | finite m e =>
            by_cases hm : m = 0 <;>
              simp [cerealRound, cerealDiv, toCereal, hm, round_to_precision,
                round_to_precision_real]
    | finite m₁ e₁ =>
        cases y with
        | nan =>
            simp [cerealRound, cerealDiv, toCereal, round_to_precision,
              round_to_precision_real]
        | posInf | negInf => simp [cerealRound, cerealDiv, toCereal]
        | finite m₂ e₂ =>
            by_cases hm₂ : m₂ = 0 <;>
              simp [cerealRound, cerealDiv, toCereal, hm₂,
                round_to_precision, round_to_precision_real]
  · cases x with
    | nan => cases y <;> simp [divRoundedValue, cerealRound, cerealDiv, toCereal]
    | posInf =>
        cases y with
        | nan | posInf | negInf =>
            simp [divRoundedValue, cerealRound, cerealDiv, toCereal]
        | finite m e =>
            by_cases hm : m = 0
            · simp [divRoundedValue, cerealRound, cerealDiv, toCereal, hm]
            · simp [divRoundedValue, cerealRound, cerealDiv, toCereal, hm]
              split <;> simp
    | negInf =>
        cases y with
        | nan | posInf | negInf =>
            simp [divRoundedValue, cerealRound, cerealDiv, toCereal]
        | finite m e =>
            by_cases hm : m = 0
            · simp [divRoundedValue, cerealRound, cerealDiv, toCereal, hm]
            · simp [divRoundedValue, cerealRound, cerealDiv, toCereal, hm]
              split <;> simp
    | finite m₁ e₁ =>
        cases y with
        | nan | posInf | negInf =>
            simp [divRoundedValue, cerealRound, cerealDiv, toCereal]
        | finite m₂ e₂ =>
            by_cases hm₂ : m₂ = 0
            · simp [divRoundedValue, cerealRound, cerealDiv, toCereal, hm₂]
            · by_cases hm₁ : m₁ = 0
              · simp [divRoundedValue, cerealRound, cerealDiv, toCereal, hm₁, hm₂]
              · simp [divRoundedValue, cerealRound, cerealDiv, toCereal, hm₂,
                  roundFiniteRat_ne_nan]

lemma div_refines
    (x y : Bits f) (rnd : RoundingMode) (sat : SaturationMode) :
    toCereal (fromBits (divide x y rnd sat)) =
      projectCereal (f := f)
        (cerealDiv (toCereal (fromBits x)) (toCereal (fromBits y))) rnd sat := by
  unfold divide
  rw [project_toCereal_refines, divRoundedValue_toCereal_refines,
    projectCereal_round_idempotent]

end Exec
end p3109_format
