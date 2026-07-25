import Flops.P3109.Exec.Refinement.Round

namespace p3109_format
namespace Exec

lemma canonicalZero_finite_safe_canonical
    {m e : Int}
    (h : canonicalZero f = Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  unfold canonicalZero at h
  simp at h
  rcases h with ⟨rfl, rfl⟩
  constructor
  · intro _; omega
  · right
    constructor
    · have hfmt : f.emin_lsb = -f.to_format.dexp := by
        simp only [to_format, neg_neg]
      rw [hfmt]
      apply bounded_0 (by omega)
    · simp only [to_format, neg_neg, Nat.cast_ofNat, mul_zero, abs_zero, vnum,
        Nat.cast_pow, Nat.ofNat_pos, pow_pos, and_self]

lemma intPow2_real_eq_zpow (n : Nat) :
    ((intPow2 n : Int) : ℝ) = (2 : ℝ) ^ (n : Int) := by
  simp [intPow2, zpow_natCast]

lemma finiteLE_refines (m₁ e₁ m₂ e₂ : Int) :
    finiteLE m₁ e₁ m₂ e₂ =
      decide (toEReal (Value.finite (f := f) m₁ e₁) ≤
        toEReal (Value.finite (f := f) m₂ e₂)) := by
  unfold finiteLE
  by_cases h : e₁ ≤ e₂
  · have hpow :
        ((intPow2 (Int.toNat (e₂ - e₁)) : Int) : ℝ) =
          (2 : ℝ) ^ (e₂ - e₁) := by
        rw [intPow2_real_eq_zpow, Int.toNat_of_nonneg (sub_nonneg.mpr h)]
    have hscale :
        ((m₂ * intPow2 (Int.toNat (e₂ - e₁)) : Int) : ℝ) *
            (2 : ℝ) ^ e₁ =
          (m₂ : ℝ) * (2 : ℝ) ^ e₂ := by
      rw [Int.cast_mul, hpow]
      rw [show e₂ = e₁ + (e₂ - e₁) by ring, zpow_add₀] <;> norm_num
      ring
    have hpos : 0 < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) e₁
    have hiff :
        (m₁ ≤ m₂ * intPow2 (Int.toNat (e₂ - e₁))) ↔
          ((m₁ : ℝ) * (2 : ℝ) ^ e₁ ≤ (m₂ : ℝ) * (2 : ℝ) ^ e₂) := by
      constructor
      · intro hle
        have hleR : (m₁ : ℝ) ≤ ((m₂ * intPow2 (Int.toNat (e₂ - e₁)) : Int) : ℝ) := by
          exact_mod_cast hle
        nlinarith
      · intro hle
        have hleR :
            (m₁ : ℝ) ≤ ((m₂ * intPow2 (Int.toNat (e₂ - e₁)) : Int) : ℝ) := by
          nlinarith
        exact_mod_cast hleR
    simp [h]
    change m₁ ≤ m₂ * intPow2 (Int.toNat (e₂ - e₁)) ↔
      (((m₁ : ℝ) * (2 : ℝ) ^ e₁ : ℝ) : EReal) ≤
        (((m₂ : ℝ) * (2 : ℝ) ^ e₂ : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff]
    exact hiff
  · have hle : e₂ ≤ e₁ := le_of_not_ge h
    have hpow :
        ((intPow2 (Int.toNat (e₁ - e₂)) : Int) : ℝ) =
          (2 : ℝ) ^ (e₁ - e₂) := by
        rw [intPow2_real_eq_zpow, Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
    have hscale :
        ((m₁ * intPow2 (Int.toNat (e₁ - e₂)) : Int) : ℝ) *
            (2 : ℝ) ^ e₂ =
          (m₁ : ℝ) * (2 : ℝ) ^ e₁ := by
      rw [Int.cast_mul, hpow]
      rw [show e₁ = e₂ + (e₁ - e₂) by ring, zpow_add₀] <;> norm_num
      ring
    have hpos : 0 < (2 : ℝ) ^ e₂ := zpow_pos (by norm_num) e₂
    have hiff :
        (m₁ * intPow2 (Int.toNat (e₁ - e₂)) ≤ m₂) ↔
          ((m₁ : ℝ) * (2 : ℝ) ^ e₁ ≤ (m₂ : ℝ) * (2 : ℝ) ^ e₂) := by
      constructor
      · intro hleInt
        have hleR : (((m₁ * intPow2 (Int.toNat (e₁ - e₂)) : Int) : ℝ)) ≤ (m₂ : ℝ) := by
          exact_mod_cast hleInt
        nlinarith
      · intro hleReal
        have hleR : (((m₁ * intPow2 (Int.toNat (e₁ - e₂)) : Int) : ℝ)) ≤ (m₂ : ℝ) := by
          nlinarith
        exact_mod_cast hleR
    simp [h]
    change m₁ * intPow2 (Int.toNat (e₁ - e₂)) ≤ m₂ ↔
      (((m₁ : ℝ) * (2 : ℝ) ^ e₁ : ℝ) : EReal) ≤
        (((m₂ : ℝ) * (2 : ℝ) ^ e₂ : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff]
    exact hiff

lemma valueLE_refines (x y : Value f) :
    valueLE x y = decide (toEReal x ≤ toEReal y) := by
  cases x <;> cases y <;>
    simp [valueLE, toEReal, bot_le, le_top, top_le_iff, le_bot_iff]
  · simpa [toEReal] using (finiteLE_refines (f := f) 0 f.emin_lsb _ _)
  · simpa using (EReal.coe_ne_top (((_ : Int) : ℝ) * (2 : ℝ) ^ (_ : Int)))
  · simpa [toEReal] using (finiteLE_refines (f := f) _ _ 0 f.emin_lsb)
  · simpa using (EReal.coe_ne_bot (((_ : Int) : ℝ) * (2 : ℝ) ^ (_ : Int)))
  · simpa [toEReal] using (finiteLE_refines (f := f) _ _ _ _)

lemma valueLT_refines (x y : Value f) :
    valueLT x y = decide (toEReal x < toEReal y) := by
  unfold valueLT
  rw [valueLE_refines, valueLE_refines]
  by_cases hxy : toEReal x ≤ toEReal y
  · by_cases hyx : toEReal y ≤ toEReal x
    · have hnlt : ¬ toEReal x < toEReal y := fun hlt => not_le_of_gt hlt hyx
      simp [hxy, hyx, hnlt]
    · have hne : toEReal x ≠ toEReal y := by
        intro heq
        exact hyx (ge_of_eq heq)
      have hlt : toEReal x < toEReal y := lt_of_le_of_ne hxy hne
      simp [hxy, hyx, hlt]
  · have hnlt : ¬ toEReal x < toEReal y := fun hlt => hxy (le_of_lt hlt)
    simp [hxy, hnlt]

lemma inFiniteRange_refines (x : Value f) :
    inFiniteRange f x =
      decide (toEReal (minFiniteValue f) ≤ toEReal x ∧
        toEReal x ≤ toEReal (maxFiniteValue f)) := by
  unfold inFiniteRange
  rw [valueLE_refines, valueLE_refines]
  by_cases hlo : toEReal (minFiniteValue f) ≤ toEReal x
  · by_cases hhi : toEReal x ≤ toEReal (maxFiniteValue f)
    · simp [hlo, hhi]
    · simp [hlo, hhi]
  · simp [hlo]

lemma inFiniteRange_finite_unsigned_nonneg
    {m e : Int}
    (hs : f.s = Signedness.unsigned)
    (hr : inFiniteRange f (Value.finite (f := f) m e) = true) :
    0 ≤ m := by
  rw [inFiniteRange_refines] at hr
  have hineq :
      toEReal (minFiniteValue f) ≤ toEReal (Value.finite (f := f) m e) ∧
        toEReal (Value.finite (f := f) m e) ≤ toEReal (maxFiniteValue f) := by
    exact of_decide_eq_true hr
  have hmin : toEReal (minFiniteValue f) = (0 : EReal) := by
    unfold minFiniteValue
    split
    · simp [toEReal]
    · contradiction
  have hle :
      (0 : EReal) ≤ (((m : ℝ) * (2 : ℝ) ^ e : ℝ) : EReal) := by
    have hle' := hineq.1
    rw [hmin] at hle'
    simpa [toEReal] using hle'
  have hleReal : (0 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ e := by
    exact EReal.coe_le_coe_iff.mp hle
  have hpow : 0 < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  have hmReal : (0 : ℝ) ≤ m := by
    nlinarith
  exact_mod_cast hmReal

lemma round_finite_safe_canonical_of_finite_nonzero
    (rnd : RoundingMode)
    (hfinite_nonzero :
      ∀ m e, m ≠ 0 →
        ∀ m' e',
          inFiniteRange f (roundFinite f m e rnd) = true →
          roundFinite f m e rnd = Value.finite (f := f) m' e' →
          @canonical_p3109 f ⟨m', e'⟩)
    (x : Value f)
    {m e : Int}
    (hrange : inFiniteRange f (round (f := f) x rnd) = true)
    (h : round (f := f) x rnd = Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  cases x with
  | nan =>
      simp [round] at h
  | posInf =>
      simp [round] at h
  | negInf =>
      simp [round] at h
  | finite m0 e0 =>
      by_cases hm0 : m0 = 0
      · subst m0
        simp [round, roundFinite] at h
        rcases h with ⟨rfl, rfl⟩
        exact canonicalZero_finite_safe_canonical (f := f) rfl
      · have hrange' :
            inFiniteRange f (roundFinite f m0 e0 rnd) = true := by
          simpa [round] using hrange
        have hfin :
            roundFinite f m0 e0 rnd = Value.finite (f := f) m e := by
          simpa [round] using h
        constructor
        · intro hs
          exact inFiniteRange_finite_unsigned_nonneg (f := f) hs
            (by simpa [hfin] using hrange')
        · exact hfinite_nonzero m0 e0 hm0 m e hrange' hfin

lemma roundFiniteCore_E_ge_emin_lsb
    (m e : Int)
    (rnd : RoundingMode) :
    f.emin_lsb ≤ (roundFiniteCore f m e rnd).E := by
  unfold roundFiniteCore
  simp only
  have hmax :
      (1 - f.bias : Int) ≤
        max (Int.ofNat (Nat.log2 (absNat m)) + e) (1 - f.bias) :=
    le_max_right _ _
  simp only [emin_lsb, emin]
  omega

lemma absNat_lt_pow_log2_succ
    {m : Int}
    (hm : m ≠ 0) :
    absNat m < 2 ^ (Nat.log2 (absNat m) + 1) := by
  have ham : absNat m ≠ 0 := by
    simpa [absNat] using Int.natAbs_ne_zero.mpr hm
  have hlog :
      Nat.log 2 (absNat m) < Nat.log2 (absNat m) + 1 := by
    rw [← Nat.log2_eq_log_two]
    exact Nat.lt_succ_self _
  exact (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) ham).mp hlog

lemma roundFiniteCore_log2_succ_add_shift_le_precision_int
    (m e : Int)
    (rnd : RoundingMode) :
    Int.ofNat (Nat.log2 (absNat m)) + 1 +
        (roundFiniteCore f m e rnd).shift ≤ f.P := by
  let L : Int := Int.ofNat (Nat.log2 (absNat m)) + e
  let M : Int := max L (1 - f.bias)
  let E : Int := M - f.P + 1
  have hLE : L ≤ M := le_max_left _ _
  have hshiftEq :
      (roundFiniteCore f m e rnd).shift = e - E := by
    simp [roundFiniteCore, absNat, L, M, E]
  rw [hshiftEq]
  dsimp [L, M, E] at hLE ⊢
  omega

lemma roundFiniteCore_log2_succ_add_shift_eq_precision_int_of_E_gt
    (m e : Int)
    (rnd : RoundingMode)
    (hEgt : f.emin_lsb < (roundFiniteCore f m e rnd).E) :
    Int.ofNat (Nat.log2 (absNat m)) + 1 +
        (roundFiniteCore f m e rnd).shift = f.P := by
  let L : Int := Int.ofNat (Nat.log2 (absNat m)) + e
  let C : Int := 1 - f.bias
  let M : Int := max L C
  let E : Int := M - f.P + 1
  have hshiftEq :
      (roundFiniteCore f m e rnd).shift = e - E := by
    simp [roundFiniteCore, absNat, L, C, M, E]
  have hEEq :
      (roundFiniteCore f m e rnd).E = E := by
    simp [roundFiniteCore, absNat, L, C, M, E]
  have heminEq : f.emin_lsb = C - f.P + 1 := by
    simp [emin_lsb, emin, C]
  have hC_lt_M : C < M := by
    rw [hEEq, heminEq] at hEgt
    omega
  have hC_lt_L : C < L := by
    by_contra hnot
    have hL_le_C : L ≤ C := le_of_not_gt hnot
    have hM_eq : M = C := max_eq_right hL_le_C
    omega
  have hM_eq : M = L := max_eq_left (le_of_lt hC_lt_L)
  rw [hshiftEq]
  change
    Int.ofNat (Nat.log2 (absNat m)) + 1 + (e - E) = (f.P : Int)
  dsimp [E]
  rw [hM_eq]
  dsimp [L]
  omega

lemma roundFiniteCore_log2_succ_add_shift_le_precision
    (m e : Int)
    (rnd : RoundingMode)
    (hs : 0 ≤ (roundFiniteCore f m e rnd).shift) :
    Nat.log2 (absNat m) + 1 +
        Int.toNat (roundFiniteCore f m e rnd).shift ≤ f.P := by
  let L : Int := Int.ofNat (Nat.log2 (absNat m)) + e
  let M : Int := max L (1 - f.bias)
  let E : Int := M - f.P + 1
  have hLE : L ≤ M := le_max_left _ _
  have hshiftEq :
      (roundFiniteCore f m e rnd).shift = e - E := by
    simp [roundFiniteCore, absNat, L, M, E]
  have htoNat :
      ((Int.toNat (roundFiniteCore f m e rnd).shift : Nat) : Int) =
        (roundFiniteCore f m e rnd).shift := by
    exact Int.toNat_of_nonneg hs
  have hcast :
      ((Nat.log2 (absNat m) + 1 +
          Int.toNat (roundFiniteCore f m e rnd).shift : Nat) : Int) =
        Int.ofNat (Nat.log2 (absNat m)) + 1 +
          (roundFiniteCore f m e rnd).shift := by
    rw [Nat.cast_add, Nat.cast_add, htoNat]
    norm_num
  have hInt :
      Int.ofNat (Nat.log2 (absNat m)) + 1 +
          (roundFiniteCore f m e rnd).shift ≤ f.P := by
    rw [hshiftEq]
    dsimp [L, M, E] at hLE ⊢
    omega
  have hNatCast :
      ((Nat.log2 (absNat m) + 1 +
          Int.toNat (roundFiniteCore f m e rnd).shift : Nat) : Int) ≤
        (f.P : Int) := by
    rw [hcast]
    exact hInt
  exact_mod_cast hNatCast

lemma roundFiniteCore_log2_succ_le_precision_add_negShift
    (m e : Int)
    (rnd : RoundingMode)
    (hs : ¬ 0 ≤ (roundFiniteCore f m e rnd).shift) :
    Nat.log2 (absNat m) + 1 ≤
      f.P + Int.toNat (-(roundFiniteCore f m e rnd).shift) := by
  have hIntBase :=
    roundFiniteCore_log2_succ_add_shift_le_precision_int
      (f := f) m e rnd
  have hnegNonneg : 0 ≤ -(roundFiniteCore f m e rnd).shift := by
    omega
  have hnegCast :
      ((Int.toNat (-(roundFiniteCore f m e rnd).shift) : Nat) : Int) =
        -(roundFiniteCore f m e rnd).shift :=
    Int.toNat_of_nonneg hnegNonneg
  have hInt :
      Int.ofNat (Nat.log2 (absNat m)) + 1 ≤
        (f.P : Int) + -(roundFiniteCore f m e rnd).shift := by
    omega
  have hLeft :
      ((Nat.log2 (absNat m) + 1 : Nat) : Int) =
        Int.ofNat (Nat.log2 (absNat m)) + 1 := by
    norm_num
  have hRight :
      ((f.P + Int.toNat (-(roundFiniteCore f m e rnd).shift) : Nat) : Int) =
        (f.P : Int) + -(roundFiniteCore f m e rnd).shift := by
    rw [Nat.cast_add, hnegCast]
  have hNatCast :
      ((Nat.log2 (absNat m) + 1 : Nat) : Int) ≤
        ((f.P + Int.toNat (-(roundFiniteCore f m e rnd).shift) : Nat) : Int) := by
    rw [hLeft, hRight]
    exact hInt
  exact_mod_cast hNatCast

lemma roundFiniteCore_q_lt_vnumPow_of_shift_nonneg
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hs : 0 ≤ (roundFiniteCore f m e rnd).shift) :
    (roundFiniteCore f m e rnd).q < vnumPow f := by
  let c := roundFiniteCore f m e rnd
  have hcond :
      0 ≤
        e -
          (max (Int.ofNat (Nat.log2 m.natAbs) + e) (1 - f.bias) -
            (f.P : Int) + 1) := by
    simpa [c, roundFiniteCore] using hs
  have hq :
      c.q = absNat m * 2 ^ Int.toNat c.shift := by
    dsimp [c]
    unfold roundFiniteCore
    simp only [absNat]
    rw [dif_pos hcond, dif_pos hcond]
  have ham_lt : absNat m < 2 ^ (Nat.log2 (absNat m) + 1) :=
    absNat_lt_pow_log2_succ (hm := hm)
  have hpos : 0 < 2 ^ Int.toNat c.shift :=
    pow_pos (by decide : 0 < 2) _
  have hq_lt :
      c.q < 2 ^ (Nat.log2 (absNat m) + 1) *
          2 ^ Int.toNat c.shift := by
    rw [hq]
    exact Nat.mul_lt_mul_of_pos_right ham_lt hpos
  have hpow_eq :
      2 ^ (Nat.log2 (absNat m) + 1) *
          2 ^ Int.toNat c.shift =
        2 ^ (Nat.log2 (absNat m) + 1 + Int.toNat c.shift) := by
    rw [← pow_add]
  have hexp :
      Nat.log2 (absNat m) + 1 + Int.toNat c.shift ≤ f.P := by
    dsimp [c]
    exact roundFiniteCore_log2_succ_add_shift_le_precision
      (f := f) m e rnd hs
  have hpow_le :
      2 ^ (Nat.log2 (absNat m) + 1 + Int.toNat c.shift) ≤
        2 ^ f.P :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
  have hq_lt_pow : c.q < 2 ^ f.P := by
    exact lt_of_lt_of_le (by simpa [hpow_eq] using hq_lt) hpow_le
  simpa [c, vnumPow] using hq_lt_pow

lemma roundFiniteCore_q_lt_vnumPow_of_shift_neg
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hs : ¬ 0 ≤ (roundFiniteCore f m e rnd).shift) :
    (roundFiniteCore f m e rnd).q < vnumPow f := by
  let c := roundFiniteCore f m e rnd
  have hcond :
      ¬ 0 ≤
        e -
          (max (Int.ofNat (Nat.log2 m.natAbs) + e) (1 - f.bias) -
            (f.P : Int) + 1) := by
    simpa [c, roundFiniteCore] using hs
  have hq :
      c.q = absNat m / 2 ^ Int.toNat (-c.shift) := by
    dsimp [c]
    unfold roundFiniteCore
    simp only [absNat]
    rw [dif_neg hcond, dif_neg hcond]
  have ham_lt : absNat m < 2 ^ (Nat.log2 (absNat m) + 1) :=
    absNat_lt_pow_log2_succ (hm := hm)
  have hexp :
      Nat.log2 (absNat m) + 1 ≤
        f.P + Int.toNat (-c.shift) := by
    dsimp [c]
    exact roundFiniteCore_log2_succ_le_precision_add_negShift
      (f := f) m e rnd hs
  have hpow_le :
      2 ^ (Nat.log2 (absNat m) + 1) ≤
        2 ^ (f.P + Int.toNat (-c.shift)) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
  have ham_lt_big :
      absNat m < 2 ^ f.P * 2 ^ Int.toNat (-c.shift) := by
    have hlt :
        absNat m < 2 ^ (f.P + Int.toNat (-c.shift)) :=
      lt_of_lt_of_le ham_lt hpow_le
    simpa [pow_add] using hlt
  have hq_lt_pow :
      c.q < 2 ^ f.P := by
    rw [hq]
    exact Nat.div_lt_of_lt_mul (by
      simpa [Nat.mul_comm] using ham_lt_big)
  simpa [c, vnumPow] using hq_lt_pow

lemma roundFiniteCore_q_ge_half_of_E_gt_shift_nonneg
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hEgt : f.emin_lsb < (roundFiniteCore f m e rnd).E)
    (hs : 0 ≤ (roundFiniteCore f m e rnd).shift) :
    2 ^ (f.P - 1) ≤ (roundFiniteCore f m e rnd).q := by
  let c := roundFiniteCore f m e rnd
  have hcond :
      0 ≤
        e -
          (max (Int.ofNat (Nat.log2 m.natAbs) + e) (1 - f.bias) -
            (f.P : Int) + 1) := by
    simpa [c, roundFiniteCore] using hs
  have hq :
      c.q = absNat m * 2 ^ Int.toNat c.shift := by
    dsimp [c]
    unfold roundFiniteCore
    simp only [absNat]
    rw [dif_pos hcond, dif_pos hcond]
  have ham_ne : absNat m ≠ 0 := by
    simpa [absNat] using Int.natAbs_ne_zero.mpr hm
  have hpow_log_le : 2 ^ Nat.log2 (absNat m) ≤ absNat m :=
    (Nat.le_log2 ham_ne).mp le_rfl
  have hEqInt :
      Int.ofNat (Nat.log2 (absNat m)) + 1 + c.shift = f.P := by
    dsimp [c]
    exact roundFiniteCore_log2_succ_add_shift_eq_precision_int_of_E_gt
      (f := f) m e rnd hEgt
  have htoNat :
      ((Int.toNat c.shift : Nat) : Int) = c.shift :=
    Int.toNat_of_nonneg hs
  have hExpEq :
      Nat.log2 (absNat m) + Int.toNat c.shift = f.P - 1 := by
    have hcast :
        ((Nat.log2 (absNat m) + Int.toNat c.shift : Nat) : Int) =
          Int.ofNat (Nat.log2 (absNat m)) + c.shift := by
      rw [Nat.cast_add, htoNat]
      norm_num
    have hcastEq :
        ((Nat.log2 (absNat m) + Int.toNat c.shift : Nat) : Int) =
          (f.P - 1 : Nat) := by
      rw [hcast]
      have hPpos : (0 : Int) < f.P := by exact_mod_cast f.h_P.1
      have hPpredCast : ((f.P - 1 : Nat) : Int) = (f.P : Int) - 1 := by
        rw [Nat.cast_sub (by exact Nat.succ_le_of_lt f.h_P.1)]
        norm_num
      rw [hPpredCast]
      omega
    exact_mod_cast hcastEq
  calc
    2 ^ (f.P - 1)
        = 2 ^ (Nat.log2 (absNat m) + Int.toNat c.shift) := by
            rw [hExpEq]
    _ = 2 ^ Nat.log2 (absNat m) * 2 ^ Int.toNat c.shift := by
            rw [pow_add]
    _ ≤ absNat m * 2 ^ Int.toNat c.shift := by
            exact Nat.mul_le_mul_right _ hpow_log_le
    _ = c.q := by rw [hq]

lemma roundFiniteCore_q_ge_half_of_E_gt_shift_neg
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hEgt : f.emin_lsb < (roundFiniteCore f m e rnd).E)
    (hs : ¬ 0 ≤ (roundFiniteCore f m e rnd).shift) :
    2 ^ (f.P - 1) ≤ (roundFiniteCore f m e rnd).q := by
  let c := roundFiniteCore f m e rnd
  have hcond :
      ¬ 0 ≤
        e -
          (max (Int.ofNat (Nat.log2 m.natAbs) + e) (1 - f.bias) -
            (f.P : Int) + 1) := by
    simpa [c, roundFiniteCore] using hs
  have hq :
      c.q = absNat m / 2 ^ Int.toNat (-c.shift) := by
    dsimp [c]
    unfold roundFiniteCore
    simp only [absNat]
    rw [dif_neg hcond, dif_neg hcond]
  have ham_ne : absNat m ≠ 0 := by
    simpa [absNat] using Int.natAbs_ne_zero.mpr hm
  have hpow_log_le : 2 ^ Nat.log2 (absNat m) ≤ absNat m :=
    (Nat.le_log2 ham_ne).mp le_rfl
  have hEqInt :
      Int.ofNat (Nat.log2 (absNat m)) + 1 + c.shift = f.P := by
    dsimp [c]
    exact roundFiniteCore_log2_succ_add_shift_eq_precision_int_of_E_gt
      (f := f) m e rnd hEgt
  have hshiftNeg : c.shift < 0 := by
    have hs' : ¬ 0 ≤ c.shift := by
      simpa [c] using hs
    omega
  have hnegNonneg : 0 ≤ -c.shift := by omega
  have hnegCast :
      ((Int.toNat (-c.shift) : Nat) : Int) = -c.shift :=
    Int.toNat_of_nonneg hnegNonneg
  have hExpEq :
      Nat.log2 (absNat m) = (f.P - 1) + Int.toNat (-c.shift) := by
    have hcast :
        (((f.P - 1) + Int.toNat (-c.shift) : Nat) : Int) =
          (f.P : Int) - 1 - c.shift := by
      rw [Nat.cast_add, hnegCast]
      have hPpredCast : ((f.P - 1 : Nat) : Int) = (f.P : Int) - 1 := by
        rw [Nat.cast_sub (by exact Nat.succ_le_of_lt f.h_P.1)]
        norm_num
      rw [hPpredCast]
      omega
    have hcastEq :
        ((Nat.log2 (absNat m) : Nat) : Int) =
          (((f.P - 1) + Int.toNat (-c.shift) : Nat) : Int) := by
      rw [hcast]
      change Int.ofNat (Nat.log2 (absNat m)) = (f.P : Int) - 1 - c.shift
      omega
    exact_mod_cast hcastEq
  have hmul_le :
      2 ^ (f.P - 1) * 2 ^ Int.toNat (-c.shift) ≤ absNat m := by
    calc
      2 ^ (f.P - 1) * 2 ^ Int.toNat (-c.shift)
          = 2 ^ ((f.P - 1) + Int.toNat (-c.shift)) := by
              rw [pow_add]
      _ = 2 ^ Nat.log2 (absNat m) := by rw [hExpEq]
      _ ≤ absNat m := hpow_log_le
  have hdiv :
      2 ^ (f.P - 1) ≤ absNat m / 2 ^ Int.toNat (-c.shift) := by
    exact (Nat.le_div_iff_mul_le (pow_pos (by decide : 0 < 2) _)).mpr hmul_le
  change 2 ^ (f.P - 1) ≤ c.q
  rw [hq]
  exact hdiv

lemma roundFiniteCore_q_ge_half_of_E_gt
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hEgt : f.emin_lsb < (roundFiniteCore f m e rnd).E) :
    2 ^ (f.P - 1) ≤ (roundFiniteCore f m e rnd).q := by
  by_cases hs : 0 ≤ (roundFiniteCore f m e rnd).shift
  · exact roundFiniteCore_q_ge_half_of_E_gt_shift_nonneg
      (f := f) m e rnd hm hEgt hs
  · exact roundFiniteCore_q_ge_half_of_E_gt_shift_neg
      (f := f) m e rnd hm hEgt hs

lemma roundFiniteCore_qplus_nonneg
    (m e : Int)
    (rnd : RoundingMode) :
    0 ≤ (roundFiniteCore f m e rnd).qplus := by
  unfold roundFiniteCore
  simp only
  split
  · split
    · exact Int.add_nonneg (Int.natCast_nonneg _) zero_le_one
    · exact Int.natCast_nonneg _
  · split
    · exact Int.add_nonneg (Int.natCast_nonneg _) zero_le_one
    · exact Int.natCast_nonneg _

lemma roundFiniteCore_q_le_qplus
    (m e : Int)
    (rnd : RoundingMode) :
    (((roundFiniteCore f m e rnd).q : Nat) : Int) ≤
      (roundFiniteCore f m e rnd).qplus := by
  unfold roundFiniteCore
  simp only
  split <;> split <;> omega

lemma roundFiniteCore_qplus_le_q_succ
    (m e : Int)
    (rnd : RoundingMode) :
    (roundFiniteCore f m e rnd).qplus ≤
      (((roundFiniteCore f m e rnd).q : Nat) : Int) + 1 := by
  unfold roundFiniteCore
  simp only
  split <;> split <;> omega

lemma roundFiniteCore_qplus_le_vnumPow_of_shift_nonneg
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hs : 0 ≤ (roundFiniteCore f m e rnd).shift) :
    (roundFiniteCore f m e rnd).qplus ≤ (vnumPow f : Int) := by
  have hq_lt :
      (roundFiniteCore f m e rnd).q < vnumPow f :=
    roundFiniteCore_q_lt_vnumPow_of_shift_nonneg
      (f := f) m e rnd hm hs
  have hq_succ :
      (((roundFiniteCore f m e rnd).q : Nat) : Int) + 1 ≤
        (vnumPow f : Int) := by
    exact_mod_cast (Nat.succ_le_of_lt hq_lt)
  exact le_trans
    (roundFiniteCore_qplus_le_q_succ (f := f) m e rnd)
    hq_succ

lemma roundFiniteCore_qplus_le_vnumPow_of_shift_neg
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hs : ¬ 0 ≤ (roundFiniteCore f m e rnd).shift) :
    (roundFiniteCore f m e rnd).qplus ≤ (vnumPow f : Int) := by
  have hq_lt :
      (roundFiniteCore f m e rnd).q < vnumPow f :=
    roundFiniteCore_q_lt_vnumPow_of_shift_neg
      (f := f) m e rnd hm hs
  have hq_succ :
      (((roundFiniteCore f m e rnd).q : Nat) : Int) + 1 ≤
        (vnumPow f : Int) := by
    exact_mod_cast (Nat.succ_le_of_lt hq_lt)
  exact le_trans
    (roundFiniteCore_qplus_le_q_succ (f := f) m e rnd)
    hq_succ

lemma roundFiniteCore_qplus_le_vnumPow
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0) :
    (roundFiniteCore f m e rnd).qplus ≤ (vnumPow f : Int) := by
  by_cases hs : 0 ≤ (roundFiniteCore f m e rnd).shift
  · exact roundFiniteCore_qplus_le_vnumPow_of_shift_nonneg
      (f := f) m e rnd hm hs
  · exact roundFiniteCore_qplus_le_vnumPow_of_shift_neg
      (f := f) m e rnd hm hs

lemma roundFiniteCore_sign_natAbs
    (m e : Int)
    (rnd : RoundingMode) :
    Int.natAbs (roundFiniteCore f m e rnd).sign = 1 := by
  unfold roundFiniteCore
  simp only
  split <;> simp

lemma roundFiniteCore_natAbs_rounded_eq_qplus
    (m e : Int)
    (rnd : RoundingMode) :
    ((Int.natAbs (roundFiniteCore f m e rnd).rounded : Nat) : Int) =
      (roundFiniteCore f m e rnd).qplus := by
  let c := roundFiniteCore f m e rnd
  have hq : 0 ≤ c.qplus := by
    dsimp [c]
    exact roundFiniteCore_qplus_nonneg (f := f) m e rnd
  have hs : Int.natAbs c.sign = 1 := by
    dsimp [c]
    exact roundFiniteCore_sign_natAbs (f := f) m e rnd
  have hrounded : c.rounded = c.sign * c.qplus := by
    dsimp [c]
    simp [roundFiniteCore]
  calc
    ((Int.natAbs c.rounded : Nat) : Int)
        = ((Int.natAbs (c.sign * c.qplus) : Nat) : Int) := by
            rw [hrounded]
    _ = ((Int.natAbs c.sign * Int.natAbs c.qplus : Nat) : Int) := by
            rw [Int.natAbs_mul]
    _ = ((Int.natAbs c.qplus : Nat) : Int) := by
            rw [hs]
            norm_num
    _ = c.qplus := by
            exact Int.natAbs_of_nonneg hq

lemma roundFiniteCore_half_le_natAbs_rounded_of_E_gt
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hEgt : f.emin_lsb < (roundFiniteCore f m e rnd).E) :
    2 ^ (f.P - 1) ≤ Int.natAbs (roundFiniteCore f m e rnd).rounded := by
  have hq :
      2 ^ (f.P - 1) ≤ (roundFiniteCore f m e rnd).q :=
    roundFiniteCore_q_ge_half_of_E_gt (f := f) m e rnd hm hEgt
  have hqInt :
      ((2 ^ (f.P - 1) : Nat) : Int) ≤
        (((roundFiniteCore f m e rnd).q : Nat) : Int) := by
    exact_mod_cast hq
  have hqplus :
      ((2 ^ (f.P - 1) : Nat) : Int) ≤
        (roundFiniteCore f m e rnd).qplus :=
    le_trans hqInt (roundFiniteCore_q_le_qplus (f := f) m e rnd)
  have hEq := roundFiniteCore_natAbs_rounded_eq_qplus (f := f) m e rnd
  rw [← hEq] at hqplus
  exact_mod_cast hqplus

lemma roundFiniteCore_E_eq_emin_lsb_of_natAbs_lt_half
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    (hlow :
      Int.natAbs (roundFiniteCore f m e rnd).rounded < 2 ^ (f.P - 1)) :
    (roundFiniteCore f m e rnd).E = f.emin_lsb := by
  have hge : f.emin_lsb ≤ (roundFiniteCore f m e rnd).E :=
    roundFiniteCore_E_ge_emin_lsb (f := f) m e rnd
  by_cases hgt : f.emin_lsb < (roundFiniteCore f m e rnd).E
  · have hhalf :
        2 ^ (f.P - 1) ≤ Int.natAbs (roundFiniteCore f m e rnd).rounded :=
      roundFiniteCore_half_le_natAbs_rounded_of_E_gt
        (f := f) m e rnd hm hgt
    exact False.elim ((not_le_of_gt hlow) hhalf)
  · omega

lemma roundFiniteCore_natAbs_rounded_le_of_qplus_le
    (m e : Int)
    (rnd : RoundingMode)
    {n : Nat}
    (h : (roundFiniteCore f m e rnd).qplus ≤ (n : Int)) :
    Int.natAbs (roundFiniteCore f m e rnd).rounded ≤ n := by
  have hEq := roundFiniteCore_natAbs_rounded_eq_qplus (f := f) m e rnd
  rw [← hEq] at h
  exact_mod_cast h

lemma roundFiniteCore_natAbs_rounded_lt_of_qplus_lt
    (m e : Int)
    (rnd : RoundingMode)
    {n : Nat}
    (h : (roundFiniteCore f m e rnd).qplus < (n : Int)) :
    Int.natAbs (roundFiniteCore f m e rnd).rounded < n := by
  have hEq := roundFiniteCore_natAbs_rounded_eq_qplus (f := f) m e rnd
  rw [← hEq] at h
  exact_mod_cast h

lemma roundFiniteCore_natAbs_rounded_lt_vnumPow_of_qplus_le
    (m e : Int)
    (rnd : RoundingMode)
    (hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hq : (roundFiniteCore f m e rnd).qplus ≤ (vnumPow f : Int)) :
    Int.natAbs (roundFiniteCore f m e rnd).rounded < vnumPow f := by
  have hle : Int.natAbs (roundFiniteCore f m e rnd).rounded ≤ vnumPow f :=
    roundFiniteCore_natAbs_rounded_le_of_qplus_le (f := f) m e rnd hq
  exact lt_of_le_of_ne hle hcore

lemma roundFinite_core_bounded_of_qplus_le
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (he' : e' = (roundFiniteCore f m e rnd).E)
    (hq : (roundFiniteCore f m e rnd).qplus ≤ (vnumPow f : Int)) :
    @bounded_float 2 f.to_format ⟨m', e'⟩ := by
  constructor
  · have hnatLt :
        Int.natAbs (roundFiniteCore f m e rnd).rounded < vnumPow f :=
      roundFiniteCore_natAbs_rounded_lt_vnumPow_of_qplus_le
        (f := f) m e rnd hcore hq
    have hintLt :
        |(roundFiniteCore f m e rnd).rounded| < ((vnumPow f : Nat) : Int) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hnatLt
    rw [hm']
    simpa [vnum, vnumPow, to_format] using hintLt
  · rw [he']
    simpa [to_format] using roundFiniteCore_E_ge_emin_lsb (f := f) m e rnd

lemma roundFinite_core_bounded
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hm : m ≠ 0)
    (hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (he' : e' = (roundFiniteCore f m e rnd).E) :
    @bounded_float 2 f.to_format ⟨m', e'⟩ := by
  exact roundFinite_core_bounded_of_qplus_le
    (f := f) m e rnd hcore hm' he'
    (roundFiniteCore_qplus_le_vnumPow (f := f) m e rnd hm)

lemma roundFinite_core_abs_lt_vnumPow
    (m e : Int)
    (rnd : RoundingMode)
    {m' : Int}
    (hm : m ≠ 0)
    (hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded) :
    |m'| < ((2 ^ f.P : Nat) : Int) := by
  have hnatLt :
      Int.natAbs (roundFiniteCore f m e rnd).rounded < vnumPow f :=
    roundFiniteCore_natAbs_rounded_lt_vnumPow_of_qplus_le
      (f := f) m e rnd hcore
      (roundFiniteCore_qplus_le_vnumPow (f := f) m e rnd hm)
  have hintLt :
      |(roundFiniteCore f m e rnd).rounded| < ((vnumPow f : Nat) : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnatLt
  rw [hm']
  simpa [vnumPow] using hintLt

lemma roundFinite_core_low_mag_exp_eq_emin_lsb
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hm : m ≠ 0)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (he' : e' = (roundFiniteCore f m e rnd).E)
    (hlow : |m'| < ((2 ^ (f.P - 1) : Nat) : Int)) :
    e' = f.emin_lsb := by
  have hlowCore :
      |(roundFiniteCore f m e rnd).rounded| <
        ((2 ^ (f.P - 1) : Nat) : Int) := by
    rw [← hm']
    exact hlow
  have hlowNat :
      Int.natAbs (roundFiniteCore f m e rnd).rounded < 2 ^ (f.P - 1) := by
    rw [← Int.natCast_natAbs] at hlowCore
    exact_mod_cast hlowCore
  have hE :=
    roundFiniteCore_E_eq_emin_lsb_of_natAbs_lt_half
      (f := f) m e rnd hm hlowNat
  rw [he']
  exact hE

lemma roundFinite_output_exp_ge_emin_lsb
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (h : roundFinite f m e rnd = Value.finite (f := f) m' e') :
    f.emin_lsb ≤ e' := by
  unfold roundFinite at h
  split at h
  · simp at h
    rcases h with ⟨rfl, rfl⟩
    exact le_rfl
  · let c := roundFiniteCore f m e rnd
    have hE : f.emin_lsb ≤ c.E := by
      dsimp [c]
      exact roundFiniteCore_E_ge_emin_lsb (f := f) m e rnd
    change
      (if Int.natAbs c.rounded = vnumPow f then
          Value.finite (f := f) (c.rounded / 2) (c.E + 1)
        else
          Value.finite (f := f) c.rounded c.E) =
        Value.finite (f := f) m' e' at h
    split at h
    · simp at h
      rcases h with ⟨rfl, rfl⟩
      omega
    · simp at h
      rcases h with ⟨rfl, rfl⟩
      exact hE

lemma roundFinite_output_cases
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (h : roundFinite f m e rnd = Value.finite (f := f) m' e') :
    (m = 0 ∧ m' = 0 ∧ e' = f.emin_lsb) ∨
      (m ≠ 0 ∧
        Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f ∧
        m' = (roundFiniteCore f m e rnd).rounded / 2 ∧
        e' = (roundFiniteCore f m e rnd).E + 1) ∨
      (m ≠ 0 ∧
        Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f ∧
        m' = (roundFiniteCore f m e rnd).rounded ∧
        e' = (roundFiniteCore f m e rnd).E) := by
  by_cases hm : m = 0
  · subst m
    simp [roundFinite] at h
    rcases h with ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · let c := roundFiniteCore f m e rnd
    unfold roundFinite at h
    rw [if_neg hm] at h
    change
      (if Int.natAbs c.rounded = vnumPow f then
          Value.finite (f := f) (c.rounded / 2) (c.E + 1)
        else
          Value.finite (f := f) c.rounded c.E) =
        Value.finite (f := f) m' e' at h
    by_cases hc : Int.natAbs c.rounded = vnumPow f
    · rw [if_pos hc] at h
      simp at h
      rcases h with ⟨rfl, rfl⟩
      exact Or.inr (Or.inl ⟨hm, by simpa [c] using hc, rfl, rfl⟩)
    · rw [if_neg hc] at h
      simp at h
      rcases h with ⟨rfl, rfl⟩
      exact Or.inr (Or.inr ⟨hm, by simpa [c] using hc, rfl, rfl⟩)

lemma roundFinite_output_cases_of_nonzero
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    {m' e' : Int}
    (h : roundFinite f m e rnd = Value.finite (f := f) m' e') :
      (Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f ∧
        m' = (roundFiniteCore f m e rnd).rounded / 2 ∧
        e' = (roundFiniteCore f m e rnd).E + 1) ∨
      (Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f ∧
        m' = (roundFiniteCore f m e rnd).rounded ∧
        e' = (roundFiniteCore f m e rnd).E) := by
  rcases roundFinite_output_cases (f := f) m e rnd h with hzero | hrest
  · exact False.elim (hm hzero.1)
  · rcases hrest with hcarry | hcore
    · exact Or.inl ⟨hcarry.2.1, hcarry.2.2.1, hcarry.2.2.2⟩
    · exact Or.inr ⟨hcore.2.1, hcore.2.2.1, hcore.2.2.2⟩

lemma roundFinite_output_signif_eq_core_or_carry
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    {m' e' : Int}
    (h : roundFinite f m e rnd = Value.finite (f := f) m' e') :
    m' = (roundFiniteCore f m e rnd).rounded / 2 ∨
      m' = (roundFiniteCore f m e rnd).rounded := by
  rcases roundFinite_output_cases_of_nonzero (f := f) m e rnd hm h with hcarry | hcore
  · exact Or.inl hcarry.2.1
  · exact Or.inr hcore.2.1

lemma roundFinite_output_exp_eq_core_or_carry
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    {m' e' : Int}
    (h : roundFinite f m e rnd = Value.finite (f := f) m' e') :
    e' = (roundFiniteCore f m e rnd).E + 1 ∨
      e' = (roundFiniteCore f m e rnd).E := by
  rcases roundFinite_output_cases_of_nonzero (f := f) m e rnd hm h with hcarry | hcore
  · exact Or.inl hcarry.2.2
  · exact Or.inr hcore.2.2

lemma roundFinite_output_canonical_of_branch_obligations
    (m e : Int)
    (rnd : RoundingMode)
    (hm : m ≠ 0)
    {m' e' : Int}
    (h : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (hcarry :
      Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f →
        m' = (roundFiniteCore f m e rnd).rounded / 2 →
        e' = (roundFiniteCore f m e rnd).E + 1 →
        @canonical_p3109 f ⟨m', e'⟩)
    (hcore :
      Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f →
        m' = (roundFiniteCore f m e rnd).rounded →
        e' = (roundFiniteCore f m e rnd).E →
        @canonical_p3109 f ⟨m', e'⟩) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  rcases roundFinite_output_cases_of_nonzero (f := f) m e rnd hm h with hcarryCase | hcoreCase
  · exact hcarry hcarryCase.1 hcarryCase.2.1 hcarryCase.2.2
  · exact hcore hcoreCase.1 hcoreCase.2.1 hcoreCase.2.2

lemma roundFinite_carry_half_natAbs
    (c : RoundFiniteCore f)
    (hcarry : Int.natAbs c.rounded = vnumPow f) :
    Int.natAbs (c.rounded / 2) = 2 ^ (f.P - 1) := by
  have hpow : vnumPow f = 2 * 2 ^ (f.P - 1) := by
    have hP : (f.P - 1) + 1 = f.P := by
      simpa [Nat.succ_eq_add_one] using
        (Nat.succ_pred_eq_of_pos f.h_P.1)
    rw [vnumPow]
    nth_rewrite 1 [← hP]
    rw [pow_succ, Nat.mul_comm]
  have hdvdNat : (2 : Nat) ∣ Int.natAbs c.rounded := by
    rw [hcarry, vnumPow]
    exact dvd_pow_self 2 f.h_P.1.ne'
  have hdvdInt : (2 : Int) ∣ c.rounded := by
    exact Int.natCast_dvd.mpr hdvdNat
  have hmul : c.rounded / 2 * 2 = c.rounded := by
    exact Int.ediv_mul_cancel hdvdInt
  have hnat := congrArg Int.natAbs hmul
  norm_num [Int.natAbs_mul, hcarry, hpow] at hnat
  rw [Nat.mul_comm 2 (2 ^ (f.P - 1))] at hnat
  exact Nat.mul_right_cancel (by decide : 0 < 2) hnat

lemma p_pow_pred_lt_pow_sub_one
    (f : p3109_format)
    (hPgt : 1 < f.P) :
    ((2 ^ (f.P - 1) : Nat) : Int) < ((2 ^ f.P : Nat) : Int) - 1 := by
  have hP : f.P = (f.P - 1) + 1 := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.succ_pred_eq_of_pos f.h_P.1).symm
  have hpow : ((2 ^ f.P : Nat) : Int) =
      2 * ((2 ^ (f.P - 1) : Nat) : Int) := by
    rw [hP, pow_succ]
    norm_num [Nat.cast_mul, Nat.mul_comm]
  have hhalf : (2 : Int) ≤ ((2 ^ (f.P - 1) : Nat) : Int) := by
    have hleNat : 2 ^ 1 ≤ 2 ^ (f.P - 1) := by
      exact pow_le_pow_right₀ (by decide : 0 < 2) (by omega)
    norm_num at hleNat
    exact_mod_cast hleNat
  omega

lemma p_pow_pred_lt_pow_sub_two
    (f : p3109_format)
    (hPgt : 2 < f.P) :
    ((2 ^ (f.P - 1) : Nat) : Int) < ((2 ^ f.P : Nat) : Int) - 2 := by
  have hP : f.P = (f.P - 1) + 1 := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.succ_pred_eq_of_pos f.h_P.1).symm
  have hpow : ((2 ^ f.P : Nat) : Int) =
      2 * ((2 ^ (f.P - 1) : Nat) : Int) := by
    rw [hP, pow_succ]
    norm_num [Nat.cast_mul, Nat.mul_comm]
  have hhalf : (4 : Int) ≤ ((2 ^ (f.P - 1) : Nat) : Int) := by
    have hleNat : 2 ^ 2 ≤ 2 ^ (f.P - 1) := by
      exact pow_le_pow_right₀ (by decide : 0 < 2) (by omega)
    norm_num at hleNat
    exact_mod_cast hleNat
  omega

lemma canonical_p3109_normal_of_natAbs_half_exp_range
    {m e : Int}
    (hmag : Int.natAbs m = 2 ^ (f.P - 1))
    (hemin : f.emin_lsb ≤ e)
    (hemax : e ≤ f.emax_lsb) :
    @canonical_p3109 f ⟨m, e⟩ := by
  left
  constructor
  · constructor
    · simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat]
      rw [← Int.natCast_natAbs, hmag]
      have hltExp : f.P - 1 < f.P :=
        Nat.pred_lt (Nat.ne_of_gt f.h_P.1)
      exact_mod_cast
        (pow_lt_pow_right₀ (by decide : 1 < 2) hltExp)
    · simpa [to_format] using hemin
  · constructor
    · simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat, abs_mul,
        Nat.abs_ofNat]
      rw [← Int.natCast_natAbs, hmag]
      have hP : f.P = (f.P - 1) + 1 := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.succ_pred_eq_of_pos f.h_P.1).symm
      have hpow : ((2 ^ f.P : Nat) : Int) =
          2 * ((2 ^ (f.P - 1) : Nat) : Int) := by
        rw [hP, pow_succ]
        norm_num [Nat.cast_mul, Nat.mul_comm]
      exact le_of_eq hpow
    · constructor
      · exact hemax
      · intro hPgt _
        cases hs : f.s <;> cases hd : f.d
        · simp [hs, hd]
        · simp [hs, hd]
          rw [← Int.natCast_natAbs, hmag]
          exact p_pow_pred_lt_pow_sub_one f hPgt
        · simp [hs, hd]
          rw [← Int.natCast_natAbs, hmag]
          exact p_pow_pred_lt_pow_sub_one f hPgt
        · by_cases hp2 : f.P = 2
          · simp [hs, hd, hp2]
          · simp [hs, hd, hp2]
            rw [← Int.natCast_natAbs, hmag]
            have hPgt2 : 2 < f.P := by omega
            exact p_pow_pred_lt_pow_sub_two f hPgt2

lemma roundFinite_carry_canonical_of_exp_le
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hcarry : Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded / 2)
    (he' : e' = (roundFiniteCore f m e rnd).E + 1)
    (hemax : (roundFiniteCore f m e rnd).E + 1 ≤ f.emax_lsb) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  have hmag : Int.natAbs m' = 2 ^ (f.P - 1) := by
    rw [hm']
    exact roundFinite_carry_half_natAbs (f := f)
      (roundFiniteCore f m e rnd) hcarry
  have hEminCore : f.emin_lsb ≤ (roundFiniteCore f m e rnd).E :=
    roundFiniteCore_E_ge_emin_lsb (f := f) m e rnd
  have hemin : f.emin_lsb ≤ e' := by
    rw [he']
    omega
  have hemax' : e' ≤ f.emax_lsb := by
    rw [he']
    exact hemax
  exact canonical_p3109_normal_of_natAbs_half_exp_range
    (f := f) hmag hemin hemax'

end Exec
end p3109_format

