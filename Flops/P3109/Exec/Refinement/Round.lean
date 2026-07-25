import Flops.P3109.Projection
import Flops.P3109.Bijection
import Flops.P3109.Exec.Ops
import Flops.P3109.Exec.Project
import Flops.P3109.Exec.Value
import Flops.P3109.Exec.Round
import Flops.P3109.Exec.Saturate
import Mathlib.Algebra.Order.Floor.Semifield

namespace p3109_format
namespace Exec

lemma zpow_neg_one_eq_inv_two : (2⁻¹ : ℝ) = (1 : ℝ) / 2 := by
  norm_num [zpow_neg]

-- Basic refinement bridge: `toBits` returns a representative whose
-- `fromBits` form is semantically equal to the original p3109 value.
lemma toBits_refines (f : p3109_format) (x : p3109 f) :
    toEReal (fromBits (toBits (f := f) x)) = (x.to_ereal : EReal) := by
  simpa using (fromBits_toBits (f := f) x)

-- The executable decode/encode pair is a true bit-level round-trip.
lemma decode_refines (x : Bits f) :
    toEReal (fromBits x) = p3109.to_ereal (p3109.n_to_p3109 (f := f) x) := by
  simpa using (toEReal_fromBits (f := f) x)

lemma encode_refines (x : Bits f) :
    Exec.encode (Exec.decode x) = x := by
  apply Fin.ext
  calc
    (Exec.encode (Exec.decode x)).val
        = encodeNat (Exec.decode x) % 2 ^ f.K := rfl
    _ = encodeNat (Exec.decode x) := by
      exact Nat.mod_eq_of_lt (encode_lt_of_decode (f := f) x)
    _ = (x : Nat) := encode_decode_eq x

lemma classify_refines (x : Bits f) :
    classify x = decode x := by
  rfl

lemma one_le_K (f : p3109_format) : 1 ≤ f.K := by
  exact Nat.succ_le_of_lt (Nat.lt_trans (by decide : 0 < 2) f.h_K)

lemma pow_pred_lt_pow (f : p3109_format) : 2 ^ (f.K - 1) < 2 ^ f.K := by
  apply pow_lt_pow_right₀ (by decide : 1 < 2)
  exact Nat.sub_lt (one_le_K f) (by decide : 0 < 1)

lemma pow_pred_lt_pow_sub_one (f : p3109_format) :
    2 ^ (f.K - 1) < 2 ^ f.K - 1 := by
  have hk : f.K - 1 + 1 = f.K := Nat.sub_add_cancel (one_le_K f)
  have hge : 2 ≤ 2 ^ (f.K - 1) := by
    rw [← pow_one 2]
    apply pow_le_pow_right₀ (by decide : 1 ≤ 2)
    exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Nat.lt_trans (by decide : 1 < 2) f.h_K))
  rw [← hk, pow_add]
  norm_num
  omega

lemma two_le_pow_K (f : p3109_format) : 2 ≤ 2 ^ f.K := by
  rw [← pow_one 2]
  apply pow_le_pow_right₀ (by decide : 1 ≤ 2)
  exact one_le_K f

lemma four_le_pow_K (f : p3109_format) : 4 ≤ 2 ^ f.K := by
  rw [show (4 : Nat) = 2 ^ 2 by decide]
  apply pow_le_pow_right₀ (by decide : 1 ≤ 2)
  exact Nat.le_of_lt f.h_K

lemma zero_lt_pow_pred (f : p3109_format) : 0 < 2 ^ (f.K - 1) := by
  exact pow_pos (by decide : 0 < 2) (f.K - 1)

/-
The executable round/saturate/project path now returns `Value`/`Bits`, so the
old definitional refinement lemmas are intentionally split into smaller facts.
The remaining finite-nonzero rounding theorem relates integer quotient/remainder
arithmetic in `roundFinite` to the real `floor`/`fract` specification.
-/

def normalizedRoundAway (f : p3109_format) (x S Δ : ℝ) (E : Int)
    (RNITE : ℝ → Int) : RoundingMode → Prop
  | .RNE =>
      (2⁻¹ : ℝ) < Δ ∨
        Δ = (2⁻¹ : ℝ) ∧
          if 1 < f.P then
            Odd (⌊S⌋ : Int)
          else
            Odd (E + f.bias) ∧ (0 ≤ S → 1 ≤ S)
  | .RNA => (2⁻¹ : ℝ) ≤ Δ
  | .RU => 0 < Δ ∧ 0 < x
  | .RD => 0 < Δ ∧ x < 0
  | .RZ => False
  | .RTO =>
      0 < Δ ∧
        (if 1 < f.P then
          Even (⌊S⌋ : Int)
        else
          0 ≤ S ∧ S < 1 ∨ Even (E + f.bias))
  | .StochasticA N R _ =>
      (2 ^ N : Int) ≤ ⌊Δ * (2 ^ N : ℝ)⌋ + (R : Int)
  | .StochasticB N R _ =>
      (2 ^ (N + 1) : Int) ≤
        ⌊Δ * (2 ^ (N + 1) : ℝ)⌋ + 2 * (R : Int) + 1
  | .StochasticC N R _ =>
      (2 ^ N : Int) ≤ RNITE (Δ * (2 ^ N : ℝ)) + (R : Int)

lemma intLog_ratCast {q : ℚ} (_hqpos : 0 < q) :
    Int.log 2 (q : ℝ) = Int.log 2 q := by
  unfold Int.log
  by_cases hq : 1 ≤ q
  · have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    rw [if_pos hqR, if_pos hq]
    congr 1
    have hfloor :
        ⌊(q : ℝ)⌋₊ = ⌊q⌋₊ := by
      calc
        ⌊(q : ℝ)⌋₊ = (⌊(q : ℝ)⌋ : Int).toNat := (Int.floor_toNat (q : ℝ)).symm
        _ = (⌊q⌋ : Int).toNat := congrArg Int.toNat (Rat.floor_cast (α := ℝ) q)
        _ = ⌊q⌋₊ := Int.floor_toNat q
    exact congrArg (Nat.log 2) hfloor
  · have hqR : ¬ (1 : ℝ) ≤ (q : ℝ) := by
      intro h
      exact hq (by exact_mod_cast h)
    rw [if_neg hqR, if_neg hq]
    congr 1
    have hcast : (((q⁻¹ : ℚ) : ℝ)) = ((q : ℝ)⁻¹) := by norm_num
    have hceil :
        ⌈((q : ℝ)⁻¹)⌉₊ = ⌈q⁻¹⌉₊ := by
      calc
        ⌈((q : ℝ)⁻¹)⌉₊ = (⌈((q : ℝ)⁻¹)⌉ : Int).toNat := (Int.ceil_toNat ((q : ℝ)⁻¹)).symm
        _ = (⌈(q⁻¹ : ℚ)⌉ : Int).toNat := by
          simpa [hcast] using congrArg Int.toNat (Rat.ceil_cast (α := ℝ) (q⁻¹))
        _ = ⌈q⁻¹⌉₊ := Int.ceil_toNat (q⁻¹)
    exact congrArg (fun n : Nat => (n : Int)) (congrArg (Nat.clog 2) hceil)

lemma round_to_precision_real_idempotent (x : ℝ) (rnd : RoundingMode) :
    @round_to_precision_real f (@round_to_precision_real f x rnd) rnd =
      @round_to_precision_real f x rnd := by
  obtain ⟨a, hb, ha⟩ := round_to_precision_exists_bounded (f := f) x rnd
  calc
    @round_to_precision_real f (@round_to_precision_real f x rnd) rnd
        = @round_to_precision_real f (a : ℝ) rnd := by rw [← ha]
    _ = @round_to_precision_generic f (a : ℝ) rnd := by
          exact round_to_precision_eq (f := f) (a : ℝ) rnd
    _ = (@round_to_fp f rnd (a : ℝ) : ℝ) := by
          exact round_to_fp_eq (f := f) (a : ℝ) rnd
    _ = (a : ℝ) := round_to_fp_bounded_self (f := f) rnd a hb
    _ = @round_to_precision_real f x rnd := ha

lemma round_to_precision_idempotent (x : EReal) (rnd : RoundingMode) :
    @round_to_precision f (@round_to_precision f x rnd) rnd =
      @round_to_precision f x rnd := by
  cases x
  · rfl
  · rename_i r
    exact congrArg (fun y : ℝ => (y : EReal))
      (round_to_precision_real_idempotent (f := f) r rnd)
  · rfl

lemma intNatAbs_cast_real (m : Int) :
    ((Int.natAbs m : Nat) : ℝ) = |(m : ℝ)| := by
  cases m with
  | ofNat n =>
      simp [Int.natAbs]
  | negSucc n =>
      have hneg : ((Int.negSucc n : Int) : ℝ) < 0 := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        simp [Int.cast_negSucc]
        linarith
      rw [abs_of_neg hneg]
      simp [Int.natAbs]

lemma round_nan_refines (rnd : RoundingMode) :
    toEReal (round (f := f) .nan rnd) =
      @round_to_precision f (toEReal (Value.nan (f := f))) rnd := by
  simp [round, toEReal, round_to_precision, round_to_precision_real]

lemma round_posInf_refines (rnd : RoundingMode) :
    toEReal (round (f := f) .posInf rnd) =
      @round_to_precision f (toEReal (Value.posInf (f := f))) rnd := by
  simp [round, toEReal, round_to_precision]

lemma round_negInf_refines (rnd : RoundingMode) :
    toEReal (round (f := f) .negInf rnd) =
      @round_to_precision f (toEReal (Value.negInf (f := f))) rnd := by
  simp [round, toEReal, round_to_precision]

lemma round_zero_refines (e : Int) (rnd : RoundingMode) :
    toEReal (round (f := f) (.finite 0 e) rnd) =
      @round_to_precision f (toEReal (Value.finite (f := f) 0 e)) rnd := by
  simp [round, roundFinite, toEReal, round_to_precision, round_to_precision_real]

lemma round_finite_nonzero_refines (m e : Int) (rnd : RoundingMode) (hm : m ≠ 0) :
    toEReal (round (f := f) (.finite m e) rnd) =
      @round_to_precision f (toEReal (Value.finite (f := f) m e)) rnd := by
  let x : ℝ := (m : ℝ) * (2 : ℝ) ^ e
  let am : Nat := Int.natAbs m
  let logAbs : Int := Int.ofNat (Nat.log2 am) + e
  let E : Int := max logAbs (1 - f.bias) - f.P + 1
  let shift : Int := e - E
  let pow : Nat :=
    if _ : 0 ≤ shift then
      2 ^ Int.toNat shift
    else
      2 ^ Int.toNat (-shift)
  let q : Nat := if _ : 0 ≤ shift then Int.natAbs m * pow else am / pow
  let r : Nat := if _ : 0 ≤ shift then 0 else am % pow
  let d : Nat := if _ : 0 ≤ shift then 1 else pow
  let S : ℝ := |x| * (2 : ℝ) ^ (-E)
  let Δ : ℝ := Int.fract S
  let RNITE (X : ℝ) : Int :=
    if Int.fract X < (2⁻¹ : ℝ) ∨ (Int.fract X = (2⁻¹ : ℝ) ∧ Even ⌊X⌋) then
      ⌊X⌋
    else
      ⌊X⌋ + 1
  have hx : x ≠ 0 := by
    dsimp [x]
    apply mul_ne_zero
    · exact_mod_cast hm
    · exact ne_of_gt (by positivity)
  have hE :
      E = max (Int.log 2 |x|) (1 - f.bias) - f.P + 1 := by
    dsimp [E, logAbs, am, x]
    congr 1
    have hpow_pos : 0 < (2 : ℝ) ^ e := by positivity
    have hlog_mul :
        Int.log 2 (|(m : ℝ)| * (2 : ℝ) ^ e) =
          Int.log 2 |(m : ℝ)| + e := by
      simpa [abs_mul, abs_of_pos hpow_pos] using
        (log_mul' (m := (m : ℝ)) e (by exact_mod_cast hm))
    have hlog_abs :
        Int.log 2 |((m : ℝ) * (2 : ℝ) ^ e)| =
          Int.log 2 |(m : ℝ)| + e := by
      simpa [abs_mul, abs_of_pos hpow_pos] using hlog_mul
    rw [hlog_abs]
    have hNatLog :
        (Nat.log2 (Int.natAbs m) : Int) = Int.log 2 |(m : ℝ)| := by
      rw [Nat.log2_eq_log_two]
      have hdigitsNat := digits_abs (m := m)
      have hdigitsReal := digits_abs' (m := m)
      have hnatAbs : |m|.toNat = Int.natAbs m := by
        cases m with
        | ofNat n =>
            simp [Int.natAbs]
        | negSucc n =>
            rw [abs_of_neg (by simp)]
            simp [Int.natAbs]
      rw [hnatAbs] at hdigitsNat
      omega
    rw [hNatLog]
  have hScaled :
      (⌊S⌋ : Int) = (q : Int) ∧ Int.fract S = (r : ℝ) / (d : ℝ) := by
    have hAbsM : |(m : ℝ)| = (Int.natAbs m : ℝ) := by
      cases m with
      | ofNat n =>
          simp [Int.natAbs]
      | negSucc n =>
          rw [abs_of_neg (by
            have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
            norm_num
            linarith)]
          simp [Int.natAbs]
    have hS_general : S = (am : ℝ) * (2 : ℝ) ^ shift := by
      dsimp [S, x, am, shift]
      calc
        |(m : ℝ) * (2 : ℝ) ^ e| * (2 : ℝ) ^ (-E)
            = ((Int.natAbs m : ℝ) * (2 : ℝ) ^ e) * (2 : ℝ) ^ (-E) := by
                have hpowAbs : |(2 : ℝ) ^ e| = (2 : ℝ) ^ e := by
                  exact abs_of_pos (by positivity)
                rw [abs_mul, hpowAbs, hAbsM]
        _ = (Int.natAbs m : ℝ) * ((2 : ℝ) ^ e * (2 : ℝ) ^ (-E)) := by ring
        _ = (Int.natAbs m : ℝ) * (2 : ℝ) ^ (e + -E) := by
              rw [zpow_add₀] <;> norm_num
        _ = (Int.natAbs m : ℝ) * (2 : ℝ) ^ (e - E) := by simp [sub_eq_add_neg]
    by_cases hs : 0 ≤ shift
    · have hPow : (pow : ℝ) = (2 : ℝ) ^ shift := by
        dsimp [pow]
        rw [if_pos hs]
        rw [Nat.cast_pow]
        norm_num
        rw [← zpow_natCast]
        rw [Int.toNat_of_nonneg hs]
      have hSq : S = (q : ℝ) := by
        calc
          S = (am : ℝ) * (2 : ℝ) ^ shift := hS_general
          _ = (am : ℝ) * (pow : ℝ) := by rw [hPow]
          _ = ((am * pow : Nat) : ℝ) := by norm_cast
          _ = (q : ℝ) := by simp [q, hs, am]
      constructor
      · rw [hSq]
        exact Int.floor_natCast q
      · rw [hSq]
        simp [Int.fract, r, d, hs]
    · -- First revision target: Euclidean division of `Int.natAbs m` by
      -- `2 ^ Int.toNat (E - e)` gives the semantic floor and fraction.
      have hlt : shift < 0 := lt_of_not_ge hs
      have hneg_nonneg : 0 ≤ -shift := by omega
      have hPow : (pow : ℝ) = (2 : ℝ) ^ (-shift) := by
        dsimp [pow]
        rw [if_neg hs]
        rw [Nat.cast_pow]
        norm_num
        rw [← zpow_natCast]
        rw [Int.toNat_of_nonneg hneg_nonneg]
        rw [zpow_neg]
      have hShiftPow : (2 : ℝ) ^ shift = ((2 : ℝ) ^ (-shift))⁻¹ := by
        simpa [neg_neg] using (zpow_neg (a := (2 : ℝ)) (n := -shift))
      have hSdiv : S = (am : ℝ) / (pow : ℝ) := by
        calc
          S = (am : ℝ) * (2 : ℝ) ^ shift := hS_general
          _ = (am : ℝ) * ((2 : ℝ) ^ (-shift))⁻¹ := by rw [hShiftPow]
          _ = (am : ℝ) * (pow : ℝ)⁻¹ := by rw [hPow]
          _ = (am : ℝ) / (pow : ℝ) := by rw [div_eq_mul_inv]
      have hFloorNat :
          Nat.floor ((am : ℝ) / (pow : ℝ)) = am / pow := by
        simpa using (Nat.floor_div_eq_div (K := ℝ) am pow)
      have hFloorDiv :
          (⌊(am : ℝ) / (pow : ℝ)⌋ : Int) = (am / pow : Nat) := by
        have hnonneg : 0 ≤ (am : ℝ) / (pow : ℝ) := by positivity
        have hfloor_nonneg : 0 ≤ (⌊(am : ℝ) / (pow : ℝ)⌋ : Int) :=
          Int.floor_nonneg.mpr hnonneg
        have htoNat :
            (⌊(am : ℝ) / (pow : ℝ)⌋ : Int).toNat = am / pow := by
          simpa [Int.floor_toNat] using hFloorNat
        calc
          (⌊(am : ℝ) / (pow : ℝ)⌋ : Int)
              = ((⌊(am : ℝ) / (pow : ℝ)⌋ : Int).toNat : Int) := by
                  exact (Int.toNat_of_nonneg hfloor_nonneg).symm
          _ = (am / pow : Nat) := by exact_mod_cast htoNat
      have hFractDiv :
          Int.fract ((am : ℝ) / (pow : ℝ)) =
            ((am % pow : Nat) : ℝ) / (pow : ℝ) := by
        simpa using
          (Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := am) (n := pow))
      constructor
      · rw [hSdiv, hFloorDiv]
        simp [q, hs, am]
      · rw [hSdiv, hFractDiv]
        simp [r, d, hs, am]
  classical
  let semAway : Bool :=
    match rnd with
    | .RD => decide (Δ > 0 ∧ x < 0)
    | .RU => decide (Δ > 0 ∧ x > 0)
    | .RZ => false
    | .RNE =>
        decide
          (Δ > (2⁻¹ : ℝ) ∨
            (Δ = (2⁻¹ : ℝ) ∧
              if f.P > 1 then
                Even ((⌊S⌋ : Int) + 1)
              else
                Even (E + f.bias + 1) ∧ ¬ (⌊S⌋ : Int) = 0))
    | .RNA => decide (Δ ≥ (2⁻¹ : ℝ))
    | .RTO =>
        decide
          (0 < Δ ∧
            (if 1 < f.P then
              Even (⌊S⌋ : Int)
            else
              (⌊S⌋ : Int) = 0 ∨ Even (E + f.bias)))
    | .StochasticA N R _ =>
        decide (⌊Δ * (2 ^ N : ℝ)⌋ + (R : Int) ≥ (2 ^ N : Int))
    | .StochasticB N R _ =>
        decide
          (⌊Δ * (2 ^ (N + 1) : ℝ)⌋ + (2 * (R : Int) + 1) ≥
            (2 ^ (N + 1) : Int))
    | .StochasticC N R _ =>
        decide (RNITE (Δ * (2 ^ N : ℝ)) + (R : Int) ≥ (2 ^ N : Int))
  let semAwayProp : Prop :=
    match rnd with
    | .RD => Δ > 0 ∧ x < 0
    | .RU => Δ > 0 ∧ x > 0
    | .RZ => False
    | .RNE =>
        Δ > (2⁻¹ : ℝ) ∨
          (Δ = (2⁻¹ : ℝ) ∧
            if f.P > 1 then
              Even ((⌊S⌋ : Int) + 1)
            else
              Even (E + f.bias + 1) ∧ ¬ (⌊S⌋ : Int) = 0)
    | .RNA => Δ ≥ (2⁻¹ : ℝ)
    | .RTO =>
        0 < Δ ∧
          (if 1 < f.P then
            Even (⌊S⌋ : Int)
          else
            (⌊S⌋ : Int) = 0 ∨ Even (E + f.bias))
    | .StochasticA N R _ =>
        ⌊Δ * (2 ^ N : ℝ)⌋ + (R : Int) ≥ (2 ^ N : Int)
    | .StochasticB N R _ =>
        ⌊Δ * (2 ^ (N + 1) : ℝ)⌋ + (2 * (R : Int) + 1) ≥
          (2 ^ (N + 1) : Int)
    | .StochasticC N R _ =>
        RNITE (Δ * (2 ^ N : ℝ)) + (R : Int) ≥ (2 ^ N : Int)
  have hSemAwayBool : semAway = decide semAwayProp := by
    cases rnd <;> simp [semAway, semAwayProp]
  have hd_pos : 0 < d := by
    by_cases hs : 0 ≤ shift
    · simp [d, hs]
    · simpa [d, pow, hs] using
        (pow_pos (by decide : 0 < 2) (Int.toNat (-shift)))
  have hDelta : Δ = (r : ℝ) / (d : ℝ) := by
    simpa [Δ] using hScaled.2
  have hDelta_pos_iff : 0 < Δ ↔ r ≠ 0 := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    rw [hDelta]
    constructor
    · intro h
      intro hr
      simp [hr] at h
    · intro hr
      exact div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hr)) hdR
  have hx_neg_iff : x < 0 ↔ m < 0 := by
    have hpow_pos : 0 < (2 : ℝ) ^ e := by positivity
    dsimp [x]
    constructor
    · intro h
      have hmR : (m : ℝ) < 0 := by
        rcases (mul_neg_iff.mp h) with hmul | hmul
        · linarith
        · exact hmul.1
      exact_mod_cast hmR
    · intro h
      exact mul_neg_of_neg_of_pos (by exact_mod_cast h) hpow_pos
  have hx_pos_iff : 0 < x ↔ 0 < m := by
    have hpow_pos : 0 < (2 : ℝ) ^ e := by positivity
    dsimp [x]
    constructor
    · intro h
      have hmR : 0 < (m : ℝ) := (mul_pos_iff_of_pos_right hpow_pos).mp h
      exact_mod_cast hmR
    · intro h
      exact mul_pos (by exact_mod_cast h) hpow_pos
  have hDelta_ge_half_iff : 2 * r ≥ d ↔ Δ ≥ (2⁻¹ : ℝ) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    rw [hDelta]
    constructor
    · intro h
      have hreal : (d : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast h
      rw [zpow_neg_one_eq_inv_two]
      rw [ge_iff_le, le_div_iff₀ hdR]
      nlinarith
    · intro h
      rw [zpow_neg_one_eq_inv_two] at h
      rw [ge_iff_le, le_div_iff₀ hdR] at h
      have hreal : (d : ℝ) ≤ 2 * (r : ℝ) := by nlinarith
      exact_mod_cast hreal
  have hDelta_gt_half_iff : 2 * r > d ↔ Δ > (2⁻¹ : ℝ) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    rw [hDelta]
    constructor
    · intro h
      have hreal : (d : ℝ) < 2 * (r : ℝ) := by exact_mod_cast h
      rw [zpow_neg_one_eq_inv_two]
      rw [gt_iff_lt, lt_div_iff₀ hdR]
      nlinarith
    · intro h
      rw [zpow_neg_one_eq_inv_two] at h
      rw [gt_iff_lt, lt_div_iff₀ hdR] at h
      have hreal : (d : ℝ) < 2 * (r : ℝ) := by nlinarith
      exact_mod_cast hreal
  have hDelta_eq_half_iff : 2 * r = d ↔ Δ = (2⁻¹ : ℝ) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    rw [hDelta]
    constructor
    · intro h
      have hreal : 2 * (r : ℝ) = (d : ℝ) := by exact_mod_cast h
      rw [zpow_neg_one_eq_inv_two]
      field_simp [hdR.ne']
      nlinarith
    · intro h
      rw [zpow_neg_one_eq_inv_two] at h
      field_simp [hdR.ne'] at h
      have hreal : 2 * (r : ℝ) = (d : ℝ) := by nlinarith
      exact_mod_cast hreal
  have hq_zero_iff : q = 0 ↔ (⌊S⌋ : Int) = 0 := by
    rw [hScaled.1]
    constructor <;> intro h <;> exact_mod_cast h
  have hq_ne_zero_iff : q ≠ 0 ↔ ¬(⌊S⌋ : Int) = 0 := by
    constructor
    · intro h hfloor
      apply h
      exact hq_zero_iff.mpr hfloor
    · intro h hq
      apply h
      exact hq_zero_iff.mp hq
  have hScaledMulDiv (N : Nat) :
      Δ * (2 ^ N : ℝ) = (((r * 2 ^ N : Nat) : ℝ) / (d : ℝ)) := by
    calc
      Δ * (2 ^ N : ℝ)
          = ((r : ℝ) / (d : ℝ)) * (2 ^ N : ℝ) := by rw [hDelta]
      _ = ((r : ℝ) * (2 ^ N : ℝ)) / (d : ℝ) := by ring
      _ = (((r * 2 ^ N : Nat) : ℝ) / (d : ℝ)) := by norm_cast
  have hScaledFloor (N : Nat) :
      (⌊Δ * (2 ^ N : ℝ)⌋ : Int) = ((r * 2 ^ N) / d : Nat) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    have hFloorNat :
        Nat.floor (Δ * (2 ^ N : ℝ)) = (r * 2 ^ N) / d := by
      rw [hScaledMulDiv N]
      simpa using (Nat.floor_div_eq_div (K := ℝ) (r * 2 ^ N) d)
    have hnonneg : 0 ≤ Δ * (2 ^ N : ℝ) := by
      rw [hScaledMulDiv N]
      positivity
    have hfloor_nonneg : 0 ≤ (⌊Δ * (2 ^ N : ℝ)⌋ : Int) :=
      Int.floor_nonneg.mpr hnonneg
    have htoNat :
        (⌊Δ * (2 ^ N : ℝ)⌋ : Int).toNat = (r * 2 ^ N) / d := by
      simpa [Int.floor_toNat] using hFloorNat
    calc
      (⌊Δ * (2 ^ N : ℝ)⌋ : Int)
          = ((⌊Δ * (2 ^ N : ℝ)⌋ : Int).toNat : Int) := by
              exact (Int.toNat_of_nonneg hfloor_nonneg).symm
      _ = ((r * 2 ^ N) / d : Nat) := by exact_mod_cast htoNat
  have hScaledFract (N : Nat) :
      Int.fract (Δ * (2 ^ N : ℝ)) =
        (((r * 2 ^ N) % d : Nat) : ℝ) / (d : ℝ) := by
    rw [hScaledMulDiv N]
    simpa using
      (Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := r * 2 ^ N) (n := d))
  have hRoundAway : roundAwayInt f q r d E m rnd = semAway := by
    cases rnd with
    | RD =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        have hProp : (m < 0 ∧ r ≠ 0) ↔ (0 < Δ ∧ x < 0) := by
          constructor
          · intro h
            exact ⟨hDelta_pos_iff.mpr h.2, hx_neg_iff.mpr h.1⟩
          · intro h
            exact ⟨hx_neg_iff.mp h.2, hDelta_pos_iff.mp h.1⟩
        simpa [hProp]
    | RU =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        have hProp : (0 < m ∧ r ≠ 0) ↔ (0 < Δ ∧ 0 < x) := by
          constructor
          · intro h
            exact ⟨hDelta_pos_iff.mpr h.2, hx_pos_iff.mpr h.1⟩
          · intro h
            exact ⟨hx_pos_iff.mp h.2, hDelta_pos_iff.mp h.1⟩
        simpa [hProp]
    | RZ =>
        rfl
    | RNE =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        simpa [hDelta_gt_half_iff, hDelta_eq_half_iff, hScaled.1]
    | RNA =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        simpa [hDelta_ge_half_iff]
    | RTO =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        simpa [hDelta_pos_iff, hScaled.1]
    | StochasticA N R h =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        have hProp :
            ((r * 2 ^ N) / d + R ≥ 2 ^ N) ↔
              ((⌊Δ * (2 ^ N : ℝ)⌋ : Int) + (R : Int) ≥ (2 ^ N : Int)) := by
          rw [hScaledFloor N]
          constructor <;> intro hineq <;> exact_mod_cast hineq
        simpa [hProp]
    | StochasticB N R h =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        have hProp :
            ((r * 2 ^ (N + 1)) / d + 2 * R + 1 ≥ 2 ^ (N + 1)) ↔
              ((⌊Δ * (2 ^ (N + 1) : ℝ)⌋ : Int) + (2 * (R : Int) + 1) ≥
                (2 ^ (N + 1) : Int)) := by
          rw [hScaledFloor (N + 1)]
          constructor <;> intro hineq <;> exact_mod_cast hineq
        simpa [hProp]
    | StochasticC N R h =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        let scaled : Nat := r * 2 ^ N
        let qN : Nat := scaled / d
        let remN : Nat := scaled % d
        have hFloorN :
            (⌊Δ * (2 ^ N : ℝ)⌋ : Int) = (qN : Nat) := by
          simpa [scaled, qN] using hScaledFloor N
        have hFractN :
            Int.fract (Δ * (2 ^ N : ℝ)) =
              ((remN : Nat) : ℝ) / (d : ℝ) := by
          simpa [scaled, remN] using hScaledFract N
        have hRem_lt_half :
            2 * remN < d ↔ Int.fract (Δ * (2 ^ N : ℝ)) < (2⁻¹ : ℝ) := by
          have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
          rw [hFractN]
          constructor
          · intro hlt
            have hreal : 2 * (remN : ℝ) < (d : ℝ) := by exact_mod_cast hlt
            rw [zpow_neg_one_eq_inv_two]
            rw [div_lt_iff₀ hdR]
            nlinarith
          · intro hlt
            rw [zpow_neg_one_eq_inv_two] at hlt
            rw [div_lt_iff₀ hdR] at hlt
            have hreal : 2 * (remN : ℝ) < (d : ℝ) := by nlinarith
            exact_mod_cast hreal
        have hRem_eq_half :
            2 * remN = d ↔ Int.fract (Δ * (2 ^ N : ℝ)) = (2⁻¹ : ℝ) := by
          have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
          rw [hFractN]
          constructor
          · intro heq
            have hreal : 2 * (remN : ℝ) = (d : ℝ) := by exact_mod_cast heq
            rw [zpow_neg_one_eq_inv_two]
            field_simp [hdR.ne']
            nlinarith
          · intro heq
            rw [zpow_neg_one_eq_inv_two] at heq
            field_simp [hdR.ne'] at heq
            have hreal : 2 * (remN : ℝ) = (d : ℝ) := by nlinarith
            exact_mod_cast hreal
        have hRNITE :
            ((if 2 * remN < d ∨ (2 * remN = d ∧ Even qN)
              then qN else qN + 1 : Nat) : Int) =
                RNITE (Δ * (2 ^ N : ℝ)) := by
          dsimp [RNITE]
          have hCondIff :
              (2 * remN < d ∨ (2 * remN = d ∧ Even qN)) ↔
                (Int.fract (Δ * (2 ^ N : ℝ)) < (2⁻¹ : ℝ) ∨
                  Int.fract (Δ * (2 ^ N : ℝ)) = (2⁻¹ : ℝ) ∧
                    Even (⌊Δ * (2 ^ N : ℝ)⌋ : Int)) := by
            constructor
            · intro hcond
              rcases hcond with hlt | ⟨heq, heven⟩
              · exact Or.inl (hRem_lt_half.mp hlt)
              · right
                constructor
                · exact hRem_eq_half.mp heq
                · have hevenInt : Even (qN : Int) := by exact_mod_cast heven
                  simpa [hFloorN] using hevenInt
            · intro hcond
              rcases hcond with hlt | ⟨heq, heven⟩
              · exact Or.inl (hRem_lt_half.mpr hlt)
              · right
                constructor
                · exact hRem_eq_half.mpr heq
                · have hevenInt : Even (qN : Int) := by
                    simpa [hFloorN] using heven
                  exact_mod_cast hevenInt
          by_cases hsem :
              Int.fract (Δ * (2 ^ N : ℝ)) < (2⁻¹ : ℝ) ∨
                Int.fract (Δ * (2 ^ N : ℝ)) = (2⁻¹ : ℝ) ∧
                  Even (⌊Δ * (2 ^ N : ℝ)⌋ : Int)
          · have hcond := hCondIff.mpr hsem
            rw [if_pos hcond, if_pos hsem]
            exact hFloorN.symm
          · have hcond :
                ¬(2 * remN < d ∨ (2 * remN = d ∧ Even qN)) := by
              intro hcond
              exact hsem (hCondIff.mp hcond)
            rw [if_neg hcond, if_neg hsem]
            rw [hFloorN]
            norm_cast
        have hProp :
            ((if 2 * remN < d ∨ (2 * remN = d ∧ Even qN)
              then qN else qN + 1) + R ≥ 2 ^ N) ↔
                (RNITE (Δ * (2 ^ N : ℝ)) + (R : Int) ≥ (2 ^ N : Int)) := by
          rw [← hRNITE]
          constructor <;> intro hineq <;> exact_mod_cast hineq
        simpa [scaled, qN, remN, hProp]
  let qInt : Int := q
  let qplus : Int := if roundAwayInt f q r d E m rnd then qInt + 1 else qInt
  let sign : Int := if m < 0 then -1 else 1
  let rounded : Int := sign * qplus
  have hSignReal : x.sign = (sign : ℝ) := by
    by_cases hmneg : m < 0
    · have hxneg : x < 0 := hx_neg_iff.mpr hmneg
      rw [Real.sign_of_neg hxneg]
      simp [sign, hmneg]
    · have hmpos : 0 < m := by
        have hmnonneg : 0 ≤ m := le_of_not_gt hmneg
        exact lt_of_le_of_ne hmnonneg (Ne.symm hm)
      have hxpos : 0 < x := hx_pos_iff.mpr hmpos
      rw [Real.sign_of_pos hxpos]
      simp [sign, hmneg]
  have hQplusSem : qplus = (⌊S⌋ : Int) + if semAway then 1 else 0 := by
    dsimp [qplus, qInt]
    rw [hRoundAway, hScaled.1]
    cases semAway <;> simp
  have hRoundedSem :
      (rounded : ℝ) =
        x.sign * (((⌊S⌋ : Int) + if semAway then 1 else 0 : Int) : ℝ) := by
    dsimp [rounded]
    rw [hQplusSem]
    rw [Int.cast_mul]
    rw [← hSignReal]
  have hSemAwayIte :
      (if semAwayProp then (1 : Int) else 0) = if semAway then 1 else 0 := by
    by_cases hp : semAwayProp
    · have hb : semAway = true := by
        simp [hSemAwayBool, hp]
      simp [hp, hb]
    · have hb : semAway = false := by
        simp [hSemAwayBool, hp]
      simp [hp, hb]
  have hSemAwayNorm :
      normalizedRoundAway f x S Δ E RNITE rnd ↔ semAwayProp := by
    cases rnd <;>
      simp [normalizedRoundAway, semAwayProp, gt_iff_lt, even_add_one,
        Int.floor_eq_zero_iff, Set.mem_Ico, not_and, not_lt, ge_iff_le]
    omega
  have hSemAwayNormIte :
      (if normalizedRoundAway f x S Δ E RNITE rnd then (1 : Int) else 0) =
        if semAway then 1 else 0 := by
    calc
      (if normalizedRoundAway f x S Δ E RNITE rnd then (1 : Int) else 0)
          = if semAwayProp then 1 else 0 := by
              by_cases hp : semAwayProp
              · have hn : normalizedRoundAway f x S Δ E RNITE rnd :=
                  hSemAwayNorm.mpr hp
                simp [hp, hn]
              · have hn : ¬ normalizedRoundAway f x S Δ E RNITE rnd :=
                  fun hn => hp (hSemAwayNorm.mp hn)
                simp [hp, hn]
      _ = if semAway then 1 else 0 := hSemAwayIte
  have hSemanticShape :
      (@round_to_precision_real f x rnd : EReal) =
        (((rounded : ℝ) * (2 : ℝ) ^ E : ℝ) : EReal) := by
    have hReal :
        @round_to_precision_real f x rnd =
          (rounded : ℝ) * (2 : ℝ) ^ E := by
      have hIncReal :
          (if normalizedRoundAway f x S Δ E RNITE rnd then (1 : ℝ) else 0) =
            if semAway then (1 : ℝ) else 0 := by
        exact_mod_cast hSemAwayNormIte
      have hRoundedSemExpanded :
          (rounded : ℝ) =
            x.sign * (((⌊S⌋ : Int) : ℝ) + if semAway then (1 : ℝ) else 0) := by
        simpa [Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero] using
          hRoundedSem
      simp only [round_to_precision_real, hx, ↓reduceIte, gt_iff_lt,
        even_add_one, Int.floor_eq_zero_iff, Set.mem_Ico, not_and, not_lt,
        ge_iff_le, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
        ← hE]
      change
        x.sign *
            (((⌊S⌋ : Int) : ℝ) +
              if normalizedRoundAway f x S Δ E RNITE rnd then (1 : ℝ) else 0) *
              (2 : ℝ) ^ E =
          (rounded : ℝ) * (2 : ℝ) ^ E
      rw [hIncReal, ← hRoundedSemExpanded]
    exact congrArg (fun y : ℝ => (y : EReal)) hReal
  have hRoundFinite :
      toEReal (roundFinite f m e rnd) =
        (@round_to_precision_real f x rnd : EReal) := by
    have hExecShape :
        toEReal (roundFinite f m e rnd) =
          (((rounded : ℝ) * (2 : ℝ) ^ E : ℝ) : EReal) := by
      let c := roundFiniteCore f m e rnd
      have hcE : c.E = E := by
        simp [c, roundFiniteCore, absNat, am, logAbs, E]
      have hcRounded : c.rounded = rounded := by
        simp [c, roundFiniteCore, absNat, am, logAbs, E, shift, pow, q, r, d,
          qInt, qplus, sign, rounded]
      have hcarry_value :
          Int.natAbs rounded = vnumPow f →
            (((rounded / 2 : Int) : ℝ) * (2 : ℝ) ^ (E + 1) : ℝ) =
              (rounded : ℝ) * (2 : ℝ) ^ E := by
        intro hcarry
        have htwo_dvd_rounded : (2 : Int) ∣ rounded := by
          exact Int.natCast_dvd.mpr (by
            rw [hcarry, vnumPow]
            exact dvd_pow_self 2 f.h_P.1.ne')
        have hhalf : (rounded / 2 : Int) * 2 = rounded := by
          exact Int.ediv_mul_cancel htwo_dvd_rounded
        calc
          ((rounded / 2 : Int) : ℝ) * (2 : ℝ) ^ (E + 1)
              = ((rounded / 2 : Int) : ℝ) * ((2 : ℝ) ^ E * (2 : ℝ)) := by
                  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
          _ = (((rounded / 2 : Int) * 2 : Int) : ℝ) * (2 : ℝ) ^ E := by
                  rw [Int.cast_mul]
                  ring
          _ = (rounded : ℝ) * (2 : ℝ) ^ E := by
                  rw [hhalf]
      unfold roundFinite
      rw [if_neg hm]
      change
        toEReal
            (if Int.natAbs c.rounded = vnumPow f then
              Value.finite (f := f) (c.rounded / 2) (c.E + 1)
            else
              Value.finite (f := f) c.rounded c.E) =
          (((rounded : ℝ) * (2 : ℝ) ^ E : ℝ) : EReal)
      rw [hcRounded, hcE]
      by_cases hcarry : Int.natAbs rounded = vnumPow f
      · rw [if_pos hcarry]
        exact congrArg (fun y : ℝ => (y : EReal)) (hcarry_value hcarry)
      · rw [if_neg hcarry]
        simp [toEReal]
    rw [hExecShape, hSemanticShape]
  simpa [round, toEReal, round_to_precision, x] using hRoundFinite

set_option maxHeartbeats 1000000 in
lemma roundFiniteRat_refines
    (num den : Nat)
    (e : Int)
    (neg : Bool)
    (rnd : RoundingMode)
    (hnum : num ≠ 0)
    (hden : den ≠ 0) :
    toEReal (roundFiniteRat f num den e neg rnd) =
      @round_to_precision f
        (((if neg then
            -(((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ e)
          else
            ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ e) : ℝ) : EReal)
        rnd := by
  let mag : ℝ := ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ e
  let x : ℝ := if neg then -mag else mag
  let logAbs : Int := floorLog2RatShift num den e
  let E : Int := max logAbs (1 - f.bias) - f.P + 1
  let shift : Int := e - E
  let pow : Nat :=
    if _ : 0 ≤ shift then
      2 ^ Int.toNat shift
    else
      2 ^ Int.toNat (-shift)
  let scaledNum : Nat := if _ : 0 ≤ shift then num * pow else num
  let scaledDen : Nat := if _ : 0 ≤ shift then den else den * pow
  let q : Nat := scaledNum / scaledDen
  let r : Nat := scaledNum % scaledDen
  let d : Nat := scaledDen
  let S : ℝ := |x| * (2 : ℝ) ^ (-E)
  let Δ : ℝ := Int.fract S
  let RNITE (X : ℝ) : Int :=
    if Int.fract X < (2⁻¹ : ℝ) ∨ (Int.fract X = (2⁻¹ : ℝ) ∧ Even ⌊X⌋) then
      ⌊X⌋
    else
      ⌊X⌋ + 1
  let sign : Int := if neg then -1 else 1
  have hden_pos_nat : 0 < den := Nat.pos_of_ne_zero hden
  have hnum_pos_nat : 0 < num := Nat.pos_of_ne_zero hnum
  have hdenR : (den : ℝ) ≠ 0 := by exact_mod_cast hden
  have hmag_pos : 0 < mag := by
    dsimp [mag]
    positivity
  have hx : x ≠ 0 := by
    by_cases hn : neg
    · simp [x, hn, hmag_pos.ne']
    · simp [x, hn, hmag_pos.ne']
  have hAbsX : |x| = mag := by
    by_cases hn : neg
    · simp [x, hn, abs_of_pos hmag_pos]
    · simp [x, hn, abs_of_pos hmag_pos]
  have hE :
      E = max (Int.log 2 |x|) (1 - f.bias) - f.P + 1 := by
    dsimp [E, logAbs]
    have hqpos : 0 < (((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ e) := by
      positivity
    have hcast :
        ((((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ e : ℚ) : ℝ) = mag := by
      dsimp [mag]
      norm_num
    have hlog :
        floorLog2RatShift num den e = Int.log 2 |x| := by
      calc
        floorLog2RatShift num den e
            = Int.log 2 (((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ e) := rfl
        _ = Int.log 2 ((((num : ℚ) / (den : ℚ)) * (2 : ℚ) ^ e : ℚ) : ℝ) :=
              (intLog_ratCast hqpos).symm
        _ = Int.log 2 |x| := by rw [hcast, hAbsX]
    rw [hlog]
  have hPow_pos : 0 < pow := by
    by_cases hs : 0 ≤ shift
    · simp [pow, hs]
    · simp [pow, hs]
  have hd_pos : 0 < d := by
    dsimp [d, scaledDen]
    by_cases hs : 0 ≤ shift
    · simpa [hs] using hden_pos_nat
    · have hmul : 0 < den * pow := Nat.mul_pos hden_pos_nat hPow_pos
      simpa [hs] using hmul
  have hScaled :
      (⌊S⌋ : Int) = (q : Int) ∧ Int.fract S = (r : ℝ) / (d : ℝ) := by
    have hS_general : S = ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ shift := by
      dsimp [S, mag, shift]
      rw [hAbsX]
      calc
        (((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ e) * (2 : ℝ) ^ (-E)
            = ((num : ℝ) / (den : ℝ)) *
                ((2 : ℝ) ^ e * (2 : ℝ) ^ (-E)) := by ring
        _ = ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ (e + -E) := by
              rw [zpow_add₀] <;> norm_num
        _ = ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ (e - E) := by
              simp [sub_eq_add_neg]
    have hScaledRatio : S = (scaledNum : ℝ) / (scaledDen : ℝ) := by
      by_cases hs : 0 ≤ shift
      · have hPow : (pow : ℝ) = (2 : ℝ) ^ shift := by
          dsimp [pow]
          rw [if_pos hs]
          rw [Nat.cast_pow]
          norm_num
          rw [← zpow_natCast]
          rw [Int.toNat_of_nonneg hs]
        calc
          S = ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ shift := hS_general
          _ = ((num : ℝ) * (pow : ℝ)) / (den : ℝ) := by
                rw [← hPow]
                field_simp [hdenR]
          _ = (scaledNum : ℝ) / (scaledDen : ℝ) := by
                simp [scaledNum, scaledDen, hs]
      · have hneg_nonneg : 0 ≤ -shift := by omega
        have hPow : (pow : ℝ) = (2 : ℝ) ^ (-shift) := by
          dsimp [pow]
          rw [if_neg hs]
          rw [Nat.cast_pow]
          change (2 : ℝ) ^ Int.toNat (-shift) = (2 : ℝ) ^ (-shift)
          rw [← zpow_natCast (a := (2 : ℝ)) (n := Int.toNat (-shift))]
          rw [Int.toNat_of_nonneg hneg_nonneg]
        have hShiftPow : (2 : ℝ) ^ shift = ((2 : ℝ) ^ (-shift))⁻¹ := by
          simpa [neg_neg] using (zpow_neg (a := (2 : ℝ)) (n := -shift)).symm
        calc
          S = ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ shift := hS_general
          _ = ((num : ℝ) / (den : ℝ)) * ((2 : ℝ) ^ (-shift))⁻¹ := by
                rw [hShiftPow]
          _ = ((num : ℝ) / (den : ℝ)) / (pow : ℝ) := by
                rw [← hPow]
                rfl
          _ = (num : ℝ) / ((den : ℝ) * (pow : ℝ)) := by
                have hPowR : (pow : ℝ) ≠ 0 := by
                  exact_mod_cast (Nat.ne_of_gt hPow_pos)
                field_simp [hdenR, hPowR]
          _ = (scaledNum : ℝ) / (scaledDen : ℝ) := by
                simp [scaledNum, scaledDen, hs]
    have hFloorNat :
        Nat.floor S = scaledNum / scaledDen := by
      rw [hScaledRatio]
      simpa using (Nat.floor_div_eq_div (K := ℝ) scaledNum scaledDen)
    have hnonneg : 0 ≤ S := by
      rw [hScaledRatio]
      positivity
    have hfloor_nonneg : 0 ≤ (⌊S⌋ : Int) :=
      Int.floor_nonneg.mpr hnonneg
    have htoNat :
        (⌊S⌋ : Int).toNat = scaledNum / scaledDen := by
      simpa [Int.floor_toNat] using hFloorNat
    have hFloorDiv :
        (⌊S⌋ : Int) = (scaledNum / scaledDen : Nat) := by
      calc
        (⌊S⌋ : Int)
            = ((⌊S⌋ : Int).toNat : Int) := by
                exact (Int.toNat_of_nonneg hfloor_nonneg).symm
        _ = (scaledNum / scaledDen : Nat) := by exact_mod_cast htoNat
    have hFractDiv :
        Int.fract S =
          ((scaledNum % scaledDen : Nat) : ℝ) / (scaledDen : ℝ) := by
      rw [hScaledRatio]
      simpa using
        (Int.fract_div_natCast_eq_div_natCast_mod
          (k := ℝ) (m := scaledNum) (n := scaledDen))
    constructor
    · simpa [q] using hFloorDiv
    · simpa [r, d] using hFractDiv
  classical
  let semAway : Bool :=
    match rnd with
    | .RD => decide (Δ > 0 ∧ x < 0)
    | .RU => decide (Δ > 0 ∧ x > 0)
    | .RZ => false
    | .RNE =>
        decide
          (Δ > (2⁻¹ : ℝ) ∨
            (Δ = (2⁻¹ : ℝ) ∧
              if f.P > 1 then
                Even ((⌊S⌋ : Int) + 1)
              else
                Even (E + f.bias + 1) ∧ ¬ (⌊S⌋ : Int) = 0))
    | .RNA => decide (Δ ≥ (2⁻¹ : ℝ))
    | .RTO =>
        decide
          (0 < Δ ∧
            (if 1 < f.P then
              Even (⌊S⌋ : Int)
            else
              (⌊S⌋ : Int) = 0 ∨ Even (E + f.bias)))
    | .StochasticA N R _ =>
        decide (⌊Δ * (2 ^ N : ℝ)⌋ + (R : Int) ≥ (2 ^ N : Int))
    | .StochasticB N R _ =>
        decide
          (⌊Δ * (2 ^ (N + 1) : ℝ)⌋ + (2 * (R : Int) + 1) ≥
            (2 ^ (N + 1) : Int))
    | .StochasticC N R _ =>
        decide (RNITE (Δ * (2 ^ N : ℝ)) + (R : Int) ≥ (2 ^ N : Int))
  let semAwayProp : Prop :=
    match rnd with
    | .RD => Δ > 0 ∧ x < 0
    | .RU => Δ > 0 ∧ x > 0
    | .RZ => False
    | .RNE =>
        Δ > (2⁻¹ : ℝ) ∨
          (Δ = (2⁻¹ : ℝ) ∧
            if f.P > 1 then
              Even ((⌊S⌋ : Int) + 1)
            else
              Even (E + f.bias + 1) ∧ ¬ (⌊S⌋ : Int) = 0)
    | .RNA => Δ ≥ (2⁻¹ : ℝ)
    | .RTO =>
        0 < Δ ∧
          (if 1 < f.P then
            Even (⌊S⌋ : Int)
          else
            (⌊S⌋ : Int) = 0 ∨ Even (E + f.bias))
    | .StochasticA N R _ =>
        ⌊Δ * (2 ^ N : ℝ)⌋ + (R : Int) ≥ (2 ^ N : Int)
    | .StochasticB N R _ =>
        ⌊Δ * (2 ^ (N + 1) : ℝ)⌋ + (2 * (R : Int) + 1) ≥
          (2 ^ (N + 1) : Int)
    | .StochasticC N R _ =>
        RNITE (Δ * (2 ^ N : ℝ)) + (R : Int) ≥ (2 ^ N : Int)
  have hSemAwayBool : semAway = decide semAwayProp := by
    cases rnd <;> simp [semAway, semAwayProp]
  have hDelta : Δ = (r : ℝ) / (d : ℝ) := by
    simpa [Δ] using hScaled.2
  have hDelta_pos_iff : 0 < Δ ↔ r ≠ 0 := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    rw [hDelta]
    constructor
    · intro h
      intro hr
      simp [hr] at h
    · intro hr
      exact div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hr)) hdR
  have hx_neg_iff : x < 0 ↔ sign < 0 := by
    by_cases hn : neg
    · have hxneg : x < 0 := by simp [x, hn, hmag_pos]
      simp [sign, hn, hxneg]
    · have hxpos : 0 < x := by simp [x, hn, hmag_pos]
      have hxnot : ¬ x < 0 := not_lt.mpr (le_of_lt hxpos)
      simp [sign, hn, hxnot]
  have hx_pos_iff : 0 < x ↔ 0 < sign := by
    by_cases hn : neg
    · have hxneg : x < 0 := by simp [x, hn, hmag_pos]
      have hxnot : ¬ 0 < x := not_lt.mpr (le_of_lt hxneg)
      simp [sign, hn, hxnot]
    · have hxpos : 0 < x := by simp [x, hn, hmag_pos]
      simp [sign, hn, hxpos]
  have hDelta_ge_half_iff : 2 * r ≥ d ↔ Δ ≥ (2⁻¹ : ℝ) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    rw [hDelta]
    constructor
    · intro h
      have hreal : (d : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast h
      rw [zpow_neg_one_eq_inv_two]
      rw [ge_iff_le, le_div_iff₀ hdR]
      nlinarith
    · intro h
      rw [zpow_neg_one_eq_inv_two] at h
      rw [ge_iff_le, le_div_iff₀ hdR] at h
      have hreal : (d : ℝ) ≤ 2 * (r : ℝ) := by nlinarith
      exact_mod_cast hreal
  have hDelta_gt_half_iff : 2 * r > d ↔ Δ > (2⁻¹ : ℝ) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    rw [hDelta]
    constructor
    · intro h
      have hreal : (d : ℝ) < 2 * (r : ℝ) := by exact_mod_cast h
      rw [zpow_neg_one_eq_inv_two]
      rw [gt_iff_lt, lt_div_iff₀ hdR]
      nlinarith
    · intro h
      rw [zpow_neg_one_eq_inv_two] at h
      rw [gt_iff_lt, lt_div_iff₀ hdR] at h
      have hreal : (d : ℝ) < 2 * (r : ℝ) := by nlinarith
      exact_mod_cast hreal
  have hDelta_eq_half_iff : 2 * r = d ↔ Δ = (2⁻¹ : ℝ) := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    rw [hDelta]
    constructor
    · intro h
      have hreal : 2 * (r : ℝ) = (d : ℝ) := by exact_mod_cast h
      rw [zpow_neg_one_eq_inv_two]
      field_simp [hdR.ne']
      nlinarith
    · intro h
      rw [zpow_neg_one_eq_inv_two] at h
      field_simp [hdR.ne'] at h
      have hreal : 2 * (r : ℝ) = (d : ℝ) := by nlinarith
      exact_mod_cast hreal
  have hq_zero_iff : q = 0 ↔ (⌊S⌋ : Int) = 0 := by
    rw [hScaled.1]
    constructor <;> intro h <;> exact_mod_cast h
  have hq_ne_zero_iff : q ≠ 0 ↔ ¬(⌊S⌋ : Int) = 0 := by
    constructor
    · intro h hfloor
      apply h
      exact hq_zero_iff.mpr hfloor
    · intro h hq
      apply h
      exact hq_zero_iff.mp hq
  have hScaledMulDiv (N : Nat) :
      Δ * (2 ^ N : ℝ) = (((r * 2 ^ N : Nat) : ℝ) / (d : ℝ)) := by
    calc
      Δ * (2 ^ N : ℝ)
          = ((r : ℝ) / (d : ℝ)) * (2 ^ N : ℝ) := by rw [hDelta]
      _ = ((r : ℝ) * (2 ^ N : ℝ)) / (d : ℝ) := by ring
      _ = (((r * 2 ^ N : Nat) : ℝ) / (d : ℝ)) := by norm_cast
  have hScaledFloor (N : Nat) :
      (⌊Δ * (2 ^ N : ℝ)⌋ : Int) = ((r * 2 ^ N) / d : Nat) := by
    have hFloorNat :
        Nat.floor (Δ * (2 ^ N : ℝ)) = (r * 2 ^ N) / d := by
      rw [hScaledMulDiv N]
      simpa using (Nat.floor_div_eq_div (K := ℝ) (r * 2 ^ N) d)
    have hnonneg : 0 ≤ Δ * (2 ^ N : ℝ) := by
      rw [hScaledMulDiv N]
      positivity
    have hfloor_nonneg : 0 ≤ (⌊Δ * (2 ^ N : ℝ)⌋ : Int) :=
      Int.floor_nonneg.mpr hnonneg
    have htoNat :
        (⌊Δ * (2 ^ N : ℝ)⌋ : Int).toNat = (r * 2 ^ N) / d := by
      simpa [Int.floor_toNat] using hFloorNat
    calc
      (⌊Δ * (2 ^ N : ℝ)⌋ : Int)
          = ((⌊Δ * (2 ^ N : ℝ)⌋ : Int).toNat : Int) := by
              exact (Int.toNat_of_nonneg hfloor_nonneg).symm
      _ = ((r * 2 ^ N) / d : Nat) := by exact_mod_cast htoNat
  have hScaledFract (N : Nat) :
      Int.fract (Δ * (2 ^ N : ℝ)) =
        (((r * 2 ^ N) % d : Nat) : ℝ) / (d : ℝ) := by
    rw [hScaledMulDiv N]
    simpa using
      (Int.fract_div_natCast_eq_div_natCast_mod (k := ℝ) (m := r * 2 ^ N) (n := d))
  have hRoundAway : roundAwayInt f q r d E sign rnd = semAway := by
    cases rnd with
    | RD =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        have hProp : (sign < 0 ∧ r ≠ 0) ↔ (0 < Δ ∧ x < 0) := by
          constructor
          · intro h
            exact ⟨hDelta_pos_iff.mpr h.2, hx_neg_iff.mpr h.1⟩
          · intro h
            exact ⟨hx_neg_iff.mp h.2, hDelta_pos_iff.mp h.1⟩
        simpa [hProp]
    | RU =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        have hProp : (0 < sign ∧ r ≠ 0) ↔ (0 < Δ ∧ 0 < x) := by
          constructor
          · intro h
            exact ⟨hDelta_pos_iff.mpr h.2, hx_pos_iff.mpr h.1⟩
          · intro h
            exact ⟨hx_pos_iff.mp h.2, hDelta_pos_iff.mp h.1⟩
        simpa [hProp]
    | RZ =>
        rfl
    | RNE =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        simpa [hDelta_gt_half_iff, hDelta_eq_half_iff, hScaled.1]
    | RNA =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        simpa [hDelta_ge_half_iff]
    | RTO =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        simpa [hDelta_pos_iff, hScaled.1]
    | StochasticA N R h =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        have hProp :
            ((r * 2 ^ N) / d + R ≥ 2 ^ N) ↔
              ((⌊Δ * (2 ^ N : ℝ)⌋ : Int) + (R : Int) ≥ (2 ^ N : Int)) := by
          rw [hScaledFloor N]
          constructor <;> intro hineq <;> exact_mod_cast hineq
        simpa [hProp]
    | StochasticB N R h =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        have hProp :
            ((r * 2 ^ (N + 1)) / d + 2 * R + 1 ≥ 2 ^ (N + 1)) ↔
              ((⌊Δ * (2 ^ (N + 1) : ℝ)⌋ : Int) + (2 * (R : Int) + 1) ≥
                (2 ^ (N + 1) : Int)) := by
          rw [hScaledFloor (N + 1)]
          constructor <;> intro hineq <;> exact_mod_cast hineq
        simpa [hProp]
    | StochasticC N R h =>
        dsimp [roundAwayInt, deterministicRoundAway, Flops.Exec.RoundKernel.roundAway, semAway]
        let scaled : Nat := r * 2 ^ N
        let qN : Nat := scaled / d
        let remN : Nat := scaled % d
        have hFloorN :
            (⌊Δ * (2 ^ N : ℝ)⌋ : Int) = (qN : Nat) := by
          simpa [scaled, qN] using hScaledFloor N
        have hFractN :
            Int.fract (Δ * (2 ^ N : ℝ)) =
              ((remN : Nat) : ℝ) / (d : ℝ) := by
          simpa [scaled, remN] using hScaledFract N
        have hRem_lt_half :
            2 * remN < d ↔ Int.fract (Δ * (2 ^ N : ℝ)) < (2⁻¹ : ℝ) := by
          have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
          rw [hFractN]
          constructor
          · intro hlt
            have hreal : 2 * (remN : ℝ) < (d : ℝ) := by exact_mod_cast hlt
            rw [zpow_neg_one_eq_inv_two]
            rw [div_lt_iff₀ hdR]
            nlinarith
          · intro hlt
            rw [zpow_neg_one_eq_inv_two] at hlt
            rw [div_lt_iff₀ hdR] at hlt
            have hreal : 2 * (remN : ℝ) < (d : ℝ) := by nlinarith
            exact_mod_cast hreal
        have hRem_eq_half :
            2 * remN = d ↔ Int.fract (Δ * (2 ^ N : ℝ)) = (2⁻¹ : ℝ) := by
          have hdR : 0 < (d : ℝ) := by exact_mod_cast hd_pos
          rw [hFractN]
          constructor
          · intro heq
            have hreal : 2 * (remN : ℝ) = (d : ℝ) := by exact_mod_cast heq
            rw [zpow_neg_one_eq_inv_two]
            field_simp [hdR.ne']
            nlinarith
          · intro heq
            rw [zpow_neg_one_eq_inv_two] at heq
            field_simp [hdR.ne'] at heq
            have hreal : 2 * (remN : ℝ) = (d : ℝ) := by nlinarith
            exact_mod_cast hreal
        have hRNITE :
            ((if 2 * remN < d ∨ (2 * remN = d ∧ Even qN)
              then qN else qN + 1 : Nat) : Int) =
                RNITE (Δ * (2 ^ N : ℝ)) := by
          dsimp [RNITE]
          have hCondIff :
              (2 * remN < d ∨ (2 * remN = d ∧ Even qN)) ↔
                (Int.fract (Δ * (2 ^ N : ℝ)) < (2⁻¹ : ℝ) ∨
                  Int.fract (Δ * (2 ^ N : ℝ)) = (2⁻¹ : ℝ) ∧
                    Even (⌊Δ * (2 ^ N : ℝ)⌋ : Int)) := by
            constructor
            · intro hcond
              rcases hcond with hlt | ⟨heq, heven⟩
              · exact Or.inl (hRem_lt_half.mp hlt)
              · right
                constructor
                · exact hRem_eq_half.mp heq
                · have hevenInt : Even (qN : Int) := by exact_mod_cast heven
                  simpa [hFloorN] using hevenInt
            · intro hcond
              rcases hcond with hlt | ⟨heq, heven⟩
              · exact Or.inl (hRem_lt_half.mpr hlt)
              · right
                constructor
                · exact hRem_eq_half.mpr heq
                · have hevenInt : Even (qN : Int) := by
                    simpa [hFloorN] using heven
                  exact_mod_cast hevenInt
          by_cases hsem :
              Int.fract (Δ * (2 ^ N : ℝ)) < (2⁻¹ : ℝ) ∨
                Int.fract (Δ * (2 ^ N : ℝ)) = (2⁻¹ : ℝ) ∧
                  Even (⌊Δ * (2 ^ N : ℝ)⌋ : Int)
          · have hcond := hCondIff.mpr hsem
            rw [if_pos hcond, if_pos hsem]
            exact hFloorN.symm
          · have hcond :
                ¬(2 * remN < d ∨ (2 * remN = d ∧ Even qN)) := by
              intro hcond
              exact hsem (hCondIff.mp hcond)
            rw [if_neg hcond, if_neg hsem]
            rw [hFloorN]
            norm_cast
        have hProp :
            ((if 2 * remN < d ∨ (2 * remN = d ∧ Even qN)
              then qN else qN + 1) + R ≥ 2 ^ N) ↔
                (RNITE (Δ * (2 ^ N : ℝ)) + (R : Int) ≥ (2 ^ N : Int)) := by
          rw [← hRNITE]
          constructor <;> intro hineq <;> exact_mod_cast hineq
        simpa [scaled, qN, remN, hProp]
  let qInt : Int := q
  let qplus : Int := if roundAwayInt f q r d E sign rnd then qInt + 1 else qInt
  let rounded : Int := sign * qplus
  have hSignReal : x.sign = (sign : ℝ) := by
    by_cases hn : neg
    · have hxneg : x < 0 := by simp [x, hn, hmag_pos]
      rw [Real.sign_of_neg hxneg]
      simp [sign, hn]
    · have hxpos : 0 < x := by simp [x, hn, hmag_pos]
      rw [Real.sign_of_pos hxpos]
      simp [sign, hn]
  have hQplusSem : qplus = (⌊S⌋ : Int) + if semAway then 1 else 0 := by
    dsimp [qplus, qInt]
    rw [hRoundAway, hScaled.1]
    cases semAway <;> simp
  have hRoundedSem :
      (rounded : ℝ) =
        x.sign * (((⌊S⌋ : Int) + if semAway then 1 else 0 : Int) : ℝ) := by
    dsimp [rounded]
    rw [hQplusSem]
    rw [Int.cast_mul]
    rw [← hSignReal]
  have hSemAwayIte :
      (if semAwayProp then (1 : Int) else 0) = if semAway then 1 else 0 := by
    by_cases hp : semAwayProp
    · have hb : semAway = true := by
        simp [hSemAwayBool, hp]
      simp [hp, hb]
    · have hb : semAway = false := by
        simp [hSemAwayBool, hp]
      simp [hp, hb]
  have hSemAwayNorm :
      normalizedRoundAway f x S Δ E RNITE rnd ↔ semAwayProp := by
    cases rnd <;>
      simp [normalizedRoundAway, semAwayProp, gt_iff_lt, even_add_one,
        Int.floor_eq_zero_iff, Set.mem_Ico, not_and, not_lt, ge_iff_le]
    omega
  have hSemAwayNormIte :
      (if normalizedRoundAway f x S Δ E RNITE rnd then (1 : Int) else 0) =
        if semAway then 1 else 0 := by
    calc
      (if normalizedRoundAway f x S Δ E RNITE rnd then (1 : Int) else 0)
          = if semAwayProp then 1 else 0 := by
              by_cases hp : semAwayProp
              · have hn : normalizedRoundAway f x S Δ E RNITE rnd :=
                  hSemAwayNorm.mpr hp
                simp [hp, hn]
              · have hn : ¬ normalizedRoundAway f x S Δ E RNITE rnd :=
                  fun hn => hp (hSemAwayNorm.mp hn)
                simp [hp, hn]
      _ = if semAway then 1 else 0 := hSemAwayIte
  have hSemanticShape :
      (@round_to_precision_real f x rnd : EReal) =
        (((rounded : ℝ) * (2 : ℝ) ^ E : ℝ) : EReal) := by
    have hReal :
        @round_to_precision_real f x rnd =
          (rounded : ℝ) * (2 : ℝ) ^ E := by
      have hIncReal :
          (if normalizedRoundAway f x S Δ E RNITE rnd then (1 : ℝ) else 0) =
            if semAway then (1 : ℝ) else 0 := by
        exact_mod_cast hSemAwayNormIte
      have hRoundedSemExpanded :
          (rounded : ℝ) =
            x.sign * (((⌊S⌋ : Int) : ℝ) + if semAway then (1 : ℝ) else 0) := by
        simpa [Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero] using
          hRoundedSem
      simp only [round_to_precision_real, hx, ↓reduceIte, gt_iff_lt,
        even_add_one, Int.floor_eq_zero_iff, Set.mem_Ico, not_and, not_lt,
        ge_iff_le, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero,
        ← hE]
      change
        x.sign *
            (((⌊S⌋ : Int) : ℝ) +
              if normalizedRoundAway f x S Δ E RNITE rnd then (1 : ℝ) else 0) *
              (2 : ℝ) ^ E =
          (rounded : ℝ) * (2 : ℝ) ^ E
      rw [hIncReal, ← hRoundedSemExpanded]
    exact congrArg (fun y : ℝ => (y : EReal)) hReal
  have hRoundFinite :
      toEReal (roundFiniteRat f num den e neg rnd) =
        (@round_to_precision_real f x rnd : EReal) := by
    have hExecShape :
        toEReal (roundFiniteRat f num den e neg rnd) =
          (((rounded : ℝ) * (2 : ℝ) ^ E : ℝ) : EReal) := by
      let c := roundRatCore f num den e neg rnd
      have hcE : c.E = E := by
        simp [c, roundRatCore, logAbs, E]
      have hcRounded : c.rounded = rounded := by
        simp [c, roundRatCore, logAbs, E, shift, pow, scaledNum, scaledDen,
          q, r, d, qInt, qplus, sign, rounded]
      have hcarry_value :
          Int.natAbs rounded = vnumPow f →
            (((rounded / 2 : Int) : ℝ) * (2 : ℝ) ^ (E + 1) : ℝ) =
              (rounded : ℝ) * (2 : ℝ) ^ E := by
        intro hcarry
        have htwo_dvd_rounded : (2 : Int) ∣ rounded := by
          exact Int.natCast_dvd.mpr (by
            rw [hcarry, vnumPow]
            exact dvd_pow_self 2 f.h_P.1.ne')
        have hhalf : (rounded / 2 : Int) * 2 = rounded := by
          exact Int.ediv_mul_cancel htwo_dvd_rounded
        calc
          ((rounded / 2 : Int) : ℝ) * (2 : ℝ) ^ (E + 1)
              = ((rounded / 2 : Int) : ℝ) * ((2 : ℝ) ^ E * (2 : ℝ)) := by
                  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
          _ = (((rounded / 2 : Int) * 2 : Int) : ℝ) * (2 : ℝ) ^ E := by
                  rw [Int.cast_mul]
                  ring
          _ = (rounded : ℝ) * (2 : ℝ) ^ E := by
                  rw [hhalf]
      unfold roundFiniteRat
      rw [if_neg (by simp [hnum, hden])]
      change
        toEReal
            (if Int.natAbs c.rounded = vnumPow f then
              Value.finite (f := f) (c.rounded / 2) (c.E + 1)
            else
              Value.finite (f := f) c.rounded c.E) =
          (((rounded : ℝ) * (2 : ℝ) ^ E : ℝ) : EReal)
      rw [hcRounded, hcE]
      by_cases hcarry : Int.natAbs rounded = vnumPow f
      · rw [if_pos hcarry]
        exact congrArg (fun y : ℝ => (y : EReal)) (hcarry_value hcarry)
      · rw [if_neg hcarry]
        simp [toEReal]
    rw [hExecShape, hSemanticShape]
  have htarget :
      (((if neg then
          -(((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ e)
        else
          ((num : ℝ) / (den : ℝ)) * (2 : ℝ) ^ e) : ℝ) : EReal) =
        (x : EReal) := by
    rfl
  simpa [round_to_precision, x] using hRoundFinite

lemma round_refines (x : Value f) (rnd : RoundingMode) :
    toEReal (round x rnd) = @round_to_precision f (toEReal x) rnd := by
  cases x with
  | nan =>
      simpa using (round_nan_refines (f := f) rnd)
  | posInf =>
      simpa using (round_posInf_refines (f := f) rnd)
  | negInf =>
      simpa using (round_negInf_refines (f := f) rnd)
  | finite m e =>
      by_cases hm : m = 0
      · subst m
        simpa using (round_zero_refines (f := f) e rnd)
      · exact round_finite_nonzero_refines (f := f) m e rnd hm

end Exec
end p3109_format
