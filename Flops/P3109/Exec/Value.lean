import Flops.P3109.Defs
import Flops.P3109.Exec.Defs
import Flops.P3109.Bijection
import Mathlib.Tactic

namespace p3109_format
namespace Exec

/-!
Executable value domain for the kernel arithmetic layer.
-/
inductive Value (f : p3109_format) where
  | nan
  | posInf
  | negInf
  | finite (signif : ℤ) (exp : ℤ)
  deriving Repr, BEq, DecidableEq

-- Convert from bit-patterns into a normalised integer value representation.
def fromBits (x : Bits f) : Value f :=
  match p3109.n_to_p3109 (f := f) x with
  | .p3109_nan => .nan
  | .p3109_infinity _ false _ => .posInf
  | .p3109_infinity _ true _ => .negInf
  | .p3109_finite m e _ _ => .finite m e

/-- Convert executable value into the closed extended reals (`EReal ⊕ Unit`),
where `Sum.inr ()` represents NaN.  This is the primary semantic bridge for
NaN-faithful statements. -/
noncomputable def toCereal (x : Value f) : EReal ⊕ Unit :=
  match x with
  | .nan => Sum.inr ()
  | .posInf => Sum.inl ⊤
  | .negInf => Sum.inl ⊥
  | .finite signif e => Sum.inl ((signif : ℝ) * (2 ^ e : ℝ))

@[simp] lemma toCereal_nan : toCereal (Value.nan (f := f)) = Sum.inr () := rfl
@[simp] lemma toCereal_posInf : toCereal (Value.posInf (f := f)) = Sum.inl ⊤ := rfl
@[simp] lemma toCereal_negInf : toCereal (Value.negInf (f := f)) = Sum.inl ⊥ := rfl
@[simp] lemma toCereal_finite (m e : ℤ) :
    toCereal (Value.finite (f := f) m e) =
      Sum.inl (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) := rfl

/-- Collapse a closed-extended-real (`EReal ⊕ Unit`) to an `EReal`, mapping
NaN to `0`.  This is only a compatibility projection for older real-valued
refinement lemmas; NaN-faithful statements should use `toCereal` directly. -/
def cerealToEReal (s : EReal ⊕ Unit) : EReal := s.elim id (fun _ => 0)

@[simp] lemma cerealToEReal_inl (e : EReal) : cerealToEReal (Sum.inl e) = e := rfl
@[simp] lemma cerealToEReal_inr (u : Unit) : cerealToEReal (Sum.inr u) = 0 := rfl

/-- Compatibility projection of `toCereal` into `EReal`.
This intentionally collapses NaN to `0`; use `toCereal` for NaN-faithful specs. -/
noncomputable def toEReal (x : Value f) : EReal :=
  cerealToEReal (toCereal x)

@[simp] lemma toEReal_nan : toEReal (Value.nan (f := f)) = 0 := rfl
@[simp] lemma toEReal_posInf : toEReal (Value.posInf (f := f)) = ⊤ := rfl
@[simp] lemma toEReal_negInf : toEReal (Value.negInf (f := f)) = ⊥ := rfl
@[simp] lemma toEReal_finite (m e : ℤ) :
    toEReal (Value.finite (f := f) m e) =
      (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) := rfl

private lemma coe_two_zpow (e : ℤ) :
    (((2 : ℝ) ^ e : ℝ) : EReal) = (2 : EReal) ^ e := by
  cases e with
  | ofNat n =>
      change (((2 : ℝ) ^ (n : ℤ) : ℝ) : EReal) = (2 : EReal) ^ (n : ℤ)
      rw [zpow_natCast, zpow_natCast]
      exact EReal.coe_pow (2 : ℝ) n
  | negSucc n =>
      change (((((2 : ℝ) ^ (n + 1))⁻¹ : ℝ) : EReal)) =
        (((2 : EReal) ^ (n + 1))⁻¹)
      rw [EReal.coe_inv, EReal.coe_pow]
      congr 1

/-- For non-NaN values, `toCereal` is `Sum.inl` of `toEReal`. -/
lemma toCereal_eq_inl_toEReal {x : Value f} (h : x ≠ Value.nan) :
    toCereal x = Sum.inl (toEReal x) := by
  cases x <;> simp_all [toCereal, toEReal, cerealToEReal]

/-- Recover sign from a value where available.
Unsigned formats map non-finite values to `false` by convention. -/
def signBit (x : Value f) : Bool :=
  match x with
  | .nan => false
  | .posInf => false
  | .negInf => true
  | .finite m _ => m < 0

def neg (x : Value f) : Value f :=
  match x with
  | .nan => .nan
  | .posInf => .negInf
  | .negInf => .posInf
  | .finite m e => .finite (-m) e

def addExact (x y : Value f) : Value f :=
  match x, y with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .posInf, .posInf => .posInf
  | .negInf, .negInf => .negInf
  | .posInf, .negInf => .nan
  | .negInf, .posInf => .nan
  | .posInf, _ => .posInf
  | .negInf, _ => .negInf
  | _, .posInf => .posInf
  | _, .negInf => .negInf
  | .finite m1 e1, .finite m2 e2 =>
    if _ : e1 ≤ e2 then
      .finite (m1 + m2 * ((2 : ℤ) ^ Int.toNat (e2 - e1)) ) e1
    else
      .finite (m2 + m1 * ((2 : ℤ) ^ Int.toNat (e1 - e2)) ) e2

def subExact (x y : Value f) : Value f :=
  addExact x (neg y)

def mulExact (x y : Value f) : Value f :=
  match x, y with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .posInf, .posInf => .posInf
  | .negInf, .negInf => .posInf
  | .posInf, .negInf => .negInf
  | .negInf, .posInf => .negInf
  | .posInf, .finite m _ =>
    if m = 0 then .nan else if m < 0 then .negInf else .posInf
  | .negInf, .finite m _ =>
    if m = 0 then .nan else if m < 0 then .posInf else .negInf
  | .finite m _, .posInf =>
    if m = 0 then .nan else if m < 0 then .negInf else .posInf
  | .finite m _, .negInf =>
    if m = 0 then .nan else if m < 0 then .posInf else .negInf
  | .finite m1 e1, .finite m2 e2 =>
    .finite (m1 * m2) (e1 + e2)

lemma toEReal_neg (x : Value f) :
    toEReal (neg x) = - (toEReal x) := by
  cases x <;> simp [neg, toEReal]

lemma toEReal_addExact_finite (f : p3109_format) (m1 m2 : ℤ) (e1 e2 : Int) :
    toEReal (addExact (f := f) (Value.finite (f := f) m1 e1) (Value.finite (f := f) m2 e2)) =
      toEReal (Value.finite (f := f) m1 e1) + toEReal (Value.finite (f := f) m2 e2) := by
  by_cases h : e1 ≤ e2 <;> simp +decide [ h, addExact ];
  · norm_num [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr h)]
    rw [show e2 = e1 + (e2 - e1) by ring, zpow_add₀] <;> norm_num
    have hreal :
        (((m1 : ℝ) + (m2 : ℝ) * ((2 : ℝ) ^ (e2 - e1))) * ((2 : ℝ) ^ e1)) =
          (m1 : ℝ) * ((2 : ℝ) ^ e1) +
            (m2 : ℝ) * (((2 : ℝ) ^ e1) * ((2 : ℝ) ^ (e2 - e1))) := by
      ring_nf
    simpa [EReal.coe_mul, EReal.coe_add, coe_two_zpow] using
      congrArg (fun r : ℝ => (r : EReal)) hreal
  · norm_num [← zpow_natCast,
      Int.toNat_of_nonneg (sub_nonneg.mpr <| le_of_not_ge h)]
    rw [show e1 = e2 + (e1 - e2) by ring, zpow_add₀] <;> norm_num
    have hreal :
        (((m2 : ℝ) + (m1 : ℝ) * ((2 : ℝ) ^ (e1 - e2))) * ((2 : ℝ) ^ e2)) =
          (m1 : ℝ) * (((2 : ℝ) ^ e2) * ((2 : ℝ) ^ (e1 - e2))) +
            (m2 : ℝ) * ((2 : ℝ) ^ e2) := by
      ring_nf
    simpa [EReal.coe_mul, EReal.coe_add, coe_two_zpow] using
      congrArg (fun r : ℝ => (r : EReal)) hreal

lemma toEReal_mulExact_posInf_finite (f : p3109_format) (m : ℤ) (e : Int) :
    toEReal (mulExact (f := f) (Value.posInf (f := f)) (Value.finite (f := f) m e)) =
      toEReal (Value.posInf (f := f)) * toEReal (Value.finite (f := f) m e) := by
  by_cases hm : m = 0
  · simp [mulExact, hm]
  by_cases hmneg : m < 0
  · have hprod :
        (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) < 0 := by
      rw [EReal.coe_neg']
      exact mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (by positivity)
    simp [mulExact, hm, hmneg]
    exact (EReal.top_mul_of_neg hprod).symm
  · have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast lt_of_le_of_ne (le_of_not_gt hmneg) (Ne.symm hm)
    have hprod :
        (0 : EReal) < (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) := by
      rw [EReal.coe_pos]
      exact mul_pos hmpos (by positivity)
    simp [mulExact, hm, hmneg]
    exact (EReal.top_mul_of_pos hprod).symm

lemma toEReal_mulExact_negInf_finite (f : p3109_format) (m : ℤ) (e : Int) :
    toEReal (mulExact (f := f) (Value.negInf (f := f)) (Value.finite (f := f) m e)) =
      toEReal (Value.negInf (f := f)) * toEReal (Value.finite (f := f) m e) := by
  by_cases hm : m = 0
  · simp [mulExact, hm]
  by_cases hmneg : m < 0
  · have hprod :
        (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) < 0 := by
      rw [EReal.coe_neg']
      exact mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (by positivity)
    simp [mulExact, hm, hmneg]
    exact (EReal.bot_mul_of_neg hprod).symm
  · have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast lt_of_le_of_ne (le_of_not_gt hmneg) (Ne.symm hm)
    have hprod :
        (0 : EReal) < (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) := by
      rw [EReal.coe_pos]
      exact mul_pos hmpos (by positivity)
    simp [mulExact, hm, hmneg]
    exact (EReal.bot_mul_of_pos hprod).symm

lemma toEReal_mulExact_finite_posInf (f : p3109_format) (m : ℤ) (e : Int) :
    toEReal (mulExact (f := f) (Value.finite (f := f) m e) (Value.posInf (f := f))) =
      toEReal (Value.finite (f := f) m e) * toEReal (Value.posInf (f := f)) := by
  by_cases hm : m = 0
  · simp [mulExact, hm]
  by_cases hmneg : m < 0
  · have hprod :
        (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) < 0 := by
      rw [EReal.coe_neg']
      exact mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (by positivity)
    simp [mulExact, hm, hmneg]
    exact (EReal.mul_top_of_neg hprod).symm
  · have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast lt_of_le_of_ne (le_of_not_gt hmneg) (Ne.symm hm)
    have hprod :
        (0 : EReal) < (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) := by
      rw [EReal.coe_pos]
      exact mul_pos hmpos (by positivity)
    simp [mulExact, hm, hmneg]
    exact (EReal.mul_top_of_pos hprod).symm

lemma toEReal_mulExact_finite_negInf (f : p3109_format) (m : ℤ) (e : Int) :
    toEReal (mulExact (f := f) (Value.finite (f := f) m e) (Value.negInf (f := f))) =
      toEReal (Value.finite (f := f) m e) * toEReal (Value.negInf (f := f)) := by
  by_cases hm : m = 0
  · simp [mulExact, hm]
  by_cases hmneg : m < 0
  · have hprod :
        (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) < 0 := by
      rw [EReal.coe_neg']
      exact mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (by positivity)
    simp [mulExact, hm, hmneg]
    exact (EReal.mul_bot_of_neg hprod).symm
  · have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast lt_of_le_of_ne (le_of_not_gt hmneg) (Ne.symm hm)
    have hprod :
        (0 : EReal) < (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) := by
      rw [EReal.coe_pos]
      exact mul_pos hmpos (by positivity)
    simp [mulExact, hm, hmneg]
    exact (EReal.mul_bot_of_pos hprod).symm

lemma toEReal_mulExact_finite (f : p3109_format) (m1 m2 : ℤ) (e1 e2 : Int) :
    toEReal (mulExact (f := f) (Value.finite (f := f) m1 e1) (Value.finite (f := f) m2 e2)) =
      toEReal (Value.finite (f := f) m1 e1) * toEReal (Value.finite (f := f) m2 e2) := by
  simp [mulExact, EReal.coe_mul]
  rw [zpow_add₀] <;> norm_num
  norm_cast
  push_cast
  ring_nf

lemma toEReal_fromBits (x : Bits f) :
    toEReal (fromBits (f := f) x) = p3109.to_ereal (p3109.n_to_p3109 (f := f) x) := by
  cases h : p3109.n_to_p3109 (f := f) x with
  | p3109_nan =>
    simp [fromBits, toEReal, h, p3109.to_ereal]
  | p3109_infinity hdom sign hsign =>
    cases sign <;> simp [fromBits, toEReal, h, p3109.to_ereal]
  | p3109_finite m e hm hcanon =>
    simp [fromBits, toEReal, h, p3109.to_ereal]

end Exec
end p3109_format
