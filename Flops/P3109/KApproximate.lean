import Flops.P3109.Defs
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

namespace p3109_format
namespace p3109

/--
A numeric operation `op` on P3109 values.
It takes a list of operands `x` and returns a P3109 value.
This allows for operations with multiple inputs (e.g., addition, multiplication).
-/
def NumericOp {f : p3109_format} : Type :=
  (x : List (p3109 f)) → p3109 f

/--
Counts the number of finite P3109 values between two given values.
This is used to measure the "value steps" for κ-approximate implementations.
-/
noncomputable def ValueSteps {f : p3109_format} (a b : p3109 f) : ℕ :=
  have _ : Decidable (a.is_finite ∧ b.is_finite) := by exact Classical.propDecidable (a.is_finite ∧ b.is_finite)
  if h : a.is_finite ∧ b.is_finite then
    let value_set_finite := {v | ∃ (p : p3109 f), p.is_finite ∧ v = (p : ℝ)};
    let interval := Set.Ico (min (a : ℝ) (b : ℝ)) (max (a : ℝ) (b : ℝ));
    Set.ncard (value_set_finite ∩ interval)
  else
    0

def finite_box (f : p3109_format) : Set (ℤ × ℤ) :=
  (Set.Icc (-2^f.P) (2^f.P)) ×ˢ (Set.Icc f.emin_lsb f.emax_lsb)

instance : Finite (finite_box f) := by
  simp [finite_box]
  apply Set.finite_Icc

def to_finite_box (p : {x : p3109 f // x.is_finite}) : finite_box f :=
  ⟨(p.val.fnum, p.val.exp), by
    simp [finite_box]
    rcases p with ⟨p, hfin⟩; simp
    revert hfin
    rcases p <;> simp [is_finite]
    expose_names; simp [fnum, exp]
    have ⟨hp, hle⟩ := canonical_fp_of_canonical_p3109 _ h |> canonical_bounded
    simp [vnum, to_format] at hp hle
    rw [abs_lt] at hp
    simp [hle]
    constructor; omega
    constructor; omega
    have := canonical_exp_le_emax h
    simp at this; exact this⟩

lemma hinj : Function.Injective (@to_finite_box f) := by
    simp [Function.Injective]
    clear * -
    intro a hfina b hfinb
    simp [to_finite_box]
    intro hmeq heeq
    revert hfina
    rcases a <;> simp [is_finite]
    revert hfinb
    rcases b <;> simp [is_finite]
    simp [fnum, exp] at hmeq heeq
    simp [hmeq, heeq]


lemma value_steps_eq_zero_implies_eq {f : p3109_format} (a b : p3109 f) :
  a.is_finite →
  b.is_finite →
  @ValueSteps f a b = 0 →
  a = b := by
  intro hfa hfb heq
  by_contra hne
  revert hfa hfb
  rcases ha:a with _|_|_ <;> rcases hb:b with _|_|_ <;> simp [is_finite]
  simp [ValueSteps] at heq
  have := heq (by simp [ha, is_finite]) (by simp [hb, is_finite])
  rcases lt_or_ge (a:ℝ) (b:ℝ) with hlt|hle
  rw [min_eq_left (by linarith)] at this
  rw [max_eq_right (by linarith)] at this
  rw [Set.ncard_eq_zero (by
    apply Set.Finite.subset (s := (fun p => p.to_real) '' {p : f.p3109 | p.is_finite})
    apply Set.Finite.image
    apply Finite.of_injective (@to_finite_box f)
    apply hinj
    intro x hx
    obtain ⟨⟨p, hp_fin, rfl⟩, _⟩ := hx
    exact ⟨p, hp_fin, rfl⟩)] at this
  symm at this
  rw [Set.inter_comm, Set.inter_setOf_eq_sep] at this
  suffices (a:ℝ) ∈ (∅:Set ℝ) by simp at this
  rw [this]; simp
  constructor; assumption
  exists a; simp
  simp [ha, is_finite]
  cases lt_or_eq_of_le hle
  rw [max_eq_left (by linarith)] at this
  rw [min_eq_right (by linarith)] at this
  rw [Set.ncard_eq_zero (by
    apply Set.Finite.subset (s := (fun p => p.to_real) '' {p : f.p3109 | p.is_finite})
    apply Set.Finite.image
    apply Finite.of_injective (@to_finite_box f)
    apply hinj
    intro x hx
    obtain ⟨⟨p, hp_fin, rfl⟩, _⟩ := hx
    exact ⟨p, hp_fin, rfl⟩)] at this
  symm at this
  rw [Set.inter_comm, Set.inter_setOf_eq_sep] at this
  suffices (b:ℝ) ∈ (∅:Set ℝ) by simp at this
  rw [this]; simp
  constructor; assumption
  exists b; simp [hb, is_finite]
  apply hne
  expose_names
  simp [ha, hb, to_real] at ⊢ h_2
  have hle : |(b:ℝ)| ≤ |(a:ℝ)| := by
    simp [ha, hb]; simp [to_real, h_2]
  simp [ha, hb, to_real, abs_mul] at hle
  have hexple : e_1 ≤ e := by
    by_contra hlt; simp at hlt
    have : e+1≤e_1:=by omega
    revert hle; simp
    apply lt_of_lt_of_le (b := |(m_1:ℝ)| * |2^(e+1)|)
    rw [zpow_add₀ (by simp)]; simp [abs_mul]; rw [mul_comm _ 2]
    rw [<-lt_div_iff₀ (by simp; apply ne_of_gt; apply zpow_pos; simp), <-mul_div, <-mul_div, div_self (by simp; apply ne_of_gt; apply zpow_pos; simp)]
    simp; norm_cast
    have ⟨hlt, hemin⟩ := canonical_fp_of_canonical_p3109 _ h |> canonical_bounded
    simp [] at hlt
    apply lt_of_lt_of_le hlt
    rcases h_1 with ⟨_, hle, hemax, _⟩|⟨_, heeq, _⟩
    simp [abs_mul, mul_comm] at hle; exact hle
    simp [to_format] at heeq hemin
    exfalso; omega

    refine mul_le_mul (by simp) ?_ (by simp) (by simp)
    rw [abs_of_pos (by apply zpow_pos; simp)]
    rw [abs_of_pos (by apply zpow_pos; simp)]
    simp; exact this
  cases lt_or_eq_of_le hexple
  exfalso
  have heq : |(b:ℝ)| = |(a:ℝ)| := by
    simp [ha, hb]; simp [to_real, h_2]
  simp [ha, hb, to_real] at heq
  revert heq; simp
  apply ne_of_lt
  have : e_1+1≤e:=by omega

  apply lt_of_lt_of_le (b := |(m:ℝ)| * |2^(e_1+1)|)
  rw [zpow_add₀ (by simp)]; simp [abs_mul]; rw [mul_comm _ 2]
  rw [<-lt_div_iff₀ (by simp; apply ne_of_gt; apply zpow_pos; simp), <-mul_div, <-mul_div, div_self (by simp; apply ne_of_gt; apply zpow_pos; simp)]
  simp; norm_cast
  have ⟨hlt, hemin⟩ := canonical_fp_of_canonical_p3109 _ h_1 |> canonical_bounded
  simp [] at hlt
  apply lt_of_lt_of_le hlt
  rcases h with ⟨_, hle, hemax, _⟩|⟨_, heeq, _⟩
  simp [abs_mul, mul_comm] at hle; exact hle
  simp [to_format] at heeq hemin
  exfalso; omega
  simp [abs_mul]
  refine mul_le_mul (by simp) ?_ (by simp) (by simp)
  rw [abs_of_pos (by apply zpow_pos; simp)]
  rw [abs_of_pos (by apply zpow_pos; simp)]
  simp; exact this

  expose_names
  simp [h_3] at ⊢ h_2
  rcases h_2 with heq|hne
  simp [heq]; exfalso
  revert hne; simp
  apply ne_of_gt; apply zpow_pos; simp

/--
A predicate that defines a κ-approximate implementation `approx_op`
for a given exact numeric operation `exact_op`.
-/
def IsKApproximate {f : p3109_format} (κ : ℕ)
  (exact_op approx_op : @NumericOp f) : Prop :=
  ∀ (x : List (p3109 f)),
    -- For non-finite values, the approximate implementation must match the exact one.
    (¬ (exact_op x).is_finite → approx_op x = exact_op x) ∧
    -- For finite values, the number of value steps must be at most κ.
    ((exact_op x).is_finite → (approx_op x).is_finite ∧ @ValueSteps f (approx_op x) (exact_op x) ≤ κ)

lemma op_0_approx {f : p3109_format}
  (exact_op approx_op : @NumericOp f) :
  @IsKApproximate f 0 exact_op approx_op →
  exact_op = approx_op := by
  intro h0
  apply funext
  intro ops
  simp [IsKApproximate] at h0
  have ⟨hnf, hf⟩ := h0 ops
  clear h0
  set ex := exact_op ops with hex
  rcases ex with _|_|_
  simp [is_finite] at hnf; simp [hnf]
  simp [is_finite] at hnf; simp [hnf]
  rewrite (occs := .pos [1]) [is_finite] at hf
  simp at hf
  symm
  apply value_steps_eq_zero_implies_eq
  exact hf.1; simp [is_finite]; exact hf.2

end p3109
end p3109_format
