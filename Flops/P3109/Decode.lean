import Flops.P3109.Defs
import Flops.P3109.Emax
import Flops.P3109.Encode
import Flops.P3109.Bijection

set_option maxHeartbeats 400000

variable {f : p3109_format}

namespace p3109_format
namespace p3109


noncomputable def decode_finite (n : ℕ) : EReal :=
  let T := n % (2^(f.P - 1));
  let E := n / 2^(f.P-1) - f.bias;
  if E = -f.bias
  then T * (2^(1-f.P:ℤ):ℝ) * (2^(E+1):ℝ)
  else (1+T * (2^(1-f.P:ℤ):ℝ)) * (2^E:ℝ)

lemma decode_finite_is_finite (n : ℕ) :
  ⊤ ≠ @decode_finite f n∧ ⊥ ≠ @decode_finite f n := by
  simp [decode_finite]; split;
  norm_cast
  constructor
  apply EReal.top_ne_coe
  apply EReal.bot_ne_coe
  norm_cast
  constructor
  apply EReal.top_ne_coe
  apply EReal.bot_ne_coe

noncomputable def decode (n : Fin (2^f.K)) : EReal ⊕ Unit  :=
  let n := n.val;
  if n = 2^(f.K-1) ∧ f.s = .signed then Sum.inr ()
  else if n = 2^f.K-1 ∧ f.s = .unsigned then Sum.inr ()
  else if n = 2^(f.K-1)-1 ∧ f.s = .signed ∧ f.d = .extended then Sum.inl ⊤
  else if n = 2^f.K-1 ∧ f.s = .signed ∧ f.d = .extended then Sum.inl ⊥
  else if n = 2^f.K-2 ∧ f.s = .unsigned ∧ f.d = .extended then Sum.inl ⊤
  else if 2^(f.K-1) < n ∧ f.s = .signed then Sum.inl (-@decode_finite f (n - 2^(f.K-1)))
  else Sum.inl (@decode_finite f n)

lemma decode_finite_in_value_set (n : ℕ) (hlt : n < 2^f.K) :
  ¬(n = 2^(f.K-1) ∧ f.s = .signed) →
  ¬(n = 2^f.K-1 ∧ f.s = .unsigned) →
  ¬(n = 2^(f.K-1)-1 ∧ f.s = .signed ∧ f.d = .extended) →
  ¬(n = 2^f.K-1 ∧ f.s = .signed ∧ f.d = .extended) →
  ¬(n = 2^f.K-2 ∧ f.s = .unsigned ∧ f.d = .extended) →
  ¬(2^(f.K-1) < n ∧ f.s = .signed) →
  ∃ y, @value_set f y = Sum.inl (@decode_finite f n) := by
  intros
  simp [decode_finite]
  split
  -- subnormal
  expose_names
  clear * - h_5 h_6
  simp [h_6]
  norm_cast at h_6
  rw [Nat.div_eq_zero_iff_lt (by exact Nat.two_pow_pos (f.P - 1) )] at h_6
  rw [Nat.mod_eq_of_lt h_6]
  exists .p3109_finite n f.emin_lsb (by simp)
    (by
      have _ := f.h_P;
      right; constructor; constructor; simp [vnum, to_format]; norm_cast; apply lt_trans h_6; rw [pow_lt_pow_iff_right₀ (by simp)]; omega; simp [to_format]; simp [to_format, vnum, abs_mul];
      rify; rw [<-lt_div_iff₀' (by simp)]
      rewrite (occs := .pos [4]) [<-pow_one 2]
      rw [div_eq_mul_inv, <-pow_sub₀ _ (by simp) (by  omega)]
      norm_cast)
  simp [value_set, emin_lsb, emin]
  norm_cast
  rw [mul_assoc]; simp; left
  rw [<-zpow_add₀ (by simp)]; simp
  have _ := f.h_P
  rw [Int.subNatNat_eq_coe]; simp; omega
  -- normal, we need all the previous conditions on special values
  -- bc proving normals need them
  expose_names
  simp at h_5
  norm_cast at h_6
  simp at h_6
  norm_cast
  have := @Nat.div_add_mod n (2^(f.P-1))
  set exp := n / 2^(f.P-1) with he
  set m := n % 2^(f.P-1) with hm
  simp [Int.subNatNat_eq_coe]
  rify at this
  rw [add_comm, <-eq_sub_iff_add_eq] at this

  norm_cast at this
  norm_cast
  simp [this, Int.subNatNat_eq_coe]
  have _ : 0 ≤ m := by simp
  have _ : (0:ℤ) < 2^(f.P-1) := by apply pow_pos; simp
  -- the exponent is exp-bias-p+1!!!
  have _ := f.h_P
  exists @decode_normal f n
    (by
      simp [W]; split; expose_names; simp [heq] at *;
      apply lt_of_lt_of_le (b := 2^(f.K-1)) (by omega)
      rw [Nat.pow_le_pow_iff_right (by simp)]; omega
      apply lt_of_lt_of_le (b := 2^f.K) (by omega)
      expose_names; simp [heq] at *
      have : f.P + (f.K-f.P) = f.K := by omega
      rw [this])
    h h_1 h_2 h_3 h_4 (by simp; norm_cast; simp; exact h_6)
  simp [decode_normal]
  simp [value_set]
  have : exp - f.bias - ↑f.P + 1 = exp - f.bias + (1 - f.P) := by omega
  norm_cast
  rw [this, zpow_add₀ (by simp)]
  norm_cast
  rw [mul_comm (2^(exp-f.bias)), <-mul_assoc]
  simp; left
  rw [add_mul, hm]; simp
  rw [<-zpow_natCast, <-zpow_add₀ (by simp)]
  have _ := f.h_P

  have : ↑(f.P - 1) + Int.subNatNat 1 f.P = 0 := by
    rw [Int.ofNat_sub (by omega), Int.subNatNat_eq_coe]; omega
  simp [this]


theorem decode_in_value_set (n : Fin (2^f.K)) :
  @decode f n ∈ Set.range (@value_set f) := by
  simp [decode]
  split
  exists .p3109_nan
  split
  exists .p3109_nan
  split
  exists .p3109_infinity (by expose_names; exact h_2.2.2) false (by simp)
  split
  exists .p3109_infinity (by expose_names; exact h_3.2.2) true (by expose_names; simp [h_3])
  split
  exists .p3109_infinity (by expose_names; exact h_4.2.2) false (by simp)
  split
  have _ := n.isLt
  have ⟨y, heq⟩ := @decode_finite_in_value_set f (n-2^(f.K-1))
    (by expose_names; apply lt_of_le_of_lt _ h_6; simp)
    (by
      have _ := f.h_K
      rintro ⟨heq, hs⟩; expose_names;
      revert heq; simp; apply ne_of_lt
      rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1) (by omega)] at h_6
      simp [pow_add, mul_two] at h_6
      omega)
    (by
      have _ := f.h_K
      rintro ⟨heq, hs⟩; expose_names;
      revert heq; simp; apply ne_of_lt
      rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1) (by omega)] at h_6
      simp [pow_add, mul_two] at h_6
      omega)
    (by
      intro heq
      simp [heq.2] at *
      expose_names; apply h_3
      have _ := f.h_K
      rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1) (by omega)]
      omega)
    (by
      intro heq
      expose_names
      have : 2^(f.K-1) < 1 := by omega
      revert this; simp)
    (by
      intro heq
      simp [heq.2] at *)
    (by
      rintro ⟨hlt, heq⟩
      expose_names
      revert hlt; simp
      have _ := f.h_K
      rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1) (by omega)] at h_6
      simp [pow_add, mul_two] at h_6; omega)
  set decode_neg := @decode_finite f (n - 2^(f.K-1)) with hneg
  simp [value_set] at heq
  have ⟨hne1, hne2⟩ := @decode_finite_is_finite f (n - 2^(f.K-1))
  split at heq
  exfalso
  simp [decode_neg] at heq
  apply hne2 heq
  exfalso
  simp at heq
  apply hne1 heq
  simp at heq
  simp at heq
  expose_names
  exists .p3109_finite (-m) e (by simp [h_5]) (by
    have := canonical_p3109_negate h_7
    simp [fopp] at this
    exact this)
  simp [value_set]; exact heq
  apply decode_finite_in_value_set
  exact n.isLt
  repeat assumption

theorem normal_roundtrip_eq (x : ℝ) (exp E : ℤ) (n T : ℕ) :
  exp = max (Int.log 2 x) (1 - f.bias) →
  E = ↑(n / 2 ^ (f.P - 1)) - f.bias →
  ¬E = -f.bias →
  T = n % 2 ^ (f.P - 1) →
  x = (2 ^ (f.P - 1) + ↑T) * 2 ^ (max E (1 - f.bias) - ↑f.P + 1) →
  0 < x →
  x * (2 ^ exp)⁻¹ * (2 ^ (f.P - 1)) - (2 ^ (f.P - 1)) + (exp + f.bias) * (2 ^ (f.P - 1)) = ↑n
  := by
  have _ := f.h_P
  intro hexp he hene ht hx hxnonneg
  simp at he
  norm_cast at he
  have helo : -f.bias ≤ E := by simp [he]; norm_cast; apply zero_le
  rw [max_eq_left (by omega)] at hx
  norm_cast
  have hxlo : 2^E ≤ x := by
    simp [hx]
    rw [add_mul, <-zpow_natCast, <-zpow_add₀ (by simp)]
    have _ : 0 ≤ (T:ℝ) * 2 ^ (E - ↑f.P + 1) := by apply mul_nonneg; simp [ht]; apply zpow_nonneg; simp
    suffices (2 ^ E:ℝ) ≤ 2 ^ (↑(f.P - 1) + (E - ↑f.P + 1)) by linarith
    simp; omega
  have hxhi : x < 2^(E+1) := by
    simp [hx]
    have : (2 ^ (f.P - 1) + ↑T) < 2^f.P := by
      rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.P) (m := 1) (by omega)]
      simp [pow_add]
      have _ : T < 2^(f.P-1) := by simp [ht]; apply Nat.mod_lt; apply pow_pos; simp
      omega
    rw [<-lt_div_iff₀ (by apply zpow_pos; simp), <-zpow_sub₀ (by simp)]
    simp; norm_cast

  rw [max_eq_left (by
    rw [<-Int.zpow_le_iff_le_log (by simp) (by assumption)]
    apply le_trans _ hxlo
    simp; omega
  )] at hexp
  have : exp = E := by
    rw [hexp]
    symm
    apply log_eq_of_bound
    assumption
    exact hxlo
    exact hxhi
  rw [this, mul_assoc]
  rewrite (occs := .pos [2]) [mul_comm]
  simp [<-div_eq_mul_inv]
  rw [<-zpow_natCast, <-zpow_sub₀ (by simp)]
  simp [hx, add_mul]
  rw [<-zpow_natCast, <-zpow_add₀ (by simp), <-zpow_add₀ (by simp)]

  have : (↑(f.P - 1) + (E - ↑f.P + 1) + (↑(f.P - 1) - E)) = (f.P-1:ℕ) := by omega
  simp [this]
  rw [mul_assoc, <-zpow_add₀ (by simp)]
  have : (E - ↑f.P + 1 + (↑(f.P - 1) - E)) = 0 := by omega
  simp [this]
  rw [<-add_mul, he]; simp [ht]
  norm_cast
  rw [mul_comm]
  norm_cast
  rw [add_comm, Nat.div_add_mod]

theorem subnormal_roundtrip_eq (x : ℝ) (E : ℤ) (n T : ℕ) :
  E = -f.bias →
  E = ↑n / 2 ^ (f.P - 1) - f.bias →
  x = ↑T * 2 ^ (max E (1 - f.bias) - ↑f.P + 1) →
  0 < x →
  T = n % 2^(f.P-1) →
  x * (2 ^ max (Int.log 2 x) (1 - f.bias))⁻¹ * 2 ^ (f.P - 1) = ↑n := by

  have _ := f.h_P
  intro heeq he hx hxpos ht
  simp [heeq] at hx
  simp [he] at heeq; norm_cast at heeq
  simp at heeq
  have hteq : T = n := by simp [ht]; apply Nat.mod_eq_of_lt heeq
  rw [max_eq_right (by
    suffices Int.log 2 x < 1-f.bias by omega
    rw [<-Int.lt_zpow_iff_log_lt (by simp) (by assumption)]
    simp [hx, hteq]
    rw [<-lt_div_iff₀ (by apply zpow_pos; simp)]
    rw [<-zpow_sub₀ (by simp)]
    have : 1 - f.bias - (1 - f.bias - ↑f.P + 1) = (f.P-1:ℕ) := by omega
    simp [this]; norm_cast)]
  simp [hx]
  rw [<-div_eq_mul_inv, <-mul_div, <-zpow_sub₀ (by simp)]
  rw [mul_assoc, <-zpow_natCast]
  rw [<-zpow_add₀ (by simp)]
  have : (1 - f.bias - ↑f.P + 1 - (1 - f.bias) + (f.P-1:ℕ)) = 0 := by omega
  simp [this, hteq]

theorem hx_absurd_normal (x : ℝ) (exp E : ℤ) (mod T n : ℕ) :
  ¬x * (2 ^ exp)⁻¹ < 1 →
  T = n % 2^(f.P-1) →
  ↑mod + ↑(exp + f.bias).toNat * 2 ^ (f.P - 1) =
  x * (2 ^ exp)⁻¹ * 2 ^ (f.P - 1) - 2 ^ (f.P - 1) + (max ((Int.log 2 x)) (1 - f.bias) + f.bias) * 2 ^ (f.P - 1) →
  exp = max (Int.log 2 x) (1 - f.bias) →
  E = -f.bias →
  x = ↑T * 2 ^ (max E (1 - f.bias) - ↑f.P + 1) →
  False := by
  have _ := f.h_P
  intro hn ht heq hexp he hx
  simp [he] at hx

  apply hn
  rw [<-lt_div_iff₀ (by simp; apply zpow_pos; simp)]
  simp
  have hthi : T < 2^(f.P-1) := by simp [ht]; apply Nat.mod_lt; apply pow_pos; simp
  rify at hthi
  simp [hx];
  rw [<-lt_div_iff₀ (by apply zpow_pos; simp)]
  apply lt_of_lt_of_le hthi
  rw [le_div_iff₀ (by apply zpow_pos; simp), <-zpow_natCast, <-zpow_add₀ (by simp)]
  have : ↑(f.P - 1) + (1 - f.bias - ↑f.P + 1) = 1-f.bias := by omega
  simp [this, hexp]

theorem hx_absurd_subnormal (x : ℝ) (E : ℤ) (mod T n : ℕ) :
  x * (2 ^ max (Int.log 2 x) (1 - f.bias))⁻¹ < 1 →
  ↑mod = x * (2 ^ max (Int.log 2 x) (1 - f.bias))⁻¹ * 2 ^ (f.P - 1) →
  ¬E = -f.bias →
  E = n / 2^(f.P-1) - f.bias →
  x = (2 ^ (f.P - 1) + ↑T) * 2 ^ (max E (1 - f.bias) - ↑f.P + 1) →
  0 < x →
  False := by
  have _ := f.h_P
  intro hsub heq hne he hx hxpos
  revert hsub; simp
  norm_cast at he
  have helo : 1-f.bias ≤ E := by
    have _ : 0 ≤ (n / 2 ^ (f.P - 1)) := by apply Nat.zero_le
    omega
  rw [max_eq_left (by omega)] at hx
  have log :  (1 - f.bias) ≤ (Int.log 2 x) := by
    rw [<-Int.zpow_le_iff_le_log (by simp) (by assumption)]
    simp [hx]
    rw [add_mul, <-zpow_natCast, <-zpow_add₀ (by simp)]
    have : E = ↑(f.P - 1) + (E - ↑f.P + 1) := by omega
    rw [<-this]
    rw [<-zpow_le_zpow_iff_right₀ (a := (2:ℝ)) (by simp)] at helo
    suffices 0 ≤ T*(2^(E-f.P+1):ℝ) by linarith
    rw [<-div_le_iff₀ (by apply zpow_pos; simp)]; simp
  rw [max_eq_left (by omega)]
  have := Int.zpow_log_le_self (b := (2)) (r := x) (by simp) (by assumption)
  refine (mul_inv_le_iff₀ ?_).mp ?_
  simp; apply zpow_pos; simp
  simp at this ⊢; exact this

theorem round_trip_ident (n : Fin (2^f.K)) :
  @encode_raw f (@decode f n) (@decode_in_value_set f n) = n := by
    simp [decode]
    split; expose_names
    simp [encode_raw, h.2]; rcases n with ⟨n, _⟩; simp at ⊢ h; simp [h]
    split; expose_names
    simp [encode_raw, h_1.2]; rcases n with ⟨n, _⟩; simp at ⊢ h_1; simp [h_1]
    split; expose_names
    simp [encode_raw, encode_pos, h_2.2.1]
    rcases n with ⟨n, _⟩; simp at h_2 ⊢; simp [h_2]
    split; expose_names
    simp
    simp
    exfalso
    expose_names
    simp [h_2.2.1] at heq

    rcases n with ⟨n, _⟩
    -- arith
    split; expose_names
    simp at h_3
    simp [encode_raw, encode_pos,  h_3.1]
    unfold encode_pos_ret.n
    split; simp
    have hk := f.h_K
    rewrite (occs := .pos [3]) [<-Nat.sub_add_cancel (n := f.K) (m := 1) (by omega)]
    simp [pow_add, mul_two]
    have _ : 0 < 2^(f.K-1) := by simp
    omega
    exfalso
    expose_names
    simp [h_3] at heq
    split
    expose_names
    simp at h_4 ⊢; simp [h_4, encode_raw, encode_pos]
    split; exfalso; expose_names
    simp [h_4.2.1] at heq -- not sure what's happened
    simp
    simp
    -- negative
    split
    set n' := n - 2^(f.K-1) with hn
    simp_rw [<-hn]
    set T := n' % 2 ^ (f.P - 1) with ht
    set E := n' / 2^(f.P-1)-f.bias with he
    set dec := @decode_finite f n' with hdec
    simp_rw [<-hdec]
    unfold decode_finite at hdec
    simp_rw [<-ht, <-he] at hdec
    norm_cast at hdec
    have _ := f.h_P
    have : dec = ((if E = -f.bias then T else 2^(f.P-1)+T) * (2^(max E (1-f.bias)-f.P+1):ℝ)).toEReal := by
      simp [hdec]; split
      expose_names
      simp [h_6]
      norm_cast; rw [mul_assoc]; simp; left
      rw [<-zpow_add₀ (by simp)]
      rw [Int.subNatNat_eq_coe]; simp
      omega
      rw [max_eq_left];
      norm_cast
      rw [add_mul, ]; push_cast; rw [add_mul]; simp
      rw [<-zpow_natCast, <-zpow_add₀ (by simp)];
      have : (↑(f.P - 1) + (E - ↑f.P + 1)) = E := by omega
      simp [this]
      rw [mul_assoc, <-zpow_add₀ (by simp)]; simp; left
      rw [Int.subNatNat_eq_coe]; simp; omega
      suffices -f.bias ≤ E by omega
      simp [he]; norm_cast
      apply Nat.zero_le
    simp at this
    set x := if E = -f.bias then ↑T * (2:ℝ) ^ (max E (1 - f.bias) - ↑f.P + 1)
      else (2 ^ (f.P - 1) + ↑T) * 2 ^ (max E (1 - f.bias) - ↑f.P + 1) with hx
    simp_rw [this]
    simp_rw [<-lift_some_some_ereal]
    simp [encode_raw]
    clear hdec
    have hxnonneg : 0 ≤ x := by
      simp [hx]
      split; expose_names
      rw [<-div_le_iff₀ (by apply zpow_pos; simp)]; simp
      rw [<-div_le_iff₀ (by apply zpow_pos; simp)]; simp
      have _ : 0 ≤ T := by omega
      norm_cast; omega
    split
    exfalso; expose_names; simp at heq
    exfalso; expose_names; simp at heq; rw [lift_some_some_ereal, lift_some_none_top] at heq; apply EReal.top_ne_coe (-x); rw [<-heq]; simp
    exfalso; expose_names; simp at heq; rw [lift_some_some_ereal, lift_none_bot] at heq; apply EReal.bot_ne_coe (-x); rw [<-heq]; simp
    expose_names; simp at heq
    rw [lift_some_some_ereal, lift_some_some_ereal] at heq
    norm_cast at heq
    simp_rw [<-heq]
    rcases lt_or_eq_of_le hxnonneg with hlt|_

    rw [dif_neg (by linarith)]
    rw [dif_neg (by linarith)]
    unfold encode_pos_ret.n
    simp [encode_pos]
    split
    exfalso; expose_names; rw [lift_some_none_top] at heq_2; apply EReal.top_ne_coe (-x_2); rw [<-heq_2]; simp
    exfalso; expose_names; rw [lift_none_bot] at heq_2; apply EReal.bot_ne_coe (-x_2); rw [<-heq_2]; simp
    expose_names
    rw [lift_some_some_ereal] at heq_2
    norm_cast at heq_2
    simp [<-heq] at heq_2
    simp [<-heq_2]
    have := @encode_pos_eq f x_4 hor_1 h_10
    simp [<-lift_some_some_ereal] at this
    simp [encode_pos] at this
    unfold encode_pos_ret.n at this
    split at this
    exfalso; expose_names; rw [lift_some_none_top] at heq_5; apply EReal.coe_ne_top _ heq_5
    exfalso; expose_names; rw [lift_none_bot] at heq_5; apply EReal.coe_ne_bot _ heq_5
    expose_names
    rw [lift_some_some_ereal] at heq_5; simp at heq_5
    simp [<-heq_5, <-heq_2] at this
    split
    split at this
    simp [encode_pos_prop] at this
    split at this
    set mod := (encode_pos._proof_4 x_4 hor_1 h_10).choose.toNat % 2^(f.P-1) with hc
    simp [<-heq_5, <-heq_2] at hc; rw [<-hc] at this ⊢
    rify
    rw [this]

    split at hx
    have := @subnormal_roundtrip_eq f x E n' T (by assumption) he hx (by assumption) ht
    rw [this, hn]
    norm_cast
    omega
    exfalso
    have hf := @hx_absurd_subnormal f x E mod T n' (by assumption) this (by assumption) he hx (by assumption)
    cases hf

    exfalso; expose_names
    apply h_15
    clear * - this
    suffices x * (2 ^ max (Int.log 2 x) (1 - f.bias))⁻¹ * 2^(f.P-1) < 2^(f.P-1) by simp at this; exact this
    set choose := (encode_pos._proof_4 x_6 hor_3 h_12).choose.toNat % 2^(f.P-1) with hc
    simp [<-heq_5, <-heq_2] at hc; rw [<-hc] at this
    rw [<-sub_eq_iff_eq_add, eq_sub_iff_add_eq] at this
    rw [<-this]
    simp
    have hmodhi : choose < 2^(f.P-1) := by apply Nat.mod_lt; apply pow_pos; simp
    rify at hmodhi
    apply lt_of_lt_of_le hmodhi; simp
    norm_cast; omega

    exfalso; expose_names; apply h_14; exact h_13
    split at this
    exfalso; expose_names; apply h_13; exact h_14

    set mod := (encode_pos._proof_4 x_6 hor_3 h_12).choose.toNat % (2^(f.P-1)) with hc
    simp [<-heq_5, <-heq_2] at hc
    simp [<-hc] at ⊢ this
    simp [encode_pos_prop] at this
    split at this
    exfalso
    expose_names
    have hsub : x * (2 ^ max (Int.log 2 x) (1 - f.bias))⁻¹ * 2^(f.P-1) < 2^(f.P-1) := by simp; exact h_15
    rw [<-this] at hsub
    revert hsub; simp
    norm_cast
    suffices 2 ^ (f.P - 1) ≤ ↑(max (Int.log 2 x) (1 - f.bias) + f.bias).toNat * 2 ^ (f.P - 1) by omega
    rify; simp
    omega


    set exp := max (Int.log 2 x) (1-f.bias) with hexp
    -- simp at h_5
    split at hx
    have hf := @hx_absurd_normal f x exp E mod T n' (by assumption) ht (by norm_cast at this ⊢) hexp (by assumption) hx
    cases hf
    rify
    rw [this, <-eq_sub_iff_add_eq]; norm_cast
    simp at hn
    rw [Int.subNatNat_of_le (by omega), <-hn]
    have := @normal_roundtrip_eq f x exp E n' T hexp (by simp; exact he) (by assumption) ht hx (by assumption)
    norm_cast at this ⊢

    -- 0
    expose_names
    simp [<-h_9] at ⊢ hx
    simp at hn
    -- simp at h_5
    exfalso
    split at hx
    simp at hx
    expose_names
    simp [he] at h_10
    norm_cast at h_10
    simp [ht] at hx
    rcases hx with ht'|hf
    have : n' = 0 := by
      rw [<-Nat.div_add_mod (m := n') (n := 2^(f.P-1)), ht', h_10]
      simp
    simp [hn] at this
    omega -- this is false because n being negative has leading bit set

    revert hf; simp
    apply ne_of_gt; apply zpow_pos; simp
    revert hx; simp
    simp [ht]
    constructor
    apply ne_of_gt
    norm_cast
    omega
    apply ne_of_gt; apply zpow_pos; simp
    expose_names; simp at h_5
    set T := n % 2 ^ (f.P - 1) with ht
    set E := n / 2^(f.P-1)-f.bias with he
    set dec := @decode_finite f n with hdec
    simp_rw [<-hdec]
    unfold decode_finite at hdec
    simp_rw [<-ht, <-he] at hdec
    norm_cast at hdec
    have _ := f.h_P
    have : dec = ((if E = -f.bias then T else 2^(f.P-1)+T) * (2^(max E (1-f.bias)-f.P+1):ℝ)).toEReal := by
      simp [hdec]; split
      expose_names
      simp [h_6]
      norm_cast; rw [mul_assoc]; simp; left
      rw [<-zpow_add₀ (by simp)]
      simp [h_7]
      rw [Int.subNatNat_eq_coe]; omega
      rw [max_eq_left];
      norm_cast
      rw [add_mul, ]; push_cast; rw [add_mul]; simp
      rw [<-zpow_natCast, <-zpow_add₀ (by simp)];
      have : (↑(f.P - 1) + (E - ↑f.P + 1)) = E := by omega
      simp [this]
      rw [mul_assoc, <-zpow_add₀ (by simp)]; simp; left
      rw [Int.subNatNat_eq_coe]; simp; omega
      suffices -f.bias ≤ E by omega
      simp [he]; norm_cast
      exact Nat.zero_le (↑n / 2 ^ (f.P - 1))
    simp at this
    set x := if E = -f.bias then ↑T * (2:ℝ) ^ (max E (1 - f.bias) - ↑f.P + 1)
      else (2 ^ (f.P - 1) + ↑T) * 2 ^ (max E (1 - f.bias) - ↑f.P + 1) with hx
    simp_rw [this]
    simp_rw [<-lift_some_some_ereal]
    simp [encode_raw]
    clear hdec
    have hxnonneg : 0 ≤ x := by
      simp [hx]
      split; expose_names
      rw [<-div_le_iff₀ (by apply zpow_pos; simp)]; simp
      rw [<-div_le_iff₀ (by apply zpow_pos; simp)]; simp
      have _ : 0 ≤ T := by omega
      norm_cast; omega
    cases lt_or_eq_of_le hxnonneg
    split; exfalso; linarith
    simp [encode_pos]
    unfold encode_pos_ret.n
    split
    exfalso; expose_names; rw [lift_some_none_top] at heq; apply EReal.coe_ne_top _ heq
    exfalso; expose_names; rw [lift_none_bot] at heq; apply EReal.coe_ne_bot _ heq
    expose_names; rw [lift_some_some_ereal] at heq; simp at heq
    have := @encode_pos_eq f x_2 hor_1 h_10
    simp_rw [<-lift_some_some_ereal] at this
    simp [encode_pos] at this
    unfold encode_pos_ret.n at this
    split at this
    exfalso; expose_names; rw [lift_some_none_top] at heq_3; apply EReal.coe_ne_top _ heq_3
    exfalso; expose_names; rw [lift_none_bot] at heq_3; apply EReal.coe_ne_bot _ heq_3
    expose_names
    rw [lift_some_some_ereal] at heq_3; simp at heq_3
    simp_rw [<-heq_3, <-heq] at this ⊢
    split
    split at this
    simp [encode_pos_prop] at this
    split at this
    set mod := (encode_pos._proof_4 x_4 hor_3 h_12).choose.toNat % 2^(f.P-1) with hc
    simp [<-heq_3, <-heq] at hc
    expose_names
    rw [<-hc] at ⊢ this
    rify; rw [this]
    split at hx
    have := @subnormal_roundtrip_eq f x E n T (by assumption) he hx (by assumption) ht
    exact this
    -- subnormal false
    exfalso
    have hf := @hx_absurd_subnormal f x E mod T n (by assumption) this (by assumption) he hx (by assumption)
    cases hf

    exfalso; expose_names; clear * - h_14 h_15 this
    apply h_15
    norm_cast at this
    set exp := max (Int.log 2 x) (1-f.bias) with hexp
    simp_rw [<-hexp] at this h_15 h_14
    suffices x * (2^exp:ℝ)⁻¹ * 2^(f.P-1) < 2^(f.P-1) by simp at this; exact this
    have hexplo : (2:ℕ)^(f.P-1:ℕ) ≤  ((exp+f.bias)*2^(f.P-1)) := by simp [hexp]; omega
    suffices x * (2 ^ exp)⁻¹ * ↑(2 ^ (f.P - 1)) - ↑(2 ^ (f.P - 1)) + ↑((exp + f.bias) * ↑(2 ^ (f.P - 1))) < 2^(f.P-1) by norm_cast at this ⊢ hexplo; rify at hexplo; push_cast at this; push_cast; linarith
    push_cast at this ⊢
    rw [<-this]; norm_cast
    apply Nat.mod_lt
    apply pow_pos; simp

    exfalso
    expose_names; clear * - h_13 h_14
    apply h_14; exact h_13

    -- normal
    split at this
    exfalso
    expose_names; apply h_13; exact h_14
    simp [encode_pos_prop] at this
    set test := (encode_pos._proof_4 x_4 hor_3 h_12).choose with hc
    simp [<-heq_3, <-heq] at hc
    rw [<-hc] at this ⊢
    set mod := test.toNat % 2^(f.P-1)
    split at this
    expose_names
    exfalso
    clear * - this h_15
    revert h_15; simp
    suffices 2^(f.P-1) ≤ x * (2 ^ max (Int.log 2 x) (1 - f.bias))⁻¹ * 2 ^ (f.P - 1) by simp at this; exact this
    rw [<-this]
    have lo1 : 0 ≤ test.toNat % 2 ^ (f.P - 1) := by apply zero_le
    have lo2 : 2^(f.P-1) ≤ ↑(max (Int.log 2 x) (1 - f.bias) + f.bias).toNat * 2 ^ (f.P - 1) := by simp; omega
    rify at lo1 lo2
    linarith
    rify; rw [this]
    set exp := max (Int.log 2 x) (1-f.bias) with hexp
    split at hx
    have hf := @hx_absurd_normal f x exp E mod T n (by assumption) ht (by norm_cast at this ⊢) hexp (by assumption) hx
    cases hf
    have := @normal_roundtrip_eq f x exp E n T hexp (by simp; exact he) (by assumption) ht hx (by assumption)
    norm_cast at this
    norm_cast

    expose_names
    simp [<-h_7] at hx ⊢
    split at hx
    simp at hx
    rcases hx with ht'|_
    simp [ht] at ht'
    expose_names
    simp [he] at h_8
    norm_cast at h_8
    rw [<-Nat.div_add_mod (m := n) (n := 2^(f.P-1)), ht', h_8]
    simp
    exfalso
    expose_names
    revert h_9; clear * -
    simp; apply ne_of_gt
    apply zpow_pos; simp

    simp at hx
    exfalso
    revert hx; simp
    constructor
    apply ne_of_gt; norm_cast
    simp [ht]
    apply ne_of_gt
    apply zpow_pos; simp
