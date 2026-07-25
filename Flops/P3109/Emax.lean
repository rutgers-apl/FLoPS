import Flops.P3109.Defs

-- finite value not normal
def max_finite_bit_pattern (f : p3109_format) : ℕ :=
  match f.s, f.d with
  -- Signed: NaN is at 2^(K-1), so largest positive is one or two below that.
  | .signed, .extended => 2^(f.K - 1) - 2 -- Inf is at 2^(K-1)-1
  | .signed, .finite   => 2^(f.K - 1) - 1 -- No Inf, so this code is available
  -- Unsigned: NaN is at 2^K-1, so largest is one or two below that.
  | .unsigned, .extended => 2^f.K - 3       -- Inf is at 2^K-2
  | .unsigned, .finite   => 2^f.K - 2       -- No Inf, so this code is available

def fundamental_emax (f : p3109_format) : ℤ :=
  let x := max_finite_bit_pattern f
  let exponent_field := x / (2^(f.P - 1)) -- integer division
  -- yes, maximum value could be subnormal
  if exponent_field = 0 then 1 - f.bias
  else
  exponent_field - f.bias

namespace p3109_format
-- we keep doing case analysis on the two definitions of emax_lsb

def emax_correct (f : p3109_format) :
  f.emax = fundamental_emax f := by
  simp only [emax, fundamental_emax, Nat.div_eq_zero_iff, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and, false_or, Int.natCast_ediv, Nat.cast_pow, Nat.cast_ofNat]
  split
  --
  expose_names
  simp only [W, heq_1, heq, bias, add_tsub_cancel_right, max_finite_bit_pattern, heq_2, tsub_self, pow_zero, Nat.lt_one_iff, Int.ediv_one]
  have _ := f.h_K

  have : 3 < 2^f.K := by
    apply lt_of_lt_of_le (b := 2^2)
    simp only [Nat.reducePow, Nat.lt_add_one]
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  rw [if_neg, Nat.sub_add_cancel]
  simp only [sub_left_inj]
  rw [Int.ofNat_sub]; simp only [Nat.cast_pow, Nat.cast_ofNat]; repeat omega
  repeat simp_all only
  --
  expose_names
  simp only [max_finite_bit_pattern, heq_1, heq_2, tsub_self, pow_zero, Nat.lt_one_iff, Int.ediv_one]
  have _ := f.h_K
  have : 2 < 2^f.K  := by
    rewrite (occs := .pos [1]) [<-pow_one 2]
    rw [pow_lt_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  rw [if_neg]; simp only [W, heq_1, heq, sub_left_inj]
  rw [Nat.sub_add_cancel, Int.ofNat_sub]
  simp only [Nat.cast_pow, Nat.cast_ofNat]; repeat omega
  --
  expose_names
  simp only [max_finite_bit_pattern, heq_1, heq_2, heq, tsub_self, pow_zero, Nat.lt_one_iff, Int.ediv_one]
  have _ := f.h_K
  have : 2 < 2^(f.K-1)  := by
    rewrite (occs := .pos [1]) [<-pow_one 2]
    rw [pow_lt_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  rw [if_neg]; simp only [W, heq_1, heq, sub_left_inj]
  rw [Int.ofNat_sub]; simp only [Nat.cast_pow, Nat.cast_ofNat]
  repeat omega
  -- K=2 unsigned extended: emax_lsb can't be 2^W-1-bias bc special values take up two code points
  expose_names
  simp only [max_finite_bit_pattern, heq_1, heq_2, heq, Nat.add_one_sub_one, pow_one]
  simp only [W, heq_1, heq]
  have _ := f.h_K
  have : 2^3 ≤ 2^f.K  := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  simp only [Nat.reducePow] at this
  rw [if_neg (by omega)]
  simp only [sub_left_inj]
  rw [Int.ofNat_sub (by omega)]; simp only [Nat.cast_pow, Nat.cast_ofNat]
  rewrite (occs := .pos [2]) [<-Int.add_neg_eq_sub]
  rw [Int.add_ediv_of_dvd_left]
  simp only [Int.reduceNeg, Int.reduceDiv, Int.add_neg_eq_sub, sub_left_inj]
  rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1)]
  rewrite (occs := .pos [2]) [pow_add]
  simp only [pow_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_right₀, Nat.ofNat_pos, OfNat.ofNat_ne_one, pow_right_inj₀]; omega; omega
  rewrite [<-Nat.sub_add_cancel (n := f.K) (m := 1)]
  rewrite [pow_add]
  simp only [pow_one, dvd_mul_left]; omega
  -- the hardest
  -- we solve the goal by splitting max_finite_bit_pattern
  -- we use various excluded (already matched) patterns to get tighter bounds on K and P
  simp only [max_finite_bit_pattern]
  split
  expose_names
  rw [if_neg]; simp only [sub_left_inj]
  simp only [W, heq]
  have _ : 2^1 ≤ 2^(f.K-1) := by
    have _ := f.h_K
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  have _ : 2^1 ≤ 2^(f.P-1) := by
    simp only [heq, heq_1, imp_false, not_true_eq_false] at h_2
    have _ := f.h_P
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  rw [Int.ofNat_sub (by omega)]; simp only [Nat.cast_pow, Nat.cast_ofNat]
  have : f.K - 1 = (f.K - f.P) + (f.P - 1) := by
    have _ := f.h_K
    have ⟨_, hlt, _⟩ := f.h_P
    have _ := hlt heq
    omega
  rw [this, pow_add, Int.mul_sub_ediv_right]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by simp only [Int.reduceNeg, Int.neg_neg_iff_pos, Nat.ofNat_pos]) (by linarith)]; omega
  simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true]; simp only [not_lt]
  have ⟨_, hlt, _⟩ := f.h_P
  have _ := hlt heq
  apply le_trans (b := 2^(f.K-2))
  rw [pow_le_pow_iff_right₀]; omega; simp only [Nat.one_lt_ofNat]
  simp only [heq, heq_1, imp_false, not_true_eq_false] at h_2
  have _ : 3 ≤ f.K := by omega
  have hle : 2^1 ≤ 2^(f.K-2) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  have : f.K-1 = f.K-2+1 := by omega

  simp only [this, pow_add, pow_one, mul_two, ge_iff_le]
  simp only [pow_one] at hle
  omega

  --
  expose_names
  rw [if_neg]
  simp only [Nat.ofNat_pos, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, sub_left_inj]
  simp only [W, heq]
  have _ : 2^1 ≤ 2^(f.K-1) := by
    have _ := f.h_K
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  have _ : 2^0 ≤ 2^(f.P-1) := by
    simp only [heq, reduceCtorEq, heq_1, imp_self, implies_true] at h_3
    have _ := f.h_P
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]

  have : f.K - 1 = (f.K - f.P) + (f.P - 1) := by
    have _ := f.h_K
    have ⟨_, hlt, _⟩ := f.h_P
    have _ := hlt heq
    omega
  rw [this, pow_add, Int.mul_sub_ediv_right]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by simp only [Int.reduceNeg, Int.neg_neg_iff_pos, zero_lt_one]) (by linarith)]; omega
  simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true]; simp only [not_lt]
  have ⟨_, hlt, _⟩ := f.h_P
  have _ := hlt heq
  apply le_trans (b := 2^(f.K-2))
  rw [pow_le_pow_iff_right₀]; omega; simp only [Nat.one_lt_ofNat]
  simp only [heq, reduceCtorEq, heq_1, imp_self, implies_true] at h_3
  have _ : 2 ≤ f.K := by omega
  have hle : 2^0 ≤ 2^(f.K-2) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  have : f.K-1 = f.K-2+1 := by omega
  simp only [this, pow_add, pow_one, mul_two, ge_iff_le]
  simp only [pow_zero] at hle
  omega

  --
  have hk := f.h_K
  expose_names
  simp only [heq, heq_1, imp_false, not_true_eq_false] at h h_3
  have ⟨_, _, hle⟩ := f.h_P
  have _ := hle heq
  have _ : 2^3 ≤ 2^(f.K) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  have _ : 2^2 ≤ 2^(f.K-1) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  have _ : 2^2 ≤ 2^(f.P-1) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  rw [if_neg]
  simp only [sub_left_inj]
  simp only [W, heq]

  rw [Int.ofNat_sub (by omega)]; simp only [Nat.cast_pow, Nat.cast_ofNat]
  have : f.K = f.K-f.P+1 + (f.P-1) := by omega
  rewrite (occs := .pos [2]) [this]
  rw [pow_add (n := (f.P-1)), Int.mul_sub_ediv_right]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by simp only [Int.reduceNeg, Int.neg_neg_iff_pos, Nat.ofNat_pos]) (by linarith)]; omega
  simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true]; simp only [not_lt]
  apply le_trans (b := 2^(f.K-1))
  rw [pow_le_pow_iff_right₀]; omega; simp only [Nat.one_lt_ofNat]

  rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1)]
  simp only [pow_add, pow_one, mul_two]
  omega; omega

  --
  expose_names
  simp only [heq, heq_1, imp_false, not_true_eq_false] at h_1
  have ⟨_, _, hle⟩ := f.h_P
  have _ := hle heq
  have _ := f.h_K

  have : 2^2 ≤ 2^f.K := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  have : 2^1 ≤ 2^(f.K-1) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  have : 2^1 ≤ 2^(f.P-1) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp only [Nat.one_lt_ofNat]
  rw [if_neg]
  simp only [sub_left_inj]
  simp only [W, heq]
  rw [Int.ofNat_sub (by omega)]; simp only [Nat.cast_pow, Nat.cast_ofNat]
  have : f.K = f.K-f.P+1 + (f.P-1) := by omega
  rewrite (occs := .pos [2]) [this, pow_add]
  rw [Int.mul_sub_ediv_right]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by simp only [Int.reduceNeg, Int.neg_neg_iff_pos, Nat.ofNat_pos]) (by linarith)]; omega
  simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
  simp only [not_lt]
  apply le_trans (b := 2^(f.K-1))
  rw [pow_le_pow_iff_right₀]; omega; simp only [Nat.one_lt_ofNat]
  rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1)]
  simp only [pow_add, pow_one, mul_two]
  omega; omega

lemma emax_le {f : p3109_format} :
  f.emax_lsb + f.P-1+f.bias ≤ 2^f.W-1 := by
  simp only [emax_lsb, emax]
  split
  expose_names
  simp only [ W, heq_1, heq, bias, add_tsub_cancel_right, Nat.cast_one, sub_add_cancel, tsub_le_iff_right ]
  omega
  expose_names
  simp only [ W, heq_1, heq, bias, add_tsub_cancel_right, Nat.cast_one, sub_add_cancel, tsub_le_iff_right ]
  omega
  omega
  omega
  omega
