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
  simp [emax, fundamental_emax]
  split
  --
  expose_names
  simp [W, bias, heq_1, heq_2, heq, max_finite_bit_pattern]
  have _ := f.h_K

  have : 3 < 2^f.K := by
    apply lt_of_lt_of_le (b := 2^2)
    simp
    rw [pow_le_pow_iff_right₀]
    omega; simp
  rw [if_neg, Nat.sub_add_cancel]
  simp [Int.ofNat_sub]
  rw [Int.ofNat_sub]; simp; repeat omega
  repeat simp_all only [reduceCtorEq]
  --
  expose_names
  simp [max_finite_bit_pattern, heq_1, heq_2, heq]
  have _ := f.h_K
  have : 2 < 2^f.K  := by
    rewrite (occs := .pos [1]) [<-pow_one 2]
    rw [pow_lt_pow_iff_right₀]
    omega; simp
  rw [if_neg]; simp [W, heq_1, heq]
  rw [Nat.sub_add_cancel, Int.ofNat_sub]
  simp; repeat omega
  --
  expose_names
  simp [max_finite_bit_pattern, heq_1, heq_2, heq]
  have _ := f.h_K
  have : 2 < 2^(f.K-1)  := by
    rewrite (occs := .pos [1]) [<-pow_one 2]
    rw [pow_lt_pow_iff_right₀]
    omega; simp
  rw [if_neg]; simp [W, heq_1, heq]
  rw [Int.ofNat_sub]; simp
  repeat omega
  -- K=2 unsigned extended: emax_lsb can't be 2^W-1-bias bc special values take up two code points
  expose_names
  simp [max_finite_bit_pattern, heq_1, heq_2, heq]
  simp [W, heq_1, heq]
  have _ := f.h_K
  have : 2^3 ≤ 2^f.K  := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  simp at this
  rw [if_neg (by omega)]
  simp
  rw [Int.ofNat_sub (by omega)]; simp
  rewrite (occs := .pos [2]) [<-Int.add_neg_eq_sub]
  rw [Int.add_ediv_of_dvd_left]
  simp [Int.add_neg_eq_sub]
  rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1)]
  rewrite (occs := .pos [2]) [pow_add]
  simp; omega; omega
  rewrite [<-Nat.sub_add_cancel (n := f.K) (m := 1)]
  rewrite [pow_add]
  simp; omega
  -- the hardest
  -- we solve the goal by splitting max_finite_bit_pattern
  -- we use various excluded (already matched) patterns to get tighter bounds on K and P
  simp [max_finite_bit_pattern]
  split
  expose_names
  rw [if_neg]; simp
  simp [W, heq]
  have _ : 2^1 ≤ 2^(f.K-1) := by
    have _ := f.h_K
    rw [pow_le_pow_iff_right₀]
    omega; simp
  have _ : 2^1 ≤ 2^(f.P-1) := by
    simp [heq, heq_1] at h_2
    have _ := f.h_P
    rw [pow_le_pow_iff_right₀]
    omega; simp
  rw [Int.ofNat_sub (by omega)]; simp
  have : f.K - 1 = (f.K - f.P) + (f.P - 1) := by
    have _ := f.h_K
    have ⟨_, hlt, _⟩ := f.h_P
    have _ := hlt heq
    omega
  rw [this, pow_add, Int.mul_sub_ediv_right]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by simp) (by linarith)]; omega
  simp; simp
  have ⟨_, hlt, _⟩ := f.h_P
  have _ := hlt heq
  apply le_trans (b := 2^(f.K-2))
  rw [pow_le_pow_iff_right₀]; omega; simp
  simp [heq, heq_1] at h_2
  have _ : 3 ≤ f.K := by omega
  have hle : 2^1 ≤ 2^(f.K-2) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  have : f.K-1 = f.K-2+1 := by omega

  simp [this, pow_add, mul_two]
  simp at hle
  omega

  --
  expose_names
  rw [if_neg]
  simp
  simp [W, heq]
  have _ : 2^1 ≤ 2^(f.K-1) := by
    have _ := f.h_K
    rw [pow_le_pow_iff_right₀]
    omega; simp
  have _ : 2^0 ≤ 2^(f.P-1) := by
    simp [heq, heq_1] at h_3
    have _ := f.h_P
    rw [pow_le_pow_iff_right₀]
    omega; simp

  have : f.K - 1 = (f.K - f.P) + (f.P - 1) := by
    have _ := f.h_K
    have ⟨_, hlt, _⟩ := f.h_P
    have _ := hlt heq
    omega
  rw [this, pow_add, Int.mul_sub_ediv_right]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by simp) (by linarith)]; omega
  simp; simp
  have ⟨_, hlt, _⟩ := f.h_P
  have _ := hlt heq
  apply le_trans (b := 2^(f.K-2))
  rw [pow_le_pow_iff_right₀]; omega; simp
  simp [heq, heq_1] at h_3
  have _ : 2 ≤ f.K := by omega
  have hle : 2^0 ≤ 2^(f.K-2) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  have : f.K-1 = f.K-2+1 := by omega
  simp [this, pow_add, mul_two]
  simp at hle
  omega

  --
  have hk := f.h_K
  expose_names
  simp [heq, heq_1] at h h_3
  have ⟨_, _, hle⟩ := f.h_P
  have _ := hle heq
  have _ : 2^3 ≤ 2^(f.K) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  have _ : 2^2 ≤ 2^(f.K-1) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  have _ : 2^2 ≤ 2^(f.P-1) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  rw [if_neg]
  simp
  simp [W, heq]

  rw [Int.ofNat_sub (by omega)]; simp
  have : f.K = f.K-f.P+1 + (f.P-1) := by omega
  rewrite (occs := .pos [2]) [this]
  rw [pow_add (n := (f.P-1)), Int.mul_sub_ediv_right]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by simp) (by linarith)]; omega
  simp; simp
  apply le_trans (b := 2^(f.K-1))
  rw [pow_le_pow_iff_right₀]; omega; simp

  rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1)]
  simp [pow_add, mul_two]
  omega; omega

  --
  expose_names
  simp [heq, heq_1] at h_1
  have ⟨_, _, hle⟩ := f.h_P
  have _ := hle heq
  have _ := f.h_K

  have : 2^2 ≤ 2^f.K := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  have : 2^1 ≤ 2^(f.K-1) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  have : 2^1 ≤ 2^(f.P-1) := by
    rw [pow_le_pow_iff_right₀]
    omega; simp
  rw [if_neg]
  simp
  simp [W, heq]
  rw [Int.ofNat_sub (by omega)]; simp
  have : f.K = f.K-f.P+1 + (f.P-1) := by omega
  rewrite (occs := .pos [2]) [this, pow_add]
  rw [Int.mul_sub_ediv_right]
  rw [Int.ediv_eq_neg_one_of_neg_of_le (by simp) (by linarith)]; omega
  simp
  simp
  apply le_trans (b := 2^(f.K-1))
  rw [pow_le_pow_iff_right₀]; omega; simp
  rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1)]
  simp [pow_add, mul_two]
  omega; omega

lemma emax_le {f : p3109_format} :
  f.emax_lsb + f.P-1+f.bias ≤ 2^f.W-1 := by
  simp [emax_lsb, emax]
  split
  expose_names
  simp [bias, W, heq_2, heq, heq_1]
  omega
  expose_names
  simp [bias, W, heq_2, heq, heq_1]
  omega
  omega
  omega
  omega
