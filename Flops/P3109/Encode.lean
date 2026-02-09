import Flops.P3109.Defs
import Flops.P3109.RoundingAux

variable {f : p3109_format}

namespace p3109_format

namespace p3109

def encode_pos_prop (r : ℝ) (n : ℕ) : Prop :=
  -- exponent wrt. MSB
  let E := max (Int.log 2 r) (1-f.bias)
  -- integer significand, but now S is ℝ
  let S := r * 2^(-E) * 2^(f.P-1)
  (if S < 2^(f.P-1) then n = S else n = (S - 2^(f.P-1)) + (E+f.bias) * 2^(f.P-1))

structure encode_pos_ret (x : EReal) where
  n : ℕ
  lt : match f.s with
    |.signed => n < 2^(f.K-1)
    |.unsigned => n < 2^f.K
  h : match x with
    |(r:ℝ) => @encode_pos_prop f r n
    |_ => True

noncomputable def encode_pos (x : EReal) (hor : 0 < x)
  (h : (Sum.inl x) ∈ Set.range (@value_set f)) : @encode_pos_ret f x :=
  match x with
  |⊤ => match hs:f.s with
    |.signed => ⟨ 2^(f.K-1)-1, by simp [hs], by simp [<-lift_some_none_top] ⟩
    |.unsigned => ⟨2^f.K-2, by simp [hs], by simp [<-lift_some_none_top] ⟩
  |⊥ => by
    exfalso
    simp at hor
  |(x : ℝ) =>
    -- exponent wrt. MSB
    let E := max (Int.log 2 x) (1-f.bias)
    -- integer significand, but now S is ℝ
    let S := x * 2^(-E) * 2^(f.P-1)
    -- let T := S % 2^(f.P-1)
    have hme : ∃(m e : ℤ), m = S ∧ e = E - f.P + 1 ∧ (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
      simp [value_set] at h
      let ⟨y, heq⟩ := h
      clear h
      split at heq <;> simp at heq
      expose_names
      exists m, e
      have : e  = E - f.P + 1 := by
        have hcan := (canonical_fp_of_canonical_p3109 _ h) |> (@flt_equivalent' 2 f.to_format m e ?_ rfl).mpr
        simp [fexp, digits_abs', to_format, emin_lsb, emin] at hcan
        norm_cast at heq
        simp [E]
        simp at hor
        rw [<-abs_of_pos (a := x) hor]
        simp [<-heq, abs_mul]
        rewrite (occs := .pos [2]) [abs_of_pos (by apply zpow_pos; simp)]

        rw [log_mul']
        rewrite (occs := .pos [1]) [<-hcan]
        omega
        simp
        intro heq'
        simp [heq'] at heq
        simp [heq] at hor
        intro heq'
        simp [heq'] at heq
        simp [<-heq] at hor

      simp [this]
      norm_cast at heq
      simp [S, <-heq]
      rw [mul_assoc, this, mul_comm _ (2^(f.P-1)), <-div_eq_mul_inv, <-zpow_natCast, <-zpow_sub₀ (by simp), mul_assoc, <-zpow_add₀ (by simp)]
      have _ := f.h_P
      have heq: (E - ↑f.P + 1 + (↑(f.P - 1) - E)) = 0 := by omega
      simp [heq]; simp [<-this]
      constructor <;> assumption
    let m := hme.choose
    have mpos : 0 < m := by
      have ⟨heq, _⟩ := hme.choose_spec.choose_spec
      unfold m
      set m := hme.choose with hm
      rify; rw [heq]; simp [S]
      simp at hor
      apply mul_pos hor
      simp; apply zpow_pos; simp
    have : m = m.toNat := by
      have ⟨heq, _⟩ := hme.choose_spec.choose_spec
      simp; unfold m at *
      set m := hme.choose with hm
      omega

    let T := m.toNat % 2^(f.P-1)
    if hlt : m < 2^(f.P-1) then
    ⟨T, by
      have heq : T = m.toNat := by
        simp [T]
        apply Nat.mod_eq_of_lt
        zify; simp [<-this]; exact hlt
      suffices T < 2^(f.K-1) by split; assumption; apply lt_of_lt_of_le this; rw [Nat.pow_le_pow_iff_right (by simp)]; simp
      simp [heq, <-this]; apply lt_of_lt_of_le hlt; rify; rw [pow_le_pow_iff_right₀]; have := f.h_P; cases hs:f.s; simp [hs] at this; omega; simp [hs] at this; omega; simp,
      by
        unfold T m E S at *
        set m := hme.choose with hm
        set T := m % 2^(f.P-1) with ht
        have heq : T = m.toNat := by
          simp [T]; rw [max_eq_left (by omega)]
          rw [this]; norm_cast
          apply Nat.mod_eq_of_lt
          zify; simp [<-this]; exact hlt
        rw [ht, this] at heq
        norm_cast at heq
        rw [heq, <-this]
        set E := max (Int.log 2 x) (1 - f.bias) with he
        set S := x * 2 ^ (-E) * 2 ^ (f.P - 1) with hs

        have ⟨e, ⟨heq, _, _, hcan⟩⟩ := hme.choose_spec
        simp [<-lift_some_some_ereal]; simp [encode_pos_prop];
        simp_rw [<-he]
        rw [<-hm] at heq
        rify at hlt
        rw [heq, hs] at hlt; simp at hlt
        rw [if_pos hlt]
        simp at hs
        simp [<-hs, <-heq]
        norm_cast; simp [<-this] ⟩
    else
    --
    have explo : 1 ≤ E+f.bias := by
      have ⟨_, e, ⟨_, heq, _, hcan⟩⟩ := hme
      have ⟨_, hle⟩ := canonical_fp_of_canonical_p3109 _ hcan |> canonical_bounded
      simp [to_format, emin_lsb, emin, heq] at hle
      omega
    have heqnat : (E+f.bias).toNat = (E+f.bias) := by simp; omega
    have exphi : E+f.bias ≤ 2^f.W-1:= by
      unfold m at *
      set m := hme.choose with hm
      have ⟨e, ⟨_, heq, _, hcan⟩⟩ := hme.choose_spec
      rw [<-hm] at hcan
      rcases hcan with ⟨_, _, hemax, _⟩|⟨_, _, hlt'⟩
      simp [heq, emax_lsb, emax] at hemax
      split at hemax
      omega
      omega
      omega
      omega
      omega
      exfalso
      simp [vnum, to_format, abs_mul] at hlt'
      rw [abs_of_pos mpos] at hlt'
      apply hlt; clear hlt
      rify at hlt'; rw [<-lt_div_iff₀' (by simp)] at hlt'
      rify; rw [pow_sub₀]; simp
      exact hlt'; simp;
      have _ := f.h_P; omega
    -- 2^K = (2^W-1) * 2^(P-1) + 2^(P-1)
    ⟨T + (E+f.bias).toNat*2^(f.P-1), by
      have tup : T < 2^(f.P-1) := by
        simp [T]
        zify
        rw [<-this]
        refine Int.emod_lt_of_pos m ?_
        apply pow_pos; simp
      suffices 2^(f.P-1)-1 + (E+f.bias).toNat * 2^(f.P-1) < match f.s with
        |.signed => 2^(f.K-1)
        |.unsigned => 2^f.K by cases hs:f.s <;> simp [hs] at this ⊢; omega; omega
      zify
      rw [heqnat]
      have hle : (E + f.bias) * 2 ^ (f.P - 1) ≤ (2^f.W-1)*2^(f.P-1) := by
        refine Int.mul_le_mul_of_nonneg_right exphi ?_
        apply pow_nonneg; simp
      simp [sub_mul] at hle
      have _ := f.h_P
      rw [Int.ofNat_sub]; simp
      suffices 2^f.W*2^(f.P-1) ≤ match f.s with
        |.signed => 2^(f.K-1)
        |.unsigned => 2^f.K by cases hs:f.s <;> simp [hs] at this ⊢; zify at this; omega; zify at this; omega
      rw [<-pow_add]
      simp [W]
      expose_names
      cases hs:f.s <;> (simp [hs] at *; rw [pow_le_pow_iff_right₀ (by simp)])
      omega; omega
      suffices 0 < 2^(f.P-1) by omega
      simp, by
      -- second proof
      unfold T m E S at *
      set m := hme.choose with hm
      set T := m % 2^(f.P-1) with ht
      set E := max (Int.log 2 x) (1 - f.bias) with he
      set S := x * 2 ^ (-E) * 2 ^ (f.P - 1) with hs
      simp [<-lift_some_some_ereal]; simp [encode_pos_prop];
      simp [<-he]
      have ⟨e, ⟨heq, _, _, hcan⟩⟩ := hme.choose_spec
      rw [<-hm, hs] at heq
      have hmlo := hlt; simp at hmlo
      rify at hlt; simp [heq] at hlt
      rw [if_neg (by linarith)]
      simp at heq
      rw [<-heq]
      norm_cast; rw [<-he]

      rewrite (occs := .pos [2]) [<-heqnat]
      norm_cast; push_cast; simp
      rw [Nat.mod_def]
      have hmhi : m < 2^f.P := by
        have ⟨hlt, _⟩ := @canonical_fp_of_canonical_p3109 f _ hcan |> canonical_bounded
        rw [<-hm] at hlt
        simp [vnum, to_format] at hlt
        rw [abs_of_pos mpos] at hlt
        exact hlt

      have hdiv : m.toNat / 2^(f.P-1)=1 := by
        apply Nat.div_eq_of_lt_le; simp
        rw [this] at hmlo; norm_cast at hmlo
        simp
        rewrite (occs := .pos [1]) [<-pow_one 2]
        have _ := f.h_P
        rw [mul_comm, <-pow_add, Nat.sub_add_cancel (by omega)]
        exact hmhi
      simp [hdiv]
      rewrite (occs := .pos [2]) [this]; norm_cast
      rw [Int.ofNat_sub]; norm_cast
      rw [this] at hmlo; norm_cast at hmlo ⟩
def encode_pos_eq (x : EReal) (hor : 0 < x)
  (h : (Sum.inl x) ∈ Set.range (@value_set f)) := (@encode_pos f x hor h).h
noncomputable def encode_raw (x : EReal ⊕ Unit)
  (h : x ∈ Set.range (@value_set f)) : Fin (2^f.K) :=
  match x with
  |Sum.inr () =>
    match f.s with
    |.signed => ⟨2^(f.K-1), by have _ := f.h_K; rw [pow_lt_pow_iff_right₀]; omega; simp⟩
    |.unsigned => ⟨2^f.K-1, by simp⟩
  |Sum.inl ⊤ => let ⟨n, lt, h⟩ := @encode_pos f ⊤ (by simp) h;
    ⟨n, by split at lt; apply lt_of_lt_of_le lt; rw [Nat.pow_le_pow_iff_right (by simp)]; simp; assumption⟩
  |Sum.inl ⊥ => let ⟨n, lt, _⟩ := @encode_pos f ⊤ (by simp) (by
    simp [value_set]; simp [value_set] at h
    have ⟨y, heq⟩ := h; clear h
    rcases y with ⟨hd, s, _⟩|_|_
    cases s; simp at heq
    exists .p3109_infinity hd false (by simp)
    simp at heq; simp at heq; exfalso
    norm_cast at heq);
    ⟨n + 2^(f.K-1), by
      simp [value_set] at h;
      have ⟨x, heq⟩ := h; split at heq
      expose_names
      simp at hm
      simp [hm] at lt
      have hk := f.h_K
      rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1) (by omega)]
      simp [pow_add, mul_two]; exact lt
      exfalso; simp at heq
      exfalso; simp at heq
      exfalso; simp at heq
      exfalso; apply EReal.coe_ne_bot _ heq
      ⟩

  |Sum.inl (x : ℝ) =>
    if _ : x = 0 then 0 else
     if hlt : 0 < x then let ⟨n, lt, h⟩ := @encode_pos f x (by simp; exact hlt) h;
      ⟨n, by split at lt; apply lt_of_lt_of_le lt; rw [Nat.pow_le_pow_iff_right (by simp)]; simp; assumption⟩
    else let ⟨n, lt, _⟩ := @encode_pos f (-x) (by simp at ⊢ hlt; apply lt_of_le_of_ne hlt; simp; assumption) (by
      simp [value_set] at h ⊢
      have ⟨y, heq⟩ := h; clear h
      split at heq <;> simp at heq
      norm_cast at heq
      simp [<-heq] at hlt
      rw [<-le_div_iff₀ (by apply zpow_pos; simp)] at hlt
      simp at hlt
      expose_names
      exists .p3109_finite (-m) e (by intro _; omega) (by have := @canonical_p3109_negate f ⟨m, e⟩ h_1; simp [fopp] at this; simp [this])
      simp; norm_cast)
      ⟨n + 2^(f.K-1), by
      simp [value_set] at h;
      have ⟨x, heq⟩ := h; split at heq
      exfalso; simp at heq
      exfalso; simp at heq
      exfalso; simp at heq
      clear h
      expose_names; simp at heq; norm_cast at heq
      have hlt : x < 0 := by apply lt_of_le_of_ne; simp at hlt; exact hlt; simp; exact h
      simp [<-heq] at hlt
      rw [<-lt_div_iff₀ (by apply zpow_pos; simp)] at hlt
      simp at hlt
      cases hs:f.s; simp [hs] at lt
      have hk := f.h_K
      rewrite (occs := .pos [2]) [<-Nat.sub_add_cancel (n := f.K) (m := 1) (by omega)]
      rw [pow_add]; simp [mul_two]; exact lt
      simp [hs] at hm; exfalso; omega ⟩
