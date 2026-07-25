import Flops.P3109.Exec.Refinement.Saturate

namespace p3109_format
namespace Exec

lemma encodeValue_nan_refines :
    toEReal (fromBits (encodeValue (f := f) .nan)) = (0 : EReal) := by
  cases hs : f.s
  · have hmod : 2 ^ (f.K - 1) % 2 ^ f.K = 2 ^ (f.K - 1) := by
      exact Nat.mod_eq_of_lt (pow_pred_lt_pow f)
    simp [encodeValue, encodeValueNat, fromBits, toEReal, encodeNat, encodeSpecial, nanCode,
      signBase, p3109.n_to_p3109, hs, hmod]
  · have hpos : 0 < 2 ^ f.K := pow_pos (by decide : 0 < 2) f.K
    have hmod : (2 ^ f.K - 1) % 2 ^ f.K = 2 ^ f.K - 1 := by
      exact Nat.mod_eq_of_lt (Nat.sub_lt hpos (by decide))
    simp [encodeValue, encodeValueNat, fromBits, toEReal, encodeNat, encodeSpecial, nanCode,
      maxCode, p3109.n_to_p3109, hs, hmod]

lemma encodeValue_posInf_refines (hd : f.d = Domain.extended) :
    toEReal (fromBits (encodeValue (f := f) .posInf)) = (⊤ : EReal) := by
  cases hs : f.s
  · have hcodeLt : 2 ^ (f.K - 1) - 1 < 2 ^ f.K := by
      exact lt_of_le_of_lt (Nat.sub_le _ _) (pow_pred_lt_pow f)
    have hmod : (2 ^ (f.K - 1) - 1) % 2 ^ f.K = 2 ^ (f.K - 1) - 1 := by
      exact Nat.mod_eq_of_lt hcodeLt
    have hneNan : ¬ 2 ^ (f.K - 1) - 1 = 2 ^ (f.K - 1) := by
      have hpos : 0 < 2 ^ (f.K - 1) := pow_pos (by decide : 0 < 2) (f.K - 1)
      omega
    simp [encodeValue, encodeValueNat, fromBits, toEReal, encodeNat, encodeSpecial,
      signBase, p3109.n_to_p3109, hs, hd, hmod, hneNan]
  · have hpos : 0 < 2 ^ f.K := pow_pos (by decide : 0 < 2) f.K
    have hmaxLt : 2 ^ f.K - 1 < 2 ^ f.K := Nat.sub_lt hpos (by decide)
    have hcodeLt : 2 ^ f.K - 1 - 1 < 2 ^ f.K := by
      exact lt_of_le_of_lt (Nat.sub_le _ _) hmaxLt
    have hmod : (2 ^ f.K - 1 - 1) % 2 ^ f.K = 2 ^ f.K - 1 - 1 := by
      exact Nat.mod_eq_of_lt hcodeLt
    have hge : 2 ≤ 2 ^ f.K := two_le_pow_K f
    have hposCode : 2 ^ f.K - 1 - 1 = 2 ^ f.K - 2 := by omega
    have hneNanAfter : ¬ 2 ^ f.K - 2 = 2 ^ f.K - 1 := by omega
    simp [encodeValue, encodeValueNat, fromBits, toEReal, encodeNat, encodeSpecial,
      maxCode, p3109.n_to_p3109, hs, hd, hposCode, hneNanAfter]

lemma encodeValue_negInf_refines (hs : f.s = Signedness.signed) (hd : f.d = Domain.extended) :
    toEReal (fromBits (encodeValue (f := f) .negInf)) = (⊥ : EReal) := by
  have hpos : 0 < 2 ^ f.K := pow_pos (by decide : 0 < 2) f.K
  have hmod : (2 ^ f.K - 1) % 2 ^ f.K = 2 ^ f.K - 1 := by
    exact Nat.mod_eq_of_lt (Nat.sub_lt hpos (by decide))
  have hgt : 2 ^ (f.K - 1) < 2 ^ f.K - 1 := pow_pred_lt_pow_sub_one f
  have hltPosCode : 2 ^ (f.K - 1) - 1 < 2 ^ f.K - 1 := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) hgt
  have hneNan : ¬ 2 ^ f.K - 1 = 2 ^ (f.K - 1) := by omega
  have hnePos : ¬ 2 ^ f.K - 1 = 2 ^ (f.K - 1) - 1 := by omega
  simp [encodeValue, encodeValueNat, fromBits, toEReal, encodeNat, encodeSpecial,
    maxCode, p3109.n_to_p3109, hs, hd, hmod, hneNan, hnePos]

lemma encodeValue_zero_refines (e : Int) :
    toEReal (fromBits (encodeValue (f := f) (.finite 0 e))) =
      toEReal (Value.finite (f := f) 0 e) := by
  cases hs : f.s
  · have hneNan : ¬ 0 = 2 ^ (f.K - 1) := by
      exact ne_of_lt (zero_lt_pow_pred f)
    have hnePosInf : ¬ (0 = 2 ^ (f.K - 1) - 1 ∧ f.d = Domain.extended) := by
      intro h
      have hgt : 0 < 2 ^ (f.K - 1) - 1 := by
        have htwo : 2 ≤ 2 ^ (f.K - 1) := by
          rw [← pow_one 2]
          apply pow_le_pow_right₀ (by decide : 1 ≤ 2)
          exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Nat.lt_trans (by decide : 1 < 2) f.h_K))
        omega
      omega
    have hneNegInf : ¬ (0 = 2 ^ f.K - 1 ∧ f.d = Domain.extended) := by
      intro h
      have hpow : 2 ≤ 2 ^ f.K := two_le_pow_K f
      omega
    simp [encodeValue, encodeValueNat, finiteValueCode, fromBits, toEReal,
      p3109.n_to_p3109, p3109.n_to_p3109_finite, hs, hneNan, hnePosInf, hneNegInf]
  · have hneNan : ¬ 0 = 2 ^ f.K - 1 := by
      have hpow : 2 ≤ 2 ^ f.K := two_le_pow_K f
      omega
    have hnePosInf : ¬ (0 = 2 ^ f.K - 2 ∧ f.d = Domain.extended) := by
      intro h
      have hge : 4 ≤ 2 ^ f.K := four_le_pow_K f
      omega
    simp [encodeValue, encodeValueNat, finiteValueCode, fromBits, toEReal,
      p3109.n_to_p3109, p3109.n_to_p3109_finite, hs, hneNan, hnePosInf]

lemma encodeValue_finite_nonneg_normal_refines
    {m e : Int}
    (hs : f.s = Signedness.unsigned → 0 ≤ m)
    (hm : 0 ≤ m)
    (hn : @normal_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (.finite m e))) =
      toEReal (Value.finite (f := f) m e) := by
  have hhalf : 2 ^ (f.P - 1) ≤ m := by
    rcases hn with ⟨_, hle, _, _⟩
    simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat, abs_mul,
      Nat.abs_ofNat] at hle
    rw [abs_of_nonneg hm] at hle
    exact (_root_.le_two_mul_pow (f := f)).mp hle
  let code : Nat :=
    (m - 2 ^ (f.P - 1)).toNat +
      (e + f.P - 1 + f.bias).toNat * 2 ^ (f.P - 1)
  have hcodeLt : code < 2 ^ f.K := by
    dsimp [code]
    exact p3109.normal_encode_in_bound (f := f) hm hn
  have hfiniteCode : finiteValueCode f m e = code := by
    dsimp [finiteValueCode, code]
    have hmag : Int.natAbs m = m.toNat := by
      have hmagInt : (Int.natAbs m : Int) = m := Int.natAbs_of_nonneg hm
      have htoNatInt : (m.toNat : Int) = m := Int.toNat_of_nonneg hm
      exact Nat.cast_inj.mp (by rw [hmagInt, htoNatInt])
    rw [hmag]
    have hnotSub : ¬(e = f.emin_lsb ∧ m.toNat < 2 ^ (f.P - 1)) := by
      intro hsub
      have hlt : m < (2 ^ (f.P - 1) : Nat) := by
        have hltCast : (m.toNat : Int) < (2 ^ (f.P - 1) : Nat) := by
          exact_mod_cast hsub.2
        rw [Int.toNat_of_nonneg hm] at hltCast
        exact hltCast
      exact (not_lt_of_ge hhalf) hlt
    have hnotSign : ¬(f.s = Signedness.signed ∧ m < 0) := by
      intro hsign
      omega
    rw [if_neg hnotSub, if_neg hnotSign]
    have hmToNatNe : ¬m.toNat = 0 := by
      have hposHalf : (0 : Int) < 2 ^ (f.P - 1) := by positivity
      have hmpos : 0 < m := lt_of_lt_of_le hposHalf hhalf
      intro hzero
      have hzeroInt : (m.toNat : Int) = 0 := by exact_mod_cast hzero
      rw [Int.toNat_of_nonneg hm] at hzeroInt
      omega
    rw [if_neg hmToNatNe]
    have hsubToNat : m.toNat - 2 ^ (f.P - 1) = (m - 2 ^ (f.P - 1)).toNat := by
      have hpowLeNat : 2 ^ (f.P - 1) ≤ m.toNat := by
        have hcast : ((2 ^ (f.P - 1) : Nat) : Int) ≤ (m.toNat : Int) := by
          rw [Int.toNat_of_nonneg hm]
          exact hhalf
        exact_mod_cast hcast
      apply (Nat.cast_inj (R := Int)).mp
      have hsubNonneg : 0 ≤ m - (2 ^ (f.P - 1) : Int) := by omega
      calc
        ((m.toNat - 2 ^ (f.P - 1) : Nat) : Int)
            = (m.toNat : Int) - ((2 ^ (f.P - 1) : Nat) : Int) := by
                rw [Nat.cast_sub hpowLeNat]
        _ = m - ((2 ^ (f.P - 1) : Nat) : Int) := by
                rw [Int.toNat_of_nonneg hm]
        _ = m - (2 ^ (f.P - 1) : Int) := by
                norm_num
        _ = ((m - 2 ^ (f.P - 1)).toNat : Int) :=
                (Int.toNat_of_nonneg hsubNonneg).symm
    rw [hsubToNat]
  have hbits :
      encodeValue (f := f) (.finite m e) = ⟨code, hcodeLt⟩ := by
    apply Fin.ext
    simp [encodeValue, encodeValueNat, hfiniteCode, Nat.mod_eq_of_lt hcodeLt]
  calc
    toEReal (fromBits (encodeValue (f := f) (.finite m e)))
        = p3109.to_ereal (p3109.n_to_p3109 (f := f) (encodeValue (f := f) (.finite m e))) := by
          exact toEReal_fromBits (f := f) (encodeValue (f := f) (.finite m e))
    _ = p3109.to_ereal (p3109.p3109_finite m e hs (Or.inl hn)) := by
          rw [hbits]
          rw [p3109.normal_pos_surj (f := f) hs hn hm]
    _ = toEReal (Value.finite (f := f) m e) := by
          simp [toEReal, p3109.to_ereal]

lemma encodeValue_finite_nonneg_subnormal_refines
    {m e : Int}
    (hs : f.s = Signedness.unsigned → 0 ≤ m)
    (hm : 0 ≤ m)
    (hsub : @subnormal 2 f.to_format ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (.finite m e))) =
      toEReal (Value.finite (f := f) m e) := by
  rcases hsub with ⟨hbounded, hexp, hlt⟩
  have he : e = f.emin_lsb := by
    simpa [to_format, emin_lsb, emin] using hexp
  have hltHalfInt : m < (2 ^ (f.P - 1) : Int) := by
    simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat, abs_mul,
      Nat.abs_ofNat] at hlt
    rw [abs_of_nonneg hm] at hlt
    exact (_root_.two_mul_pow_lt (f := f)).mp hlt
  have hltHalfNat : m.toNat < 2 ^ (f.P - 1) := by
    have hcast : (m.toNat : Int) < ((2 ^ (f.P - 1) : Nat) : Int) := by
      rw [Int.toNat_of_nonneg hm]
      exact hltHalfInt
    exact_mod_cast hcast
  have hcodeLt : m.toNat < 2 ^ f.K := by
    exact p3109.subnormal_encode_in_bound (f := f) hm ⟨hbounded, hexp, hlt⟩
  have hfiniteCode : finiteValueCode f m e = m.toNat := by
    dsimp [finiteValueCode]
    have hmag : Int.natAbs m = m.toNat := by
      have hmagInt : (Int.natAbs m : Int) = m := Int.natAbs_of_nonneg hm
      have htoNatInt : (m.toNat : Int) = m := Int.toNat_of_nonneg hm
      exact Nat.cast_inj.mp (by rw [hmagInt, htoNatInt])
    rw [hmag]
    by_cases hzero : m.toNat = 0
    · simp [hzero]
    · have hsubBranch : e = f.emin_lsb ∧ m.toNat < 2 ^ (f.P - 1) := ⟨he, hltHalfNat⟩
      have hnotSign : ¬(f.s = Signedness.signed ∧ m < 0) := by
        intro hsign
        omega
      rw [if_neg hzero, if_pos hsubBranch, if_neg hnotSign]
  have hbits :
      encodeValue (f := f) (.finite m e) = ⟨m.toNat, hcodeLt⟩ := by
    apply Fin.ext
    simp [encodeValue, encodeValueNat, hfiniteCode, Nat.mod_eq_of_lt hcodeLt]
  calc
    toEReal (fromBits (encodeValue (f := f) (.finite m e)))
        = p3109.to_ereal (p3109.n_to_p3109 (f := f) (encodeValue (f := f) (.finite m e))) := by
          exact toEReal_fromBits (f := f) (encodeValue (f := f) (.finite m e))
    _ = p3109.to_ereal (p3109.p3109_finite m e hs (Or.inr ⟨hbounded, hexp, hlt⟩)) := by
          rw [hbits]
          rw [p3109.subnormal_pos_surj (f := f) hs ⟨hbounded, hexp, hlt⟩ hm]
    _ = toEReal (Value.finite (f := f) m e) := by
          simp [toEReal, p3109.to_ereal]

lemma encodeValue_finite_nonneg_canonical_refines
    {m e : Int}
    (hs : f.s = Signedness.unsigned → 0 ≤ m)
    (hm : 0 ≤ m)
    (hcan : @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (.finite m e))) =
      toEReal (Value.finite (f := f) m e) := by
  cases hcan with
  | inl hn =>
      exact encodeValue_finite_nonneg_normal_refines (f := f) hs hm hn
  | inr hsub =>
      exact encodeValue_finite_nonneg_subnormal_refines (f := f) hs hm hsub

lemma encodeValue_finite_neg_normal_refines
    {m e : Int}
    (hsSigned : f.s = Signedness.signed)
    (hm : m < 0)
    (hn : @normal_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (.finite m e))) =
      toEReal (Value.finite (f := f) m e) := by
  let pm : Int := -m
  have hpmNonneg : 0 ≤ pm := by dsimp [pm]; omega
  have hpmPos : 0 < pm := by dsimp [pm]; omega
  have hnPos : @normal_p3109 f ⟨pm, e⟩ := by
    dsimp [pm]
    simpa [fopp] using
      (normal_p3109_negate (f := f) (x := ⟨m, e⟩) hn)
  have hhalf : 2 ^ (f.P - 1) ≤ pm := by
    rcases hnPos with ⟨_, hle, _, _⟩
    simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat, abs_mul,
      Nat.abs_ofNat] at hle
    rw [abs_of_nonneg hpmNonneg] at hle
    exact (_root_.le_two_mul_pow (f := f)).mp hle
  let code : Nat :=
    (pm - 2 ^ (f.P - 1)).toNat +
      (e + f.P - 1 + f.bias).toNat * 2 ^ (f.P - 1)
  have hcodeLtSign : code < signBase f := by
    dsimp [code, signBase]
    exact p3109.normal_signed_encode_in_bound (f := f) hsSigned hpmNonneg hnPos
  have hcodeLt : code < 2 ^ f.K := by
    exact lt_of_lt_of_le hcodeLtSign (le_of_lt (pow_pred_lt_pow f))
  have hcodeNe : code ≠ 0 := by
    have hemin : f.emin_lsb ≤ e := by
      rcases hnPos with ⟨⟨_, hemin⟩, _, _, _⟩
      simpa [to_format, emin_lsb, emin] using hemin
    have hfieldOne : 1 ≤ e + f.P - 1 + f.bias := by
      simp [emin_lsb, emin] at hemin
      omega
    have hfieldNatOne : 1 ≤ (e + f.P - 1 + f.bias).toNat := by
      have hcast :
          (1 : Int) ≤ ((e + f.P - 1 + f.bias).toNat : Int) := by
        rw [Int.toNat_of_nonneg (by omega)]
        exact hfieldOne
      exact_mod_cast hcast
    have hhalfPos : 0 < 2 ^ (f.P - 1) := pow_pos (by decide : 0 < 2) _
    have hmulPos : 0 < (e + f.P - 1 + f.bias).toNat * 2 ^ (f.P - 1) :=
      Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 1) hfieldNatOne) hhalfPos
    exact Nat.ne_of_gt (lt_of_lt_of_le hmulPos (Nat.le_add_left _ _))
  have htotalLt : signBase f + code < 2 ^ f.K := by
    dsimp [signBase] at hcodeLtSign ⊢
    rewrite (occs := .pos [2]) [← Nat.sub_add_cancel (n := f.K) (m := 1) (one_le_K f)]
    simp [pow_add, mul_two]
    exact hcodeLtSign
  have hfiniteCode : finiteValueCode f m e = signBase f + code := by
    dsimp [finiteValueCode, code, pm]
    have hmag : Int.natAbs m = (-m).toNat := by
      have hmagInt : (Int.natAbs m : Int) = -m := by
        rw [← Int.natAbs_neg m]
        exact Int.natAbs_of_nonneg (by omega)
      have htoNatInt : ((-m).toNat : Int) = -m := Int.toNat_of_nonneg (by omega)
      exact Nat.cast_inj.mp (by rw [hmagInt, htoNatInt])
    rw [hmag]
    have hnotSub : ¬(e = f.emin_lsb ∧ (-m).toNat < 2 ^ (f.P - 1)) := by
      intro hsub
      have hlt : pm < (2 ^ (f.P - 1) : Nat) := by
        have hltCast : ((-m).toNat : Int) < (2 ^ (f.P - 1) : Nat) := by
          exact_mod_cast hsub.2
        dsimp [pm]
        rw [Int.toNat_of_nonneg (by omega)] at hltCast
        exact hltCast
      exact (not_lt_of_ge hhalf) hlt
    have hsign : f.s = Signedness.signed ∧ m < 0 := ⟨hsSigned, hm⟩
    rw [if_neg hnotSub, if_pos hsign]
    have hmToNatNe : ¬(-m).toNat = 0 := by
      intro hzero
      have hzeroInt : (((-m).toNat : Nat) : Int) = 0 := by exact_mod_cast hzero
      rw [Int.toNat_of_nonneg (by omega)] at hzeroInt
      omega
    rw [if_neg hmToNatNe]
    have hsubToNat :
        (-m).toNat - 2 ^ (f.P - 1) = (pm - 2 ^ (f.P - 1)).toNat := by
      have hpowLeNat : 2 ^ (f.P - 1) ≤ (-m).toNat := by
        have hcast : ((2 ^ (f.P - 1) : Nat) : Int) ≤ (((-m).toNat : Nat) : Int) := by
          rw [Int.toNat_of_nonneg (by omega)]
          exact hhalf
        exact_mod_cast hcast
      apply (Nat.cast_inj (R := Int)).mp
      have hsubNonneg : 0 ≤ pm - (2 ^ (f.P - 1) : Int) := by omega
      calc
        (((-m).toNat - 2 ^ (f.P - 1) : Nat) : Int)
            = (((-m).toNat : Nat) : Int) - ((2 ^ (f.P - 1) : Nat) : Int) := by
                rw [Nat.cast_sub hpowLeNat]
        _ = -m - ((2 ^ (f.P - 1) : Nat) : Int) := by
                rw [Int.toNat_of_nonneg (by omega)]
        _ = pm - (2 ^ (f.P - 1) : Int) := by
                dsimp [pm]
        _ = ((pm - 2 ^ (f.P - 1)).toNat : Int) :=
                (Int.toNat_of_nonneg hsubNonneg).symm
    rw [hsubToNat]
  have hbits :
      encodeValue (f := f) (.finite m e) = ⟨signBase f + code, htotalLt⟩ := by
    apply Fin.ext
    simp [encodeValue, encodeValueNat, hfiniteCode, Nat.mod_eq_of_lt htotalLt]
  have hsPos : f.s = Signedness.unsigned → 0 ≤ pm := by
    intro hsUnsigned
    rw [hsSigned] at hsUnsigned
    contradiction
  let posP : p3109 f := p3109.p3109_finite pm e hsPos (Or.inl hnPos)
  let negP : p3109 f :=
    p3109.p3109_finite m e
      (by
        intro hsUnsigned
        rw [hsSigned] at hsUnsigned
        contradiction)
      (Or.inl hn)
  have hposSurj :
      p3109.n_to_p3109 (f := f) ⟨code, hcodeLt⟩ = posP := by
    dsimp [posP, code]
    rw [p3109.normal_pos_surj (f := f) hsPos hnPos hpmNonneg]
  have hnegSurj :
      p3109.n_to_p3109 (f := f) ⟨signBase f + code, htotalLt⟩ = negP := by
    have hneg :=
      p3109.n_to_p_negate (f := f) code hsSigned hcodeNe hcodeLtSign
    calc
      p3109.n_to_p3109 (f := f) ⟨signBase f + code, htotalLt⟩
          = p3109.n_to_p3109 (f := f)
              ⟨code + 2 ^ (f.K - 1), by
                rewrite (occs := .pos [2])
                  [← Nat.sub_add_cancel (n := f.K) (m := 1) (one_le_K f)]
                simp [pow_add, mul_two]
                exact hcodeLtSign⟩ := by
                exact congrArg (fun b : Bits f => p3109.n_to_p3109 (f := f) b) (by
                  apply Fin.ext
                  simp [signBase, Nat.add_comm])
      _ = opp (p3109.n_to_p3109 (f := f) ⟨code, hcodeLt⟩) hsSigned := by
            exact hneg.symm
      _ = opp posP hsSigned := by
            rw [hposSurj]
      _ = negP := by
            dsimp [posP, negP, opp, pm]
            simp [hsSigned]
  calc
    toEReal (fromBits (encodeValue (f := f) (.finite m e)))
        = p3109.to_ereal (p3109.n_to_p3109 (f := f) (encodeValue (f := f) (.finite m e))) := by
          exact toEReal_fromBits (f := f) (encodeValue (f := f) (.finite m e))
    _ = p3109.to_ereal negP := by
          rw [hbits, hnegSurj]
    _ = toEReal (Value.finite (f := f) m e) := by
          dsimp [negP]
          simp [toEReal, p3109.to_ereal]

lemma encodeValue_finite_neg_subnormal_refines
    {m e : Int}
    (hsSigned : f.s = Signedness.signed)
    (hm : m < 0)
    (hsub : @subnormal 2 f.to_format ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (.finite m e))) =
      toEReal (Value.finite (f := f) m e) := by
  let pm : Int := -m
  have hpmNonneg : 0 ≤ pm := by dsimp [pm]; omega
  have hpmPos : 0 < pm := by dsimp [pm]; omega
  have hsubPos : @subnormal 2 f.to_format ⟨pm, e⟩ := by
    dsimp [pm]
    simpa using (subnormal_negate (β := 2) (format := f.to_format) (m := m) (e := e) hsub)
  rcases hsub with ⟨hbounded, hexp, hlt⟩
  rcases hsubPos with ⟨hboundedPos, hexpPos, hltPos⟩
  have he : e = f.emin_lsb := by
    simpa [to_format, emin_lsb, emin] using hexp
  let code : Nat := pm.toNat
  have hltHalfNat : pm.toNat < 2 ^ (f.P - 1) := by
    have hltHalfInt : pm < (2 ^ (f.P - 1) : Int) := by
      simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat, abs_mul,
        Nat.abs_ofNat] at hltPos
      rw [abs_of_nonneg hpmNonneg] at hltPos
      exact (_root_.two_mul_pow_lt (f := f)).mp hltPos
    have hcast : (pm.toNat : Int) < ((2 ^ (f.P - 1) : Nat) : Int) := by
      rw [Int.toNat_of_nonneg hpmNonneg]
      exact hltHalfInt
    exact_mod_cast hcast
  have hcodeLtSign : code < signBase f := by
    dsimp [code, signBase]
    exact p3109.subnormal_signed_encode_in_bound (f := f) hsSigned hpmNonneg
      ⟨hboundedPos, hexpPos, hltPos⟩
  have hcodeLt : code < 2 ^ f.K := by
    exact lt_of_lt_of_le hcodeLtSign (le_of_lt (pow_pred_lt_pow f))
  have hcodeNe : code ≠ 0 := by
    dsimp [code]
    intro hzero
    have hzeroInt : (pm.toNat : Int) = 0 := by exact_mod_cast hzero
    rw [Int.toNat_of_nonneg hpmNonneg] at hzeroInt
    omega
  have htotalLt : signBase f + code < 2 ^ f.K := by
    dsimp [signBase] at hcodeLtSign ⊢
    rewrite (occs := .pos [2]) [← Nat.sub_add_cancel (n := f.K) (m := 1) (one_le_K f)]
    simp [pow_add, mul_two]
    exact hcodeLtSign
  have hfiniteCode : finiteValueCode f m e = signBase f + code := by
    dsimp [finiteValueCode, code, pm]
    have hmag : Int.natAbs m = (-m).toNat := by
      have hmagInt : (Int.natAbs m : Int) = -m := by
        rw [← Int.natAbs_neg m]
        exact Int.natAbs_of_nonneg (by omega)
      have htoNatInt : ((-m).toNat : Int) = -m := Int.toNat_of_nonneg (by omega)
      exact Nat.cast_inj.mp (by rw [hmagInt, htoNatInt])
    rw [hmag]
    have hsubBranch : e = f.emin_lsb ∧ (-m).toNat < 2 ^ (f.P - 1) := by
      constructor
      · exact he
      · dsimp [pm] at hltHalfNat
        exact hltHalfNat
    have hsign : f.s = Signedness.signed ∧ m < 0 := ⟨hsSigned, hm⟩
    by_cases hzero : (-m).toNat = 0
    · have hzeroInt : (((-m).toNat : Nat) : Int) = 0 := by exact_mod_cast hzero
      rw [Int.toNat_of_nonneg (by omega)] at hzeroInt
      omega
    · rw [if_neg hzero, if_pos hsubBranch, if_pos hsign]
  have hbits :
      encodeValue (f := f) (.finite m e) = ⟨signBase f + code, htotalLt⟩ := by
    apply Fin.ext
    simp [encodeValue, encodeValueNat, hfiniteCode, Nat.mod_eq_of_lt htotalLt]
  have hsPos : f.s = Signedness.unsigned → 0 ≤ pm := by
    intro hsUnsigned
    rw [hsSigned] at hsUnsigned
    contradiction
  let posP : p3109 f := p3109.p3109_finite pm e hsPos (Or.inr ⟨hboundedPos, hexpPos, hltPos⟩)
  let negP : p3109 f :=
    p3109.p3109_finite m e
      (by
        intro hsUnsigned
        rw [hsSigned] at hsUnsigned
        contradiction)
      (Or.inr ⟨hbounded, hexp, hlt⟩)
  have hposSurj :
      p3109.n_to_p3109 (f := f) ⟨code, hcodeLt⟩ = posP := by
    dsimp [posP, code]
    rw [p3109.subnormal_pos_surj (f := f) hsPos ⟨hboundedPos, hexpPos, hltPos⟩ hpmNonneg]
  have hnegSurj :
      p3109.n_to_p3109 (f := f) ⟨signBase f + code, htotalLt⟩ = negP := by
    have hneg :=
      p3109.n_to_p_negate (f := f) code hsSigned hcodeNe hcodeLtSign
    calc
      p3109.n_to_p3109 (f := f) ⟨signBase f + code, htotalLt⟩
          = p3109.n_to_p3109 (f := f)
              ⟨code + 2 ^ (f.K - 1), by
                rewrite (occs := .pos [2])
                  [← Nat.sub_add_cancel (n := f.K) (m := 1) (one_le_K f)]
                simp [pow_add, mul_two]
                exact hcodeLtSign⟩ := by
                exact congrArg (fun b : Bits f => p3109.n_to_p3109 (f := f) b) (by
                  apply Fin.ext
                  simp [signBase, Nat.add_comm])
      _ = opp (p3109.n_to_p3109 (f := f) ⟨code, hcodeLt⟩) hsSigned := by
            exact hneg.symm
      _ = opp posP hsSigned := by
            rw [hposSurj]
      _ = negP := by
            dsimp [posP, negP, opp, pm]
            simp
  calc
    toEReal (fromBits (encodeValue (f := f) (.finite m e)))
        = p3109.to_ereal (p3109.n_to_p3109 (f := f) (encodeValue (f := f) (.finite m e))) := by
          exact toEReal_fromBits (f := f) (encodeValue (f := f) (.finite m e))
    _ = p3109.to_ereal negP := by
          rw [hbits, hnegSurj]
    _ = toEReal (Value.finite (f := f) m e) := by
          dsimp [negP]
          simp [toEReal, p3109.to_ereal]

lemma encodeValue_finite_neg_canonical_refines
    {m e : Int}
    (hsSigned : f.s = Signedness.signed)
    (hm : m < 0)
    (hcan : @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (.finite m e))) =
      toEReal (Value.finite (f := f) m e) := by
  cases hcan with
  | inl hn =>
      exact encodeValue_finite_neg_normal_refines (f := f) hsSigned hm hn
  | inr hsub =>
      exact encodeValue_finite_neg_subnormal_refines (f := f) hsSigned hm hsub

lemma encodeValue_finite_canonical_refines
    {m e : Int}
    (hs : f.s = Signedness.unsigned → 0 ≤ m)
    (hcan : @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (.finite m e))) =
      toEReal (Value.finite (f := f) m e) := by
  by_cases hm : m < 0
  · have hsSigned : f.s = Signedness.signed := by
      cases hsFormat : f.s with
      | signed => rfl
      | unsigned =>
          have hnonneg := hs hsFormat
          omega
    exact encodeValue_finite_neg_canonical_refines (f := f) hsSigned hm hcan
  · exact encodeValue_finite_nonneg_canonical_refines (f := f) hs (le_of_not_gt hm) hcan

lemma encodeValue_refines_of_canonical
    (x : Value f)
    (hpos : x = Value.posInf (f := f) → f.d = Domain.extended)
    (hneg : x = Value.negInf (f := f) → f.s = Signedness.signed ∧ f.d = Domain.extended)
    (hfin :
      ∀ m e, x = Value.finite (f := f) m e →
        (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) x)) = toEReal x := by
  cases x with
  | nan =>
      simpa [toEReal] using (encodeValue_nan_refines (f := f))
  | posInf =>
      simpa [toEReal] using (encodeValue_posInf_refines (f := f) (hpos rfl))
  | negInf =>
      have h := hneg rfl
      simpa [toEReal] using (encodeValue_negInf_refines (f := f) h.1 h.2)
  | finite m e =>
      have h := hfin m e rfl
      exact encodeValue_finite_canonical_refines (f := f) h.1 h.2

lemma project_value_refines_of_saturate_canonical
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hpos :
      saturate f (round (f := f) x rnd) sat rnd = Value.posInf (f := f) →
        f.d = Domain.extended)
    (hneg :
      saturate f (round (f := f) x rnd) sat rnd = Value.negInf (f := f) →
        f.s = Signedness.signed ∧ f.d = Domain.extended)
    (hfin :
      ∀ m e,
        saturate f (round (f := f) x rnd) sat rnd = Value.finite (f := f) m e →
          (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  let s : Value f := saturate f (round (f := f) x rnd) sat rnd
  have henc :
      toEReal (fromBits (encodeValue (f := f) s)) = toEReal s := by
    exact encodeValue_refines_of_canonical (f := f) s
      (by
        intro h
        exact hpos h)
      (by
        intro h
        exact hneg h)
      (by
        intro m e h
        exact hfin m e h)
  have hs :
      toEReal s =
        cerealToEReal (@p3109_format.saturate f
          (@round_to_precision f (toEReal x) rnd) sat rnd) := by
    dsimp [s]
    rw [saturate_refines (f := f) (round (f := f) x rnd) sat rnd]
    rw [round_refines (f := f) x rnd]
  calc
    toEReal (fromBits (project (f := f) x rnd sat))
        = toEReal (fromBits (encodeValue (f := f) s)) := by
            simp [project, s]
    _ = toEReal s := henc
    _ = cerealToEReal (@p3109_format.saturate f
          (@round_to_precision f (toEReal x) rnd) sat rnd) := hs
    _ = (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
          unfold p3109_format.p3109.project
          exact (encode_cerealToEReal _ _).symm

lemma project_rounded_value_refines_of_saturate_canonical
    (r : Value f)
    (target : EReal)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hr :
      toEReal r = @round_to_precision f target rnd)
    (hpos :
      saturate f r sat rnd = Value.posInf (f := f) →
        f.d = Domain.extended)
    (hneg :
      saturate f r sat rnd = Value.negInf (f := f) →
        f.s = Signedness.signed ∧ f.d = Domain.extended)
    (hfin :
      ∀ m e,
        saturate f r sat rnd = Value.finite (f := f) m e →
          (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (saturate f r sat rnd))) =
      (@p3109_format.p3109.project f target rnd sat) := by
  let s : Value f := saturate f r sat rnd
  have henc :
      toEReal (fromBits (encodeValue (f := f) s)) = toEReal s := by
    exact encodeValue_refines_of_canonical (f := f) s
      (by intro h; exact hpos h)
      (by intro h; exact hneg h)
      (by intro m e h; exact hfin m e h)
  have hs :
      toEReal s =
        cerealToEReal (@p3109_format.saturate f
          (@round_to_precision f target rnd) sat rnd) := by
    dsimp [s]
    rw [saturate_refines (f := f) r sat rnd]
    rw [hr]
  calc
    toEReal (fromBits (encodeValue (f := f) (saturate f r sat rnd)))
        = toEReal (fromBits (encodeValue (f := f) s)) := by
            simp [s]
    _ = toEReal s := henc
    _ = cerealToEReal (@p3109_format.saturate f
          (@round_to_precision f target rnd) sat rnd) := hs
    _ = (@p3109_format.p3109.project f target rnd sat) := by
          unfold p3109_format.p3109.project
          exact (encode_cerealToEReal _ _).symm

lemma project_rounded_value_refines_of_saturate_finite_canonical
    (r : Value f)
    (target : EReal)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hr :
      toEReal r = @round_to_precision f target rnd)
    (hfin :
      ∀ m e,
        saturate f r sat rnd = Value.finite (f := f) m e →
          (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (encodeValue (f := f) (saturate f r sat rnd))) =
      (@p3109_format.p3109.project f target rnd sat) := by
  apply project_rounded_value_refines_of_saturate_canonical
    (f := f) r target rnd sat hr
  · intro hpos
    have hcereal :
        cerealToEReal (@p3109_format.saturate f
          (@round_to_precision f target rnd) sat rnd) = (⊤ : EReal) := by
      have hs := saturate_refines (f := f) r sat rnd
      rw [hr] at hs
      rw [← hs, hpos]; rfl
    have hsem :
        @p3109_format.saturate f
          (@round_to_precision f target rnd) sat rnd = Sum.inl ⊤ :=
      cerealToEReal_eq_top hcereal
    exact p3109.saturate_ext_domain_ext (f := f)
      (@round_to_precision f target rnd) rnd sat (Or.inr hsem)
  · intro hneg
    have hcereal :
        cerealToEReal (@p3109_format.saturate f
          (@round_to_precision f target rnd) sat rnd) = (⊥ : EReal) := by
      have hs := saturate_refines (f := f) r sat rnd
      rw [hr] at hs
      rw [← hs, hneg]; rfl
    have hsem :
        @p3109_format.saturate f
          (@round_to_precision f target rnd) sat rnd = Sum.inl ⊥ :=
      cerealToEReal_eq_bot hcereal
    exact ⟨
      p3109.saturate_bot_signed (f := f)
        (@round_to_precision f target rnd) rnd sat hsem,
      p3109.saturate_ext_domain_ext (f := f)
        (@round_to_precision f target rnd) rnd sat (Or.inl hsem)⟩
  · exact hfin

lemma project_value_refines_of_saturate_finite_canonical
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hfin :
      ∀ m e,
        saturate f (round (f := f) x rnd) sat rnd = Value.finite (f := f) m e →
          (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  apply project_value_refines_of_saturate_canonical (f := f) x rnd sat
  · intro hpos
    have hcereal :
        cerealToEReal (@p3109_format.saturate f
          (@round_to_precision f (toEReal x) rnd) sat rnd) = (⊤ : EReal) := by
      have hs := saturate_refines (f := f) (round (f := f) x rnd) sat rnd
      rw [round_refines (f := f) x rnd] at hs
      rw [← hs, hpos]; rfl
    have hsem :
        @p3109_format.saturate f
          (@round_to_precision f (toEReal x) rnd) sat rnd = Sum.inl ⊤ :=
      cerealToEReal_eq_top hcereal
    exact p3109.saturate_ext_domain_ext (f := f)
      (@round_to_precision f (toEReal x) rnd) rnd sat (Or.inr hsem)
  · intro hneg
    have hcereal :
        cerealToEReal (@p3109_format.saturate f
          (@round_to_precision f (toEReal x) rnd) sat rnd) = (⊥ : EReal) := by
      have hs := saturate_refines (f := f) (round (f := f) x rnd) sat rnd
      rw [round_refines (f := f) x rnd] at hs
      rw [← hs, hneg]; rfl
    have hsem :
        @p3109_format.saturate f
          (@round_to_precision f (toEReal x) rnd) sat rnd = Sum.inl ⊥ :=
      cerealToEReal_eq_bot hcereal
    exact ⟨
      p3109.saturate_bot_signed (f := f)
        (@round_to_precision f (toEReal x) rnd) rnd sat hsem,
      p3109.saturate_ext_domain_ext (f := f)
        (@round_to_precision f (toEReal x) rnd) rnd sat (Or.inl hsem)⟩
  · exact hfin

lemma project_value_refines_of_round_finite_canonical
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hround :
      ∀ m e,
        inFiniteRange f (round (f := f) x rnd) = true →
        round (f := f) x rnd = Value.finite (f := f) m e →
        @canonical_p3109 f ⟨m, e⟩) :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  apply project_value_refines_of_saturate_finite_canonical (f := f) x rnd sat
  intro m e h
  exact saturate_round_finite_safe_canonical_of_round
    (f := f) x rnd sat hround h

lemma project_value_refines_of_roundFinite_nonzero_canonical
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hfinite_nonzero :
      ∀ m e, m ≠ 0 →
        ∀ m' e',
          inFiniteRange f (roundFinite f m e rnd) = true →
          roundFinite f m e rnd = Value.finite (f := f) m' e' →
          @canonical_p3109 f ⟨m', e'⟩) :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  apply project_value_refines_of_round_finite_canonical (f := f) x rnd sat
  intro m e hrange hround
  exact (round_finite_safe_canonical_of_finite_nonzero
    (f := f) rnd hfinite_nonzero x hrange hround).2

lemma project_value_refines_of_roundFinite_branch_canonical
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hcarry :
      ∀ m e, m ≠ 0 →
        ∀ m' e',
          inFiniteRange f (roundFinite f m e rnd) = true →
          roundFinite f m e rnd = Value.finite (f := f) m' e' →
          Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f →
          m' = (roundFiniteCore f m e rnd).rounded / 2 →
          e' = (roundFiniteCore f m e rnd).E + 1 →
          @canonical_p3109 f ⟨m', e'⟩)
    (hcore :
      ∀ m e, m ≠ 0 →
        ∀ m' e',
          inFiniteRange f (roundFinite f m e rnd) = true →
          roundFinite f m e rnd = Value.finite (f := f) m' e' →
          Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f →
          m' = (roundFiniteCore f m e rnd).rounded →
          e' = (roundFiniteCore f m e rnd).E →
          @canonical_p3109 f ⟨m', e'⟩) :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  apply project_value_refines_of_roundFinite_nonzero_canonical
    (f := f) x rnd sat
  intro m e hm m' e' hrange hfin
  exact roundFinite_output_canonical_of_branch_obligations
    (f := f) m e rnd hm hfin
    (hcarry m e hm m' e' hrange hfin)
    (hcore m e hm m' e' hrange hfin)

lemma project_value_refines_of_roundFinite_core_canonical
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hcore :
      ∀ m e, m ≠ 0 →
        ∀ m' e',
          inFiniteRange f (roundFinite f m e rnd) = true →
          roundFinite f m e rnd = Value.finite (f := f) m' e' →
          Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f →
          m' = (roundFiniteCore f m e rnd).rounded →
          e' = (roundFiniteCore f m e rnd).E →
          @canonical_p3109 f ⟨m', e'⟩) :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  apply project_value_refines_of_roundFinite_branch_canonical
    (f := f) x rnd sat
  · intro m e _hm m' e' hrange hfin hcarry hm' he'
    exact roundFinite_carry_canonical_of_inFiniteRange
      (f := f) m e rnd hrange hfin hcarry hm' he'
  · exact hcore

lemma project_value_refines_of_roundFinite_core_core_canonical
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hcore :
      ∀ m e, m ≠ 0 →
        ∀ m' e',
          inFiniteRange f (roundFinite f m e rnd) = true →
          roundFinite f m e rnd = Value.finite (f := f) m' e' →
          Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f →
          m' = (roundFiniteCore f m e rnd).rounded →
          e' = (roundFiniteCore f m e rnd).E →
          @canonical 2 f.to_format ⟨m', e'⟩) :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  apply project_value_refines_of_roundFinite_core_canonical
    (f := f) x rnd sat
  intro m e _hm m' e' hrange hfin hcoreNe hm' he'
  exact roundFinite_core_p3109_of_core_canonical
    (f := f) m e rnd hrange hfin hcoreNe hm' he'
    (hcore m e _hm m' e' hrange hfin hcoreNe hm' he')

lemma project_value_refines_of_roundFinite_core_low_exp
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hlow_exp :
      ∀ m e, m ≠ 0 →
        ∀ m' e',
          inFiniteRange f (roundFinite f m e rnd) = true →
          roundFinite f m e rnd = Value.finite (f := f) m' e' →
          Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f →
          m' = (roundFiniteCore f m e rnd).rounded →
          e' = (roundFiniteCore f m e rnd).E →
          |m'| < ((2 ^ (f.P - 1) : Nat) : Int) →
          e' = f.emin_lsb) :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  apply project_value_refines_of_roundFinite_core_canonical
    (f := f) x rnd sat
  intro m e hm m' e' hrange hfin hcoreNe hm' he'
  exact roundFinite_core_canonical_of_mag_split
    (f := f) m e rnd hm hrange hfin hcoreNe hm' he'
    (hlow_exp m e hm m' e' hrange hfin hcoreNe hm' he')

lemma project_value_refines
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (project (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f (toEReal x) rnd sat) := by
  apply project_value_refines_of_roundFinite_core_low_exp
    (f := f) x rnd sat
  intro m e hm m' e' _hrange _hfin _hcoreNe hm' he' hlow
  exact roundFinite_core_low_mag_exp_eq_emin_lsb
    (f := f) m e rnd hm hm' he' hlow

lemma projectEReal_refines
    (x : EReal)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    :
    toEReal (fromBits (projectEReal (f := f) x rnd sat)) =
      (@p3109_format.p3109.project f x rnd sat) := by
  unfold projectEReal
  simp [p3109.project, fromBits_toBits]

end Exec
end p3109_format

