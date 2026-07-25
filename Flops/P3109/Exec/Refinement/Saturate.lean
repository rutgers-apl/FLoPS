import Flops.P3109.Exec.Refinement.Canonical

namespace p3109_format
namespace Exec

lemma maxFiniteValue_refines :
    toEReal (maxFiniteValue f) = (p3109_format.max_finite (f := f) : EReal) := by
  rw [p3109_format.p3109.finite_to_ereal_eq _
    (p3109_format.p3109.max_is_finite (f := f))]
  rcases f with ⟨K, P, s, d, hK, hP⟩
  unfold maxFiniteValue p3109_format.max_finite
  by_cases hp : P = 1
  · simp [hp, toEReal, p3109_format.p3109.to_real]
  · cases s <;> cases d
    · simp [hp, toEReal, p3109_format.p3109.to_real, vnum,
        p3109_format.to_format]
    · simp [hp, toEReal, p3109_format.p3109.to_real, vnum,
        p3109_format.to_format]
    · simp [hp, toEReal, p3109_format.p3109.to_real, vnum,
        p3109_format.to_format]
    · by_cases hP2 : P = 2
      · simp [hp, hP2, toEReal, p3109_format.p3109.to_real, vnum,
          p3109_format.to_format]
      · simp [hp, hP2, toEReal, p3109_format.p3109.to_real, vnum,
          p3109_format.to_format]

lemma minFiniteValue_refines :
    toEReal (minFiniteValue f) = (p3109_format.min_finite (f := f) : EReal) := by
  rw [p3109_format.p3109.finite_to_ereal_eq _
    (p3109_format.p3109.min_is_finite (f := f))]
  rcases f with ⟨K, P, s, d, hK, hP⟩
  unfold minFiniteValue p3109_format.min_finite
  cases s
  · by_cases hp : P = 1
    · simp [hp, maxFiniteValue, p3109_format.max_finite, toEReal,
        p3109_format.p3109.to_real]
    · cases d
      · simp [hp, maxFiniteValue, p3109_format.max_finite, toEReal,
          p3109_format.p3109.to_real, vnum, p3109_format.to_format]
      · by_cases hP2 : P = 2
        · simp [hp, hP2, maxFiniteValue, p3109_format.max_finite, toEReal,
            p3109_format.p3109.to_real, vnum, p3109_format.to_format]
        · simp [hp, hP2, maxFiniteValue, p3109_format.max_finite, toEReal,
            p3109_format.p3109.to_real, vnum, p3109_format.to_format]
  · simp [toEReal, p3109_format.p3109.to_real]

lemma maxFinite_toEReal_ne_top :
    (p3109_format.max_finite (f := f)).to_ereal ≠ (⊤ : EReal) := by
  rw [p3109_format.p3109.finite_to_ereal_eq _
    (p3109_format.p3109.max_is_finite (f := f))]
  exact EReal.coe_ne_top _

lemma minFinite_toEReal_ne_bot :
    (p3109_format.min_finite (f := f)).to_ereal ≠ (⊥ : EReal) := by
  rw [p3109_format.p3109.finite_to_ereal_eq _
    (p3109_format.p3109.min_is_finite (f := f))]
  exact EReal.coe_ne_bot _

lemma top_not_in_finite_range :
    ¬ ((⊤ : EReal) ≤ (p3109_format.max_finite (f := f) : EReal) ∧
        (p3109_format.min_finite (f := f) : EReal) ≤ (⊤ : EReal)) := by
  intro h
  exact maxFinite_toEReal_ne_top (top_le_iff.mp h.1)

lemma bot_not_in_finite_range :
    ¬ ((⊥ : EReal) ≤ (p3109_format.max_finite (f := f) : EReal) ∧
        (p3109_format.min_finite (f := f) : EReal) ≤ (⊥ : EReal)) := by
  intro h
  exact minFinite_toEReal_ne_bot (le_bot_iff.mp h.2)

lemma inFiniteRange_semantic_refines (x : Value f) :
    inFiniteRange f x =
      decide (toEReal x ≤ (p3109_format.max_finite (f := f) : EReal) ∧
        (p3109_format.min_finite (f := f) : EReal) ≤ toEReal x) := by
  rw [inFiniteRange_refines, maxFiniteValue_refines, minFiniteValue_refines]
  by_cases hmin : (p3109_format.min_finite (f := f) : EReal) ≤ toEReal x
  · by_cases hmax : toEReal x ≤ (p3109_format.max_finite (f := f) : EReal)
    · simp [hmin, hmax]
    · simp [hmin, hmax]
  · simp [hmin]

lemma negOverflowValue_refines :
    toEReal (negOverflowValue f) =
      match f.s, f.d with
      | .signed, .extended => (⊥ : EReal)
      | _, _ => (p3109_format.min_finite (f := f) : EReal) := by
  unfold negOverflowValue
  cases hs : f.s <;> cases hd : f.d
  · simpa [hs, hd] using (minFiniteValue_refines (f := f))
  · simp [hs, hd, toEReal]
  · simpa [hs, hd] using (minFiniteValue_refines (f := f))
  · simpa [hs, hd] using (minFiniteValue_refines (f := f))

lemma posOverflowValue_refines :
    toEReal (posOverflowValue f) =
      match f.d with
      | .extended => (⊤ : EReal)
      | .finite => (p3109_format.max_finite (f := f) : EReal) := by
  unfold posOverflowValue
  cases hd : f.d
  · simpa [hd] using (maxFiniteValue_refines (f := f))
  · simp [hd, toEReal]

lemma valueLT_minFinite_refines (x : Value f) :
    valueLT x (minFiniteValue f) =
      decide (toEReal x < (p3109_format.min_finite (f := f) : EReal)) := by
  rw [valueLT_refines, minFiniteValue_refines]

lemma cerealToEReal_eq_top {s : EReal ⊕ Unit} (h : cerealToEReal s = ⊤) :
    s = Sum.inl ⊤ := by
  cases s with
  | inl e => rw [cerealToEReal_inl] at h; rw [h]
  | inr u => simp at h

lemma cerealToEReal_eq_bot {s : EReal ⊕ Unit} (h : cerealToEReal s = ⊥) :
    s = Sum.inl ⊥ := by
  cases s with
  | inl e => rw [cerealToEReal_inl] at h; rw [h]
  | inr u => simp at h

/-- Coercing an `encode`d value to `EReal` agrees with collapsing the underlying
    `EReal ⊕ Unit` via `cerealToEReal` (NaN ↦ 0 on both sides). -/
lemma encode_cerealToEReal (S : EReal ⊕ Unit) (h : S ∈ p3109.value_set f) :
    ((@p3109.encode f S h : p3109 f) : EReal) = cerealToEReal S := by
  cases S with
  | inr u =>
      cases u
      simp [p3109.encode, p3109.to_ereal, cerealToEReal]
  | inl e =>
      rw [cerealToEReal_inl]
      exact p3109.encode_to_ereal_local e h

/-
`Value.nan` (whose `toEReal` is `0`) is always in the finite range, since
    `min_finite ≤ 0 ≤ max_finite`.
-/
lemma inFiniteRange_nan : inFiniteRange f Value.nan = true := by
  rw [ inFiniteRange_semantic_refines ];
  -- Construct a zero finite p3109 value with `is_finite` and `(· : ℝ) = 0`.
  obtain ⟨z, hz_finite, hz_zero⟩ : ∃ z : p3109 f, z.is_finite ∧ (z : ℝ) = 0 := by
    use p3109.p3109_finite 0 f.emin_lsb (by
    exact fun _ => le_rfl) (Or.inr (by
    constructor;
    · constructor;
      · exact Int.ofNat_lt.mpr ( by exact pow_pos ( by decide ) _ );
      · repeat unfold p3109_format.emin_lsb; simp +decide [ p3109_format.to_format ] ;
    · simp +decide [ vnum ];
      unfold p3109_format.emin_lsb;
      unfold p3109_format.emin p3109_format.to_format; ring;
      unfold p3109_format.emin_lsb; ring;
      unfold p3109_format.emin; ring;))
    generalize_proofs at *;
    exact ⟨ by tauto, by simp +decide [ p3109.to_real ] ⟩;
  -- Apply the lemmas all_le_max_finite and min_finite_le_all to z.
  have h_max : (0 : ℝ) ≤ p3109_format.max_finite (f := f) := by
    have := p3109_format.p3109.all_le_max_finite z hz_finite; aesop;
  have h_min : p3109_format.min_finite (f := f) ≤ (0 : ℝ) := by
    exact hz_zero ▸ p3109_format.p3109.min_finite_le_all z hz_finite;
  convert decide_eq_true ?_;
  convert And.intro _ _;
  · convert EReal.coe_le_coe_iff.mpr h_max using 1;
    unfold p3109_format.max_finite;
    split_ifs <;> rfl;
  · convert EReal.coe_le_coe_iff.mpr h_min using 1;
    grind +suggestions

/-
Out-of-range `SatFinite` saturation refinement.
-/
lemma saturate_refines_out_satFinite (x : Value f) (rnd : RoundingMode)
    (hr : ¬ inFiniteRange f x = true) :
    toEReal (saturate f x SaturationMode.SatFinite rnd) =
      cerealToEReal (@p3109_format.saturate f (toEReal x)
        SaturationMode.SatFinite rnd) := by
  by_cases hlt : toEReal x < (p3109_format.min_finite (f := f) : EReal);
  · unfold saturate;
    simp +decide [ hr, hlt, valueLT_minFinite_refines ];
    rw [minFiniteValue_refines];
    unfold p3109_format.saturate;
    simp [hlt, not_le_of_gt hlt, cerealToEReal];
  · unfold p3109_format.saturate; simp_all +decide [ inFiniteRange_semantic_refines ] ;
    rw [ if_neg ( not_le_of_gt hr ), if_neg ( not_lt_of_ge hlt ) ];
    unfold saturate; simp +decide [ hr, hlt, inFiniteRange_semantic_refines, valueLT_minFinite_refines, minFiniteValue_refines, maxFiniteValue_refines ] ;
    rw [ if_neg ( not_le_of_gt hr ), if_neg ( not_lt_of_ge hlt ), maxFiniteValue_refines ]

/-
Out-of-range `SatPropagate` saturation refinement.
-/
lemma saturate_refines_out_satPropagate (x : Value f) (rnd : RoundingMode)
    (hr : ¬ inFiniteRange f x = true) :
    toEReal (saturate f x SaturationMode.SatPropagate rnd) =
      cerealToEReal (@p3109_format.saturate f (toEReal x)
        SaturationMode.SatPropagate rnd) := by
  cases x;
  · exact absurd inFiniteRange_nan hr;
  · have hsat :
        saturate f Value.posInf SaturationMode.SatPropagate rnd =
          posOverflowValue f := by
      unfold saturate posOverflowValue
      rw [if_neg hr]
    rw [hsat, posOverflowValue_refines]
    unfold p3109_format.saturate
    have htop :
        ¬ (toEReal (Value.posInf (f := f)) ≤
              (p3109_format.max_finite (f := f) : EReal) ∧
            (p3109_format.min_finite (f := f) : EReal) ≤
              toEReal (Value.posInf (f := f))) := by
      simpa using (top_not_in_finite_range (f := f))
    rw [if_neg htop]
    cases f.d <;> simp [toEReal, cerealToEReal]
  · unfold saturate;
    unfold p3109_format.saturate; simp +decide [ hr ] ;
    convert negOverflowValue_refines;
    cases f.s <;> cases f.d <;> simp +decide [ toEReal ];
    · cases h : min_finite.to_ereal <;> simp +decide [ h ] at hr ⊢;
    · split_ifs <;> simp_all +decide [ min_finite ];
    · split_ifs <;> simp_all +decide [ min_finite ];
  · convert saturate_refines_out_satFinite _ _ hr using 1;
    exact rnd

/-
`SatNone` saturation refinement, `posInf` input.
-/
lemma saturate_refines_out_satNone_posInf (rnd : RoundingMode) :
    toEReal (saturate f Value.posInf SaturationMode.SatNone rnd) =
      cerealToEReal (@p3109_format.saturate f (toEReal (Value.posInf (f := f)))
        SaturationMode.SatNone rnd) := by
  unfold p3109_format.saturate;
  rw [ if_neg ];
  · unfold saturate;
    cases rnd <;> cases f.s <;> cases f.d <;> simp +decide [ * ];
    all_goals simp +decide [ toEReal, cerealToEReal ];
    all_goals rw [ if_neg ];
    all_goals try exact maxFiniteValue_refines;
    all_goals simp +decide [ inFiniteRange, valueLE, minFiniteValue, maxFiniteValue ] ;
    all_goals split_ifs <;> simp +decide [ * ] ;
  · simp +decide [ toEReal, max_finite, min_finite ];
    split_ifs; all_goals exact ne_of_lt ( EReal.coe_lt_top _ )

/-
`SatNone` saturation refinement, `negInf` input.
-/
lemma saturate_refines_out_satNone_negInf (rnd : RoundingMode) :
    toEReal (saturate f Value.negInf SaturationMode.SatNone rnd) =
      cerealToEReal (@p3109_format.saturate f (toEReal (Value.negInf (f := f)))
        SaturationMode.SatNone rnd) := by
  have hSpec :
      ¬ (toEReal (Value.negInf (f := f)) ≤
            (p3109_format.max_finite (f := f) : EReal) ∧
          (p3109_format.min_finite (f := f) : EReal) ≤
            toEReal (Value.negInf (f := f))) := by
    simpa using (bot_not_in_finite_range (f := f))
  have hExec : ¬ inFiniteRange f Value.negInf = true := by
    rw [inFiniteRange_semantic_refines]
    simp [hSpec, minFinite_toEReal_ne_bot]
  unfold saturate p3109_format.saturate
  rw [if_neg hExec, if_neg hSpec]
  cases h : f.s <;> cases h' : f.d <;> cases rnd <;>
    simp +decide [h, h', negOverflowValue, cerealToEReal,
      minFiniteValue_refines, minFinite_toEReal_ne_bot]

/-
`SatNone` saturation refinement, finite input below the minimum.
-/
lemma saturate_refines_out_satNone_finite_below (m e : ℤ) (rnd : RoundingMode)
    (hlt : toEReal (Value.finite (f := f) m e) < (p3109_format.min_finite (f := f) : EReal)) :
    toEReal (saturate f (Value.finite m e) SaturationMode.SatNone rnd) =
      cerealToEReal (@p3109_format.saturate f (toEReal (Value.finite (f := f) m e))
        SaturationMode.SatNone rnd) := by
  have hltFinite :
      (((m : ℝ) * (2 ^ e : ℝ) : ℝ) : EReal) <
        (p3109_format.min_finite (f := f) : EReal) := by
    simpa using hlt
  have hltProduct :
      (((m : ℝ) : EReal) * (((2 : ℝ) ^ e : ℝ) : EReal)) <
        (p3109_format.min_finite (f := f) : EReal) := by
    rw [← EReal.coe_mul]
    exact hltFinite
  have hltProductRaw :
      (WithBot.some (WithTop.some (m : ℝ)) *
          WithBot.some (WithTop.some (((2 : ℝ) ^ e : ℝ)))) <
        (p3109_format.min_finite (f := f) : EReal) := by
    simpa [Real.toEReal] using hltProduct
  have hSpecRange :
      ¬ (toEReal (Value.finite (f := f) m e) ≤
            (p3109_format.max_finite (f := f) : EReal) ∧
          (p3109_format.min_finite (f := f) : EReal) ≤
            toEReal (Value.finite (f := f) m e)) := by
    rintro ⟨_, hmin⟩
    exact hlt.not_ge hmin
  have hExecRange : ¬ inFiniteRange f (Value.finite m e) = true := by
    rw [inFiniteRange_semantic_refines, decide_eq_true_eq]
    rintro ⟨_, hmin⟩
    exact hlt.not_ge hmin
  have hExecLT : valueLT (Value.finite (f := f) m e) (minFiniteValue f) = true := by
    rw [valueLT_minFinite_refines, decide_eq_true_eq]
    exact hlt
  unfold saturate p3109_format.saturate
  rw [if_neg hExecRange, if_pos hExecLT, if_neg hSpecRange]
  cases hs : f.s <;> cases hd : f.d <;> cases rnd <;>
    simp +decide [hExecLT, hltProductRaw, hs, hd,
      minFiniteValue_refines, negOverflowValue_refines, cerealToEReal, Real.toEReal]

/-
`SatNone` saturation refinement, finite input above the maximum.
-/
lemma saturate_refines_out_satNone_finite_above (m e : ℤ) (rnd : RoundingMode)
    (hr : ¬ inFiniteRange f (Value.finite m e) = true)
    (hge : ¬ toEReal (Value.finite (f := f) m e) < (p3109_format.min_finite (f := f) : EReal)) :
    toEReal (saturate f (Value.finite m e) SaturationMode.SatNone rnd) =
      cerealToEReal (@p3109_format.saturate f (toEReal (Value.finite (f := f) m e))
        SaturationMode.SatNone rnd) := by
  have hvlt : ¬ valueLT (Value.finite m e) (minFiniteValue f) = true := by
    rw [valueLT_minFinite_refines]; simpa using hge
  have htoe : toEReal (Value.finite (f := f) m e) = (((m : ℝ) * 2 ^ e : ℝ) : EReal) := rfl
  rw [htoe] at hge ⊢
  have hmax : (p3109_format.max_finite (f := f) : EReal) < (((m : ℝ) * 2 ^ e : ℝ) : EReal) := by
    contrapose! hr
    rw [inFiniteRange_semantic_refines, decide_eq_true_eq, htoe]
    exact ⟨hr, not_lt.mp hge⟩
  have hsemlead : ¬ ((((m : ℝ) * 2 ^ e : ℝ) : EReal) ≤ (p3109_format.max_finite (f := f) : EReal) ∧
      (p3109_format.min_finite (f := f) : EReal) ≤ (((m : ℝ) * 2 ^ e : ℝ) : EReal)) :=
    fun h => hmax.not_ge h.1
  unfold saturate p3109_format.saturate
  rw [if_neg hr, if_neg hsemlead]
  simp only [hvlt, if_false]
  rw [if_neg hge]
  rcases f with ⟨ _, _, _, _ ⟩;
  cases rnd <;> cases ‹Signedness› <;> cases ‹Domain›;
  all_goals repeat' rw [ if_neg hge ];
  all_goals try exact maxFiniteValue_refines;
  all_goals rfl

/-- Out-of-range `SatNone` saturation refinement. -/
lemma saturate_refines_out_satNone (x : Value f) (rnd : RoundingMode)
    (hr : ¬ inFiniteRange f x = true) :
    toEReal (saturate f x SaturationMode.SatNone rnd) =
      cerealToEReal (@p3109_format.saturate f (toEReal x)
        SaturationMode.SatNone rnd) := by
  cases x with
  | nan => exact absurd inFiniteRange_nan hr
  | posInf => exact saturate_refines_out_satNone_posInf rnd
  | negInf => exact saturate_refines_out_satNone_negInf rnd
  | finite m e =>
      by_cases hlt : toEReal (Value.finite (f := f) m e)
          < (p3109_format.min_finite (f := f) : EReal)
      · exact saturate_refines_out_satNone_finite_below m e rnd hlt
      · exact saturate_refines_out_satNone_finite_above m e rnd hr hlt

/-- Saturation refinement.  Because the executable `toEReal` collapses NaN to `0`,
    the semantic (`EReal ⊕ Unit`) result is compared through `cerealToEReal`. -/
lemma saturate_refines (x : Value f) (sat : SaturationMode) (rnd : RoundingMode) :
    toEReal (saturate f x sat rnd) =
      cerealToEReal (@p3109_format.saturate f (toEReal x) sat rnd) := by
  by_cases hr : inFiniteRange f x
  · unfold saturate
    rw [if_pos hr]
    have hrange := inFiniteRange_semantic_refines (f := f) x
    rw [hr] at hrange
    replace hrange := hrange.symm
    simp only [decide_eq_true_eq] at hrange
    rw [p3109_format.p3109.saturate_in_range (toEReal x) sat rnd hrange.2 hrange.1]
    rfl
  · cases sat with
    | SatFinite => exact saturate_refines_out_satFinite x rnd hr
    | SatPropagate => exact saturate_refines_out_satPropagate x rnd hr
    | SatNone => exact saturate_refines_out_satNone x rnd hr


lemma maxFiniteValue_ne_posInf : maxFiniteValue f ≠ Value.posInf (f := f) := by
  unfold maxFiniteValue
  split <;> simp

lemma maxFiniteValue_ne_negInf : maxFiniteValue f ≠ Value.negInf (f := f) := by
  unfold maxFiniteValue
  split <;> simp

lemma maxFiniteValue_ne_nan : maxFiniteValue f ≠ Value.nan (f := f) := by
  unfold maxFiniteValue
  split <;> simp

lemma minFiniteValue_ne_nan : minFiniteValue f ≠ Value.nan (f := f) := by
  unfold minFiniteValue
  split
  · simp
  · generalize maxFiniteValue f = mx
    cases mx <;> simp

lemma negOverflowValue_ne_nan : negOverflowValue f ≠ Value.nan (f := f) := by
  unfold negOverflowValue
  split
  · split <;> simp [minFiniteValue_ne_nan]
  · exact minFiniteValue_ne_nan

lemma posOverflowValue_ne_nan : posOverflowValue f ≠ Value.nan (f := f) := by
  unfold posOverflowValue
  split <;> simp [maxFiniteValue_ne_nan]

lemma minFiniteValue_ne_posInf : minFiniteValue f ≠ Value.posInf (f := f) := by
  unfold minFiniteValue
  split
  · simp
  · generalize maxFiniteValue f = mx
    cases mx <;> simp

lemma minFiniteValue_ne_negInf : minFiniteValue f ≠ Value.negInf (f := f) := by
  unfold minFiniteValue
  split
  · simp
  · generalize maxFiniteValue f = mx
    cases mx <;> simp

lemma posOverflowValue_eq_posInf_domain
    (h : posOverflowValue f = Value.posInf (f := f)) :
    f.d = Domain.extended := by
  unfold posOverflowValue at h
  split at h
  · assumption
  · exact False.elim ((maxFiniteValue_ne_posInf (f := f)) h)

lemma negOverflowValue_eq_negInf_signed_domain
    (h : negOverflowValue f = Value.negInf (f := f)) :
    f.s = Signedness.signed ∧ f.d = Domain.extended := by
  unfold negOverflowValue at h
  split at h
  · split at h
    · exact ⟨by assumption, by assumption⟩
    · exact False.elim ((minFiniteValue_ne_negInf (f := f)) h)
  · exact False.elim ((minFiniteValue_ne_negInf (f := f)) h)

lemma maxFiniteValue_finite_safe_canonical
    {m e : Int}
    (h : maxFiniteValue f = Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  unfold maxFiniteValue at h
  split at h
  · simp at h
    rcases h with ⟨rfl, rfl⟩
    constructor
    · intro _; omega
    · have _ := f.h_P
      left
      constructor
      · constructor
        · simp only [abs_one, vnum, to_format, Nat.cast_pow, Nat.cast_ofNat]
          rw [← pow_zero 2, pow_lt_pow_iff_right₀]
          · omega
          · simp only [Nat.one_lt_ofNat]
        · simp only [to_format, neg_neg]
          apply exp_check
      · constructor
        · expose_names
          simp only [vnum, to_format, h, pow_one, Nat.cast_ofNat, mul_one,
            Nat.abs_ofNat, le_refl]
        · simp only [le_refl, abs_one, forall_const, true_and]
          intro hbad
          exfalso
          omega
  · simp at h
    rcases h with ⟨rfl, rfl⟩
    let sub : Nat :=
      match f.P, f.s, f.d with
      | _, .signed, .finite => 1
      | _, .signed, .extended => 2
      | _, .unsigned, .finite => 2
      | 2, .unsigned, .extended => 1
      | _, .unsigned, .extended => 3
    change
      (f.s = Signedness.unsigned →
          0 ≤ (@vnum 2 f.to_format - sub : Int)) ∧
        @canonical_p3109 f ⟨(@vnum 2 f.to_format - sub : Int), f.emax_lsb⟩
    have hnonneg : (0 : Int) ≤ (@vnum 2 f.to_format - sub) := by
      simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat, Int.sub_nonneg]
      apply le_trans (b := (4 : Int))
      · simp only [sub]
        split <;> norm_num
      · have h4 : (4 : Int) = 2 ^ 2 := by simp only [Int.reducePow]
        rw [h4, pow_le_pow_iff_right₀]
        · have _ := f.h_P
          omega
        · simp only [Nat.one_lt_ofNat]
    constructor
    · intro _; exact hnonneg
    · left
      constructor
      · constructor
        · simp only
          rw [abs_of_nonneg hnonneg]
          simp only [sub_lt_self_iff, sub]
          split <;> norm_num
        · simp only [to_format, neg_neg]
          apply exp_check
      · constructor
        · simp only [abs_mul, Nat.abs_ofNat, le_refl, forall_const, true_and]
          rw [abs_of_nonneg hnonneg, mul_sub, two_mul]
          simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat, le_sub_iff_add_le,
            add_le_add_iff_left, sub]
          have _ := f.h_P
          split
          · apply le_trans (b := 2 ^ 2)
            · norm_num [sub]
            · change (2 : Int) ^ 2 ≤ (2 : Int) ^ f.P
              rw [pow_le_pow_iff_right₀]
              · omega
              · simp only [Nat.one_lt_ofNat]
          · apply le_trans (b := 2 ^ 2)
            · norm_num [sub]
            · change (2 : Int) ^ 2 ≤ (2 : Int) ^ f.P
              rw [pow_le_pow_iff_right₀]
              · omega
              · simp only [Nat.one_lt_ofNat]
          · apply le_trans (b := 2 ^ 2)
            · norm_num [sub]
            · change (2 : Int) ^ 2 ≤ (2 : Int) ^ f.P
              rw [pow_le_pow_iff_right₀]
              · omega
              · simp only [Nat.one_lt_ofNat]
          · apply le_trans (b := 2 ^ 2)
            · norm_num [sub]
            · change (2 : Int) ^ 2 ≤ (2 : Int) ^ f.P
              rw [pow_le_pow_iff_right₀]
              · omega
              · simp only [Nat.one_lt_ofNat]
          · apply le_trans (b := 2 ^ 3)
            · norm_num [sub]
            · change (2 : Int) ^ 3 ≤ (2 : Int) ^ f.P
              rw [pow_le_pow_iff_right₀]
              · expose_names
                have _ := f.h_P
                by_contra hlt
                have hp_le : f.P ≤ 2 := by omega
                interval_cases f.P <;> simp_all
              · simp only [Nat.one_lt_ofNat]
        · constructor
          · simp only [le_refl]
          · intro hpgt _
            have hv4 : (4 : Int) ≤ (@vnum 2 f.to_format : Int) := by
              simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat]
              have h4 : (4 : Int) = 2 ^ 2 := by norm_num
              rw [h4, pow_le_pow_iff_right₀]
              · omega
              · simp only [Nat.one_lt_ofNat]
            cases hs : f.s <;> cases hd : f.d
            · simp [hs, hd]
            · simp [hs, hd, sub]
              have hnn : 0 ≤ (@vnum 2 f.to_format : Int) - 2 := by omega
              rw [abs_of_nonneg hnn]
              omega
            · simp [hs, hd, sub]
              have hnn : 0 ≤ (@vnum 2 f.to_format : Int) - 2 := by omega
              rw [abs_of_nonneg hnn]
              omega
            · by_cases hp2 : f.P = 2
              · simp [hs, hd, hp2]
              · simp [hs, hd, hp2, sub]
                have hv8 : (8 : Int) ≤ (@vnum 2 f.to_format : Int) := by
                  simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat]
                  have h8 : (8 : Int) = 2 ^ 3 := by norm_num
                  rw [h8, pow_le_pow_iff_right₀]
                  · omega
                  · simp only [Nat.one_lt_ofNat]
                have hnn : 0 ≤ (@vnum 2 f.to_format : Int) - 3 := by omega
                rw [abs_of_nonneg hnn]
                omega

lemma maxFiniteValue_finite_bounds (f : p3109_format) :
    ∃ mx me,
      maxFiniteValue f = Value.finite (f := f) mx me ∧
        me = f.emax_lsb ∧
        ((2 ^ (f.P - 1) : Nat) : Int) ≤ mx ∧
        mx < ((2 ^ f.P : Nat) : Int) := by
  rcases f with ⟨K, P, s, d, hK, hP⟩
  unfold maxFiniteValue
  by_cases hp : P = 1
  · subst P
    simp
  · rw [dif_neg hp]
    cases s <;> cases d
    · refine ⟨((2 ^ P : Nat) : Int) - 1, _, rfl, rfl, ?_, ?_⟩
      · have hhalf : ((2 ^ (P - 1) : Nat) : Int) ≤ ((2 ^ P : Nat) : Int) - 1 := by
          have hPgt : 1 < P := by omega
          simpa using le_of_lt (p_pow_pred_lt_pow_sub_one
            ⟨K, P, Signedness.signed, Domain.finite, hK, hP⟩ hPgt)
        exact hhalf
      · change ((2 ^ P : Nat) : Int) - 1 < ((2 ^ P : Nat) : Int)
        omega
    · refine ⟨((2 ^ P : Nat) : Int) - 2, _, rfl, rfl, ?_, ?_⟩
      · have hhalf : ((2 ^ (P - 1) : Nat) : Int) ≤ ((2 ^ P : Nat) : Int) - 2 := by
          have hPgt : 1 < P := by omega
          have hsub1 := p_pow_pred_lt_pow_sub_one
            ⟨K, P, Signedness.signed, Domain.extended, hK, hP⟩ hPgt
          have hsub1' :
              ((2 ^ (P - 1) : Nat) : Int) < ((2 ^ P : Nat) : Int) - 1 := by
            simpa using hsub1
          omega
        exact hhalf
      · change ((2 ^ P : Nat) : Int) - 2 < ((2 ^ P : Nat) : Int)
        omega
    · refine ⟨((2 ^ P : Nat) : Int) - 2, _, rfl, rfl, ?_, ?_⟩
      · have hhalf : ((2 ^ (P - 1) : Nat) : Int) ≤ ((2 ^ P : Nat) : Int) - 2 := by
          have hPgt : 1 < P := by omega
          have hsub1 := p_pow_pred_lt_pow_sub_one
            ⟨K, P, Signedness.unsigned, Domain.finite, hK, hP⟩ hPgt
          have hsub1' :
              ((2 ^ (P - 1) : Nat) : Int) < ((2 ^ P : Nat) : Int) - 1 := by
            simpa using hsub1
          omega
        exact hhalf
      · change ((2 ^ P : Nat) : Int) - 2 < ((2 ^ P : Nat) : Int)
        omega
    · by_cases hp2 : P = 2
      · subst P
        simp [maxFiniteValue]
      · refine ⟨((2 ^ P : Nat) : Int) - 3, _, ?_, rfl, ?_, ?_⟩
        · simp [hp2]
        · have hhalf : ((2 ^ (P - 1) : Nat) : Int) ≤ ((2 ^ P : Nat) : Int) - 3 := by
            have hPgt : 2 < P := by omega
            have hsub2 := p_pow_pred_lt_pow_sub_two
              ⟨K, P, Signedness.unsigned, Domain.extended, hK, hP⟩ hPgt
            have hsub2' :
                ((2 ^ (P - 1) : Nat) : Int) < ((2 ^ P : Nat) : Int) - 2 := by
              simpa using hsub2
            omega
          exact hhalf
        · change ((2 ^ P : Nat) : Int) - 3 < ((2 ^ P : Nat) : Int)
          omega

lemma roundFinite_carry_pos_exp_le_of_inFiniteRange
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (hcarry : Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded / 2)
    (he' : e' = (roundFiniteCore f m e rnd).E + 1)
    (hmpos : 0 < m') :
    (roundFiniteCore f m e rnd).E + 1 ≤ f.emax_lsb := by
  by_contra hnot
  have hgt : f.emax_lsb < e' := by
    rw [he']
    omega
  obtain ⟨mx, me, hmax, hme, _, hmxLt⟩ := maxFiniteValue_finite_bounds f
  have hrparts := Bool.and_eq_true_iff.mp hrange
  have hhiBool := hrparts.2
  rw [hfin, hmax] at hhiBool
  have hnotExp : ¬ e' ≤ me := by
    rw [hme]
    omega
  simp [valueLE, finiteLE, hnotExp] at hhiBool
  have hle : m' * intPow2 (Int.toNat (e' - me)) ≤ mx := by
    exact hhiBool
  have hmag : Int.natAbs m' = 2 ^ (f.P - 1) := by
    rw [hm']
    exact roundFinite_carry_half_natAbs (f := f)
      (roundFiniteCore f m e rnd) hcarry
  have hm'eq : m' = ((2 ^ (f.P - 1) : Nat) : Int) := by
    have hcast : ((Int.natAbs m' : Nat) : Int) = m' :=
      Int.natAbs_of_nonneg (le_of_lt hmpos)
    rw [hmag] at hcast
    exact hcast.symm
  have hshiftPos : 1 ≤ Int.toNat (e' - me) := by
    have hdiff : (1 : Int) ≤ e' - me := by
      rw [hme]
      omega
    simpa using Int.toNat_le_toNat hdiff
  have hpow2 : (2 : Int) ≤ intPow2 (Int.toNat (e' - me)) := by
    unfold intPow2
    have hpowNat : 2 ^ 1 ≤ 2 ^ Int.toNat (e' - me) :=
      pow_le_pow_right₀ (by decide : 0 < 2) hshiftPos
    norm_num at hpowNat
    exact_mod_cast hpowNat
  have hPpow : ((2 ^ f.P : Nat) : Int) =
      2 * ((2 ^ (f.P - 1) : Nat) : Int) := by
    have hP : f.P = (f.P - 1) + 1 := by
      simpa [Nat.succ_eq_add_one] using
        (Nat.succ_pred_eq_of_pos f.h_P.1).symm
    rw [hP, pow_succ]
    norm_num [Nat.cast_mul, Nat.mul_comm]
  have hprodGe :
      ((2 ^ f.P : Nat) : Int) ≤ m' * intPow2 (Int.toNat (e' - me)) := by
    rw [hm'eq, hPpow]
    nlinarith [hpow2, show (0 : Int) ≤ ((2 ^ (f.P - 1) : Nat) : Int) by positivity]
  have hpowLeMx : ((2 ^ f.P : Nat) : Int) ≤ mx := le_trans hprodGe hle
  exact not_lt_of_ge hpowLeMx hmxLt

lemma roundFinite_carry_neg_exp_le_of_inFiniteRange
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (hcarry : Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded / 2)
    (he' : e' = (roundFiniteCore f m e rnd).E + 1)
    (hmneg : m' < 0) :
    (roundFiniteCore f m e rnd).E + 1 ≤ f.emax_lsb := by
  by_cases hsUnsigned : f.s = Signedness.unsigned
  · have hnonneg : 0 ≤ m' :=
      inFiniteRange_finite_unsigned_nonneg (f := f) hsUnsigned
        (by simpa [hfin] using hrange)
    omega
  · by_contra hnot
    have hgt : f.emax_lsb < e' := by
      rw [he']
      omega
    obtain ⟨mx, me, hmax, hme, _, hmxLt⟩ := maxFiniteValue_finite_bounds f
    have hmin : minFiniteValue f = Value.finite (f := f) (-mx) me := by
      unfold minFiniteValue
      rw [dif_neg hsUnsigned, hmax]
    have hrparts := Bool.and_eq_true_iff.mp hrange
    have hloBool := hrparts.1
    rw [hmin, hfin] at hloBool
    have hleExp : me ≤ e' := by
      rw [hme]
      omega
    simp [valueLE, finiteLE, hleExp] at hloBool
    have hle : -mx ≤ m' * intPow2 (Int.toNat (e' - me)) := by
      exact hloBool
    have hmag : Int.natAbs m' = 2 ^ (f.P - 1) := by
      rw [hm']
      exact roundFinite_carry_half_natAbs (f := f)
        (roundFiniteCore f m e rnd) hcarry
    have hm'eq : m' = -((2 ^ (f.P - 1) : Nat) : Int) := by
      have hcast : ((Int.natAbs (-m') : Nat) : Int) = -m' :=
        Int.natAbs_of_nonneg (by omega)
      rw [Int.natAbs_neg, hmag] at hcast
      omega
    have hshiftPos : 1 ≤ Int.toNat (e' - me) := by
      have hdiff : (1 : Int) ≤ e' - me := by
        rw [hme]
        omega
      simpa using Int.toNat_le_toNat hdiff
    have hpow2 : (2 : Int) ≤ intPow2 (Int.toNat (e' - me)) := by
      unfold intPow2
      have hpowNat : 2 ^ 1 ≤ 2 ^ Int.toNat (e' - me) :=
        pow_le_pow_right₀ (by decide : 0 < 2) hshiftPos
      norm_num at hpowNat
      exact_mod_cast hpowNat
    have hPpow : ((2 ^ f.P : Nat) : Int) =
        2 * ((2 ^ (f.P - 1) : Nat) : Int) := by
      have hP : f.P = (f.P - 1) + 1 := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.succ_pred_eq_of_pos f.h_P.1).symm
      rw [hP, pow_succ]
      norm_num [Nat.cast_mul, Nat.mul_comm]
    have hprodLe :
        m' * intPow2 (Int.toNat (e' - me)) ≤
          -((2 ^ f.P : Nat) : Int) := by
      rw [hm'eq, hPpow]
      nlinarith [hpow2,
        show (0 : Int) ≤ ((2 ^ (f.P - 1) : Nat) : Int) by positivity]
    have hminLePow : -mx ≤ -((2 ^ f.P : Nat) : Int) := le_trans hle hprodLe
    have hpowLtMin : -((2 ^ f.P : Nat) : Int) < -mx := by
      omega
    exact not_lt_of_ge hminLePow hpowLtMin

lemma roundFinite_carry_exp_le_of_inFiniteRange
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (hcarry : Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded / 2)
    (he' : e' = (roundFiniteCore f m e rnd).E + 1) :
    (roundFiniteCore f m e rnd).E + 1 ≤ f.emax_lsb := by
  rcases lt_trichotomy m' 0 with hmneg | hzero | hmpos
  · exact roundFinite_carry_neg_exp_le_of_inFiniteRange
      (f := f) m e rnd hrange hfin hcarry hm' he' hmneg
  · have hmag : Int.natAbs m' = 2 ^ (f.P - 1) := by
      rw [hm']
      exact roundFinite_carry_half_natAbs (f := f)
        (roundFiniteCore f m e rnd) hcarry
    rw [hzero] at hmag
    have hpowPos : 0 < 2 ^ (f.P - 1) := pow_pos (by decide : 0 < 2) _
    simp at hmag
    omega
  · exact roundFinite_carry_pos_exp_le_of_inFiniteRange
      (f := f) m e rnd hrange hfin hcarry hm' he' hmpos

lemma roundFinite_carry_canonical_of_inFiniteRange
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (hcarry : Int.natAbs (roundFiniteCore f m e rnd).rounded = vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded / 2)
    (he' : e' = (roundFiniteCore f m e rnd).E + 1) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  have hemax := roundFinite_carry_exp_le_of_inFiniteRange
    (f := f) m e rnd hrange hfin hcarry hm' he'
  exact roundFinite_carry_canonical_of_exp_le
    (f := f) m e rnd hcarry hm' he' hemax

lemma finite_half_mag_exp_le_of_inFiniteRange
    {m' e' : Int}
    (hrange : inFiniteRange f (Value.finite (f := f) m' e') = true)
    (hhalf :
      ((2 ^ (f.P - 1) : Nat) : Int) ≤ ((Int.natAbs m' : Nat) : Int)) :
    e' ≤ f.emax_lsb := by
  by_contra hnot
  have hgt : f.emax_lsb < e' := by omega
  obtain ⟨mx, me, hmax, hme, _, hmxLt⟩ := maxFiniteValue_finite_bounds f
  have hshiftPos : 1 ≤ Int.toNat (e' - me) := by
    have hdiff : (1 : Int) ≤ e' - me := by
      rw [hme]
      omega
    simpa using Int.toNat_le_toNat hdiff
  have hpow2 : (2 : Int) ≤ intPow2 (Int.toNat (e' - me)) := by
    unfold intPow2
    have hpowNat : 2 ^ 1 ≤ 2 ^ Int.toNat (e' - me) :=
      pow_le_pow_right₀ (by decide : 0 < 2) hshiftPos
    norm_num at hpowNat
    exact_mod_cast hpowNat
  have hPpow : ((2 ^ f.P : Nat) : Int) =
      2 * ((2 ^ (f.P - 1) : Nat) : Int) := by
    have hP : f.P = (f.P - 1) + 1 := by
      simpa [Nat.succ_eq_add_one] using
        (Nat.succ_pred_eq_of_pos f.h_P.1).symm
    rw [hP, pow_succ]
    norm_num [Nat.cast_mul, Nat.mul_comm]
  rcases lt_trichotomy m' 0 with hmneg | hzero | hmpos
  · by_cases hsUnsigned : f.s = Signedness.unsigned
    · have hnonneg : 0 ≤ m' :=
        inFiniteRange_finite_unsigned_nonneg (f := f) hsUnsigned hrange
      omega
    · have hmin : minFiniteValue f = Value.finite (f := f) (-mx) me := by
        unfold minFiniteValue
        rw [dif_neg hsUnsigned, hmax]
      have hrparts := Bool.and_eq_true_iff.mp hrange
      have hloBool := hrparts.1
      rw [hmin] at hloBool
      have hleExp : me ≤ e' := by
        rw [hme]
        omega
      simp [valueLE, finiteLE, hleExp] at hloBool
      have hle : -mx ≤ m' * intPow2 (Int.toNat (e' - me)) := by
        exact hloBool
      have hmLe : m' ≤ -((2 ^ (f.P - 1) : Nat) : Int) := by
        have hcast : ((Int.natAbs (-m') : Nat) : Int) = -m' :=
          Int.natAbs_of_nonneg (by omega)
        rw [Int.natAbs_neg] at hcast
        omega
      have hprodLe :
          m' * intPow2 (Int.toNat (e' - me)) ≤
            -((2 ^ f.P : Nat) : Int) := by
        rw [hPpow]
        nlinarith [hmLe, hpow2,
          show (0 : Int) ≤ ((2 ^ (f.P - 1) : Nat) : Int) by positivity]
      have hminLePow : -mx ≤ -((2 ^ f.P : Nat) : Int) := le_trans hle hprodLe
      have hpowLtMin : -((2 ^ f.P : Nat) : Int) < -mx := by
        omega
      exact not_lt_of_ge hminLePow hpowLtMin
  · rw [hzero] at hhalf
    have hpowPos : 0 < 2 ^ (f.P - 1) := pow_pos (by decide : 0 < 2) _
    have hpowPosInt : (0 : Int) < ((2 ^ (f.P - 1) : Nat) : Int) := by
      exact_mod_cast hpowPos
    simp at hhalf
    exact not_le_of_gt hpowPosInt hhalf
  · have hrparts := Bool.and_eq_true_iff.mp hrange
    have hhiBool := hrparts.2
    rw [hmax] at hhiBool
    have hnotExp : ¬ e' ≤ me := by
      rw [hme]
      omega
    simp [valueLE, finiteLE, hnotExp] at hhiBool
    have hle : m' * intPow2 (Int.toNat (e' - me)) ≤ mx := by
      exact hhiBool
    have hmGe : ((2 ^ (f.P - 1) : Nat) : Int) ≤ m' := by
      have hcast : ((Int.natAbs m' : Nat) : Int) = m' :=
        Int.natAbs_of_nonneg (le_of_lt hmpos)
      omega
    have hprodGe :
        ((2 ^ f.P : Nat) : Int) ≤
          m' * intPow2 (Int.toNat (e' - me)) := by
      rw [hPpow]
      nlinarith [hmGe, hpow2,
        show (0 : Int) ≤ ((2 ^ (f.P - 1) : Nat) : Int) by positivity]
    have hpowLeMx : ((2 ^ f.P : Nat) : Int) ≤ mx := le_trans hprodGe hle
    exact not_lt_of_ge hpowLeMx hmxLt

lemma finite_high_le_of_inFiniteRange_aligned
    {m e mx me : Int}
    (hrange : inFiniteRange f (Value.finite (f := f) m e) = true)
    (hmax : maxFiniteValue f = Value.finite (f := f) mx me)
    (he : e = me) :
    m ≤ mx := by
  subst e
  have hrparts := Bool.and_eq_true_iff.mp hrange
  have hhiBool := hrparts.2
  rw [hmax] at hhiBool
  simp [valueLE, finiteLE, intPow2] at hhiBool
  exact hhiBool

lemma finite_low_le_of_inFiniteRange_aligned
    {m e mn me : Int}
    (hrange : inFiniteRange f (Value.finite (f := f) m e) = true)
    (hmin : minFiniteValue f = Value.finite (f := f) mn me)
    (he : e = me) :
    mn ≤ m := by
  subst e
  have hrparts := Bool.and_eq_true_iff.mp hrange
  have hloBool := hrparts.1
  rw [hmin] at hloBool
  simp [valueLE, finiteLE, intPow2] at hloBool
  exact hloBool

lemma finite_emax_special_bound_of_inFiniteRange
    {m e : Int}
    (hrange : inFiniteRange f (Value.finite (f := f) m e) = true)
    (he : e = f.emax_lsb) :
    1 < f.P →
      match f.s, f.d with
      | .signed, .finite => True
      | .signed, .extended
      | .unsigned, .finite =>
          |m| < @vnum 2 f.to_format - 1
      | .unsigned, .extended =>
          match f.P with
          | 2 => True
          | _ => |m| < @vnum 2 f.to_format - 2 := by
  intro hPgt
  have hPne : ¬ f.P = 1 := by omega
  cases hs : f.s <;> cases hd : f.d
  · simp [hs, hd]
  · simp [hs, hd]
    let mx : Int := ((2 ^ f.P : Nat) : Int) - 2
    have hmax : maxFiniteValue f = Value.finite (f := f) mx f.emax_lsb := by
      unfold maxFiniteValue
      rw [dif_neg hPne]
      simp [mx, hs, hd]
    have hmin : minFiniteValue f = Value.finite (f := f) (-mx) f.emax_lsb := by
      unfold minFiniteValue
      have hnotUnsigned : ¬ f.s = Signedness.unsigned := by
        rw [hs]
        decide
      rw [dif_neg hnotUnsigned, hmax]
    have hhi : m ≤ mx :=
      finite_high_le_of_inFiniteRange_aligned (f := f) hrange hmax he
    have hlo : -mx ≤ m :=
      finite_low_le_of_inFiniteRange_aligned (f := f) hrange hmin he
    have habs : |m| ≤ mx := by
      exact abs_le.mpr ⟨hlo, hhi⟩
    have hmxlt : mx < @vnum 2 f.to_format - 1 := by
      dsimp [mx]
      simp [vnum, to_format]
    exact lt_of_le_of_lt habs hmxlt
  · simp [hs, hd]
    let mx : Int := ((2 ^ f.P : Nat) : Int) - 2
    have hmax : maxFiniteValue f = Value.finite (f := f) mx f.emax_lsb := by
      unfold maxFiniteValue
      rw [dif_neg hPne]
      simp [mx, hs, hd]
    have hhi : m ≤ mx :=
      finite_high_le_of_inFiniteRange_aligned (f := f) hrange hmax he
    have hnonneg : 0 ≤ m :=
      inFiniteRange_finite_unsigned_nonneg (f := f) (by simpa [hs]) hrange
    have habs : |m| = m := abs_of_nonneg hnonneg
    rw [habs]
    have hmxlt : mx < @vnum 2 f.to_format - 1 := by
      dsimp [mx]
      simp [vnum, to_format]
    exact lt_of_le_of_lt hhi hmxlt
  · by_cases hp2 : f.P = 2
    · simp [hs, hd, hp2]
    · simp [hs, hd, hp2]
      let mx : Int := ((2 ^ f.P : Nat) : Int) - 3
      have hmax : maxFiniteValue f = Value.finite (f := f) mx f.emax_lsb := by
        unfold maxFiniteValue
        rw [dif_neg hPne]
        simp [mx, hs, hd, hp2]
      have hhi : m ≤ mx :=
        finite_high_le_of_inFiniteRange_aligned (f := f) hrange hmax he
      have hnonneg : 0 ≤ m :=
        inFiniteRange_finite_unsigned_nonneg (f := f) (by simpa [hs]) hrange
      have habs : |m| = m := abs_of_nonneg hnonneg
      rw [habs]
      have hmxlt : mx < @vnum 2 f.to_format - 2 := by
        dsimp [mx]
        simp [vnum, to_format]
      exact lt_of_le_of_lt hhi hmxlt

lemma canonical_p3109_normal_of_natAbs_exp_range
    {m e : Int}
    (hlo :
      ((2 ^ (f.P - 1) : Nat) : Int) ≤ |m|)
    (hhi : |m| < ((2 ^ f.P : Nat) : Int))
    (hemin : f.emin_lsb ≤ e)
    (hemax : e ≤ f.emax_lsb)
    (hspecial :
      1 < f.P →
        e = f.emax_lsb →
          match f.s, f.d with
          | .signed, .finite => True
          | .signed, .extended
          | .unsigned, .finite =>
              |m| < @vnum 2 f.to_format - 1
          | .unsigned, .extended =>
              match f.P with
              | 2 => True
              | _ => |m| < @vnum 2 f.to_format - 2) :
    @canonical_p3109 f ⟨m, e⟩ := by
  left
  constructor
  · constructor
    · simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat]
      exact hhi
    · simpa [to_format] using hemin
  · constructor
    · simp only [vnum, to_format, Nat.cast_pow, Nat.cast_ofNat, abs_mul,
        Nat.abs_ofNat]
      have hmul : 2 * ((2 ^ (f.P - 1) : Nat) : Int) ≤ 2 * |m| := by
        nlinarith
      have hPpow : ((2 ^ f.P : Nat) : Int) =
          2 * ((2 ^ (f.P - 1) : Nat) : Int) := by
        have hP : f.P = (f.P - 1) + 1 := by
          simpa [Nat.succ_eq_add_one] using
            (Nat.succ_pred_eq_of_pos f.h_P.1).symm
        rw [hP, pow_succ]
        norm_num [Nat.cast_mul, Nat.mul_comm]
      calc
        ((2 ^ f.P : Nat) : Int) =
            2 * ((2 ^ (f.P - 1) : Nat) : Int) := hPpow
        _ ≤ 2 * |m| := hmul
    · exact ⟨hemax, hspecial⟩

lemma roundFinite_core_canonical_of_normal_bounds
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (_hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (he' : e' = (roundFiniteCore f m e rnd).E)
    (hlo :
      ((2 ^ (f.P - 1) : Nat) : Int) ≤ |m'|)
    (hhi : |m'| < ((2 ^ f.P : Nat) : Int))
    (hspecial :
      1 < f.P →
        e' = f.emax_lsb →
          match f.s, f.d with
          | .signed, .finite => True
          | .signed, .extended
          | .unsigned, .finite =>
              |m'| < @vnum 2 f.to_format - 1
          | .unsigned, .extended =>
              match f.P with
              | 2 => True
              | _ => |m'| < @vnum 2 f.to_format - 2) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  have hhalfNat :
      ((2 ^ (f.P - 1) : Nat) : Int) ≤ ((Int.natAbs m' : Nat) : Int) := by
    rw [Int.natCast_natAbs]
    exact hlo
  have hrangeFinite : inFiniteRange f (Value.finite (f := f) m' e') = true := by
    simpa [hfin] using hrange
  have hemax : e' ≤ f.emax_lsb :=
    finite_half_mag_exp_le_of_inFiniteRange (f := f) hrangeFinite hhalfNat
  have heminCore : f.emin_lsb ≤ (roundFiniteCore f m e rnd).E :=
    roundFiniteCore_E_ge_emin_lsb (f := f) m e rnd
  have hemin : f.emin_lsb ≤ e' := by
    rw [he']
    exact heminCore
  exact canonical_p3109_normal_of_natAbs_exp_range
    (f := f) hlo hhi hemin hemax hspecial

lemma roundFinite_core_canonical_of_normal_mag
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (he' : e' = (roundFiniteCore f m e rnd).E)
    (hlo :
      ((2 ^ (f.P - 1) : Nat) : Int) ≤ |m'|)
    (hhi : |m'| < ((2 ^ f.P : Nat) : Int)) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  exact roundFinite_core_canonical_of_normal_bounds
    (f := f) m e rnd hrange hfin hcore hm' he' hlo hhi
    (by
      intro hP hemax
      exact finite_emax_special_bound_of_inFiniteRange
        (f := f)
        (by simpa [hfin] using hrange)
        hemax hP)

lemma roundFinite_core_canonical_of_normal_mag_auto_hi
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hm : m ≠ 0)
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (he' : e' = (roundFiniteCore f m e rnd).E)
    (hlo :
      ((2 ^ (f.P - 1) : Nat) : Int) ≤ |m'|) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  exact roundFinite_core_canonical_of_normal_mag
    (f := f) m e rnd hrange hfin hcore hm' he' hlo
    (roundFinite_core_abs_lt_vnumPow (f := f) m e rnd hm hcore hm')

lemma roundFinite_core_canonical_of_subnormal_mag
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hm : m ≠ 0)
    (hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (he' : e' = (roundFiniteCore f m e rnd).E)
    (hlo :
      |m'| < ((2 ^ (f.P - 1) : Nat) : Int))
    (hemin : e' = f.emin_lsb) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  right
  exact (subnormal_eq (f := f.to_format) (x := ⟨m', e'⟩)).mp
    ⟨roundFinite_core_bounded
      (f := f) m e rnd hm hcore hm' he',
     by simpa [to_format, emin_lsb, emin] using hemin,
     by simpa [to_format] using hlo⟩

lemma roundFinite_core_canonical_of_mag_split
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hm : m ≠ 0)
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (he' : e' = (roundFiniteCore f m e rnd).E)
    (hlow_exp :
      |m'| < ((2 ^ (f.P - 1) : Nat) : Int) → e' = f.emin_lsb) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  by_cases hlow : |m'| < ((2 ^ (f.P - 1) : Nat) : Int)
  · exact roundFinite_core_canonical_of_subnormal_mag
      (f := f) m e rnd hm hcore hm' he' hlow (hlow_exp hlow)
  · exact roundFinite_core_canonical_of_normal_mag_auto_hi
      (f := f) m e rnd hm hrange hfin hcore hm' he'
      (le_of_not_gt hlow)

lemma canonical_p3109_of_canonical_inFiniteRange
    {m e : Int}
    (hrange : inFiniteRange f (Value.finite (f := f) m e) = true)
    (hcan : @canonical 2 f.to_format ⟨m, e⟩) :
    @canonical_p3109 f ⟨m, e⟩ := by
  have hcan' : @canonical' f.to_format ⟨m, e⟩ := by
    exact (canonical_eq (f := f.to_format) (x := ⟨m, e⟩)).mpr hcan
  rcases hcan' with hn | hsub
  · rcases hn with ⟨hbounded, hlo'⟩
    have hlo : ((2 ^ (f.P - 1) : Nat) : Int) ≤ |m| := by
      simpa [to_format] using hlo'
    have hhi : |m| < ((2 ^ f.P : Nat) : Int) := by
      simpa [bounded_float, vnum, to_format] using hbounded.1
    have hemin : f.emin_lsb ≤ e := by
      simpa [bounded_float, to_format] using hbounded.2
    have hhalfNat :
        ((2 ^ (f.P - 1) : Nat) : Int) ≤ ((Int.natAbs m : Nat) : Int) := by
      rw [Int.natCast_natAbs]
      exact hlo
    have hemax : e ≤ f.emax_lsb :=
      finite_half_mag_exp_le_of_inFiniteRange (f := f) hrange hhalfNat
    exact canonical_p3109_normal_of_natAbs_exp_range
      (f := f) hlo hhi hemin hemax
      (by
        intro hP hemaxEq
        exact finite_emax_special_bound_of_inFiniteRange
          (f := f) hrange hemaxEq hP)
  · right
    exact (subnormal_eq (f := f.to_format) (x := ⟨m, e⟩)).mp hsub

lemma roundFinite_core_p3109_of_core_canonical
    (m e : Int)
    (rnd : RoundingMode)
    {m' e' : Int}
    (hrange : inFiniteRange f (roundFinite f m e rnd) = true)
    (hfin : roundFinite f m e rnd = Value.finite (f := f) m' e')
    (_hcore : Int.natAbs (roundFiniteCore f m e rnd).rounded ≠ vnumPow f)
    (_hm' : m' = (roundFiniteCore f m e rnd).rounded)
    (_he' : e' = (roundFiniteCore f m e rnd).E)
    (hcan : @canonical 2 f.to_format ⟨m', e'⟩) :
    @canonical_p3109 f ⟨m', e'⟩ := by
  exact canonical_p3109_of_canonical_inFiniteRange
    (f := f)
    (by simpa [hfin] using hrange)
    hcan

lemma minFiniteValue_finite_safe_canonical
    {m e : Int}
    (h : minFiniteValue f = Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  unfold minFiniteValue at h
  split at h
  · simp at h
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
  · generalize hmx : maxFiniteValue f = mx at h
    cases mx with
    | nan => exact False.elim ((maxFiniteValue_ne_nan (f := f)) hmx)
    | posInf => exact False.elim ((maxFiniteValue_ne_posInf (f := f)) hmx)
    | negInf => exact False.elim ((maxFiniteValue_ne_negInf (f := f)) hmx)
    | finite mxm mxe =>
        simp at h
        rcases h with ⟨rfl, rfl⟩
        have hmax := maxFiniteValue_finite_safe_canonical (f := f) hmx
        constructor
        · intro hs
          expose_names
          contradiction
        · simpa [fopp] using
            (canonical_p3109_negate (f := f) (x := ⟨mxm, mxe⟩) hmax.2)

lemma posOverflowValue_finite_safe_canonical
    {m e : Int}
    (h : posOverflowValue f = Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  unfold posOverflowValue at h
  split at h
  · simp at h
  · exact maxFiniteValue_finite_safe_canonical (f := f) h

lemma negOverflowValue_finite_safe_canonical
    {m e : Int}
    (h : negOverflowValue f = Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  unfold negOverflowValue at h
  split at h
  · split at h
    · simp at h
    · exact minFiniteValue_finite_safe_canonical (f := f) h
  · exact minFiniteValue_finite_safe_canonical (f := f) h

lemma saturate_finite_safe_canonical_of_input
    (x : Value f)
    (sat : SaturationMode)
    (rnd : RoundingMode)
    (hx :
      ∀ m e, inFiniteRange f x = true → x = Value.finite (f := f) m e →
        @canonical_p3109 f ⟨m, e⟩)
    {m e : Int}
    (h : saturate f x sat rnd = Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  cases sat with
  | SatFinite =>
      by_cases hr : inFiniteRange f x
      · unfold saturate at h
        simp [hr] at h
        constructor
        · intro hs
          exact inFiniteRange_finite_unsigned_nonneg (f := f) hs
            (by simpa [h] using hr)
        · exact hx m e hr h
      · unfold saturate at h
        simp [hr] at h
        by_cases hlo : valueLT x (minFiniteValue f)
        · simp [hlo] at h
          exact minFiniteValue_finite_safe_canonical (f := f) h
        · simp [hlo] at h
          exact maxFiniteValue_finite_safe_canonical (f := f) h
  | SatPropagate =>
      by_cases hr : inFiniteRange f x
      · unfold saturate at h
        simp [hr] at h
        constructor
        · intro hs
          exact inFiniteRange_finite_unsigned_nonneg (f := f) hs
            (by simpa [h] using hr)
        · exact hx m e hr h
      · cases x with
        | nan =>
            unfold saturate at h
            simp [hr] at h
            by_cases hlo : valueLT Value.nan (minFiniteValue f)
            · simp [hlo] at h
              exact minFiniteValue_finite_safe_canonical (f := f) h
            · simp [hlo] at h
              exact maxFiniteValue_finite_safe_canonical (f := f) h
        | posInf =>
            unfold saturate at h
            simp [hr] at h
            split at h
            · simp at h
            · exact maxFiniteValue_finite_safe_canonical (f := f) h
        | negInf =>
            unfold saturate at h
            simp [hr] at h
            exact negOverflowValue_finite_safe_canonical (f := f) h
        | finite xm xe =>
            unfold saturate at h
            simp [hr] at h
            by_cases hlo : valueLT (Value.finite (f := f) xm xe) (minFiniteValue f)
            · simp [hlo] at h
              exact minFiniteValue_finite_safe_canonical (f := f) h
            · simp [hlo] at h
              exact maxFiniteValue_finite_safe_canonical (f := f) h
  | SatNone =>
  unfold saturate at h;
  rcases x with ( _ | _ | _ | x );
  · contrapose! h;
    split_ifs <;> simp +decide [ inFiniteRange_nan ] at *;
  · -- posInf: saturate = if f.d = extended then posInf else maxFiniteValue f
    split_ifs at h with h1 h2 <;>
      first
        | exact maxFiniteValue_finite_safe_canonical h
        | exact Value.noConfusion h;
  · have hExec : ¬ inFiniteRange f Value.negInf = true := by
      rw [inFiniteRange_semantic_refines]
      simp [bot_not_in_finite_range (f := f), minFinite_toEReal_ne_bot]
    rw [if_neg hExec] at h
    cases hsign : f.s <;> cases hdomain : f.d <;>
      simp_all +decide [hsign, hdomain]
  · by_cases hr : inFiniteRange f ( Value.finite x ‹_› ) <;> simp +decide [ hr ] at h ⊢;
    · have := inFiniteRange_finite_unsigned_nonneg ( f := f ) ( m := x ) ( e := ‹_› ) ; aesop;
    · split_ifs at h;
      · cases rnd <;> cases hsign : f.s <;> cases hdomain : f.d <;>
          simp +decide [hsign, hdomain] at h
        all_goals
          simpa [hsign] using (minFiniteValue_finite_safe_canonical (f := f) h)
      · cases rnd <;> cases hsign : f.s <;> cases hdomain : f.d <;>
          simp +decide [hsign, hdomain] at h
        all_goals
          simpa [hsign] using (maxFiniteValue_finite_safe_canonical (f := f) h)

lemma saturate_round_finite_safe_canonical_of_round
    (x : Value f)
    (rnd : RoundingMode)
    (sat : SaturationMode)
    (hround :
      ∀ m e,
        inFiniteRange f (round (f := f) x rnd) = true →
        round (f := f) x rnd = Value.finite (f := f) m e →
        @canonical_p3109 f ⟨m, e⟩)
    {m e : Int}
    (h :
      saturate f (round (f := f) x rnd) sat rnd =
        Value.finite (f := f) m e) :
    (f.s = Signedness.unsigned → 0 ≤ m) ∧ @canonical_p3109 f ⟨m, e⟩ := by
  exact saturate_finite_safe_canonical_of_input
    (f := f) (x := round (f := f) x rnd) sat rnd hround h

end Exec
end p3109_format
