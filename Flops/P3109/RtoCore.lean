/-
  Core RTO (Round-To-Odd) properties for `to_odd` and `round_fp`.
  These are independent of the P3109 format specifics.
-/
import Flops.Core.RoundOp

variable {format : Format}

set_option maxHeartbeats 400000

/-- When P > 1, `to_odd` always produces an odd integer for non-integer input. -/
lemma to_odd_odd_of_fract_ne_zero (e : ℤ) (m : ℝ) :
    1 < format.precision →
    Int.fract m ≠ 0 →
    Odd (@to_odd format e m) := by
  intros h1 h2; unfold to_odd; split_ifs <;> simp_all +decide [ parity_simps ] ;
  rw [ ceil_eq_floor_add_one_of_fract_ne0 ] <;> simp_all +decide [ parity_simps ]

/-- When P > 1, `|to_odd e m| < vnum` for non-integer m with |m| < vnum.
    This means `round_fp_ne0` doesn't apply the vnum adjustment. -/
lemma to_odd_abs_lt_vnum (e : ℤ) (m : ℝ) :
    1 < format.precision →
    Int.fract m ≠ 0 →
    |m| < @vnum 2 format →
    |@to_odd format e m| < @vnum 2 format := by
  unfold to_odd;
  split_ifs <;> simp_all +decide [ abs_lt ];
  · intro h1 h2 h3 h4; constructor <;> contrapose! h2;
    · rw [ Int.le_iff_lt_or_eq ] at h2;
      cases h2 <;> simp_all +decide [ Int.floor_lt ];
      · linarith;
      · exact absurd ‹Odd vnum› ( by unfold vnum; norm_num [ Nat.even_pow ] ; linarith );
    · rw [ Int.le_floor ] at h2 ; norm_cast at *;
      linarith;
  · intro h1 h2 h3 h4; constructor <;> contrapose! h2;
    · rw [ Int.ceil_le ] at h2;
      norm_num +zetaDelta at *;
      grind;
    · contrapose! h2;
      refine' lt_of_le_of_ne _ _;
      · exact Int.ceil_le.mpr ( mod_cast h4.le );
      · intro h; simp_all +decide [ Int.ceil_eq_iff ] ;
        norm_num [ show ⌊m⌋ = vnum - 1 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ] at *;
        exact absurd ‹Odd vnum› ( by unfold vnum; norm_num [ Nat.even_pow ] ; linarith )

/-
fract sm ≠ 0 implies fract |sm| ≠ 0 (non-integer is preserved by abs)
-/
lemma fract_abs_ne_zero_of_fract_ne_zero (m : ℝ) :
    Int.fract m ≠ 0 →
    Int.fract |m| ≠ 0 := by
      cases abs_cases m <;> simp +decide [ * ]

/-- Scaled mantissa has nonzero fractional part when x is not representable. -/
lemma fract_scaled_mantissa_ne_zero_of_not_representable (x : ℝ) :
    x ≠ 0 →
    (@round_fp format (@to_odd format) x : ℝ) ≠ x →
    Int.fract (@scaled_mantissa format x) ≠ 0 := by
  refine' fun hx hx' hx'' => hx' _;
  obtain ⟨n, hn⟩ : ∃ n : ℤ, @scaled_mantissa format x = n := by
    exact ⟨ _, eq_of_sub_eq_zero hx'' ⟩;
  have h_round_fp : @round_fp format (@to_odd format) x = (x : ℝ) := by
    have h_bounded : @bounded_float 2 format ⟨n, @fexp_real' format x⟩ := by
      have h_bounded : |n| < @vnum 2 format := by
        have h_bounded : |(n : ℝ)| < 2 ^ format.precision := by
          exact hn ▸ scaled_mantissa_bounded x;
        norm_cast at h_bounded;
      exact ⟨ h_bounded, by exact le_max_right _ _ ⟩
    convert round_fp_bounded_self (@to_odd format) _ h_bounded;
    · unfold to_real scaled_mantissa at *;
      convert congr_arg ( · * ( 2 : ℝ ) ^ ( @fexp_real' format x ) ) hn using 1 ; ring;
      norm_num [ zpow_ne_zero ];
    · unfold to_real scaled_mantissa at *;
      convert congr_arg ( · * ( 2 : ℝ ) ^ ( @fexp_real' format x ) ) hn using 1 ; ring;
      norm_num [ zpow_ne_zero ];
  exact h_round_fp

/-
round_fp to_odd produces odd fnum when P > 1 and x is non-representable and nonzero.
-/
theorem round_fp_to_odd_fnum_odd_P_gt_1 (x : ℝ) :
    1 < format.precision →
    x ≠ 0 →
    (@round_fp format (@to_odd format) x : ℝ) ≠ x →
    Odd (@round_fp format (@to_odd format) x).fnum := by
      intro h1 h2 h3
      have h_fract_sm : Int.fract (@scaled_mantissa format x) ≠ 0 := by
        exact fract_scaled_mantissa_ne_zero_of_not_representable x h2 h3
      have h_abs_sm : |@scaled_mantissa format x| < @vnum 2 format := by
        convert scaled_mantissa_bounded x using 1;
        unfold vnum; norm_num;
      have h_abs_odd : |@to_odd format (@fexp_real' format x) (@scaled_mantissa format x)| < @vnum 2 format := by
        exact to_odd_abs_lt_vnum (fexp_real' x) (scaled_mantissa x) h1 h_fract_sm h_abs_sm
      have h_odd : Odd (@to_odd format (@fexp_real' format x) (@scaled_mantissa format x)) := by
        exact to_odd_odd_of_fract_ne_zero (fexp_real' x) (scaled_mantissa x) h1 h_fract_sm;
      unfold round_fp; simp +decide [ round_fp_ne0, h2 ] ;
      grind

/-
For P = 1, to_odd always produces a value in {-2, -1, 1, 2} for nonzero input
    with non-integer absolute value.
-/
lemma to_odd_P1_in_set (e : ℤ) (m : ℝ) :
    format.precision = 1 →
    m ≠ 0 →
    Int.fract |m| ≠ 0 →
    |m| < @vnum 2 format →
    @to_odd format e m = 1 ∨ @to_odd format e m = -1 ∨
    @to_odd format e m = 2 ∨ @to_odd format e m = -2 := by
      unfold to_odd;
      unfold vnum; simp +decide [ * ] ;
      intro h1 h2 h3 h4; split_ifs <;> simp_all +decide ;
      · norm_num [ show ⌊|m|⌋ = 1 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ];
      · norm_num [ show ⌊|m|⌋ = 1 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ];
      · norm_num [ Int.ceil_eq_iff ];
        grind +revert;
      · rcases eq_or_ne ⌈|m|⌉ 1 <;> rcases eq_or_ne ⌈|m|⌉ 2 <;> simp_all +decide [ Int.ceil_eq_iff ];
        grind

/-
For P = 1, round_fp_ne0 with to_odd always produces fnum ∈ {-1, 1}.
-/
lemma round_fp_ne0_to_odd_P1_fnum (x : ℝ) :
    format.precision = 1 →
    x ≠ 0 →
    Int.fract (@scaled_mantissa format x) ≠ 0 →
    (@round_fp_ne0 format (@to_odd format) x).fnum = 1 ∨
    (@round_fp_ne0 format (@to_odd format) x).fnum = -1 := by
      intro h₀ h₁ h₂;
      -- Apply the lemma to_odd_P1_in_set to get the possible values of to_odd.
      have h_to_odd : @to_odd format (@fexp_real' format x) (@scaled_mantissa format x) = 1 ∨ @to_odd format (@fexp_real' format x) (@scaled_mantissa format x) = -1 ∨ @to_odd format (@fexp_real' format x) (@scaled_mantissa format x) = 2 ∨ @to_odd format (@fexp_real' format x) (@scaled_mantissa format x) = -2 := by
        apply to_odd_P1_in_set;
        · exact h₀;
        · exact fun h => h₂ <| h.symm ▸ by norm_num;
        · exact fract_abs_ne_zero_of_fract_ne_zero (scaled_mantissa x) h₂;
        · convert scaled_mantissa_bounded x using 1;
          norm_num [ vnum ];
      unfold round_fp_ne0;
      unfold vnum;
      simp_all only [ne_eq, Int.reduceNeg, pow_one, Nat.cast_ofNat]
      cases h_to_odd with
      | inl h => simp_all only [abs_one, OfNat.one_ne_ofNat, ↓reduceIte, Int.reduceNeg, reduceCtorEq, or_false]
      | inr h_1 =>
        cases h_1 with
        | inl h => simp_all only [Int.reduceNeg, abs_neg, abs_one, OfNat.one_ne_ofNat, ↓reduceIte, reduceCtorEq, or_true]
        | inr h_2 =>
          cases h_2 with
          | inl h =>
            simp_all only [Nat.abs_ofNat, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Int.ediv_self,
              Int.reduceNeg, reduceCtorEq, or_false]
          | inr h_1 =>
            simp_all only [Int.reduceNeg, abs_neg, Nat.abs_ofNat, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              Int.neg_ediv_self, reduceCtorEq, or_true]

/-- round_fp to_odd produces odd fnum when P = 1 and x is non-representable and nonzero. -/
theorem round_fp_to_odd_fnum_odd_P_eq_1 (x : ℝ) :
    format.precision = 1 →
    x ≠ 0 →
    (@round_fp format (@to_odd format) x : ℝ) ≠ x →
    Odd (@round_fp format (@to_odd format) x).fnum := by
  intro hp hx hne
  have hfr := fract_scaled_mantissa_ne_zero_of_not_representable x hx hne
  simp only [round_fp, hx, ↓reduceIte]
  rcases round_fp_ne0_to_odd_P1_fnum x hp hx hfr with h|h <;> simp only [h, odd_one, Int.reduceNeg, odd_neg]

/-- round_fp with to_odd produces odd fnum for non-representable nonzero values. -/
theorem round_fp_to_odd_fnum_odd (x : ℝ) :
    x ≠ 0 →
    (@round_fp format (@to_odd format) x : ℝ) ≠ x →
    Odd (@round_fp format (@to_odd format) x).fnum := by
  intro hx hne
  by_cases hp : format.precision = 1
  · exact round_fp_to_odd_fnum_odd_P_eq_1 x hp hx hne
  · have := format.precpos; exact round_fp_to_odd_fnum_odd_P_gt_1 x (by omega) hx hne
