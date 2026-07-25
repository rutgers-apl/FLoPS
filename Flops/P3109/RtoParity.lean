/-
  Parity of max_finite and min_finite significands for P3109 formats.
-/
import Flops.P3109.Defs

variable {f : p3109_format}

set_option maxHeartbeats 400000

namespace p3109_format
namespace p3109

/-
max_finite has odd fnum for signed finite format.
-/
lemma max_finite_fnum_odd_signed_finite :
    f.s = .signed →
    f.d = .finite →
    Odd (@max_finite f).fnum := by
      intro hs hd;
      unfold max_finite;
      split_ifs <;> simp_all +decide [ fnum ];
      unfold vnum; simp +decide [ *, parity_simps ] ;
      exact f.h_P.1.ne'

/-
max_finite has odd fnum for unsigned extended format.
-/
lemma max_finite_fnum_odd_unsigned_extended :
    f.s = .unsigned →
    f.d = .extended →
    Odd (@max_finite f).fnum := by
      intro hs hd
      by_cases hP : f.P = 1 ∨ f.P = 2;
      · unfold max_finite; cases hP <;> simp +decide [ * ] ;
        · exact ⟨ 0, rfl ⟩;
        · simp +decide [ *, p3109_format.to_format ];
          exact ⟨ 1, rfl ⟩;
      · unfold max_finite;
        split_ifs <;> simp_all +decide [ vnum ];
        have h_odd : Odd (2 ^ f.to_format.precision - 3 : ℤ) := by
          simp +decide [ parity_simps ];
          exact f.h_P.1.ne';
        exact h_odd

/-
max_finite has even fnum for signed extended format with P > 1.
-/
lemma max_finite_fnum_even_signed_extended :
    f.s = .signed →
    f.d = .extended →
    1 < f.P →
    Even (@max_finite f).fnum := by
      intros hs hd hp
      have h_sub : (@max_finite f).fnum = @vnum 2 f.to_format - 2 := by
        unfold max_finite;
        simp_all only
        split
        next h => simp_all only [lt_self_iff_false]
        next h => rfl
      generalize_proofs at *;
      simp_all +decide [ vnum ];
      exact even_iff_two_dvd.mpr ( dvd_pow_self _ ( by linarith [ f.to_format.precpos ] ) )

/-
max_finite has even fnum for unsigned finite format with P > 1.
-/
lemma max_finite_fnum_even_unsigned_finite :
    f.s = .unsigned →
    f.d = .finite →
    1 < f.P →
    Even (@max_finite f).fnum := by
      unfold max_finite;
      split_ifs <;> simp_all +decide [ fnum ];
      intro hs hd hP; unfold vnum; norm_num [ hs, hd, hP, parity_simps ] ;
      exact ne_of_gt ( f.h_P.1 )

/-
min_finite has even fnum (= 0) for unsigned format.
-/
lemma min_finite_fnum_even_unsigned :
    f.s = .unsigned →
    Even (@min_finite f).fnum := by
      intro h
      unfold min_finite
      simp only [fnum, h, ↓reduceDIte, Even.zero]

/-
min_finite has odd fnum for signed finite format.
-/
lemma min_finite_fnum_odd_signed_finite :
    f.s = .signed →
    f.d = .finite →
    Odd (@min_finite f).fnum := by
      intro hs hd
      have h_max_finite : Odd (@max_finite f).fnum := by
        exact max_finite_fnum_odd_signed_finite hs hd;
      convert h_max_finite.neg using 1;
      unfold min_finite;
      cases h : @max_finite f
      · simp_all only [reduceCtorEq]
      · simp_all only [reduceCtorEq, ↓reduceDIte]; rfl
      · simp_all only [reduceCtorEq, ↓reduceDIte]; rfl

/-
min_finite has even fnum for signed extended format with P > 1.
-/
lemma min_finite_fnum_even_signed_extended :
    f.s = .signed →
    f.d = .extended →
    1 < f.P →
    Even (@min_finite f).fnum := by
      intro hs hd hP
      have h_even : Even (@max_finite f).fnum := by
        exact max_finite_fnum_even_signed_extended hs hd hP;
      unfold min_finite;
      cases h : @max_finite f ; simp_all +decide [ parity_simps ];
      · grind;
      · split_ifs <;> simp_all +decide [ parity_simps ];
        exact even_iff_two_dvd.mpr ( dvd_neg.mpr ( even_iff_two_dvd.mp h_even ) )

end p3109
end p3109_format
