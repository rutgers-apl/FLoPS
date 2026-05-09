import Mathlib
import Flops.Core.RoundOp
import Flops.P3109.Defs
import Flops.P3109.Rounding

/-!
# Properties of P3109 Stochastic Rounding

Properties of stochastic rounding modes A, B, and C from the P3109 standard,

## Main results

### Integer preservation
* `stochastic_A_integer`, `stochastic_B_integer`, `stochastic_C_integer`:
  Stochastic rounding preserves integers (all three modes).

### Counting and summation (Mode A)
* `roundup_count_nat`: Pure combinatorial counting lemma.
* `stochastic_A_roundup_count`: Number of R values causing round-up in Mode A
  equals ⌊η · 2^N⌋.toNat.
* `stochastic_A_sum`: Sum of rounded mantissas over all valid R.

### Approximate unbiasedness (Mode A)
* `stochastic_A_mean_error_bound`: The bias of Mode A is bounded by 1/(2^N - 1).

### Exact bias (Mode A / SRFF)
* `roundup_count_full_range`: Roundup count over the full range {0, ..., 2^N − 1}.
* `stochastic_A_pointwise_bias_nonpos`: Pointwise bias is non-positive.
* `stochastic_A_pointwise_bias_lb`: Pointwise bias is bounded below by −1/2^N.
* `gauss_sum_real`: The Gauss arithmetic sum identity over ℝ.
* `stochastic_A_exact_bias`: The exact bias is −1/2^{N+1}.

### SRF (Mode B) unbiasedness and √n bound
* `srf_roundup_count`: Round-up count with +½ offset.
* `srf_pointwise_unbiased`: Pointwise unbiasedness of SRF.
* `srf_exact_bias`: Exact bias of SRF is zero.
* `srf_second_moment`: Second moment of SRF rounding error.
* `variance_single_le_quarter`: η(1−η) ≤ 1/4.
* `independent_cross_term_zero`: Cross terms vanish for zero-mean functions.
* `product_sum_factors`: Product-space sum factorization.
* `variance_sum_bound`: Variance of sum bounded by n/4.
* `srf_summation_rms_bound`: RMS summation error ≤ √(n/4).
* `srf_summation_sqrt_n`: RMS summation error ≤ √n/2.
-/

open Classical Finset

noncomputable section

variable {format : Format}

/-! ## Integer preservation -/

/-
When the mantissa is an integer, Mode A stochastic rounding returns it exactly.
    This follows because `Int.fract |↑m| = 0` for integers, making the round-up
    condition `0 + R ≥ 2^N` always false (since `R < 2^N`).
-/
lemma stochastic_A_integer (N : ℕ) (R : ℕ) (h : 0 ≤ R ∧ R < 2^N) (e : ℤ) (m : ℤ) :
    stochastic (.A N R h) e (m : ℝ) = m := by
      unfold stochastic;
      cases abs_cases ( m : ℝ ) <;> simp +decide [ * ];
      · split_ifs <;> norm_cast at * <;> omega;
      · norm_num [ show ⌊- ( m : ℝ ) ⌋ = -m by exact_mod_cast Int.floor_intCast _, Int.fract ];
        split_ifs <;> norm_cast at * <;> linarith

/-
When the mantissa is an integer, Mode B stochastic rounding returns it exactly.
-/
lemma stochastic_B_integer (N : ℕ) (R : ℕ) (h : 0 ≤ R ∧ R < 2^N) (e : ℤ) (m : ℤ) :
    stochastic (.B N R h) e (m : ℝ) = m := by
      unfold stochastic;
      cases abs_cases ( m : ℝ ) <;> simp +decide [ * ];
      · split_ifs <;> norm_cast at * <;> ring_nf at * <;> omega;
      · norm_num [ show ⌊- ( m : ℝ ) ⌋ = -m by exact_mod_cast Int.floor_intCast _ ];
        norm_num [ show Int.fract ( -m : ℝ ) = 0 by exact_mod_cast Int.fract_intCast _ ];
        split_ifs <;> norm_cast at * <;> omega

/-
When the mantissa is an integer, Mode C stochastic rounding returns it exactly.
-/
lemma stochastic_C_integer (N : ℕ) (R : ℕ) (h : 0 ≤ R ∧ R < 2^N) (e : ℤ) (m : ℤ) :
    stochastic (.C N R h) e (m : ℝ) = m := by
      -- Since $m$ is an integer, $|m|$ is also an integer, and thus its fractional part is zero.
      have h_frac : Int.fract |(m : ℝ)| = 0 := by
        cases abs_cases ( m : ℝ ) <;> simp +decide [ * ]
      generalize_proofs at *;
      simp [stochastic, h_frac];
      unfold stochastic.RNITE; norm_num [ h_frac ] ;
      split_ifs <;> norm_cast at * <;> simp_all +decide [ Int.floor_eq_iff ];
      · linarith;
      · grind +revert;
      · exact ⟨ le_abs_self _, by rw [ abs_of_pos ( by positivity ) ] ; linarith ⟩;
      · norm_num [ abs_of_nonpos ( by norm_cast : ( m : ℝ ) ≤ 0 ) ];
        norm_num [ Int.floor_neg ]

/-! ## Counting and summation for Mode A -/

/-
Pure combinatorial counting: for 0 ≤ k < 2^N, the number of R ∈ {1,...,2^N-1}
    satisfying `k + R ≥ 2^N` is exactly k.

    When k = 0: no R < 2^N satisfies R ≥ 2^N, so the count is 0.
    When 0 < k < 2^N: the satisfying R values are {2^N - k, ..., 2^N - 1}, which has k elements.
-/
lemma roundup_count_nat (N : ℕ) (k : ℕ) (hk : k < 2 ^ N) :
    ((Icc 1 (2 ^ N - 1)).filter (fun R => 2 ^ N ≤ k + R)).card = k := by
      rw [ Finset.card_eq_of_bijective ];
      use fun i hi => 2 ^ N - k + i;
      · simp +zetaDelta at *;
        exact fun a ha₁ ha₂ ha₃ => ⟨ a - ( 2 ^ N - k ), by omega, by omega ⟩;
      · grind;
      · grobner

/-
The floor of η·2^N is non-negative and less than 2^N when 0 ≤ η < 1.
-/
lemma floor_eta_bound (N : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    0 ≤ ⌊η * (2 : ℝ) ^ N⌋ ∧ ⌊η * (2 : ℝ) ^ N⌋ < (2 : ℤ) ^ N := by
      exact ⟨ Int.floor_nonneg.2 ( by positivity ), Int.floor_lt.2 ( by norm_num; nlinarith [ pow_pos ( zero_lt_two' ℝ ) N ] ) ⟩

/-
The number of R ∈ {1,...,2^N-1} causing Mode A to round up
    equals ⌊η·2^N⌋.toNat, where η is the fractional part of the mantissa.
-/
lemma stochastic_A_roundup_count (N : ℕ) (_hN : 0 < N) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ((Icc 1 (2 ^ N - 1)).filter
      (fun R : ℕ => decide ((2 : ℤ) ^ N ≤ ⌊η * (2 : ℝ) ^ N⌋ + (R : ℤ)))).card
    = (⌊η * (2 : ℝ) ^ N⌋).toNat := by
      convert roundup_count_nat N _ _;
      · norm_num [ ← Int.ofNat_le, Int.toNat_of_nonneg ( Int.floor_nonneg.mpr ( mul_nonneg hη0 ( pow_nonneg zero_le_two _ ) ) ) ];
      · rw [ ← Int.ofNat_lt, Int.toNat_of_nonneg ( Int.floor_nonneg.mpr ( by positivity ) ) ] ; exact Int.floor_lt.mpr ( by norm_num; nlinarith [ pow_pos ( zero_lt_two' ℝ ) N ] )

/-
Sum of if-then-else values over all valid R for Mode A.
    The sum decomposes into a constant part `(2^N-1) * a` and a counting part `⌊η·2^N⌋`.
    This is the key formula for computing the average rounded value.
-/
lemma stochastic_A_sum (N : ℕ) (hN : 0 < N) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (a : ℤ) :
    (Icc 1 (2 ^ N - 1)).sum
      (fun R : ℕ => if (2 : ℤ) ^ N ≤ ⌊η * (2 : ℝ) ^ N⌋ + (R : ℤ) then a + 1 else a)
    = ((2 : ℤ) ^ N - 1) * a + ⌊η * (2 : ℝ) ^ N⌋ := by
      -- The sum of if-then-else expressions can be split into a constant part and a counting part.
      have h_split : (∑ R ∈ Icc 1 (2 ^ N - 1 : ℕ), (if (2 ^ N : ℤ) ≤ ⌊η * (2 : ℝ) ^ N⌋ + R then a + 1 else a)) = (∑ R ∈ Icc 1 (2 ^ N - 1 : ℕ), a) + (∑ R ∈ Icc 1 (2 ^ N - 1 : ℕ), (if (2 ^ N : ℤ) ≤ ⌊η * (2 : ℝ) ^ N⌋ + R then 1 else 0)) := by
        simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => by split_ifs <;> ring;
      have h_count : ((Icc 1 (2 ^ N - 1 : ℕ)).filter (fun R : ℕ => decide ((2 : ℤ) ^ N ≤ ⌊η * (2 : ℝ) ^ N⌋ + (R : ℤ)))).card = (⌊η * (2 : ℝ) ^ N⌋).toNat := by
        convert stochastic_A_roundup_count N hN η hη0 hη1 using 1;
      simp_all +decide [ Finset.sum_ite ];
      exact Int.floor_nonneg.mpr ( mul_nonneg hη0 ( pow_nonneg zero_le_two _ ) )

/-! ## Approximate unbiasedness for Mode A -/

/-
The bias of Mode A stochastic rounding at the mantissa level:
    `|⌊η·2^N⌋ / (2^N - 1) - η| < 1 / (2^N - 1)` for 0 ≤ η < 1 and N > 0.

    This means the average rounded mantissa (over all valid R) approximates the
    true mantissa with error strictly less than `1/(2^N - 1)` ULPs.
    As N increases, the bound shrinks exponentially, approaching exact unbiasedness.
-/
lemma stochastic_A_mean_error_bound (N : ℕ) (hN : 0 < N)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    |(⌊η * (2 : ℝ) ^ N⌋ : ℝ) / ((2 : ℝ) ^ N - 1) - η| < 1 / ((2 : ℝ) ^ N - 1) := by
      rw [ abs_lt ];
      constructor <;> nlinarith [ show ( 2 : ℝ ) ^ N > 1 by exact one_lt_pow₀ ( by norm_num ) ( by linarith ), Int.floor_le ( η * 2 ^ N ), Int.lt_floor_add_one ( η * 2 ^ N ), mul_div_cancel₀ ( ⌊η * 2 ^ N⌋ : ℝ ) ( by linarith [ show ( 2 : ℝ ) ^ N > 1 by exact one_lt_pow₀ ( by norm_num ) ( by linarith ) ] : ( 2 ^ N - 1 : ℝ ) ≠ 0 ), mul_div_cancel₀ ( 1 : ℝ ) ( by linarith [ show ( 2 : ℝ ) ^ N > 1 by exact one_lt_pow₀ ( by norm_num ) ( by linarith ) ] : ( 2 ^ N - 1 : ℝ ) ≠ 0 ) ]

/-! ## Exact bias for Mode A (SRFF) -/

/-
For k < 2^N, the number of R ∈ {0, ..., 2^N − 1} satisfying k + R ≥ 2^N is exactly k.
    This extends `roundup_count_nat` to the full range including R = 0.
    When R = 0, the condition k + 0 ≥ 2^N fails since k < 2^N, so R = 0 never contributes.
-/
lemma roundup_count_full_range (N : ℕ) (k : ℕ) (hk : k < 2 ^ N) :
    ((Finset.range (2 ^ N)).filter (fun R => 2 ^ N ≤ k + R)).card = k := by
  have hIfull : {R ∈ Finset.range (2 ^ N) | 2 ^ N ≤ k + R} = Finset.Ico (2 ^ N - k) (2 ^ N) := by
    grind +qlia;
  simp_all +decide [ Nat.sub_sub_self hk.le ]

/-
Pointwise exact bias: for η ∈ [0, 1), the bias ⌊η·2^N⌋/2^N − η is non-positive.
    This follows from ⌊x⌋ ≤ x.
-/
lemma stochastic_A_pointwise_bias_nonpos (N : ℕ)
    (η : ℝ) (_hη0 : 0 ≤ η) (_hη1 : η < 1) :
    (⌊η * (2 : ℝ) ^ N⌋ : ℝ) / (2 : ℝ) ^ N - η ≤ 0 := by
  rw [ sub_nonpos, div_le_iff₀ ] <;> norm_num ; linarith [ Int.floor_le ( η * 2 ^ N ) ]

/-
Pointwise exact bias: for η ∈ [0, 1), the bias ⌊η·2^N⌋/2^N − η is strictly greater
    than −1/2^N. This follows from ⌊x⌋ > x − 1.
-/
lemma stochastic_A_pointwise_bias_lb (N : ℕ)
    (η : ℝ) (_hη0 : 0 ≤ η) (_hη1 : η < 1) :
    -(1 : ℝ) / (2 : ℝ) ^ N < (⌊η * (2 : ℝ) ^ N⌋ : ℝ) / (2 : ℝ) ^ N - η := by
  rw [ div_sub', div_lt_div_iff_of_pos_right ] <;> first | positivity | nlinarith [ Int.lt_floor_add_one ( η * 2 ^ N ), ( pow_pos ( zero_lt_two' ℝ ) N ) ] ;

/-
The Gauss sum identity cast to ℝ: the sum of the first M natural numbers
    equals M * (M − 1) / 2.
-/
lemma gauss_sum_real (M : ℕ) :
    (∑ k ∈ Finset.range M, (k : ℝ)) = (M : ℝ) * ((M : ℝ) - 1) / 2 := by
  induction M with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ]; linarith

/-
The exact bias of Mode A stochastic rounding (SRFF), averaged uniformly over
R ∈ {0, ..., 2^N − 1} and the fractional part η ∈ [0, 1), equals −1/2^{N+1}.

This formalizes the main result from §III-C of the paper:

  bias = (1/2^{2N}) · Σ_{k=0}^{2^N−1} k − 1/2
       = (1/2^{2N}) · 2^N(2^N − 1)/2 − 1/2
       = (1 − 2^{−N})/2 − 1/2
       = −2^{−(N+1)}

The bias is always negative: SRFF systematically rounds down.
-/
theorem stochastic_A_exact_bias (N : ℕ) (_hN : 0 < N) :
    (∑ k ∈ Finset.range (2 ^ N), (k : ℝ)) / ((2 : ℝ) ^ N) ^ 2 - 1 / 2 =
    -(1 : ℝ) / 2 ^ (N + 1) := by
  rw [ gauss_sum_real ] ; ring ; norm_num [ pow_succ' ];
  norm_num [ sq, pow_mul' ] ; ring;
  norm_num [ pow_mul', ← mul_pow ]

/-! ## Phase 1: SRF Unbiasedness -/

/-
The +½ offset in SRF makes the discrete average exact. The condition becomes
R ≥ 2^N − k − 0.5, i.e. R ≥ 2^N − k (since R is a natural). The satisfying set
is {2^N − k, ..., 2^N − 1}, which has k elements.
-/
lemma srf_roundup_count (N : ℕ) (k : ℕ) (hk : k < 2 ^ N) :
    ((Finset.range (2 ^ N)).filter
      (fun R => (2 : ℝ) ^ N ≤ (k : ℝ) + ((R : ℝ) + 0.5))).card
    = k := by
  norm_num [ add_comm, Finset.card_image_of_injective, Function.Injective, Finset.filter_image ];
  convert roundup_count_full_range N k hk using 2;
  ext; norm_num; rw [ ← @Nat.cast_le ℝ ] ; ring;
  intro _; norm_num; constructor <;> intros <;> norm_cast at * ;
  · rw [ div_add', div_add', le_div_iff₀ ] at * <;> norm_cast at * ; linarith;
  · field_simp;
    norm_cast ; linarith

/-
Direct consequence of `srf_roundup_count`. The average round-up probability
equals k/2^N = η, so the bias is zero for each discretized η.
-/
lemma srf_pointwise_unbiased (N : ℕ) (hN : 0 < N)
    (k : ℕ) (hk : k < 2 ^ N) :
    ((Finset.range (2 ^ N)).filter
      (fun R => (2 : ℝ) ^ N ≤ (k : ℝ) + ((R : ℝ) + 0.5))).card
    / (2 : ℝ) ^ N
    = (k : ℝ) / (2 : ℝ) ^ N := by
  convert congr_arg ( fun x : ℕ => ( x : ℝ ) / 2 ^ N ) ( srf_roundup_count ( N := N ) ( k := k ) hk ) using 1

/-
The overall SRF bias is zero: the average rounding error, computed by summing
the error for each (k, R) pair, is exactly 0. For each k, the inner sum over R
decomposes into k terms of (1 − k/2^N) and (2^N − k) terms of (−k/2^N),
which telescope to 0. The original roadmap formulation
`∑(2^N − k) / (2^N)^2 − 1/2 = 0` was incorrect (it equals 1/2^{N+1}).
-/
theorem srf_exact_bias (N : ℕ) (hN : 0 < N) :
    (∑ k ∈ Finset.range (2 ^ N),
      (∑ R ∈ Finset.range (2 ^ N),
        if (2 : ℝ) ^ N ≤ (k : ℝ) + ((R : ℝ) + 0.5)
        then 1 - (k : ℝ) / (2 : ℝ) ^ N
        else -((k : ℝ) / (2 : ℝ) ^ N)))
    = 0 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ k ∈ Finset.range (2 ^ N), ∑ R ∈ Finset.range (2 ^ N), (if (2 : ℝ) ^ N ≤ (k : ℝ) + ((R : ℝ) + 0.5) then (1 : ℝ) - k / (2 : ℝ) ^ N else -(k / (2 : ℝ) ^ N)) = ∑ k ∈ Finset.range (2 ^ N), (k : ℝ) * (1 - k / (2 : ℝ) ^ N) + ∑ k ∈ Finset.range (2 ^ N), ((2 : ℝ) ^ N - k) * (-(k / (2 : ℝ) ^ N)) := by
    rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
    intro k hk; rw [ Finset.sum_ite ] ; norm_num [ srf_roundup_count ] ; ring;
    rw [ show ( Finset.filter ( fun x : ℕ => 2 ^ N ≤ 1 / 2 + ( k : ℝ ) + x ) ( Finset.range ( 2 ^ N ) ) ) = Finset.Ico ( 2 ^ N - k ) ( 2 ^ N ) from ?_, show ( Finset.filter ( fun x : ℕ => 1 / 2 + ( k : ℝ ) + x < 2 ^ N ) ( Finset.range ( 2 ^ N ) ) ) = Finset.range ( 2 ^ N - k ) from ?_ ] <;> norm_num [ Nat.cast_sub ( show k ≤ 2 ^ N from Finset.mem_range_le hk ) ] ; ring;
    · ext x; norm_num at *; rw [ ← @Nat.cast_lt ℝ ] at *; norm_num at *; constructor <;> intros <;> try linarith;
      · exact lt_tsub_iff_left.mpr ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith );
      · exact ⟨ by norm_cast; omega, by linarith [ show ( x : ℝ ) + k + 1 ≤ 2 ^ N by norm_cast; omega ] ⟩;
    · ext x; simp [Finset.inter_filter, Finset.mem_Ico];
      rw [ inv_eq_one_div, div_add', div_add', le_div_iff₀ ] <;> norm_cast ; ring;
      constructor <;> intro h <;> omega;
  convert h_fubini using 1 ; ring;
  norm_num [ Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, ← mul_pow ]

/-! ## Phase 2: Variance Bound for a Single Rounding -/

/-
Split the sum into the filter (k terms contributing (1−η)²) and its complement
(2^N−k terms contributing η²), where η = k/2^N. Use `srf_roundup_count` for
the cardinality. Expand and simplify to η(1−η).
-/
lemma srf_second_moment (N : ℕ) (hN : 0 < N)
    (k : ℕ) (hk : k < 2 ^ N) :
    (1 / (2 : ℝ) ^ N) *
      ((Finset.range (2 ^ N)).sum
        (fun R => if (2 : ℝ) ^ N ≤ (k : ℝ) + ((R : ℝ) + 0.5)
                  then (1 - (k : ℝ) / (2 : ℝ) ^ N) ^ 2
                  else ((k : ℝ) / (2 : ℝ) ^ N) ^ 2))
    = ((k : ℝ) / (2 : ℝ) ^ N) * (1 - (k : ℝ) / (2 : ℝ) ^ N) := by
  -- Apply `h_filter_card` to rewrite the sum.
  have h_sum_split : (∑ R ∈ Finset.range (2 ^ N), if (2 : ℝ) ^ N ≤ (k : ℝ) + ((R : ℝ) + 0.5) then (1 - (k : ℝ) / (2 : ℝ) ^ N) ^ 2 else ((k : ℝ) / (2 : ℝ) ^ N) ^ 2) = (k : ℝ) * (1 - (k : ℝ) / (2 : ℝ) ^ N) ^ 2 + (2 ^ N - k) * ((k : ℝ) / (2 : ℝ) ^ N) ^ 2 := by
    rw [ Finset.sum_ite ];
    simp +zetaDelta at *;
    congr;
    · convert srf_roundup_count N k hk using 1;
      refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> aesop;
    · rw [ show ( Finset.filter ( fun x : ℕ => ( k : ℝ ) + ( x + 0.5 ) < 2 ^ N ) ( Finset.range ( 2 ^ N ) ) ) = Finset.range ( 2 ^ N - k ) from ?_ ] ; norm_num [ hk.le ];
      ext x; norm_num; constructor <;> intros <;> norm_cast at *;
      · exact lt_tsub_iff_left.mpr ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast at *; linarith );
      · exact ⟨ lt_of_lt_of_le ‹_› ( Nat.sub_le _ _ ), by rw [ Nat.cast_pow ] ; linarith [ show ( x : ℝ ) + 1 ≤ 2 ^ N - k from by exact le_tsub_of_add_le_left <| by norm_cast; linarith [ Nat.sub_add_cancel hk.le ] ] ⟩;
  grind

/-
Completing the square: η(1−η) = 1/4 − (η−1/2)². Since squares are non-negative,
the result follows.
-/
lemma variance_single_le_quarter (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    η * (1 - η) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (η - 1 / 2)]

/-! ## Phase 3: Independence and Variance of Sums -/

/-
Factor as (∑ f R₁) * (∑ g R₂) using `Finset.sum_mul_sum`. Both factors are zero
by hypothesis.
-/
lemma independent_cross_term_zero (N : ℕ) (M : ℕ)
    (f g : ℕ → ℝ)
    (hf : (∑ R ∈ Finset.range M, f R) = 0)
    (hg : (∑ R ∈ Finset.range M, g R) = 0) :
    (∑ R₁ ∈ Finset.range M, ∑ R₂ ∈ Finset.range M,
      f R₁ * g R₂) = 0 := by
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hf, hg ]

/-
The sum over all `Rs : Fin n → Fin M` can be decomposed: the coordinates other
than i and j each contribute a factor of M (summing over M values of a constant),
while coordinates i and j contribute their respective marginal sums.
-/
set_option maxHeartbeats 400000 in
lemma product_sum_factors (n : ℕ) (M : ℕ) (hM : 0 < M)
    (f : Fin n → ℕ → ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    (∑ Rs ∈ Finset.univ (α := Fin n → Fin M),
      f i (Rs i).val * f j (Rs j).val)
    = (M : ℝ) ^ (n - 2) *
      (∑ Ri ∈ Finset.range M, f i Ri) *
      (∑ Rj ∈ Finset.range M, f j Rj) := by
  -- The sum over all Rs : Fin n → Fin M can be decomposed into a product of sums over each coordinate by Fubini's theorem.
  have h_decomp : ∑ Rs : Fin n → Fin M, (f i (Rs i)) * (f j (Rs j)) = (∏ k : Fin n, (∑ Ri : Fin M, if k = i then f i Ri else if k = j then f j Ri else 1)) := by
    rw [ Finset.prod_sum ];
    refine' Finset.sum_bij ( fun Rs _ => fun k _ => Rs k ) _ _ _ _ <;> simp +decide [ Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun k => b k ( Finset.mem_univ k ), rfl ⟩;
    · intro a; rw [ Finset.prod_eq_single ⟨ i, by aesop ⟩, Finset.prod_eq_single ⟨ j, by aesop ⟩ ] <;> aesop;
  simp_all +decide [ Finset.sum_range, Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
  simp_all +decide [ Finset.card_erase_of_mem, Finset.mem_erase, ne_comm ] ; ring;
  aesop

/-
Expand (∑ᵢ εᵢ)² = ∑ᵢ εᵢ² + ∑_{i≠j} εᵢεⱼ. The cross terms vanish by
`product_sum_factors` + `h_mean`. The diagonal terms are bounded by n/4.
-/
lemma variance_sum_bound (n : ℕ) (N : ℕ)
    (err : Fin n → ℕ → ℝ)
    (h_mean : ∀ i, (∑ R ∈ Finset.range (2 ^ N), err i R) = 0)
    (h_var : ∀ i, (∑ R ∈ Finset.range (2 ^ N), (err i R) ^ 2)
              / (2 : ℝ) ^ N ≤ 1 / 4) :
    (∑ Rs ∈ Finset.univ (α := Fin n → Fin (2 ^ N)),
      (∑ i : Fin n, err i (Rs i).val) ^ 2)
    / ((2 : ℝ) ^ N) ^ n
    ≤ (n : ℝ) / 4 := by
  have h_expand : (∑ Rs : Fin n → Fin (2 ^ N), (∑ i, err i (Rs i).val) ^ 2) = ∑ i, ∑ j, (∑ Rs : Fin n → Fin (2 ^ N), err i (Rs i).val * err j (Rs j).val) := by
    simp +decide only [sq, Finset.mul_sum _ _ _, mul_comm];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  -- Apply the lemma `product_sum_factors` to each term in the double sum.
  have h_apply_factors : ∀ i j : Fin n, (∑ Rs : Fin n → Fin (2 ^ N), err i (Rs i).val * err j (Rs j).val) = if i = j then (2 ^ N : ℝ) ^ (n - 1) * (∑ R ∈ Finset.range (2 ^ N), err i R ^ 2) else 0 := by
    intro i j;
    split_ifs with hij;
    · have h_diag : (∑ Rs : Fin n → Fin (2 ^ N), err i (Rs i).val ^ 2) = (∏ j : Fin n, (∑ R : Fin (2 ^ N), if j = i then err i R ^ 2 else 1)) := by
        rw [ Finset.prod_sum ];
        refine' Finset.sum_bij ( fun Rs _ => fun j _ => Rs j ) _ _ _ _ <;> simp +decide;
        · simp +decide [ funext_iff ];
        · exact fun b => ⟨ fun j => b j ( Finset.mem_univ j ), funext fun j => rfl ⟩;
      simp_all +decide [ ← sq, Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
      rw [ mul_comm, Finset.sum_range ];
    · convert product_sum_factors n ( 2 ^ N ) ( by positivity ) ( fun k R => err k R ) i j hij using 1 ; norm_num [ h_mean ];
  rcases n <;> simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
  norm_num [ pow_succ, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, div_le_iff₀ ] at *;
  exact le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun _ _ => h_var _ ) ( by positivity ) ) ( by norm_num [ Finset.sum_mul _ _ _ ] ; ring_nf; norm_num )

/-! ## Phase 4: Assembly -/

/-
Chain the results: verify h_mean from herr + srf_pointwise_unbiased, verify
h_var from herr + srf_second_moment + variance_single_le_quarter, apply
variance_sum_bound, then Real.sqrt_le_sqrt.
-/
theorem srf_summation_rms_bound (n : ℕ) (N : ℕ) (hN : 0 < N)
    (ks : Fin n → ℕ) (hks : ∀ i, ks i < 2 ^ N)
    (err : Fin n → ℕ → ℝ)
    (herr : ∀ i R, err i R =
      if (2 : ℝ) ^ N ≤ (ks i : ℝ) + ((R : ℝ) + 0.5)
      then 1 - (ks i : ℝ) / (2 : ℝ) ^ N
      else -((ks i : ℝ) / (2 : ℝ) ^ N)) :
    Real.sqrt ((∑ Rs ∈ Finset.univ (α := Fin n → Fin (2 ^ N)),
      (∑ i : Fin n, err i (Rs i).val) ^ 2)
      / ((2 : ℝ) ^ N) ^ n)
    ≤ Real.sqrt ((n : ℝ) / 4) := by
  apply Real.sqrt_le_sqrt;
  apply variance_sum_bound n N err;
  · intro i
    have := srf_pointwise_unbiased N hN (ks i) (hks i)
    simp_all +decide [ Finset.sum_ite ];
    rw [ show ( Finset.filter ( fun x : ℕ => ( ks i : ℝ ) + ( x + 0.5 ) < 2 ^ N ) ( Finset.range ( 2 ^ N ) ) ) = Finset.range ( 2 ^ N ) \ ( Finset.filter ( fun x : ℕ => ( ks i : ℝ ) + ( x + 0.5 ) ≥ 2 ^ N ) ( Finset.range ( 2 ^ N ) ) ) by ext; aesop, Finset.card_sdiff ] ; norm_num [ this ];
    convert congr_arg ( fun x : ℕ => ( x : ℝ ) - x * ( ks i / 2 ^ N ) + - ( ( 2 ^ N - x ) * ( ks i / 2 ^ N ) ) ) ( show Finset.card ( Finset.filter ( fun x : ℕ => ( ks i : ℝ ) + ( x + 1 / 2 ) ≥ 2 ^ N ) ( Finset.range ( 2 ^ N ) ) ) = ks i from ?_ ) using 1;
    · rw [ Nat.cast_sub ] <;> norm_num;
      · exact Or.inl ( by rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] );
      · exact le_trans ( Finset.card_le_card ( Finset.inter_subset_right ) ) ( by norm_num );
    · field_simp
      ring;
    · convert this using 1;
      rw [ Finset.card_filter, Finset.card_filter ];
      rw [ Finset.sum_image ] <;> norm_num;
  · intro i
    have := srf_second_moment N hN (ks i) (hks i)
    simp [herr] at this;
    simp_all +decide [ div_eq_inv_mul ];
    nlinarith only [ sq_nonneg ( ( 2 ^ N : ℝ ) ⁻¹ * ks i - 1 / 2 ), mul_inv_cancel₀ ( show ( 2 ^ N : ℝ ) ≠ 0 by positivity ) ]

/-
From `srf_summation_rms_bound`, rewrite √(n/4) = √n / √4 = √n / 2.
-/
theorem srf_summation_sqrt_n (n : ℕ) (N : ℕ) (hN : 0 < N)
    (ks : Fin n → ℕ) (hks : ∀ i, ks i < 2 ^ N)
    (err : Fin n → ℕ → ℝ)
    (herr : ∀ i R, err i R =
      if (2 : ℝ) ^ N ≤ (ks i : ℝ) + ((R : ℝ) + 0.5)
      then 1 - (ks i : ℝ) / (2 : ℝ) ^ N
      else -((ks i : ℝ) / (2 : ℝ) ^ N)) :
    Real.sqrt ((∑ Rs ∈ Finset.univ (α := Fin n → Fin (2 ^ N)),
      (∑ i : Fin n, err i (Rs i).val) ^ 2)
      / ((2 : ℝ) ^ N) ^ n)
    ≤ Real.sqrt (n : ℝ) / 2 := by
  convert srf_summation_rms_bound n N hN ks hks err herr using 1 ; norm_num

/-! ## Phase 0: RNITE (Round to Nearest Integer, Ties to Even) -/

/--
RNITE rounds a real to the nearest integer, with ties to even.
This matches the P3109 definition in §5.11.3 and `stochastic.RNITE`.
-/
noncomputable def rnite (x : ℝ) : ℤ :=
  if x - ⌊x⌋ < 1/2 then ⌊x⌋
  else if x - ⌊x⌋ > 1/2 then ⌊x⌋ + 1
  else if Even ⌊x⌋ then ⌊x⌋
  else ⌊x⌋ + 1

/-
RNITE returns a value within 1/2 of its input.
-/
lemma rnite_nearest (x : ℝ) : |x - (rnite x : ℝ)| ≤ 1 / 2 := by
  unfold rnite; split_ifs <;> norm_num [ abs_le ];
  · constructor <;> linarith [ Int.fract_add_floor x, Int.fract_nonneg x, Int.fract_lt_one x ];
  · constructor <;> linarith [ Int.floor_le x, Int.lt_floor_add_one x ];
  · constructor <;> linarith [ Int.fract_add_floor x, Int.fract_nonneg x, Int.fract_lt_one x ];
  · grind +extAll

/-
RNITE of an integer is itself.
-/
lemma rnite_integer (n : ℤ) : rnite (n : ℝ) = n := by
  -- Since $n$ is an integer, $x - \lfloor x \rfloor = 0$, so we are in the first case.
  simp [rnite]

/-
For 0 ≤ x < 2^N, RNITE(x) ∈ {0, ..., 2^N}.
The value 2^N is possible (e.g. RNITE(2^N - 0.5) when 2^N is even).
-/
lemma rnite_range (N : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 2 ^ N) :
    0 ≤ rnite x ∧ rnite x ≤ (2 : ℤ) ^ N := by
  have h_rnite_bounds : |x - (rnite x : ℝ)| ≤ 1 / 2 := by
    exact?
  generalize_proofs at *; (
  exact ⟨ Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ abs_le.mp h_rnite_bounds ], Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ abs_le.mp h_rnite_bounds ] ⟩)

/-
RNITE is unbiased over the 2^D finite-precision inputs in [0, 2^N):
the sum of rounding errors is zero.

Inputs are i · 2^N / 2^D for i = 0, ..., 2^D - 1.
-/
lemma rnite_unbiased_finite (N D : ℕ) (hN : 0 < N) (hND : N ≤ D) :
    (∑ i ∈ Finset.range (2 ^ D),
      ((rnite ((i : ℝ) * 2 ^ N / 2 ^ D) : ℝ) - (i : ℝ) * 2 ^ N / 2 ^ D))
    = 0 := by
  -- By pairing each $i$ with $2^D - i$, we can show that the sum of the errors is zero.
  have h_pair : ∀ k : ℕ, k < 2 ^ D → (rnite ((k : ℝ) * 2 ^ N / 2 ^ D) - (k : ℝ) * 2 ^ N / 2 ^ D) + (rnite ((2 ^ D - k : ℝ) * 2 ^ N / 2 ^ D) - (2 ^ D - k : ℝ) * 2 ^ N / 2 ^ D) = 0 := by
    intros k hk_lt
    have h_eq : (2 ^ D - k : ℝ) * 2 ^ N / 2 ^ D = 2 ^ N - (k : ℝ) * 2 ^ N / 2 ^ D := by
      rw [ sub_mul, sub_div, mul_div_cancel_left₀ _ ( by positivity ) ];
    have h_rnite_symm : ∀ x : ℝ, rnite (2 ^ N - x) = 2 ^ N - rnite x := by
      intro x
      simp [rnite];
      rw [ Int.fract, Int.fract ];
      rw [ show ⌊2 ^ N - x⌋ = 2 ^ N - ⌊x⌋ - ( if x - ⌊x⌋ = 0 then 0 else 1 ) by
            split_ifs <;> norm_num [ Int.floor_eq_iff ] at *;
            · rw [ Int.fract_eq_iff ] at * ; aesop;
            · constructor <;> linarith [ Int.fract_add_floor x, Int.fract_nonneg x, Int.fract_lt_one x, show ( Int.fract x : ℝ ) > 0 from lt_of_le_of_ne ( Int.fract_nonneg x ) ( Ne.symm ‹_› ) ] ] ; norm_num ; ring;
      split_ifs <;> norm_num <;> try linarith [ Int.fract_add_floor x, Int.fract_nonneg x, Int.fract_lt_one x ];
      · simp_all +decide [ parity_simps ];
        exact absurd ( ‹Odd ⌊x⌋ ↔ ¬N = 0›.mpr hN.ne' ) ( by simpa using ‹Even ⌊x⌋› );
      · simp_all +decide [ parity_simps ];
    rw [ h_eq, h_rnite_symm ] ; ring;
    norm_num;
  -- By pairing each $i$ with $2^D - i$, we can show that the sum of the errors is zero. Hence, the total sum is zero.
  have h_sum_zero : ∑ i ∈ Finset.range (2 ^ D), (rnite ((i : ℝ) * 2 ^ N / 2 ^ D) - (i : ℝ) * 2 ^ N / 2 ^ D) = ∑ i ∈ Finset.range (2 ^ D), (rnite ((2 ^ D - i : ℝ) * 2 ^ N / 2 ^ D) - (2 ^ D - i : ℝ) * 2 ^ N / 2 ^ D) := by
    apply Finset.sum_bij (fun i hi => if i = 0 then 0 else 2^D - i);
    · grind;
    · grind;
    · intro b hb; use if b = 0 then 0 else 2 ^ D - b; simp_all +decide [ Nat.sub_sub_self ( show b ≤ 2 ^ D from Finset.mem_range_le hb ) ] ;
      grind;
    · intro i hi; split_ifs <;> simp_all +decide [ Nat.cast_sub ( show i ≤ 2 ^ D from Finset.mem_range_le hi ) ] ;
      unfold rnite; norm_num;
      norm_num [ show ⌊ ( 2 : ℝ ) ^ N⌋ = 2 ^ N by exact_mod_cast Int.floor_intCast _ ];
      norm_num [ show Int.fract ( 2 ^ N : ℝ ) = 0 by exact_mod_cast Int.fract_intCast _ ];
  have := Finset.sum_congr rfl fun i hi => h_pair i ( Finset.mem_range.mp hi ) ; norm_num [ Finset.sum_add_distrib ] at * ; linarith;

/-! ## Phase 1: SRC Reduction to SRFF at N = D -/

/-
SRFF is unbiased when applied to values that are exact multiples of 2^{-N}.
That is, when η = k/2^N for integer k, the discrete average of the
round-up indicator over R ∈ {0,...,2^N-1} equals exactly k/2^N.
-/
lemma srff_unbiased_at_multiples (N : ℕ) (hN : 0 < N)
    (k : ℕ) (hk : k < 2 ^ N) :
    ((Finset.range (2 ^ N)).filter
      (fun R => 2 ^ N ≤ k + R)).card / (2 : ℝ) ^ N
    = (k : ℝ) / (2 : ℝ) ^ N := by
  rw [ roundup_count_full_range N k hk ]

/-
For SRC: first RNITE the scaled fractional part, then apply SRFF.
The round-up count is rnite(η · 2^N).toNat.
-/
lemma src_roundup_count (N : ℕ) (hN : 0 < N)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hk : (rnite (η * 2 ^ N)).toNat < 2 ^ N) :
    ((Finset.range (2 ^ N)).filter
      (fun R => 2 ^ N ≤ (rnite (η * 2 ^ N)).toNat + R)).card
    = (rnite (η * 2 ^ N)).toNat := by
  convert roundup_count_full_range N _ hk using 1

/-
Edge case: when rnite(η · 2^N) = 2^N, every R triggers round-up.
-/
lemma src_roundup_count_overflow (N : ℕ) (hN : 0 < N)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hk : rnite (η * 2 ^ N) = (2 : ℤ) ^ N) :
    ((Finset.range (2 ^ N)).filter
      (fun R => 2 ^ N ≤ (rnite (η * 2 ^ N)).toNat + R)).card
    = 2 ^ N := by
  rw [ Finset.filter_true_of_mem ] <;> simp +decide [ hk ];
  grind

/-! ## Phase 2: SRC Pointwise Unbiasedness -/

/-
The pointwise bias of SRC at fractional part η = j/2^D:
the bias equals rnite(η · 2^N) / 2^N - η.
-/
lemma src_pointwise_bias (N D : ℕ) (hN : 0 < N) (hND : N ≤ D)
    (j : ℕ) (hj : j < 2 ^ D) :
    let η := (j : ℝ) / 2 ^ D
    ((Finset.range (2 ^ N)).filter
      (fun R => 2 ^ N ≤ (rnite (η * 2 ^ N)).toNat + R)).card
    / (2 : ℝ) ^ N - η
    = (rnite ((j : ℝ) * 2 ^ N / 2 ^ D) : ℝ) / 2 ^ N
      - (j : ℝ) / 2 ^ D := by
  by_cases hk : ( rnite ( j * 2 ^ N / 2 ^ D ) ).toNat < 2 ^ N <;> simp_all +decide [ mul_div_left_comm ];
  · convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( src_roundup_count N hN ( j / 2 ^ D ) ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; norm_cast; linarith ) ?_ ) using 1;
    · norm_num [ div_mul_eq_mul_div ];
      exact_mod_cast Eq.symm ( Int.toNat_of_nonneg ( show 0 ≤ rnite ( ( j : ℝ ) * 2 ^ N / 2 ^ D ) from by
                                                      unfold rnite; split_ifs <;> norm_num;
                                                      · positivity;
                                                      · exact add_nonneg ( Int.floor_nonneg.mpr ( by positivity ) ) zero_le_one;
                                                      · positivity;
                                                      · exact add_nonneg ( Int.floor_nonneg.mpr ( by positivity ) ) zero_le_one ) );
    · rw [ div_mul_eq_mul_div ] ; norm_cast;
      grind;
  · have h_eq : rnite (j * 2 ^ N / 2 ^ D : ℝ) = 2 ^ N := by
      refine' le_antisymm _ _;
      · have := rnite_range N ( j * 2 ^ N / 2 ^ D ) ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; norm_cast; nlinarith [ pow_pos ( zero_lt_two' ℕ ) N, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hND ] ) ; aesop;
      · exact hk;
    simp_all +decide [ mul_div_right_comm ];
    norm_cast ; norm_num [ Finset.filter_true_of_mem ]

/-
The total bias of SRC, averaged over all 2^D finite-precision inputs, is exactly zero.
This is the main result from §III-F: SRC is unbiased for finite-precision inputs.
-/
theorem src_exact_bias_finite_precision (N D : ℕ) (hN : 0 < N) (hND : N ≤ D) :
    (∑ j ∈ Finset.range (2 ^ D),
      (((Finset.range (2 ^ N)).filter
        (fun R => 2 ^ N ≤ (rnite (((j : ℝ) / 2 ^ D) * 2 ^ N)).toNat + R)).card
      / (2 : ℝ) ^ N - (j : ℝ) / 2 ^ D))
    = 0 := by
  -- By `src_pointwise_bias`, each summand equals `(rnite (j * 2^N / 2^D) : ℝ) / 2^N - j / 2^D`.
  have h_sum : ∑ j ∈ Finset.range (2 ^ D), ((Finset.range (2 ^ N)).filter (fun R => 2 ^ N ≤ (rnite ((j : ℝ) / 2 ^ D * 2 ^ N)).toNat + R)).card / (2 : ℝ) ^ N - ∑ j ∈ Finset.range (2 ^ D), (j : ℝ) / 2 ^ D = ∑ j ∈ Finset.range (2 ^ D), ((rnite ((j : ℝ) * 2 ^ N / 2 ^ D) : ℝ) / 2 ^ N - (j : ℝ) / 2 ^ D) := by
    rw [ ← Finset.sum_sub_distrib ];
    refine Finset.sum_congr rfl fun j hj => ?_;
    convert src_pointwise_bias N D hN hND j ( Finset.mem_range.mp hj ) using 1;
  simp_all +decide [ Finset.sum_sub_distrib ];
  convert congr_arg ( fun x : ℝ => x / 2 ^ N ) ( rnite_unbiased_finite N D hN hND ) using 1 <;> norm_num [ Finset.sum_div _ _ _ ];
  norm_num [ sub_div, Finset.sum_div _ _ _ ];
  exact Finset.sum_congr rfl fun _ _ => by rw [ eq_div_iff ( by positivity ) ] ; ring;

/-! ## Phase 3: SRC Variance Bound -/

/-
The second moment of the SRC rounding error, averaged over R.
For η' = k/2^N: E_R[ε²] = η'(1 - η').
-/
lemma src_second_moment (N : ℕ) (hN : 0 < N)
    (k : ℕ) (hk : k < 2 ^ N) :
    (1 / (2 : ℝ) ^ N) *
      ((Finset.range (2 ^ N)).sum
        (fun R => if 2 ^ N ≤ k + R
                  then (1 - (k : ℝ) / (2 : ℝ) ^ N) ^ 2
                  else ((k : ℝ) / (2 : ℝ) ^ N) ^ 2))
    = ((k : ℝ) / (2 : ℝ) ^ N) * (1 - (k : ℝ) / (2 : ℝ) ^ N) := by
  convert srf_second_moment N hN k hk using 1;
  convert rfl using 3 ; norm_num ; ring;
  split_ifs <;> norm_num at * <;> norm_cast at *;
  · rw [ div_add', div_add', le_div_iff₀ ] at * <;> norm_cast at * ; linarith [ Nat.pow_le_pow_right two_pos hN ];
  · rw [ div_add', div_add', div_lt_iff₀ ] at * <;> norm_cast at * ; linarith [ Nat.pow_le_pow_right two_pos hN ]

/-
The second moment of SRC error relative to the *true* input η (not η').
-/
lemma src_variance_vs_true_input (_N : ℕ) (_hN : 0 < _N)
    (η η' : ℝ) (_hη0 : 0 ≤ η) (_hη1 : η < 1)
    (_hη'0 : 0 ≤ η') (_hη'1 : η' ≤ 1)
    (hclose : |η' - η| ≤ 1 / 2) :
    η' * (1 - η) ^ 2 + (1 - η') * η ^ 2 ≤ 1 / 4 + |η' - η| := by
  cases abs_cases ( η' - η ) <;> push_cast [ * ] <;> nlinarith [ sq_nonneg ( η - 1 / 2 ) ]

/-! ## Phase 4: Assembly — √n for SRC -/

/-
For n independent SRC stochastic roundings with N random bits,
applied to finite-precision inputs with D ≥ N excess bits,
the RMS total error is at most √n / 2 ULPs.
-/
theorem src_summation_sqrt_n (n : ℕ) (N : ℕ) (hN : 0 < N)
    (ks : Fin n → ℕ) (hks : ∀ i, ks i < 2 ^ N)
    (err : Fin n → ℕ → ℝ)
    (herr : ∀ i R, err i R =
      if 2 ^ N ≤ ks i + R
      then 1 - (ks i : ℝ) / (2 : ℝ) ^ N
      else -((ks i : ℝ) / (2 : ℝ) ^ N)) :
    Real.sqrt ((∑ Rs ∈ Finset.univ (α := Fin n → Fin (2 ^ N)),
      (∑ i : Fin n, err i (Rs i).val) ^ 2)
      / ((2 : ℝ) ^ N) ^ n)
    ≤ Real.sqrt (n : ℝ) / 2 := by
  have := variance_sum_bound n N (fun i R => err i R);
  refine Real.sqrt_le_iff.mpr ⟨ ?_, ?_ ⟩;
  · positivity;
  · convert this _ _ using 1;
    · norm_num [ div_pow ];
    · intro i; specialize hks i; simp_all +decide [ Finset.sum_ite ] ;
      rw [ show ( Finset.filter ( fun x => 2 ^ N ≤ ks i + x ) ( Finset.range ( 2 ^ N ) ) ) = Finset.Ico ( 2 ^ N - ks i ) ( 2 ^ N ) from ?_, show ( Finset.filter ( fun x => ks i + x < 2 ^ N ) ( Finset.range ( 2 ^ N ) ) ) = Finset.range ( 2 ^ N - ks i ) from ?_ ] <;> norm_num [ Nat.cast_sub hks.le ] ; ring;
      · norm_num [ mul_assoc, ← mul_pow ];
      · grind;
      · grind;
    · -- Apply the variance_single_le_quarter lemma to each term in the sum.
      have h_var_single : ∀ i, (∑ R ∈ Finset.range (2 ^ N), (err i R) ^ 2) / (2 ^ N : ℝ) ≤ 1 / 4 := by
        intro i
        have h_var : (∑ R ∈ Finset.range (2 ^ N), (err i R) ^ 2) / (2 ^ N : ℝ) = (ks i : ℝ) / (2 ^ N : ℝ) * (1 - (ks i : ℝ) / (2 ^ N : ℝ)) := by
          convert src_second_moment N hN ( ks i ) ( hks i ) using 1;
          grind
        exact h_var.symm ▸ by linarith [ sq_nonneg ( ( ks i : ℝ ) / 2 ^ N - 1 / 2 ) ] ;
      assumption

end
