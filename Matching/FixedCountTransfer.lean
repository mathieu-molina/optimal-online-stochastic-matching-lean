import Matching.FinitePolicySampling
import Matching.FixedPoissonComparison
import Matching.PoissonDiagonalBound

/-! An exact fixed-count transfer for finite causal matching policies.
Random policies, including policies obtained by fixing independent clocks
and random seeds, are arbitrary probability laws on finite causal policies.
The Poisson benchmark is the count mixture of actual iid offline optima. -/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem fixedOnlineValue_excess_bound (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (n : ℕ) (hn : 0 < n) (k : ℕ) :
    fixedOnlineValue N ν k ≤ fixedOnlineValue N ν n +
      ((k - n : ℕ) : ℝ) / n * fixedCountOffline N ν n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hkn : k ≤ n
  · simpa [Nat.sub_eq_zero_of_le hkn] using fixedOnlineValue_monotone N ν hkn
  · have hnk : n ≤ k := le_of_not_ge hkn
    have hs := fixedOnlineValue_sampling N ν n k hn hnk
    have hb := mul_le_mul_of_nonneg_left (fixedOnlineValue_le_offline N ν n)
      (sub_nonneg.mpr (Nat.cast_le.mpr hnk) : (0 : ℝ) ≤ (k : ℝ) - n)
    rw [Nat.cast_sub hnk]
    apply (mul_le_mul_right hnR).mp
    have he : (fixedOnlineValue N ν n + ((k : ℝ) - n) / n * fixedCountOffline N ν n) * n =
        (n : ℝ) * fixedOnlineValue N ν n + ((k : ℝ) - n) * fixedCountOffline N ν n := by
      field_simp
      <;> ring
    rw [he]
    nlinarith

theorem summable_fixedOnlineValue_poisson (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    Summable (fun k => poissonWeight n k * fixedOnlineValue N ν k) :=
  summable_poisson_mul_bounded n _ (Fintype.card ι) (fixedOnlineValue_nonneg N ν)
    (fun k => (fixedOnlineValue_le_offline N ν k).trans (fixedCountOffline_le_card N ν k))

theorem fixedOnlineValue_poisson_upper (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (n : ℕ) (hn : 0 < n) :
    poissonAverage n (fixedOnlineValue N ν) ≤
      fixedOnlineValue N ν n + poissonWeight n n * fixedCountOffline N ν n := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum := ((poissonWeight_sum (n : ℝ≥0)).mul_right (fixedOnlineValue N ν n)).add
    (((poissonWeight_excess n).div_const (n : ℝ)).mul_right (fixedCountOffline N ν n))
  have he : (n : ℝ) * poissonWeight n n / n = poissonWeight n n := by field_simp
  have he' (k : ℕ) : poissonWeight n k * fixedOnlineValue N ν n +
      (((k - n : ℕ) : ℝ) * poissonWeight n k / n) * fixedCountOffline N ν n =
      poissonWeight n k * (fixedOnlineValue N ν n +
        ((k - n : ℕ) : ℝ) / n * fixedCountOffline N ν n) := by ring
  simp only [NNReal.coe_natCast, one_mul, Pi.add_apply, he, he'] at hsum
  exact hasSum_le (fun k => mul_le_mul_of_nonneg_left (fixedOnlineValue_excess_bound N ν n hn k)
    (poissonWeight_nonneg (Nat.cast_nonneg n) k))
      (summable_fixedOnlineValue_poisson N ν n).hasSum hsum

noncomputable def randomizedPolicyReward {N : σ → Finset ι} (ν : Measure σ) {k : ℕ}
    (π : Measure (FiniteOnlinePolicy N k)) : ℝ := ∫ P, P.expectedReward ν ∂π

theorem randomizedPolicyReward_le_value {N : σ → Finset ι} (ν : Measure σ) {k : ℕ}
    (π : Measure (FiniteOnlinePolicy N k)) [IsProbabilityMeasure π] :
    randomizedPolicyReward ν π ≤ fixedOnlineValue N ν k := by
  have h := integral_mono (μ := π) Integrable.of_finite
    (integrable_const (fixedOnlineValue N ν k)) (finite_policy_le_value ν)
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

theorem randomizedPolicyReward_nonneg {N : σ → Finset ι} (ν : Measure σ) {k : ℕ}
    (π : Measure (FiniteOnlinePolicy N k)) : 0 ≤ randomizedPolicyReward ν π :=
  integral_nonneg (fun P => P.expectedReward_nonneg ν)

theorem poisson_randomized_reward_le (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (π : ∀ k, Measure (FiniteOnlinePolicy N k))
    [∀ k, IsProbabilityMeasure (π k)] (n : ℕ) :
    poissonAverage n (fun k => randomizedPolicyReward ν (π k)) ≤
      poissonAverage n (fixedOnlineValue N ν) := by
  have hs := summable_poisson_mul_bounded n (fun k => randomizedPolicyReward ν (π k))
    (Fintype.card ι) (fun k => randomizedPolicyReward_nonneg ν (π k))
    (fun k => (randomizedPolicyReward_le_value ν (π k)).trans
      ((fixedOnlineValue_le_offline N ν k).trans (fixedCountOffline_le_card N ν k)))
  exact hasSum_le (fun k => mul_le_mul_of_nonneg_left (randomizedPolicyReward_le_value ν (π k))
    (poissonWeight_nonneg (Nat.cast_nonneg n) k)) hs.hasSum (summable_fixedOnlineValue_poisson N ν n).hasSum

theorem fixed_count_policy_transfer (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (π : ∀ k, Measure (FiniteOnlinePolicy N k))
    [∀ k, IsProbabilityMeasure (π k)] (n : ℕ) (hn : 0 < n) :
    poissonAverage n (fun k => randomizedPolicyReward ν (π k)) -
      poissonWeight n n * fixedCountOffline N ν n ≤ (bestFinitePolicy N ν n).expectedReward ν := by
  have h := (poisson_randomized_reward_le N ν π n).trans (fixedOnlineValue_poisson_upper N ν n hn)
  change _ ≤ fixedOnlineValue N ν n
  linarith

theorem fixed_count_competitive_transfer (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (π : ∀ k, Measure (FiniteOnlinePolicy N k))
    [∀ k, IsProbabilityMeasure (π k)] (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (hcompetitive : c * poissonAverage n (fixedCountOffline N ν) ≤
      poissonAverage n (fun k => randomizedPolicyReward ν (π k))) :
    (c - (c + 1) * poissonWeight n n) * fixedCountOffline N ν n ≤
      (bestFinitePolicy N ν n).expectedReward ν := by
  have hF := mul_le_mul_of_nonneg_left (fixedCountOffline_poisson_lower N ν n hn) hc
  have hP := fixed_count_policy_transfer N ν π n hn
  nlinarith

theorem fixed_count_competitive_transfer_sqrt (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (π : ∀ k, Measure (FiniteOnlinePolicy N k))
    [∀ k, IsProbabilityMeasure (π k)] (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (hcompetitive : c * poissonAverage n (fixedCountOffline N ν) ≤
      poissonAverage n (fun k => randomizedPolicyReward ν (π k))) :
    (c - (c + 1) / Real.sqrt (2 * Real.pi * (n : ℝ))) * fixedCountOffline N ν n ≤
      (bestFinitePolicy N ν n).expectedReward ν := by
  apply le_trans _ (fixed_count_competitive_transfer N ν π n hn c hc hcompetitive)
  apply mul_le_mul_of_nonneg_right _ (fixedCountOffline_nonneg N ν n)
  have h := mul_le_mul_of_nonneg_left (poissonWeight_diagonal_le n hn) (show 0 ≤ c + 1 by linarith)
  simpa only [mul_one_div] using sub_le_sub_left h c

theorem fixed_count_matching_transfer (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (π : ∀ k, Measure (FiniteOnlinePolicy N k))
    [∀ k, IsProbabilityMeasure (π k)] (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (hcompetitive : c * poissonAverage n (fixedCountOffline N ν) ≤
      poissonAverage n (fun k => randomizedPolicyReward ν (π k))) :
    ∃ P : FiniteOnlinePolicy N n,
      (c - (c + 1) * poissonWeight n n) * fixedCountOffline N ν n ≤
        ∫ x, ((P.matching x).size : ℝ) ∂iidArrivalLaw ν n := by
  refine ⟨bestFinitePolicy N ν n, ?_⟩
  simp_rw [FiniteOnlinePolicy.matching_size]
  exact fixed_count_competitive_transfer N ν π n hn c hc hcompetitive

theorem fixed_count_matching_transfer_sqrt (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (π : ∀ k, Measure (FiniteOnlinePolicy N k))
    [∀ k, IsProbabilityMeasure (π k)] (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (hcompetitive : c * poissonAverage n (fixedCountOffline N ν) ≤
      poissonAverage n (fun k => randomizedPolicyReward ν (π k))) :
    ∃ P : FiniteOnlinePolicy N n,
      (c - (c + 1) / Real.sqrt (2 * Real.pi * (n : ℝ))) * fixedCountOffline N ν n ≤
        ∫ x, ((P.matching x).size : ℝ) ∂iidArrivalLaw ν n := by
  refine ⟨bestFinitePolicy N ν n, ?_⟩
  simp_rw [FiniteOnlinePolicy.matching_size]
  exact fixed_count_competitive_transfer_sqrt N ν π n hn c hc hcompetitive

end StochasticMatching
