import Matching.FixedCountOffline
import Matching.PoissonTransferMoments

/-! Exact comparison between the iid offline benchmark and its Poisson
count mixture. No concavity or sampling inequality is assumed. -/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace StochasticMatching

noncomputable def poissonAverage (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑' k, poissonWeight n k * f k

theorem summable_poisson_mul_bounded (n : ℕ) (f : ℕ → ℝ) (M : ℝ)
    (h0 : ∀ k, 0 ≤ f k) (hM : ∀ k, f k ≤ M) :
    Summable (fun k => poissonWeight n k * f k) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (poissonWeight_nonneg (Nat.cast_nonneg n) k) (h0 k))
    (fun k => mul_le_mul_of_nonneg_left (hM k) (poissonWeight_nonneg (Nat.cast_nonneg n) k))
  exact (poissonWeight_sum (n : ℝ≥0)).summable.mul_right M

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem fixedCountOffline_shortfall_bound (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (1 - ((n - k : ℕ) : ℝ) / n) * fixedCountOffline N ν n ≤ fixedCountOffline N ν k := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hkn : k ≤ n
  · by_cases hk : k = 0
    · subst k
      simpa [div_self hnR.ne'] using fixedCountOffline_nonneg N ν 0
    · have hs := fixedCountOffline_sampling N ν k n (Nat.pos_of_ne_zero hk) hkn
      rw [Nat.cast_sub hkn]
      have he : (1 - ((n : ℝ) - k) / n) * fixedCountOffline N ν n =
          ((k : ℝ) * fixedCountOffline N ν n) / n := by field_simp
      rw [he]
      exact (div_le_iff₀ hnR).mpr (by simpa [mul_comm] using hs)
  · have hnk : n ≤ k := le_of_not_ge hkn
    simpa [Nat.sub_eq_zero_of_le hnk] using fixedCountOffline_monotone N ν hnk

theorem summable_fixedCountOffline_poisson (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν]
    (n : ℕ) : Summable (fun k => poissonWeight n k * fixedCountOffline N ν k) :=
  summable_poisson_mul_bounded n _ (Fintype.card ι) (fixedCountOffline_nonneg N ν)
    (fixedCountOffline_le_card N ν)

theorem fixedCountOffline_poisson_lower (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 0 < n) :
    (1 - poissonWeight n n) * fixedCountOffline N ν n ≤ poissonAverage n (fixedCountOffline N ν) := by
  let F := fixedCountOffline N ν n
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hlow := ((poissonWeight_sum (n : ℝ≥0)).mul_right F).sub
    (((poissonWeight_shortfall n).div_const (n : ℝ)).mul_right F)
  have he : F - ((n : ℝ) * poissonWeight n n / n) * F = (1 - poissonWeight n n) * F := by
    field_simp [hnR]
    <;> ring
  have hpoint (k : ℕ) : poissonWeight n k * F - (((n - k : ℕ) : ℝ) * poissonWeight n k / n) * F =
      poissonWeight n k * ((1 - ((n - k : ℕ) : ℝ) / n) * F) := by ring
  simp only [NNReal.coe_natCast, one_mul, Pi.sub_apply, he, hpoint] at hlow
  exact hasSum_le (fun k => mul_le_mul_of_nonneg_left (fixedCountOffline_shortfall_bound N ν n hn k)
    (poissonWeight_nonneg (Nat.cast_nonneg n) k)) hlow (summable_fixedCountOffline_poisson N ν n).hasSum

end StochasticMatching
