import Matching.PoissonThresholdAugmentation

/-! Poisson/exponential deficiency duality for a monotonically indexed chain
of job sets, including the independent random threshold.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

theorem indexed_poisson_exponential_chain_law {n : ℕ} (N : σ → Finset ι)
    (intensity : σ → ℝ≥0) (A : Fin n → Finset ι) (hA : Monotone A) (a : ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | ∀ k, (a : ℝ) < supplyDeficiency N (fun s => (intensity s : ℝ)) z (A k)} =
      ((independentPoissons intensity).prod (poissonMeasure a)).real
        {p : (σ → ℕ) × ℕ | ∀ k,
          (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) (A k)} := by
  have h := nested_subset_waiting_threshold_law A hA (fun k => touchingTypes N (A k))
    ((touchingTypes_mono N).comp hA) intensity a
  have hl : {z : ι → ℝ | ∀ k, (a : ℝ) < supplyDeficiency N (fun s => (intensity s : ℝ)) z (A k)} =
      {z | ∀ k, (a : ℝ) + ∑ s ∈ touchingTypes N (A k), (intensity s : ℝ) < ∑ i ∈ A k, z i} := by
    ext z
    simp only [mem_setOf_eq, supplyDeficiency, lt_sub_iff_add_lt, supplyCoverage_eq_touching_sum]
  have hr : {p : (σ → ℕ) × ℕ | ∀ k,
        (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) (A k)} =
      {p | ∀ k, p.2 + (∑ s ∈ touchingTypes N (A k), p.1 s) < (A k).card} := by
    ext p
    simp only [mem_setOf_eq]
    apply forall_congr'
    intro k
    simp only [supplyDeficiency, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← arrivalCoverageCount_cast, lt_sub_iff_add_lt, ← Nat.cast_add, Nat.cast_lt,
      arrivalCoverageCount_eq_touching_sum]
  rw [hl, hr]
  exact h

end StochasticMatching
