import Matching.ExponentialChainRecurrence
import Matching.PoissonChainRecurrence

/-! Joint exponential/Poisson duality for arbitrary finite chains, first
for independent increments and then for nested subsets of arrival types.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {n : ℕ} {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

theorem exponential_poisson_finite_chain_law (A : Fin n → Finset ι) (hA : Monotone A)
    (a : Fin n → ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | ∀ k, ((cumulativeFin a k : ℝ≥0) : ℝ) < ∑ i ∈ A k, z i} =
      (independentPoissons a).real {x | ∀ k, cumulativeFin x k < (A k).card} :=
  (exponential_nested_chain_value A hA a).trans (poisson_chain_value a (fun k => (A k).card)).symm

theorem nested_subset_waiting_count_law (A : Fin n → Finset ι) (hA : Monotone A)
    (F : Fin n → Finset σ) (hF : Monotone F) (a : σ → ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | ∀ k, ((∑ s ∈ F k, a s : ℝ≥0) : ℝ) < ∑ i ∈ A k, z i} =
      (independentPoissons a).real {x | ∀ k, (∑ s ∈ F k, x s) < (A k).card} := by
  let b : Fin n → ℝ≥0 := fun k => ∑ s ∈ disjointed F k, a s
  have hk : ∀ k, cumulativeFin b k = ∑ s ∈ F k, a s := fun k =>
    (nested_sum_eq_block_sums F hF a k).symm
  have he := exponential_poisson_finite_chain_law A hA b
  simp only [hk] at he
  have hp := congrArg (fun μ : Measure (Fin n → ℕ) => μ.real {x | ∀ k, x k < (A k).card})
    (nested_poisson_counts_law a F hF)
  dsimp only at hp
  rw [map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    map_measureReal_apply (measurable_of_countable _) (Set.to_countable _).measurableSet] at hp
  exact he.trans hp.symm

end StochasticMatching
