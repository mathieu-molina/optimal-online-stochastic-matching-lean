import Matching.PoissonExponentialChainLaw

/-! Unconditional expected offline equality for every finite stochastic
matching instance, using the proved chain law rather than a hypothesis.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

theorem maximum_deficiency_mixture (N : σ → Finset ι) (intensity : σ → ℝ≥0) (a : ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | (a : ℝ) < maxSupplyDeficiency N (fun s => (intensity s : ℝ)) z} =
      ∫ counts, poissonLowerTail a (hallDeficiency (arrivalNeighbors N counts)) ∂independentPoissons intensity :=
  maximum_deficiency_mixture_of_chain_law N intensity (poisson_exponential_chain_law N intensity) a

theorem expected_offline_equality (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    (∫ z, offlineValue (supplyRegion N (fun s => (intensity s : ℝ))) z ∂independentExponentials) =
      ∫ counts, arrivalOfflineValue N counts ∂independentPoissons intensity :=
  expected_offline_equality_of_chain_law N intensity (poisson_exponential_chain_law N intensity)

end StochasticMatching
