import Matching.IndexedDeficiencyChainLaw
import Matching.ChainEnumeration
import Matching.OfflineDualityReduction

/-! The complete finite Poisson/exponential chain law (Lemma 3.4), with the
random Poisson threshold and arbitrary overlapping arrival neighborhoods.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

theorem poisson_exponential_nested_family_law (N : σ → Finset ι) (intensity : σ → ℝ≥0)
    (C : Finset (Finset ι)) (hC : NestedFamily C) (a : ℝ≥0) :
    (independentExponentials (ι := ι)).real
      (chainExceedance (supplyDeficiency N (fun s => (intensity s : ℝ))) a C) =
    ((independentPoissons intensity).prod (poissonMeasure a)).real
      {p : (σ → ℕ) × ℕ | ∀ A ∈ C,
        (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) A} := by
  obtain ⟨e, hmono, he⟩ := nested_family_enumeration C hC
  have h := indexed_poisson_exponential_chain_law N intensity e hmono a
  have hl : chainExceedance (supplyDeficiency N (fun s => (intensity s : ℝ))) a C =
      {z : ι → ℝ | ∀ k, (a : ℝ) < supplyDeficiency N (fun s => (intensity s : ℝ)) z (e k)} := by
    ext z
    exact forall_mem_iff_forall_enumeration C e he _
  have hr : {p : (σ → ℕ) × ℕ | ∀ A ∈ C,
        (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) A} =
      {p | ∀ k, (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) (e k)} := by
    ext p
    exact forall_mem_iff_forall_enumeration C e he _
  rw [hl, hr]
  exact h

theorem poisson_exponential_chain_law (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    PoissonExponentialChainLaw N intensity := by
  intro a C hC
  exact poisson_exponential_nested_family_law N intensity C
    (mem_finiteChains.mp (Finset.mem_erase.mp hC).2).2 a

end StochasticMatching
