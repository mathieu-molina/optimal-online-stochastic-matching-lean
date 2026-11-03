import Matching.SupermodularTail

/-! The chain formula also holds at a measurable random threshold. This is a
pointwise consequence of supermodularity, so no independence is required for
this combinatorial step of the Poisson/exponential comparison.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

theorem supermodular_sub_constant {d : Finset ι → ℝ} (hd : SupermodularFinset d) (c : ℝ) :
    SupermodularFinset (fun A => d A - c) := by
  intro A B
  have h := hd A B
  dsimp only
  linarith

theorem supermodular_random_threshold_chain_formula (μ : Measure Ω) [IsFiniteMeasure μ]
    {d : Ω → Finset ι → ℝ} (hd : ∀ A, Measurable (fun ω => d ω A))
    (hmod : ∀ᵐ ω ∂μ, SupermodularFinset (d ω)) (T : Ω → ℝ) (hT : Measurable T) :
    μ.real {ω | ∃ A, T ω < d ω A} =
      ∑ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
        (-chainWeight C) * μ.real {ω | ∀ A ∈ C, T ω < d ω A} := by
  have h := supermodular_max_tail_chain_formula μ (fun A => (hd A).sub hT)
    (hmod.mono (fun ω hω => supermodular_sub_constant hω (T ω))) 0
  simpa only [maximumExceedance, chainExceedance, sub_pos] using h

variable {Ω' : Type*} [MeasurableSpace Ω']

theorem maximum_random_threshold_eq_of_chain_laws (μ : Measure Ω) (ν : Measure Ω')
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {d : Ω → Finset ι → ℝ} {e : Ω' → Finset ι → ℝ}
    (hd : ∀ A, Measurable (fun ω => d ω A))
    (he : ∀ A, Measurable (fun ω => e ω A))
    (hdmod : ∀ᵐ ω ∂μ, SupermodularFinset (d ω))
    (hemod : ∀ᵐ ω ∂ν, SupermodularFinset (e ω)) (a : ℝ) (T : Ω' → ℝ) (hT : Measurable T)
    (hchain : ∀ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
      μ.real (chainExceedance d a C) = ν.real {ω | ∀ A ∈ C, T ω < e ω A}) :
    μ.real (maximumExceedance d a) = ν.real {ω | ∃ A, T ω < e ω A} := by
  rw [supermodular_max_tail_chain_formula μ hd hdmod,
    supermodular_random_threshold_chain_formula ν he hemod T hT]
  apply Finset.sum_congr rfl
  intro C hC
  rw [hchain C hC]

end StochasticMatching
