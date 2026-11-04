import Matching.ConditionalTransport
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! Glue conditional identities established under individual branch measures
into an identity on the original sample space. The branch events must be
observable in the conditioning sigma-algebra; coverage is required only a.e.
-/

open MeasureTheory Set

namespace StochasticMatching

variable {Ω κ : Type*} [mΩ : MeasurableSpace Ω] [Countable κ]

theorem conditionalExpectation_of_branch_cover (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (s : κ → Set Ω)
    (hs : ∀ j, MeasurableSet[m] (s j))
    (hcover : ∀ᵐ x ∂μ, ∃ j, x ∈ s j) {f g : Ω → ℝ} (hf : Integrable f μ)
    (hlocal : ∀ j, g =ᵐ[μ.restrict (s j)] (μ.restrict (s j))[f | m]) :
    g =ᵐ[μ] μ[f | m] := by
  have hall : ∀ᵐ x ∂μ, ∀ j, x ∈ s j → g x = (μ[f | m]) x := by
    apply ae_all_iff.mpr
    intro j
    apply (ae_restrict_iff' (hm _ (hs j))).mp
    exact (hlocal j).trans (condExp_restrict_ae_eq_restrict hm (hs j) hf)
  filter_upwards [hall, hcover] with x hx hc
  obtain ⟨j, hj⟩ := hc
  exact hx j hj

end StochasticMatching
