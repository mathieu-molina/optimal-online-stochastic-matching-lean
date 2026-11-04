import Matching.HistoryReconstruction

/-! Allocation data after revealing a completed job's demand. Surviving
coordinates retain their original labels, and the resulting data can be fed
back into the posterior ODE construction.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching.PosteriorData

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : PosteriorData H ι)

noncomputable def afterCompletion (j : ι) {c : H × ℝ → ℝ} (hc : Measurable c) :
    PosteriorData (H × ℝ) {i : ι // i ≠ j} where
  allocation x i := p.allocation (x.1.1, (splitDemand j).symm (c x.1, x.2)) i.1
  measurable_allocation := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.1).comp (p.measurable_allocation.comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((splitDemand j).symm.measurable.comp
          ((hc.comp measurable_fst).prodMk measurable_snd))))
  bound := p.bound
  allocation_nonneg h z i := p.allocation_nonneg h.1 ((splitDemand j).symm (c h, z)) i.1
  allocation_le h z i := p.allocation_le h.1 ((splitDemand j).symm (c h, z)) i.1

theorem completion_resampling_conditionalExpectation
    (q : HistoryServiceFamily H ι) (ν : Measure H) [IsFiniteMeasure ν]
    (j : ι) {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (i : ι) :
    (fun x : H × (ι → ℝ) => ∫ z,
      p.allocation (x.1, ξ x.1 +
        (q.curves x.1).reconstructMarked j (q.clock j x, z)) i ∂independentExponentials)
      =ᵐ[(ν.prod independentExponentials).restrict (q.winner j)]
    ((ν.prod independentExponentials).restrict (q.winner j))[
      fun x => p.allocation (x.1, ξ x.1 + x.2) i |
      (inferInstance : MeasurableSpace (H × ℝ)).comap (fun x => (x.1, q.clock j x))] := by
  let f : H × (ι → ℝ) → ℝ := fun x => p.allocation (x.1, ξ x.1 + x.2) i
  have hf : Measurable f := (measurable_pi_apply i).comp (p.measurable_allocation.comp
    (measurable_fst.prodMk ((hξ.comp measurable_fst).add measurable_snd)))
  have hb : ∀ x, ‖f x‖ ≤ (p.bound : ℝ) := by
    intro x
    rw [Real.norm_of_nonneg (p.allocation_nonneg x.1 (ξ x.1 + x.2) i)]
    exact p.allocation_le x.1 (ξ x.1 + x.2) i
  exact q.completion_conditionalExpectation ν j f hf hb

theorem afterCompletion_rate (j : ι) {c : H × ℝ → ℝ} (hc : Measurable c)
    (h : H × ℝ) (x : {i : ι // i ≠ j} → ℝ) (i : {i : ι // i ≠ j}) :
    posteriorRate (p.afterCompletion j hc).allocation h x i =
      ∫ z, p.allocation (h.1, (splitDemand j).symm (c h, x + z)) i.1
        ∂independentExponentials := rfl

end StochasticMatching.PosteriorData
