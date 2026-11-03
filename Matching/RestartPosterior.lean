import Matching.CompletionPosterior
import Matching.PosteriorService

/-! Restart the posterior allocation model at an observed first completion.
The completed demand is frozen, survivor labels are retained, and the new
posterior rate is the conditional allocation on that winner branch.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching.PosteriorData

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : PosteriorData H ι)

noncomputable def restartData (q : HistoryServiceFamily H ι)
    {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (j : ι) :
    PosteriorData (H × ℝ) {i : ι // i ≠ j} :=
  p.afterCompletion j
    ((((measurable_pi_apply j).comp hξ).comp measurable_fst).add (q.measurable_service j))

noncomputable def restartInitial (q : HistoryServiceFamily H ι)
    (ξ : H → (ι → ℝ)) (j : ι) (h : H × ℝ) (i : {i : ι // i ≠ j}) : ℝ :=
  ξ h.1 i.1 + (q.curves h.1).service i.1 h.2

omit p in
theorem measurable_restartInitial (q : HistoryServiceFamily H ι)
    {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (j : ι) :
    Measurable (restartInitial q ξ j) := by
  apply measurable_pi_lambda
  intro i
  exact (((measurable_pi_apply i.1).comp hξ).comp measurable_fst).add
    (q.measurable_service i.1)

omit p in
theorem reconstruct_add_initial (q : HistoryServiceFamily H ι)
    (ξ : H → (ι → ℝ)) (j : ι) (h : H × ℝ) (z : {i : ι // i ≠ j} → ℝ) :
    ξ h.1 + (q.curves h.1).reconstructMarked j (h.2, z) =
      (splitDemand j).symm (ξ h.1 j + (q.curves h.1).service j h.2,
        restartInitial q ξ j h + z) := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [ServiceCurveFamily.reconstructMarked, splitDemand, Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [ServiceCurveFamily.reconstructMarked, splitDemand, Equiv.funSplitAt, Equiv.piSplitAt,
      hk, restartInitial, add_comm, add_left_comm, add_assoc]

theorem restart_rate_conditionalExpectation (q : HistoryServiceFamily H ι)
    (ν : Measure H) [IsFiniteMeasure ν] (j : ι)
    {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (i : {i : ι // i ≠ j}) :
    (fun x : H × (ι → ℝ) => posteriorRate (p.restartData q hξ j).allocation
      (x.1, q.clock j x) (restartInitial q ξ j (x.1, q.clock j x)) i)
      =ᵐ[(ν.prod independentExponentials).restrict (q.winner j)]
    ((ν.prod independentExponentials).restrict (q.winner j))[
      fun x => p.allocation (x.1, ξ x.1 + x.2) i.1 |
      (inferInstance : MeasurableSpace (H × ℝ)).comap (fun x => (x.1, q.clock j x))] := by
  have hid := p.completion_resampling_conditionalExpectation q ν j hξ i.1
  have heq : (fun x : H × (ι → ℝ) => posteriorRate (p.restartData q hξ j).allocation
      (x.1, q.clock j x) (restartInitial q ξ j (x.1, q.clock j x)) i) =
      (fun x : H × (ι → ℝ) => ∫ z,
        p.allocation (x.1, ξ x.1 +
          (q.curves x.1).reconstructMarked j (q.clock j x, z)) i.1 ∂independentExponentials) := by
    funext x
    change (∫ z, p.allocation (x.1,
        (splitDemand j).symm (ξ x.1 j + (q.curves x.1).service j (q.clock j x),
          restartInitial q ξ j (x.1, q.clock j x) + z)) i.1 ∂independentExponentials) = _
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    exact congrArg (fun v => p.allocation (x.1, v) i.1)
      (reconstruct_add_initial q ξ j (x.1, q.clock j x) z).symm
  rw [heq]
  exact hid

end StochasticMatching.PosteriorData
