import Matching.MarkedRoutingTrajectory
import Matching.RenewalInputTrajectory

/-! Recording online decisions preserves the full independent-renewal input
law, including every typed arrival and every intermediate observed log. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem markedTrajectory_renewal_input_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c))
    (x : RoutingCursor n H ι × RoutedMemory σ J) :
    Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ J) =>
      fun k => Sum.map id (fun y : RoutingCursor n H ι × RoutedMemory σ J =>
        (s.cursorHorizon n label y.1, routedMemoryInput y.2)) (z k))
      (s.markedTrajectory n label N c hc hmem x) =
      Measure.map (loggedIndependentStreamPath c hc Subtype.val measurable_subtype_coe
        (fun b => b.2) (remainingTimeUpdate (E := σ)) measurable_remainingTimeUpdate
        (s.cursorHorizon n label x.1, routedMemoryInput x.2)) independentRenewalStreams := by
  have h := congrArg (Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ) =>
    fun k => Sum.map id (fun y => (s.cursorHorizon n label y.1, y.2)) (z k)))
    (s.markedTrajectory_erase_marks n label N c hc hmem x)
  have hf : Measurable (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ) =>
      fun k => Sum.map id (fun y => (s.cursorHorizon n label y.1, y.2)) (z k)) :=
    measurable_pi_lambda _ (fun k => (measurable_id.sumMap
      ((s.measurable_cursorHorizon n label).prodMap measurable_id)).comp (measurable_pi_apply k))
  have he : Measurable (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ J) => fun k =>
      Sum.map id (fun y : RoutingCursor n H ι × RoutedMemory σ J => (y.1, routedMemoryInput y.2)) (z k)) :=
    measurable_pi_lambda _ (fun k => (measurable_id.sumMap (measurable_fst.prodMk
      (measurable_routedMemoryInput.comp measurable_snd))).comp (measurable_pi_apply k))
  rw [Measure.map_map hf he, s.loggedTrajectory_renewal_input_law] at h
  have heq : (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ J) => fun k =>
      Sum.map id (fun y => (s.cursorHorizon n label y.1, y.2))
        (Sum.map id (fun y => (y.1, routedMemoryInput y.2)) (z k))) =
      (fun z => fun k => Sum.map id (fun y => (s.cursorHorizon n label y.1, routedMemoryInput y.2)) (z k)) := by
    funext z k
    cases z k <;> rfl
  simpa only [Function.comp_def, heq] using h

end StochasticMatching.PosteriorStage
