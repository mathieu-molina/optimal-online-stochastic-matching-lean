import Matching.MarkedMatchingOutput
import Matching.CursorPayoffLaw

/-! Equality of the actual matching-cardinality payoff law and the stopped
completion-log payoff law, hence equality of their expected rewards. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {H ι σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem measurable_observedRoutingMatching_reward {A : Type*} [MeasurableSpace A]
    (N : σ → Finset ι) : Measurable (fun z : ℕ → Unit ⊕ (A × RoutedMemory σ ι) =>
      ((observedRoutingMatching N z).size : ℝ)) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (measurable_observedRoutingMatching_size N)

namespace PosteriorStage

theorem markedTrajectory_cursor_law (n : ℕ) (s : PosteriorStage H ι)
    (N : σ → Finset ι) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N c))
    (x : RoutingCursor n H ι × RoutedMemory σ ι) :
    Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ ι) =>
      fun k => Sum.map id Prod.fst (z k)) (s.markedTrajectory n id N c hc hmem x) =
      s.routingTrajectory n id N c hc hmem x.1 := by
  have h := congrArg (Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ) =>
    fun k => Sum.map id Prod.fst (z k))) (s.markedTrajectory_erase_marks n id N c hc hmem x)
  have hf : Measurable (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ) =>
      fun k => Sum.map id Prod.fst (z k)) :=
    measurable_pi_lambda _ (fun k => (measurable_id.sumMap measurable_fst).comp (measurable_pi_apply k))
  have he : Measurable (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ ι) => fun k =>
      Sum.map id (fun y : RoutingCursor n H ι × RoutedMemory σ ι => (y.1, routedMemoryInput y.2)) (z k)) :=
    measurable_pi_lambda _ (fun k => (measurable_id.sumMap (measurable_fst.prodMk
      (measurable_routedMemoryInput.comp measurable_snd))).comp (measurable_pi_apply k))
  rw [Measure.map_map hf he, s.loggedTrajectory_cursor_law] at h
  have heq : (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ ι) => fun k =>
      Sum.map id Prod.fst (Sum.map id (fun y => (y.1, routedMemoryInput y.2)) (z k))) =
      (fun z => fun k => Sum.map id Prod.fst (z k)) := by
    funext z k
    cases z k <;> rfl
  simpa only [Function.comp_def, heq] using h

theorem markedTrajectory_matching_payoff_law (s : PosteriorStage H ι)
    (N : σ → Finset ι) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N c)) (h : H) :
    Measure.map (fun z => ((observedRoutingMatching N z).size : ℝ))
      (s.markedTrajectory (Fintype.card ι) id N c hc hmem
        (initialRoutingCursor (Fintype.card ι) h, emptyRoutedMemory)) =
      Measure.map (completionLogReward (Fintype.card ι)) (s.onlineCompletionLogLaw N c hc hmem h) := by
  let n := Fintype.card ι
  let F := fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ ι) =>
    fun k => Sum.map id Prod.fst (z k)
  have hF : Measurable F :=
    measurable_pi_lambda _ (fun k => (measurable_id.sumMap measurable_fst).comp (measurable_pi_apply k))
  have heq : ∀ᵐ z ∂s.markedTrajectory n id N c hc hmem (initialRoutingCursor n h, emptyRoutedMemory),
      ((observedRoutingMatching N z).size : ℝ) = cursorDepthPayoff n (F z) := by
    filter_upwards [s.markedTrajectory_matching_size n id Function.injective_id N c hc hmem h] with z hz
    rw [hz.2]
    change ((lastLiveObservation (fun y => cursorDepth n y.1) 0 z : ℕ) : ℝ) =
      lastLiveObservation (fun x => (cursorDepth n x : ℝ)) 0 (F z)
    rw [lastLiveObservation_map]
    simpa only [Nat.cast_zero, Function.comp_def] using
      lastLiveObservation_comp (fun k : ℕ => (k : ℝ))
        (fun y : RoutingCursor n H ι × RoutedMemory σ ι => cursorDepth n y.1) 0 z
  rw [Measure.map_congr heq]
  change Measure.map (cursorDepthPayoff n ∘ F) _ = _
  rw [← Measure.map_map (measurable_cursorDepthPayoff n) hF,
    s.markedTrajectory_cursor_law, s.routingTrajectory_payoff_law]

theorem markedTrajectory_expected_matching_size (s : PosteriorStage H ι)
    (N : σ → Finset ι) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N c)) (h : H) :
    (∫ z, ((observedRoutingMatching N z).size : ℝ)
      ∂s.markedTrajectory (Fintype.card ι) id N c hc hmem
        (initialRoutingCursor (Fintype.card ι) h, emptyRoutedMemory)) =
      ∫ L, completionLogReward (Fintype.card ι) L ∂s.onlineCompletionLogLaw N c hc hmem h := by
  have he := congrArg (fun μ : Measure ℝ => ∫ r, r ∂μ)
    (s.markedTrajectory_matching_payoff_law N c hc hmem h)
  dsimp only at he
  rw [integral_map_of_stronglyMeasurable (f := fun r : ℝ => r)
      (measurable_observedRoutingMatching_reward (A := RoutingCursor (Fintype.card ι) H ι) N)
      measurable_id.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (f := fun r : ℝ => r) (measurable_completionLogReward (Fintype.card ι))
      measurable_id.stronglyMeasurable] at he
  exact he

end PosteriorStage
end StochasticMatching
