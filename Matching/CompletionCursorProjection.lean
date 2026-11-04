import Matching.CompletionOutputTermination
import Matching.TerminalPayloadProjection

/-! Forgetting the retained completion output recovers the exact original
posterior cursor trajectory, with all its previously proved process laws. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem completionRoutingKernel_live (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (x : RoutingCursor n H ι) :
    s.completionRoutingKernel n label L elapsed k N capacity hc hmem (.inr x) =
      Measure.map (fun u => fillTerminal (s.cursorLog n label L elapsed k x, u))
        (routingTransition N capacity hc (s.cursorService n label)
          (s.cursorService_supply_feasible n label N capacity hc hmem) (s.typedCursorUpdate n label) x) := by
  letI := historyRoutingKernel_markov N capacity hc (s.completionStateService n label)
    (s.completionStateService_feasible n label N capacity hc hmem)
  letI := historyRoutingKernel_markov N capacity hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N capacity hc hmem)
  have hu : Measurable (fun e : Unit ⊕ (ℝ × (σ × Option J)) => s.typedCursorUpdate n label (x, e)) :=
    (s.measurable_typedCursorUpdate n label).comp measurable_prodMk_left
  have hm : Measurable (fun u : Unit ⊕ RoutingCursor n H ι =>
      fillTerminal (s.cursorLog n label L elapsed k x, u)) :=
    measurable_fillTerminal.comp (measurable_const.prodMk measurable_id)
  unfold completionRoutingKernel routingTransition
  rw [eventUpdateKernel_apply _ _ (measurable_routingJobUpdate _
      (s.measurable_completionStateUpdate n label L hL elapsed he k)),
    eventUpdateKernel_apply _ _ (s.measurable_typedCursorUpdate n label),
    Measure.map_map hm hu]
  rfl

theorem completionRoutingTrajectory_cursor_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (x : RoutingCursor n H ι) :
    letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
    Measure.map (fun z : ℕ → CompletionLog J ⊕ RoutingCursor n H ι =>
      fun m => forgetTerminal (z m))
      (markovTrajectory (s.completionRoutingKernel n label L elapsed k N capacity hc hmem) (.inr x)) =
      s.routingTrajectory n label N capacity hc hmem x := by
  try dsimp only
  letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
  letI := routingTransition_markov N capacity hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N capacity hc hmem)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label)
  exact terminalPayload_trajectory_projection _ _ (s.cursorLog n label L elapsed k)
    (s.completionRoutingKernel_terminal n label L hL elapsed he k N capacity hc hmem)
    (s.completionRoutingKernel_live n label L hL elapsed he k N capacity hc hmem) (.inr x)

end StochasticMatching.PosteriorStage
