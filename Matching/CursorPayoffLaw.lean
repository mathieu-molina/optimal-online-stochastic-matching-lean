import Matching.TerminalPayloadPayoff
import Matching.CompletionCursorProjection
import Matching.OnlineCompletionLaw
import Matching.CursorCombinatorics

/-! The last live cursor depth has exactly the payoff law of the stopped
completion log. This connects the matching invariant to the scheduling
payoff already established in the archive. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {H ι : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

noncomputable def cursorDepthPayoff (n : ℕ) (z : ℕ → Unit ⊕ RoutingCursor n H ι) : ℝ :=
  lastLiveObservation (fun x => (cursorDepth n x : ℝ)) 0 z

theorem measurable_cursorDepthPayoff (n : ℕ) :
    Measurable (cursorDepthPayoff (H := H) (ι := ι) n) :=
  measurable_lastLiveObservation _ ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_cursorDepth n)) 0

namespace PosteriorStage
variable {σ : Type} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem routingTrajectory_payoff_law (s : PosteriorStage H ι)
    (N : σ → Finset ι) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N c)) (h : H) :
    Measure.map (cursorDepthPayoff (Fintype.card ι))
      (s.routingTrajectory (Fintype.card ι) id N c hc hmem (initialRoutingCursor (Fintype.card ι) h)) =
      Measure.map (completionLogReward (Fintype.card ι)) (s.onlineCompletionLogLaw N c hc hmem h) := by
  let n := Fintype.card ι
  let L : H → CompletionLog ι := fun _ => emptyCompletionLog
  let e : H → ℝ := fun _ => 0
  let K := s.completionRoutingKernel n id L e 0 N c hc hmem
  letI := s.completionRoutingKernel_markov n id L measurable_const e measurable_const 0 N c hc hmem
  let O := s.cursorLog n id L e 0
  let g := completionLogReward (J := ι) n
  let a : RoutingCursor n H ι := initialRoutingCursor n h
  have hpay := terminalPayload_lastLive_payoff_ae K
    (routingTransition N c hc (s.cursorService n id)
      (s.cursorService_supply_feasible n id N c hc hmem) (s.typedCursorUpdate n id))
    O (s.measurable_cursorLog n id L measurable_const e measurable_const 0)
    g (measurable_completionLogReward n) 0 a
    (s.completionRoutingKernel_live n id L measurable_const e measurable_const 0 N c hc hmem)
    (s.completionRoutingTrajectory_finite_termination n id L measurable_const e measurable_const 0
      N c hc hmem (.inr a))
  have hdepth : g ∘ O = fun x : RoutingCursor n H ι => (cursorDepth n x : ℝ) := by
    funext x
    exact s.cursorLogReward_eq_depth n id x
  have heq : ∀ᵐ z ∂markovTrajectory K (.inr a),
      cursorDepthPayoff n (fun k => forgetTerminal (z k)) =
        g (s.stoppedCompletionLog n id L e 0 z) := by
    filter_upwards [hpay] with z hz
    change lastLiveObservation (fun x => (cursorDepth n x : ℝ)) 0 _ = _
    rw [← hdepth, hz]
    unfold stoppedCompletionLog stoppedOutput recordedCompletionLog
    cases z (firstEntryTime (Set.range Sum.inl) z) <;> rfl
  have hf : Measurable (fun z : ℕ → CompletionLog ι ⊕ RoutingCursor n H ι =>
      fun k => forgetTerminal (z k)) :=
    measurable_pi_lambda _ (fun k => measurable_forgetTerminal.comp (measurable_pi_apply k))
  rw [← s.completionRoutingTrajectory_cursor_law n id L measurable_const e measurable_const 0 N c hc hmem a,
    Measure.map_map (measurable_cursorDepthPayoff n) hf]
  change Measure.map (cursorDepthPayoff n ∘ (fun z k => forgetTerminal (z k)))
    (markovTrajectory K (.inr a)) = Measure.map g
      (Measure.map (s.stoppedCompletionLog n id L e 0) (markovTrajectory K (.inr a)))
  rw [Measure.map_map (measurable_completionLogReward n)
    (s.measurable_stoppedCompletionLog n id L measurable_const e measurable_const 0)]
  exact Measure.map_congr heq

end PosteriorStage
end StochasticMatching
