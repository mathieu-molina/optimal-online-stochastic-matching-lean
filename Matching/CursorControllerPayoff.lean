import Matching.CursorControllerProjection
import Matching.PoissonControllerReward
import Matching.StoppedRewardExpectation
import Matching.CursorPayoffLaw

/-! The general controller embedding preserves the established scheduling
payoff. No conditional-count representation or fixed-count transfer is used. -/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace StochasticMatching.PosteriorStage
variable {H ι σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem toPoissonController_output_le (s : PosteriorStage H ι)
    (N : σ → Finset ι) (a : σ → ℝ≥0)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N (fun s => (a s : ℝ)))) (h : H) :
    (∫ L, completionLogReward (Fintype.card ι) L
      ∂s.onlineCompletionLogLaw N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg) hmem h) ≤
        (s.toPoissonController (Fintype.card ι) id Function.injective_id le_rfl N a hmem).expectedReward
          (initialRoutingCursor (Fintype.card ι) h) := by
  let n := Fintype.card ι
  let P := s.toPoissonController n id Function.injective_id le_rfl N a hmem
  let x : RoutingCursor n H ι := initialRoutingCursor n h
  let L := routingTransition N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    (s.cursorService n id) (s.cursorService_supply_feasible n id N _ (fun s => (a s).coe_nonneg) hmem)
    (s.typedCursorUpdate n id)
  let g : Finset ι → ℝ := fun B => (Fintype.card ι : ℝ) - B.card
  have hg : Measurable g := measurable_of_countable _
  have hterm := s.toPoissonController_finite_termination n id Function.injective_id le_rfl N a hmem x
  have hpay := terminalPayload_lastLive_payoff_ae P.step L (cursorAvailable n id)
    (measurable_cursorAvailable n id) g hg 0 x
    (s.toPoissonController_step_live n id Function.injective_id le_rfl N a hmem) hterm
  have hdepth : g ∘ cursorAvailable (H := H) n (id : ι → ι) =
      fun y => (cursorDepth n y : ℝ) := by
    funext y
    have hh := cursorAvailable_card_add_depth n (id : ι → ι) Function.injective_id le_rfl y
    have hc : ((cursorAvailable n id y).card : ℝ) + (cursorDepth n y : ℝ) = Fintype.card ι := by
      exact_mod_cast hh
    change (Fintype.card ι : ℝ) - (cursorAvailable n id y).card = _
    linarith
  have hR : Sum.elim g (g ∘ cursorAvailable (H := H) n (id : ι → ι)) = P.reward := by
    funext y
    cases y <;> rfl
  have heq : ∀ᵐ z ∂markovTrajectory P.step (.inr x),
      cursorDepthPayoff n (fun k => forgetTerminal (z k)) =
        stoppedOutput (Set.range Sum.inl) P.reward z := by
    filter_upwards [hpay] with z hz
    change lastLiveObservation (fun y => (cursorDepth n y : ℝ)) 0 _ = _
    rw [← hdepth, hz, hR]
  have hF : Measurable (fun z : ℕ → ControllerState (RoutingCursor n H ι) ι =>
      fun k => forgetTerminal (z k)) :=
    measurable_pi_lambda _ (fun k => measurable_forgetTerminal.comp (measurable_pi_apply k))
  have he : (∫ z, stoppedOutput (Set.range Sum.inl) P.reward z ∂markovTrajectory P.step (.inr x)) =
      ∫ z, cursorDepthPayoff n z ∂s.routingTrajectory n id N (fun s => (a s : ℝ))
        (fun s => (a s).coe_nonneg) hmem x := by
    rw [← s.toPoissonController_trajectory_projection n id Function.injective_id le_rfl N a hmem x,
      integral_map_of_stronglyMeasurable hF (measurable_cursorDepthPayoff n).stronglyMeasurable]
    exact integral_congr_ae (heq.mono (fun z hz => hz.symm))
  have hlaw := congrArg (fun μ : Measure ℝ => ∫ r, r ∂μ)
    (s.routingTrajectory_payoff_law N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg) hmem h)
  dsimp only at hlaw
  rw [integral_map_of_stronglyMeasurable (f := fun r : ℝ => r) (measurable_cursorDepthPayoff n)
    measurable_id.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (f := fun r : ℝ => r) (measurable_completionLogReward n)
      measurable_id.stronglyMeasurable] at hlaw
  rw [← hlaw, ← he]
  apply expected_stopped_reward_le P.step (Set.range Sum.inl) measurableSet_range_inl
    (by rintro _ ⟨B, rfl⟩; rfl) P.reward P.reward_measurable (Fintype.card ι : ℝ) _ (.inr x) hterm
  intro y
  rw [abs_of_nonneg (P.reward_bounds y).1]
  exact (P.reward_bounds y).2

end StochasticMatching.PosteriorStage
