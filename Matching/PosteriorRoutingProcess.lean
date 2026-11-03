import Matching.PosteriorCursorDeadline
import Matching.GuardedArrivalUpdate
import Matching.StoppedRoutingLaw

/-! A concrete stopped online routing process for the posterior scheduling
policy. Its allocation is feasible at every state, and its entire remaining-
time trajectory agrees with the arrival-only Markov process.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def guardedCursorUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :=
  guardedEventUpdate (fun x => ((s.cursorService n label).curves x).deadline) (s.cursorUpdate n label)

theorem measurable_guardedCursorUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.guardedCursorUpdate n label) :=
  measurable_guardedEventUpdate _ (s.cursorService n label).deadline_measurable _ (s.measurable_cursorUpdate n label)

noncomputable def typedCursorUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι × (Unit ⊕ (ℝ × (σ × Option J)))) : Unit ⊕ RoutingCursor n H ι :=
  s.guardedCursorUpdate n label (x.1, arrivalJobProjection x.2)

theorem measurable_typedCursorUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.typedCursorUpdate (σ := σ) n label) :=
  (s.measurable_guardedCursorUpdate n label).comp
    (measurable_fst.prodMk (measurable_arrivalJobProjection.comp measurable_snd))

noncomputable def cursorHorizon (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι) : PositiveHorizon :=
  ⟨((s.cursorService n label).curves x).deadline, ((s.cursorService n label).curves x).deadline_pos⟩

theorem measurable_cursorHorizon (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.cursorHorizon n label) := (s.cursorService n label).deadline_measurable.subtype_mk

theorem typedCursorUpdate_time_projection (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι) (e : Unit ⊕ (ℝ × (σ × Option J))) :
    Sum.map id (s.cursorHorizon n label) (s.typedCursorUpdate n label (x, e)) =
      remainingTimeUpdate (s.cursorHorizon n label x, arrivalTypeProjection e) := by
  have h := guardedEventUpdate_time_projection
    (fun x => ((s.cursorService n label).curves x).deadline)
    (fun x => ((s.cursorService n label).curves x).deadline_pos)
    (s.cursorUpdate n label) (s.cursorUpdate_deadline n label) x (arrivalJobProjection e)
  cases e with
  | inl e => exact h
  | inr e => exact h

theorem cursorService_supply_feasible (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (x : RoutingCursor n H ι) (t : ℝ) (ht : t ∈ Icc 0 ((s.cursorService n label).curves x).deadline) :
    (fun j => ((s.cursorService n label).curves x).rate j t) ∈ supplyRegion N capacity :=
  s.cursorService_rate_mem n label (zero_mem_supplyRegion N capacity hc)
    (supplyRegion_convex N capacity) (supplyRegion_closed N capacity)
    (supplyRegion_downward N capacity) hmem x t ht

noncomputable def routingTrajectory (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (x : RoutingCursor n H ι) :
    Measure (ℕ → Unit ⊕ RoutingCursor n H ι) :=
  onlineRoutingTrajectory N capacity hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N capacity hc hmem)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label) x

theorem routingTrajectory_finite_termination (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (x : RoutingCursor n H ι) :
    ∀ᵐ z ∂s.routingTrajectory n label N capacity hc hmem x, ∃ k, z k = Sum.inl () := by
  apply onlineRoutingTrajectory_finite_termination N capacity hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N capacity hc hmem)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label)
    (fun _ => rfl) s.horizon (s.cursorService_deadline_le n label) x

theorem routingTrajectory_time_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (x : RoutingCursor n H ι) :
    Measure.map (fun z : ℕ → Unit ⊕ RoutingCursor n H ι =>
        fun k => Sum.map id (s.cursorHorizon n label) (z k))
      (s.routingTrajectory n label N capacity hc hmem x) =
      poissonInputTrajectory capacity hc Subtype.val measurable_subtype_coe (fun b => b.2)
        (remainingTimeUpdate (E := σ)) measurable_remainingTimeUpdate (s.cursorHorizon n label x) := by
  apply stopped_routing_input_law N capacity hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N capacity hc hmem)
    Subtype.val measurable_subtype_coe (fun b => b.2)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label)
    remainingTimeUpdate measurable_remainingTimeUpdate
    (s.cursorHorizon n label) (s.measurable_cursorHorizon n label) (fun _ => rfl)
    (s.typedCursorUpdate_time_projection n label) x

end StochasticMatching.PosteriorStage
