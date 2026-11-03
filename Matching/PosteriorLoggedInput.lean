import Matching.PosteriorRoutingProcess
import Matching.LoggedRoutingLaw

/-! The concrete posterior policy with every typed arrival retained. Its
complete log law is the arrival-only law, and recording arrivals leaves the
policy cursor trajectory unchanged.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def loggedTrajectory (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (x : RoutingCursor n H ι × ArrivalMemory σ) :
    Measure (ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ)) :=
  loggedRoutingTrajectory N capacity hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N capacity hc hmem)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label) x

theorem loggedTrajectory_input_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (x : RoutingCursor n H ι × ArrivalMemory σ) :
    Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ) =>
        fun k => Sum.map id (fun y => (s.cursorHorizon n label y.1, y.2)) (z k))
      (s.loggedTrajectory n label N capacity hc hmem x) =
      loggedInputTrajectory capacity hc Subtype.val measurable_subtype_coe (fun b => b.2)
        (remainingTimeUpdate (E := σ)) measurable_remainingTimeUpdate
        (s.cursorHorizon n label x.1, x.2) :=
  logged_routing_input_law N capacity hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N capacity hc hmem)
    Subtype.val measurable_subtype_coe (fun b => b.2)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label)
    remainingTimeUpdate measurable_remainingTimeUpdate
    (s.cursorHorizon n label) (s.measurable_cursorHorizon n label) (fun _ => rfl)
    (s.typedCursorUpdate_time_projection n label) x

theorem loggedTrajectory_cursor_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (x : RoutingCursor n H ι × ArrivalMemory σ) :
    Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × ArrivalMemory σ) =>
        fun k => Sum.map id Prod.fst (z k)) (s.loggedTrajectory n label N capacity hc hmem x) =
      s.routingTrajectory n label N capacity hc hmem x.1 :=
  logged_routing_forget_law N capacity hc (s.cursorService n label)
    (s.cursorService_supply_feasible n label N capacity hc hmem)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label) x

theorem loggedTrajectory_finite_termination (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (x : RoutingCursor n H ι × ArrivalMemory σ) :
    ∀ᵐ z ∂s.loggedTrajectory n label N capacity hc hmem x, ∃ k, z k = Sum.inl () := by
  apply onlineRoutingTrajectory_finite_termination N capacity hc
    ((s.cursorService n label).comap Prod.fst measurable_fst)
    (fun y t ht => s.cursorService_supply_feasible n label N capacity hc hmem y.1 t ht)
    (loggedEventUpdate (s.typedCursorUpdate n label) arrivalTypeProjection)
    (measurable_loggedEventUpdate _ (s.measurable_typedCursorUpdate n label) _ measurable_arrivalTypeProjection)
    (fun _ => rfl) s.horizon (fun y => s.cursorService_deadline_le n label y.1) x

end StochasticMatching.PosteriorStage
