import Matching.PosteriorRoutingProcess
import Matching.StoppedResidualCoupling

/-! Instantiate the surviving-demand coupling with the concrete posterior
cursor and its absorbing online routing trajectory.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def residualRoutingKernel (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) :
    Kernel ((Unit ⊕ RoutingCursor n H ι) × (J → ℝ))
      ((Unit ⊕ RoutingCursor n H ι) × (J → ℝ)) :=
  let p := s.cursorService n label
  let hp := s.cursorService_supply_feasible n label N capacity hc hmem
  let q := (stoppedServiceFamily p).withRejectionClock (∑ a, capacity a)
    (fun x t ht => supplyRegion_total_rate_le N capacity hc
      (stoppedServiceFamily_feasible N capacity hc p hp x t ht))
  latentExponentialKernel q (stoppedEventUpdate (s.guardedCursorUpdate n label))

theorem residualRoutingKernel_markov (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) :
    IsMarkovKernel (s.residualRoutingKernel n label N capacity hc hmem) :=
  latentExponentialKernel_markov _ _
    (measurable_stoppedEventUpdate _ (s.measurable_guardedCursorUpdate n label))

set_option maxHeartbeats 1000000 in
theorem routingTrajectory_residual_coupling (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (k : ℕ) (x : RoutingCursor n H ι) :
    (iterateKernel (s.residualRoutingKernel n label N capacity hc hmem) k ∘ₖ
      freshResidualKernel (independentExponentials (ι := J))) (.inr x) =
      (Measure.map (fun z : ℕ → Unit ⊕ RoutingCursor n H ι => z k)
        (s.routingTrajectory n label N capacity hc hmem x)).prod
          (independentExponentials (ι := J)) := by
  let p := s.cursorService n label
  let hp := s.cursorService_supply_feasible n label N capacity hc hmem
  letI := historyRoutingKernel_markov N capacity hc p hp
  let U := s.guardedCursorUpdate n label
  have hU : Measurable U := s.measurable_guardedCursorUpdate n label
  letI := eventUpdateKernel_markov (historyRoutingKernel N capacity p)
    (typedJobEventUpdate (σ := σ) U) (measurable_typedJobEventUpdate U hU)
  have he := stopped_online_residual_coupling N capacity hc p hp U hU k x
  have hm : Measure.map (fun z : ℕ → Unit ⊕ RoutingCursor n H ι => z k)
      (s.routingTrajectory n label N capacity hc hmem x) =
      iterateKernel (absorbingKernel
        (eventUpdateKernel (historyRoutingKernel N capacity p) (typedJobEventUpdate U))) k (.inr x) :=
    markovTrajectory_coordinate_law
      (absorbingKernel (eventUpdateKernel (historyRoutingKernel N capacity p) (typedJobEventUpdate U)))
      (.inr x) k
  rw [hm]
  exact he

end StochasticMatching.PosteriorStage
