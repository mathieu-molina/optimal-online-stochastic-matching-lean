import Matching.CompletionOutputState
import Matching.RestartObservationLaw
import Matching.FiniteOnlineCoupling

/-! The full predicted scheduling-output law is invariant under any finite
number of actual routed arrivals. Terminal states retain their actual log.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem completionStateService_feasible (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) :
    ∀ b t, t ∈ Icc 0 ((s.completionStateService n label).curves b).deadline →
      (fun j => ((s.completionStateService n label).curves b).rate j t) ∈ supplyRegion N capacity := by
  intro b t ht
  cases b with
  | inl _ => exact zero_mem_supplyRegion N capacity hc
  | inr x => exact s.cursorService_supply_feasible n label N capacity hc hmem x t ht

noncomputable def completionRoutingKernel (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) :
    Kernel (CompletionLog J ⊕ RoutingCursor n H ι) (CompletionLog J ⊕ RoutingCursor n H ι) :=
  let p := s.completionStateService n label
  letI := historyRoutingKernel_markov N capacity hc p (s.completionStateService_feasible n label N capacity hc hmem)
  eventUpdateKernel (historyRoutingKernel N capacity p) (routingJobUpdate (s.completionStateUpdate n label L elapsed k))

theorem completionRoutingKernel_markov (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) :
    IsMarkovKernel (s.completionRoutingKernel n label L elapsed k N capacity hc hmem) := by
  letI := historyRoutingKernel_markov N capacity hc (s.completionStateService n label)
    (s.completionStateService_feasible n label N capacity hc hmem)
  exact eventUpdateKernel_markov _ _ (measurable_routingJobUpdate _
    (s.measurable_completionStateUpdate n label L hL elapsed he k))

noncomputable def completionObservationKernel (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) :
    Kernel (CompletionLog J ⊕ RoutingCursor n H ι) (CompletionLog J) :=
  residualObservationKernel (independentExponentials (ι := J))
    (s.completionStateObservation n label L hL elapsed he k)

theorem completionObservationKernel_harmonic (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) :
    s.completionObservationKernel n label L hL elapsed he k ∘ₖ
      s.completionRoutingKernel n label L elapsed k N capacity hc hmem =
        s.completionObservationKernel n label L hL elapsed he k := by
  let p := s.completionStateService n label
  let hp := s.completionStateService_feasible n label N capacity hc hmem
  letI := historyRoutingKernel_markov N capacity hc p hp
  let hΛ := fun b t ht => supplyRegion_total_rate_le N capacity hc (hp b t ht)
  let U := s.completionStateUpdate n label L elapsed k
  have hU : Measurable U := s.measurable_completionStateUpdate n label L hL elapsed he k
  have h := restart_observation_harmonic (p.withRejectionClock (∑ a, capacity a) hΛ) U hU
    (s.completionStateObservation n label L hL elapsed he k)
    (s.measurable_completionStateObservation n label L hL elapsed he k)
    (s.completionStateObservation_preserved_ae n label hinj L hL elapsed he k (∑ a, capacity a) hΛ)
  rw [← routing_job_update_kernel_law N capacity hc p hp U hU] at h
  exact h

theorem completionObservationKernel_iterate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (m : ℕ) :
    s.completionObservationKernel n label L hL elapsed he k ∘ₖ
      iterateKernel (s.completionRoutingKernel n label L elapsed k N capacity hc hmem) m =
        s.completionObservationKernel n label L hL elapsed he k :=
  kernel_harmonic_iterate _ _
    (s.completionObservationKernel_harmonic n label hinj L hL elapsed he k N capacity hc hmem) m

theorem completionObservationKernel_terminal (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (log : CompletionLog J) :
    s.completionObservationKernel n label L hL elapsed he k (.inl log) = Measure.dirac log := by
  rw [completionObservationKernel, residualObservationKernel_apply _ _
    (s.measurable_completionStateObservation n label L hL elapsed he k)]
  change Measure.map (fun _ => log) (independentExponentials (ι := J)) = _
  rw [Measure.map_const, measure_univ, one_smul]

theorem completionObservationKernel_initial (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (h : H) :
    s.completionObservationKernel n label L hL elapsed he k (.inr (initialRoutingCursor n h)) =
      Measure.map (fun r : J → ℝ =>
        AdaptivePlan.run (tracePlan n s label L hL elapsed he k) (h, fun i => r (label i))) independentExponentials := by
  rw [completionObservationKernel, residualObservationKernel_apply _ _
    (s.measurable_completionStateObservation n label L hL elapsed he k)]
  congr 1
  funext r
  exact s.cursorContinuation_initial n label L hL elapsed he k h r

end StochasticMatching.PosteriorStage
