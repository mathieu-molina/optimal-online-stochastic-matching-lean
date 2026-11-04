import Matching.CompletionOutputLaw

/-! The output-retaining routing process stops almost surely, with the same
explicit geometric bound as the original routing trajectory.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory BigOperators ENNReal
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem completionRoutingKernel_terminal (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (log : CompletionLog J) :
    s.completionRoutingKernel n label L elapsed k N capacity hc hmem (.inl log) =
      Measure.dirac (.inl log) := by
  letI := historyRoutingKernel_markov N capacity hc (s.completionStateService n label)
    (s.completionStateService_feasible n label N capacity hc hmem)
  rw [completionRoutingKernel, eventUpdateKernel_apply _ _
    (measurable_routingJobUpdate _ (s.measurable_completionStateUpdate n label L hL elapsed he k))]
  change Measure.map (fun _ => Sum.inl log) _ = _
  rw [Measure.map_const, measure_univ, one_smul]

theorem completionRoutingKernel_live_bound (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (x : RoutingCursor n H ι) :
    s.completionRoutingKernel n label L elapsed k N capacity hc hmem (.inr x) (Set.range Sum.inr) ≤
      1 - ENNReal.ofReal (Real.exp (-((∑ a, capacity a) * s.horizon))) := by
  let p := s.completionStateService n label
  let hp := s.completionStateService_feasible n label N capacity hc hmem
  letI := historyRoutingKernel_markov N capacity hc p hp
  let U := routingJobUpdate (σ := σ) (s.completionStateUpdate n label L elapsed k)
  have hU : Measurable U := measurable_routingJobUpdate _ (s.measurable_completionStateUpdate n label L hL elapsed he k)
  change eventUpdateKernel (historyRoutingKernel N capacity p) U (.inr x) (Set.range Sum.inr) ≤ _
  have hu : Measurable (fun e => U (.inr x, e)) := hU.comp measurable_prodMk_left
  rw [eventUpdateKernel_apply _ U hU, Measure.map_apply hu measurableSet_range_inr]
  apply le_trans (measure_mono ?_) (routingNextArrival_continuation_bound N capacity hc
    ((s.cursorService n label).curves x) (s.cursorService_supply_feasible n label N capacity hc hmem x)
    s.horizon (s.cursorService_deadline_le n label x))
  intro e he
  cases e with
  | inl u =>
    cases u
    change Sum.inl (s.cursorLog n label L elapsed k x) ∈ Set.range Sum.inr at he
    simpa using he
  | inr e => exact ⟨e, rfl⟩

theorem completionRoutingKernel_geometric_step (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (b : CompletionLog J ⊕ RoutingCursor n H ι) :
    s.completionRoutingKernel n label L elapsed k N capacity hc hmem b (Set.range Sum.inr) ≤
      (Set.range Sum.inr).indicator
        (fun _ => 1 - ENNReal.ofReal (Real.exp (-((∑ a, capacity a) * s.horizon)))) b := by
  cases b with
  | inl log =>
    rw [s.completionRoutingKernel_terminal n label L hL elapsed he k N capacity hc hmem log]
    simp [Measure.dirac_apply' _ measurableSet_range_inr]
  | inr x =>
    simpa using s.completionRoutingKernel_live_bound n label L hL elapsed he k N capacity hc hmem x

theorem completionRoutingKernel_survival_bound (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (m : ℕ)
    (b : CompletionLog J ⊕ RoutingCursor n H ι) :
    iterateKernel (s.completionRoutingKernel n label L elapsed k N capacity hc hmem) m b (Set.range Sum.inr) ≤
      (1 - ENNReal.ofReal (Real.exp (-((∑ a, capacity a) * s.horizon)))) ^ m := by
  letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
  exact iterateKernel_geometric_bound _ _ measurableSet_range_inr _
    (s.completionRoutingKernel_geometric_step n label L hL elapsed he k N capacity hc hmem) m b

theorem completionRoutingTrajectory_finite_termination (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (b : CompletionLog J ⊕ RoutingCursor n H ι) :
    letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
    ∀ᵐ z ∂markovTrajectory (s.completionRoutingKernel n label L elapsed k N capacity hc hmem) b,
      ∃ m, z m ∈ Set.range Sum.inl := by
  try dsimp only
  letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
  filter_upwards [markovTrajectory_finite_exit _ _ measurableSet_range_inr _
    (routing_continuation_bound_lt_one capacity s.horizon)
    (s.completionRoutingKernel_geometric_step n label L hL elapsed he k N capacity hc hmem) b] with z hz
  obtain ⟨m, hm⟩ := hz
  refine ⟨m, ?_⟩
  cases hz : z m with
  | inl log => exact ⟨log, rfl⟩
  | inr x => exact False.elim (hm ⟨x, hz.symm⟩)

end StochasticMatching.PosteriorStage
