import Matching.CompletionOutputTermination
import Matching.StoppedOutput

/-! The actual output at the first terminal routing state has exactly the
original posterior scheduling completion-log law.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory BigOperators ENNReal
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def recordedCompletionLog (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ) :
    CompletionLog J ⊕ RoutingCursor n H ι → CompletionLog J :=
  Sum.elim id (s.cursorLog n label L elapsed k)

theorem measurable_recordedCompletionLog (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) :
    Measurable (s.recordedCompletionLog n label L elapsed k) :=
  measurable_id.sumElim (s.measurable_cursorLog n label L hL elapsed he k)

theorem completionOutput_approximation (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (m : ℕ)
    (b : CompletionLog J ⊕ RoutingCursor n H ι) (B : Set (CompletionLog J)) (hB : MeasurableSet B) :
    let ν := s.completionObservationKernel n label L hL elapsed he k b
    let μ := Measure.map (s.recordedCompletionLog n label L elapsed k)
      (iterateKernel (s.completionRoutingKernel n label L elapsed k N capacity hc hmem) m b)
    let q := 1 - ENNReal.ofReal (Real.exp (-((∑ a, capacity a) * s.horizon)))
    ν B ≤ μ B + q ^ m ∧ μ B ≤ ν B + q ^ m := by
  letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
  let K := s.completionRoutingKernel n label L elapsed k N capacity hc hmem
  let F := s.completionStateObservation n label L hL elapsed he k
  have hF : Measurable F := s.measurable_completionStateObservation n label L hL elapsed he k
  let O := s.recordedCompletionLog n label L elapsed k
  have hO : Measurable O := s.measurable_recordedCompletionLog n label L hL elapsed he k
  have hagree : ∀ a ∉ (Set.range Sum.inr : Set (CompletionLog J ⊕ RoutingCursor n H ι)),
      ∀ r, F (a, r) = O a := by
    intro a ha r
    cases a with
    | inl log => rfl
    | inr x => exact False.elim (ha ⟨x, rfl⟩)
  have hp := residualObservation_approximation (independentExponentials (ι := J)) (iterateKernel K m b)
    F hF O hO (Set.range Sum.inr) measurableSet_range_inr hagree B hB
  have hv := congrArg (fun Q => Q b)
    (s.completionObservationKernel_iterate n label hinj L hL elapsed he k N capacity hc hmem m)
  change (residualObservationKernel (independentExponentials (ι := J)) F ∘ₖ iterateKernel K m) b = _ at hv
  rw [residualObservationKernel_comp_apply _ F hF] at hv
  rw [hv] at hp
  have hb := s.completionRoutingKernel_survival_bound n label L hL elapsed he k N capacity hc hmem m b
  exact ⟨hp.1.trans (add_le_add_left hb _), hp.2.trans (add_le_add_left hb _)⟩

noncomputable def stoppedCompletionLog (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (elapsed : H → ℝ) (k : ℕ) :
    (ℕ → CompletionLog J ⊕ RoutingCursor n H ι) → CompletionLog J :=
  stoppedOutput (Set.range Sum.inl) (s.recordedCompletionLog n label L elapsed k)

theorem measurable_stoppedCompletionLog (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) :
    Measurable (s.stoppedCompletionLog n label L elapsed k) :=
  measurable_stoppedOutput _ measurableSet_range_inl _ (s.measurable_recordedCompletionLog n label L hL elapsed he k)

theorem stoppedCompletionLog_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity))
    (b : CompletionLog J ⊕ RoutingCursor n H ι) :
    letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
    Measure.map (s.stoppedCompletionLog n label L elapsed k)
      (markovTrajectory (s.completionRoutingKernel n label L elapsed k N capacity hc hmem) b) =
        s.completionObservationKernel n label L hL elapsed he k b := by
  try dsimp only
  letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
  have habs : ∀ a ∈ (Set.range Sum.inl : Set (CompletionLog J ⊕ RoutingCursor n H ι)),
      s.completionRoutingKernel n label L elapsed k N capacity hc hmem a = Measure.dirac a := by
    intro a ha
    obtain ⟨log, rfl⟩ := ha
    exact s.completionRoutingKernel_terminal n label L hL elapsed he k N capacity hc hmem log
  have hbound : ∀ m, iterateKernel (s.completionRoutingKernel n label L elapsed k N capacity hc hmem) m b
      (Set.range Sum.inl)ᶜ ≤ (1 - ENNReal.ofReal (Real.exp (-((∑ a, capacity a) * s.horizon)))) ^ m := by
    intro m
    have hcset : (Set.range (Sum.inl : CompletionLog J → CompletionLog J ⊕ RoutingCursor n H ι))ᶜ =
        Set.range Sum.inr := by ext a; cases a <;> simp
    rw [hcset]
    exact s.completionRoutingKernel_survival_bound n label L hL elapsed he k N capacity hc hmem m b
  exact stoppedOutput_law_of_geometric_approximation _ (Set.range Sum.inl) measurableSet_range_inl habs
    (s.recordedCompletionLog n label L elapsed k) (s.measurable_recordedCompletionLog n label L hL elapsed he k)
    b _ _ (routing_continuation_bound_lt_one capacity s.horizon) hbound
    (fun m B hB => s.completionOutput_approximation n label hinj L hL elapsed he k N capacity hc hmem m b B hB)

theorem initial_stoppedCompletionLog_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ)
    (N : σ → Finset J) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N capacity)) (h : H) :
    letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
    Measure.map (s.stoppedCompletionLog n label L elapsed k)
      (markovTrajectory (s.completionRoutingKernel n label L elapsed k N capacity hc hmem)
        (.inr (initialRoutingCursor n h))) =
      Measure.map (fun r : J → ℝ =>
        AdaptivePlan.run (tracePlan n s label L hL elapsed he k) (h, fun i => r (label i))) independentExponentials := by
  try dsimp only
  letI := s.completionRoutingKernel_markov n label L hL elapsed he k N capacity hc hmem
  rw [s.stoppedCompletionLog_law n label hinj L hL elapsed he k N capacity hc hmem,
    s.completionObservationKernel_initial n label L hL elapsed he k h]

end StochasticMatching.PosteriorStage
