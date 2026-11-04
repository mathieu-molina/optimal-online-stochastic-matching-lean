import Matching.CursorMarkedInvariant
import Matching.LastRoutedMatching
import Matching.ArrivalLogPoissonLaw

/-! The concrete posterior policy returns an actual matching on its own
observed arrival copies. Its size is the last live completion count, and
its observed input counts have the independent Poisson law. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem markedTrajectory_probability (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c))
    (x : RoutingCursor n H ι × RoutedMemory σ J) :
    IsProbabilityMeasure (s.markedTrajectory n label N c hc hmem x) := by
  unfold markedTrajectory markedRoutingTrajectory onlineRoutingTrajectory
  infer_instance

theorem markedTrajectory_initial_live (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c))
    (x : RoutingCursor n H ι × RoutedMemory σ J) :
    ∀ᵐ z ∂s.markedTrajectory n label N c hc hmem x, z 0 ≠ .inl () := by
  let p := (s.cursorService n label).comap (Prod.fst : RoutingCursor n H ι × RoutedMemory σ J → _) measurable_fst
  let hp := fun (y : RoutingCursor n H ι × RoutedMemory σ J) t ht =>
    s.cursorService_supply_feasible n label N c hc hmem y.1 t ht
  let U := loggedEventUpdate (s.typedCursorUpdate (σ := σ) n label) id
  have hU := measurable_loggedEventUpdate _ (s.measurable_typedCursorUpdate (σ := σ) n label) id measurable_id
  letI := routingTransition_markov N c hc p hp U hU
  exact markovTrajectory_initial_mem (absorbingKernel (routingTransition N c hc p hp U)) (.inr x)
    {a | a ≠ .inl ()} measurableSet_unitTerminal.compl (by simp)

theorem markedTrajectory_finite_termination (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c))
    (x : RoutingCursor n H ι × RoutedMemory σ J) :
    ∀ᵐ z ∂s.markedTrajectory n label N c hc hmem x, ∃ k, z k = .inl () := by
  apply onlineRoutingTrajectory_finite_termination N c hc
    ((s.cursorService n label).comap Prod.fst measurable_fst)
    (fun y t ht => s.cursorService_supply_feasible n label N c hc hmem y.1 t ht)
    (loggedEventUpdate (s.typedCursorUpdate n label) id)
    (measurable_loggedEventUpdate _ (s.measurable_typedCursorUpdate n label) id measurable_id)
    (fun _ => rfl) s.horizon (fun y => s.cursorService_deadline_le n label y.1) x

theorem markedTrajectory_matching_size (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c)) (h : H) :
    ∀ᵐ z ∂s.markedTrajectory n label N c hc hmem (initialRoutingCursor n h, emptyRoutedMemory),
      RoutedMemoryValid N (lastRoutedMemory z) ∧
      (observedRoutingMatching N z).size =
        lastLiveObservation (fun y : RoutingCursor n H ι × RoutedMemory σ J => cursorDepth n y.1) 0 z := by
  filter_upwards [s.markedTrajectory_valid n label hinj N c hc hmem h,
    s.markedTrajectory_initial_live n label N c hc hmem (initialRoutingCursor n h, emptyRoutedMemory),
    s.markedTrajectory_finite_termination n label N c hc hmem (initialRoutingCursor n h, emptyRoutedMemory)]
    with z hz hzero hterm
  obtain ⟨x, hx, hm⟩ := lastLiveObservation_spec Prod.snd emptyRoutedMemory z hzero hterm
  have hv := hz (firstEntryTime {a | a = .inl ()} z - 1)
  rw [hx] at hv
  change CursorMemoryValid N n label x at hv
  change lastRoutedMemory z = x.2 at hm
  have hmvalid : RoutedMemoryValid N (lastRoutedMemory z) := hm.symm ▸ hv.1
  refine ⟨hmvalid, ?_⟩
  rw [observedRoutingMatching_size_of_valid N z hmvalid, hm]
  unfold lastLiveObservation
  rw [hx]
  exact hv.2.2

theorem markedTrajectory_counts_law (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (c : σ → ℝ) (hc : ∀ a, 0 ≤ c a)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N c)) (x : RoutingCursor n H ι) :
    Measure.map lastRoutedCounts (s.markedTrajectory n label N c hc hmem (x, emptyRoutedMemory)) =
      independentPoissons (horizonIntensity c hc (s.cursorHorizon n label x)) := by
  have h := congrArg (Measure.map (lastArrivalCounts (A := RoutingCursor n H ι) (σ := σ)))
    (s.markedTrajectory_erase_marks n label N c hc hmem (x, emptyRoutedMemory))
  have hf : Measurable (fun z : ℕ → Unit ⊕ (RoutingCursor n H ι × RoutedMemory σ J) => fun k =>
      Sum.map id (fun y : RoutingCursor n H ι × RoutedMemory σ J => (y.1, routedMemoryInput y.2)) (z k)) := by
    apply measurable_pi_lambda
    intro k
    exact (measurable_id.sumMap (measurable_fst.prodMk
      (measurable_routedMemoryInput.comp measurable_snd))).comp (measurable_pi_apply k)
  rw [Measure.map_map measurable_lastArrivalCounts hf] at h
  have he : routedMemoryInput (emptyRoutedMemory (σ := σ) (ι := J)) = emptyArrivalMemory σ := rfl
  rw [he, s.loggedTrajectory_counts_law] at h
  simpa only [Function.comp_def, lastRoutedCounts_erase_marks] using h

end StochasticMatching.PosteriorStage
