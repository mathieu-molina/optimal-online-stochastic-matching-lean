import Matching.MarkedMatchingPayoff
import Matching.LoggedRoutingBenchmark

/-! A matching-cardinality guarantee on the concrete online policy's own
Poisson input. Decisions are the recorded history-dependent routing marks;
the matching reader only relabels the individual arrivals after termination.
The paper's impossibility upper bound and fixed-count transfer are separate. -/
open MeasureTheory Set ProbabilityTheory
open scoped NNReal
namespace StochasticMatching
variable {ι σ : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def coverageMatchingTrajectory (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Measure (ℕ → Unit ⊕ (RoutingCursor (Fintype.card ι) Unit ι × RoutedMemory σ ι)) :=
  (coveragePosteriorData N a).initialStage.markedTrajectory (Fintype.card ι) id N
    (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    ((coveragePosteriorData N a).initial_feasibleAllocation (coveragePosteriorData_feasible N a))
    (initialRoutingCursor (Fintype.card ι) (), emptyRoutedMemory)

theorem coverageMatchingTrajectory_probability (N : σ → Finset ι) (a : σ → ℝ≥0) :
    IsProbabilityMeasure (coverageMatchingTrajectory N a) :=
  (coveragePosteriorData N a).initialStage.markedTrajectory_probability (Fintype.card ι) id N
    (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg) _ _

theorem coverageMatchingTrajectory_erase_marks (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Measure.map (fun z : ℕ → Unit ⊕ (RoutingCursor (Fintype.card ι) Unit ι × RoutedMemory σ ι) =>
      fun k => Sum.map id (fun y : RoutingCursor (Fintype.card ι) Unit ι × RoutedMemory σ ι =>
        (y.1, routedMemoryInput y.2)) (z k)) (coverageMatchingTrajectory N a) =
      coverageLoggedTrajectory N a :=
  (coveragePosteriorData N a).initialStage.markedTrajectory_erase_marks (Fintype.card ι) id N
    (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg) _ _

theorem coverageMatchingTrajectory_counts_law (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Measure.map lastRoutedCounts (coverageMatchingTrajectory N a) = independentPoissons a := by
  have h := congrArg (Measure.map (lastArrivalCounts (A := RoutingCursor (Fintype.card ι) Unit ι) (σ := σ)))
    (coverageMatchingTrajectory_erase_marks N a)
  have hf : Measurable (fun z : ℕ → Unit ⊕ (RoutingCursor (Fintype.card ι) Unit ι × RoutedMemory σ ι) =>
      fun k => Sum.map id (fun y : RoutingCursor (Fintype.card ι) Unit ι × RoutedMemory σ ι =>
        (y.1, routedMemoryInput y.2)) (z k)) :=
    measurable_pi_lambda _ (fun k => (measurable_id.sumMap (measurable_fst.prodMk
      (measurable_routedMemoryInput.comp measurable_snd))).comp (measurable_pi_apply k))
  rw [Measure.map_map measurable_lastArrivalCounts hf, coverageLoggedTrajectory_counts_law] at h
  simpa only [Function.comp_def, lastRoutedCounts_erase_marks] using h

theorem coverageMatchingTrajectory_matching_valid (N : σ → Finset ι) (a : σ → ℝ≥0) :
    ∀ᵐ z ∂coverageMatchingTrajectory N a,
      RoutedMemoryValid N (lastRoutedMemory z) ∧
      (observedRoutingMatching N z).size = routedMemoryAccepted (lastRoutedMemory z) := by
  have h := (coveragePosteriorData N a).initialStage.markedTrajectory_matching_size (Fintype.card ι)
    id Function.injective_id N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    ((coveragePosteriorData N a).initial_feasibleAllocation (coveragePosteriorData_feasible N a)) ()
  filter_upwards [h] with z hz
  exact ⟨hz.1, observedRoutingMatching_size_of_valid N z hz.1⟩

theorem coverageMatchingTrajectory_expected_matching (N : σ → Finset ι) (a : σ → ℝ≥0) :
    (∫ z, ((observedRoutingMatching N z).size : ℝ) ∂coverageMatchingTrajectory N a) =
      ∫ L, completionLogReward (Fintype.card ι) L ∂coverageRoutingOutputLaw N a :=
  (coveragePosteriorData N a).initialStage.markedTrajectory_expected_matching_size N
    (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    ((coveragePosteriorData N a).initial_feasibleAllocation (coveragePosteriorData_feasible N a)) ()

theorem coverageMatchingTrajectory_expected_offline (N : σ → Finset ι) (a : σ → ℝ≥0) :
    (∫ z, arrivalOfflineValue N (lastRoutedCounts z) ∂coverageMatchingTrajectory N a) =
      ∫ counts, arrivalOfflineValue N counts ∂independentPoissons a := by
  rw [← coverageMatchingTrajectory_counts_law N a]
  exact (integral_map_of_stronglyMeasurable measurable_lastRoutedCounts
    (measurable_of_countable (arrivalOfflineValue N)).stronglyMeasurable).symm

theorem coverageMatchingTrajectory_integrable_matching (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Integrable (fun z => ((observedRoutingMatching N z).size : ℝ)) (coverageMatchingTrajectory N a) := by
  letI := coverageMatchingTrajectory_probability N a
  apply (integrable_const (Fintype.card ι : ℝ)).mono'
    (measurable_observedRoutingMatching_reward N).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast observedRoutingMatching_size_le N z)

theorem coverageMatchingTrajectory_integrable_offline (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Integrable (fun z => arrivalOfflineValue N (lastRoutedCounts z)) (coverageMatchingTrajectory N a) := by
  letI := coverageMatchingTrajectory_probability N a
  apply (integrable_const (Fintype.card ι : ℝ)).mono'
    ((measurable_of_countable (arrivalOfflineValue N)).comp measurable_lastRoutedCounts).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only [Function.comp_def]
    rw [Real.norm_of_nonneg (arrivalOfflineValue_nonneg N _)]
    exact arrivalOfflineValue_le_card N _)

theorem coverage_online_matching_guarantee (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Comparison.ratio *
      (∫ z, arrivalOfflineValue N (lastRoutedCounts z) ∂coverageMatchingTrajectory N a) ≤
      ∫ z, ((observedRoutingMatching N z).size : ℝ) ∂coverageMatchingTrajectory N a := by
  rw [coverageMatchingTrajectory_expected_offline, coverageMatchingTrajectory_expected_matching]
  exact coverageRoutingOutput_vs_poisson_benchmark N a

end StochasticMatching
