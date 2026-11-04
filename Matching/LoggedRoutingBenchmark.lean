import Matching.ArrivalLogPoissonLaw
import Matching.RoutingPoissonBenchmark

/-! The offline benchmark is now evaluated on the arrivals observed by the
concrete policy. Turning its completion reward into a matching cardinality
remains a separate combinatorial obligation. -/
open MeasureTheory Set ProbabilityTheory
open scoped NNReal
namespace StochasticMatching
variable {ι σ : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def coverageLoggedTrajectory (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Measure (ℕ → Unit ⊕ (RoutingCursor (Fintype.card ι) Unit ι × ArrivalMemory σ)) :=
  (coveragePosteriorData N a).initialStage.loggedTrajectory (Fintype.card ι) id N
    (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    ((coveragePosteriorData N a).initial_feasibleAllocation (coveragePosteriorData_feasible N a))
    (initialRoutingCursor (Fintype.card ι) (), emptyArrivalMemory σ)

theorem coverageLoggedTrajectory_counts_law (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Measure.map lastArrivalCounts (coverageLoggedTrajectory N a) = independentPoissons a := by
  have h := (coveragePosteriorData N a).initialStage.loggedTrajectory_counts_law (Fintype.card ι)
    id N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    ((coveragePosteriorData N a).initial_feasibleAllocation (coveragePosteriorData_feasible N a))
    (initialRoutingCursor (Fintype.card ι) ())
  have he : horizonIntensity (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
      ((coveragePosteriorData N a).initialStage.cursorHorizon (Fintype.card ι) id
        (initialRoutingCursor (Fintype.card ι) ())) = a := by
    funext s
    apply Subtype.ext
    change (a s : ℝ) * (((coveragePosteriorData N a).initialStage.cursorService (Fintype.card ι) id).curves
      (initialRoutingCursor (Fintype.card ι) ())).deadline = (a s : ℝ)
    rw [PosteriorStage.cursorService_initial_deadline]
    exact mul_one _
  rw [he] at h
  exact h

theorem coverageLoggedTrajectory_expected_offline (N : σ → Finset ι) (a : σ → ℝ≥0) :
    (∫ z, arrivalOfflineValue N (lastArrivalCounts z) ∂coverageLoggedTrajectory N a) =
      ∫ counts, arrivalOfflineValue N counts ∂independentPoissons a := by
  rw [← coverageLoggedTrajectory_counts_law N a]
  exact (integral_map_of_stronglyMeasurable measurable_lastArrivalCounts
    (measurable_of_countable (arrivalOfflineValue N)).stronglyMeasurable).symm

theorem coverageRoutingOutput_vs_observed_offline (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Comparison.ratio * (∫ z, arrivalOfflineValue N (lastArrivalCounts z) ∂coverageLoggedTrajectory N a) ≤
      ∫ L, completionLogReward (Fintype.card ι) L ∂coverageRoutingOutputLaw N a := by
  rw [coverageLoggedTrajectory_expected_offline]
  exact coverageRoutingOutput_vs_poisson_benchmark N a

end StochasticMatching
