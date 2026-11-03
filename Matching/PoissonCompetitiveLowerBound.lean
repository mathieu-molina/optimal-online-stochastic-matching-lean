import Matching.OnlineMatchingGuarantee
import Matching.MarkedRenewalInput
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Public Poisson-model lower bound, with the constant written exactly as
1 - e / e^e. There is no fixed-count transfer hypothesis. This establishes
achievability, not the distinct impossibility direction of optimality. -/
open MeasureTheory Set ProbabilityTheory
open scoped NNReal
namespace StochasticMatching

theorem Comparison.ratio_eq_e_rpow :
    Comparison.ratio = 1 - Real.exp 1 / (Real.exp 1) ^ (Real.exp 1) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp, one_mul]
  exact Comparison.ratio_eq_exp_quotient

variable {ι σ : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def poissonOfflineOptimum (N : σ → Finset ι) (a : σ → ℝ≥0) : ℝ :=
  ∫ counts, arrivalOfflineValue N counts ∂independentPoissons a

noncomputable def coverageMatchingReward (N : σ → Finset ι) (a : σ → ℝ≥0) : ℝ :=
  ∫ z, ((observedRoutingMatching N z).size : ℝ) ∂coverageMatchingTrajectory N a

theorem poisson_matching_lower_bound (N : σ → Finset ι) (a : σ → ℝ≥0) :
    (1 - Real.exp 1 / (Real.exp 1) ^ (Real.exp 1)) * poissonOfflineOptimum N a ≤
      coverageMatchingReward N a := by
  rw [← Comparison.ratio_eq_e_rpow]
  have h := coverage_online_matching_guarantee N a
  rwa [coverageMatchingTrajectory_expected_offline] at h

theorem poisson_matching_ratio_lower_bound (N : σ → Finset ι) (a : σ → ℝ≥0)
    (hOPT : 0 < poissonOfflineOptimum N a) :
    1 - Real.exp 1 / (Real.exp 1) ^ (Real.exp 1) ≤
      coverageMatchingReward N a / poissonOfflineOptimum N a :=
  (le_div_iff₀ hOPT).mpr (poisson_matching_lower_bound N a)

noncomputable def coverageInputProjection (N : σ → Finset ι) (a : σ → ℝ≥0)
    (z : ℕ → Unit ⊕ (RoutingCursor (Fintype.card ι) Unit ι × RoutedMemory σ ι)) :
    ℕ → Unit ⊕ (PositiveHorizon × ArrivalMemory σ) := fun k =>
  Sum.map id (fun y =>
    ((coveragePosteriorData N a).initialStage.cursorHorizon (Fintype.card ι) id y.1,
      routedMemoryInput y.2)) (z k)

theorem coverageInputProjection_measurable (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Measurable (coverageInputProjection N a) := by
  apply measurable_pi_lambda
  intro k
  exact (measurable_id.sumMap
    (((coveragePosteriorData N a).initialStage.measurable_cursorHorizon (Fintype.card ι) id).prodMap
      measurable_routedMemoryInput)).comp (measurable_pi_apply k)

theorem coverageMatchingTrajectory_full_input_law (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Measure.map (coverageInputProjection N a) (coverageMatchingTrajectory N a) =
      Measure.map (renewalArrivalPath (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
        (⟨1, zero_lt_one⟩ : PositiveHorizon)) independentRenewalStreams := by
  have h := (coveragePosteriorData N a).initialStage.markedTrajectory_renewal_input_law
    (Fintype.card ι) id N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    ((coveragePosteriorData N a).initial_feasibleAllocation (coveragePosteriorData_feasible N a))
    (initialRoutingCursor (Fintype.card ι) (), emptyRoutedMemory)
  have he : (coveragePosteriorData N a).initialStage.cursorHorizon (Fintype.card ι) id
      (initialRoutingCursor (Fintype.card ι) ()) = (⟨1, zero_lt_one⟩ : PositiveHorizon) := by
    apply Subtype.ext
    exact PosteriorStage.cursorService_initial_deadline _ _ _ _
  rw [he] at h
  exact h

theorem poisson_matching_lower_bound_certificate (N : σ → Finset ι) (a : σ → ℝ≥0) :
    IsProbabilityMeasure (coverageMatchingTrajectory N a) ∧
    (Measure.map (coverageInputProjection N a) (coverageMatchingTrajectory N a) =
      Measure.map (renewalArrivalPath (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
        (⟨1, zero_lt_one⟩ : PositiveHorizon)) independentRenewalStreams) ∧
    (Measure.map lastRoutedCounts (coverageMatchingTrajectory N a) = independentPoissons a) ∧
    (∀ᵐ z ∂coverageMatchingTrajectory N a,
      RoutedMemoryValid N (lastRoutedMemory z) ∧
      (observedRoutingMatching N z).size = routedMemoryAccepted (lastRoutedMemory z)) ∧
    Integrable (fun z => ((observedRoutingMatching N z).size : ℝ)) (coverageMatchingTrajectory N a) ∧
    Integrable (fun z => arrivalOfflineValue N (lastRoutedCounts z)) (coverageMatchingTrajectory N a) ∧
    (1 - Real.exp 1 / (Real.exp 1) ^ (Real.exp 1)) * poissonOfflineOptimum N a ≤
      coverageMatchingReward N a :=
  ⟨coverageMatchingTrajectory_probability N a, coverageMatchingTrajectory_full_input_law N a,
    coverageMatchingTrajectory_counts_law N a, coverageMatchingTrajectory_matching_valid N a,
    coverageMatchingTrajectory_integrable_matching N a, coverageMatchingTrajectory_integrable_offline N a,
    poisson_matching_lower_bound N a⟩

end StochasticMatching
