import Matching.OnlineCompletionLaw
import Matching.GreedyAllocation
import Matching.ExpectedOfflineEquality

/-! The expected output of the concrete arrival-driven routing construction
is bounded against the independent-Poisson offline benchmark. This does not
yet identify the routing construction's complete input process with the
independent renewal-stream realization. -/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι σ : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def coveragePosteriorData (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    PosteriorData Unit ι :=
  PosteriorData.ofCompact
    ((measurable_greedyAllocation N (fun a => (intensity a : ℝ))).comp measurable_snd)
    (supplyRegion_compact N (fun a => (intensity a : ℝ)))
    (fun _ hx => supplyRegion_nonneg N (fun a => (intensity a : ℝ)) hx)
    (fun _ z => (greedyAllocation_properties N (fun a => (intensity a : ℝ))
      (fun a => (intensity a).coe_nonneg) z).1)

theorem coveragePosteriorData_allocation (N : σ → Finset ι) (intensity : σ → ℝ≥0)
    (h : Unit) (z : ι → ℝ) :
    (coveragePosteriorData N intensity).allocation (h, z) =
      greedyAllocation N (fun a => (intensity a : ℝ)) z := rfl

theorem coveragePosteriorData_feasible (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    ∀ h z, (coveragePosteriorData N intensity).allocation (h, z) ∈
      supplyRegion N (fun a => (intensity a : ℝ)) :=
  fun _ z => (greedyAllocation_properties N _ (fun a => (intensity a).coe_nonneg) z).1

noncomputable def coverageRoutingOutputLaw (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    Measure (CompletionLog ι) :=
  (coveragePosteriorData N intensity).initialStage.onlineCompletionLogLaw N
    (fun a => (intensity a : ℝ)) (fun a => (intensity a).coe_nonneg)
    ((coveragePosteriorData N intensity).initial_feasibleAllocation
      (coveragePosteriorData_feasible N intensity)) ()

theorem coverageRoutingOutputLaw_probability (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    IsProbabilityMeasure (coverageRoutingOutputLaw N intensity) :=
  (coveragePosteriorData N intensity).initialStage.onlineCompletionLogLaw_probability N
    (fun a => (intensity a : ℝ)) (fun a => (intensity a).coe_nonneg) _ ()

theorem coverageRoutingOutput_vs_poisson_benchmark (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    Comparison.ratio * (∫ counts, arrivalOfflineValue N counts ∂independentPoissons intensity) ≤
      ∫ L, completionLogReward (Fintype.card ι) L ∂coverageRoutingOutputLaw N intensity := by
  rw [← expected_offline_equality N intensity]
  have h := (coveragePosteriorData N intensity).posterior_routing_payoff_guarantee N
    (fun a => (intensity a : ℝ)) (fun a => (intensity a).coe_nonneg)
    (coveragePosteriorData_feasible N intensity)
    (fun _ z hz i => greedyAllocation_cap_nonnegative N _
      (fun a => (intensity a).coe_nonneg) z hz i) ()
  simpa only [coveragePosteriorData_allocation,
    greedyAllocation_optimal N _ (fun a => (intensity a).coe_nonneg)] using h

end StochasticMatching
