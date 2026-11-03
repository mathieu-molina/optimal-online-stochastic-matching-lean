import Matching.CompletionStoppedLaw
import Matching.LogReward
import Matching.ServiceGuarantee

/-! The actual posterior routing output and its expected payoff. These laws
refer to the arrival-driven routing kernel; identification of the full input
process with independent renewal streams is a separate obligation. -/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def onlineCompletionLogLaw (s : PosteriorStage H ι)
    (N : σ → Finset ι) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N capacity)) (h : H) :
    Measure (CompletionLog ι) := by
  letI := s.completionRoutingKernel_markov (Fintype.card ι) id (fun _ => emptyCompletionLog)
    measurable_const (fun _ => 0) measurable_const 0 N capacity hc hmem
  exact Measure.map
    (s.stoppedCompletionLog (Fintype.card ι) id (fun _ => emptyCompletionLog) (fun _ => 0) 0)
    (markovTrajectory (s.completionRoutingKernel (Fintype.card ι) id
      (fun _ => emptyCompletionLog) (fun _ => 0) 0 N capacity hc hmem)
      (.inr (initialRoutingCursor (Fintype.card ι) h)))

theorem onlineCompletionLogLaw_eq (s : PosteriorStage H ι)
    (N : σ → Finset ι) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N capacity)) (h : H) :
    s.onlineCompletionLogLaw N capacity hc hmem h =
      Measure.map (fun r => s.completionLog id (h, r)) independentExponentials :=
  s.initial_stoppedCompletionLog_law (Fintype.card ι) id Function.injective_id
    (fun _ => emptyCompletionLog) measurable_const (fun _ => 0) measurable_const 0
    N capacity hc hmem h

theorem onlineCompletionLogLaw_probability (s : PosteriorStage H ι)
    (N : σ → Finset ι) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N capacity)) (h : H) :
    IsProbabilityMeasure (s.onlineCompletionLogLaw N capacity hc hmem h) := by
  rw [s.onlineCompletionLogLaw_eq N capacity hc hmem h]
  exact isProbabilityMeasure_map
    ((s.measurable_completionLog id).comp (measurable_const.prodMk measurable_id)).aemeasurable

theorem expected_onlineCompletionLogReward (s : PosteriorStage H ι)
    (N : σ → Finset ι) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : s.data.FeasibleAllocation id (supplyRegion N capacity)) (h : H) :
    (∫ L, completionLogReward (Fintype.card ι) L ∂s.onlineCompletionLogLaw N capacity hc hmem h) =
      ∫ r, (s.completionCount (h, r) : ℝ) ∂independentExponentials := by
  have hm : Measurable (fun r => s.completionLog id (h, r)) :=
    (s.measurable_completionLog id).comp (measurable_const.prodMk measurable_id)
  rw [s.onlineCompletionLogLaw_eq N capacity hc hmem h,
    integral_map_of_stronglyMeasurable hm
      (measurable_completionLogReward (Fintype.card ι)).stronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun r => s.completionLogReward_eq_count id (h, r)))

end StochasticMatching.PosteriorStage
namespace StochasticMatching.PosteriorData
variable {H ι σ : Type} [MeasurableSpace H] [MeasurableSingletonClass H]
  [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem posterior_routing_payoff_guarantee (p : PosteriorData H ι)
    (N : σ → Finset ι) (capacity : σ → ℝ) (hc : ∀ a, 0 ≤ capacity a)
    (hmem : ∀ h z, p.allocation (h, z) ∈ supplyRegion N capacity)
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i) (h : H) :
    Comparison.ratio * (∫ z, ∑ i, p.allocation (h, z) i ∂independentExponentials) ≤
      ∫ L, completionLogReward (Fintype.card ι) L
        ∂p.initialStage.onlineCompletionLogLaw N capacity hc (p.initial_feasibleAllocation hmem) h := by
  rw [p.initialStage.expected_onlineCompletionLogReward]
  have hp := p.posterior_policy_guarantee hcap (Measure.dirac h)
  have hi : Integrable (fun x => (p.initialStage.completionCount x : ℝ))
      ((Measure.dirac h).prod independentExponentials) :=
    PosteriorStage.integrable_countPlan (Fintype.card ι) p.initialStage 0 _
  rw [integral_prod _ (p.integrable_total_allocation (Measure.dirac h)),
    integral_prod _ hi] at hp
  simpa only [integral_dirac] using hp

end StochasticMatching.PosteriorData
