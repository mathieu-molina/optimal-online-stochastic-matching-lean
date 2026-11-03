import Matching.AdaptedRegularity
import Matching.PathLogValidity
import Matching.TraceValidity
import Matching.TraceLabels
import Matching.AdaptedWork
import Matching.CoordinateGuarantee

/-! A public existence statement from a measurable offline allocation in a
compact convex downward closed nonnegative region. The witnesses are an
observable rate process and its physical completion log, with the quantitative
work and completion guarantees and their exact expectation identity. This is the scheduling construction; the matching
reduction and the paper's optimality upper bound are separate statements.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem exists_observable_service_policy
    (Y : H × (ι → ℝ) → (ι → ℝ)) (hY : Measurable Y)
    {P : Set (ι → ℝ)} (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hPnonneg : ∀ v ∈ P, ∀ i, 0 ≤ v i)
    (hmem : ∀ h z, Y (h, z) ∈ P)
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, Y (h, z) i ≤ z i)
    (ν : Measure H) [IsProbabilityMeasure ν] :
    ∃ (L : H × (ι → ℝ) → CompletionLog ι) (r : ℝ × (H × (ι → ℝ)) → (ι → ℝ)),
      Measurable L ∧ Measurable r ∧
      (∀ x, LogLabelsDistinct (L x)) ∧
      (∀ x k, Fintype.card ι ≤ k → L x k = Sum.inl ()) ∧
      (∀ t, @Measurable (H × (ι → ℝ)) (ι → ℝ)
        ((inferInstance : MeasurableSpace (H × CompletionLog ι)).comap (observedAt Prod.fst L t))
        inferInstance (fun x => r (t, x))) ∧
      (∀ q, r q ∈ P) ∧
      (∀ x, (∫ u in (0 : ℝ)..1, r (u, x)) ∈ P) ∧
      (∀ x, Continuous (fun t => ∫ u in (0 : ℝ)..t, r (u, x))) ∧
      (∀ x i, Monotone (fun t => (∫ u in (0 : ℝ)..t, r (u, x)) i)) ∧
      (∀ᵐ x ∂ν.prod independentExponentials, ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
        0 ≤ (∫ u in (0 : ℝ)..t, r (u, x)) i ∧
          (∫ u in (0 : ℝ)..t, r (u, x)) i ≤ x.2 i) ∧
      (∀ᵐ x ∂ν.prod independentExponentials, ∀ k i τ d,
        L x k = Sum.inr (i, τ, d) → 0 ≤ τ ∧ τ < 1 ∧ d = x.2 i ∧
          ∀ t, τ ≤ t → (∫ u in (0 : ℝ)..t, r (u, x)) i = d) ∧
      Integrable (fun x => ∑ i, (∫ u in (0 : ℝ)..1, r (u, x)) i)
        (ν.prod independentExponentials) ∧
      ((∫ x, ∑ i, (∫ u in (0 : ℝ)..1, r (u, x)) i ∂ν.prod independentExponentials) =
        ∫ x, (∑ i, if (∫ u in (0 : ℝ)..1, r (u, x)) i = x.2 i then (1 : ℝ) else 0)
          ∂ν.prod independentExponentials) ∧
      (∀ i, Comparison.ratio * (∫ x, Y x i ∂ν.prod independentExponentials) ≤
        ∫ x, (∫ u in (0 : ℝ)..1, r (u, x)) i ∂ν.prod independentExponentials) ∧
      (Comparison.ratio * (∫ x, ∑ i, Y x i ∂ν.prod independentExponentials) ≤
        ∫ x, ∑ i, (∫ u in (0 : ℝ)..1, r (u, x)) i ∂ν.prod independentExponentials) ∧
      Comparison.ratio * (∫ x, ∑ i, Y x i ∂ν.prod independentExponentials) ≤
        ∫ x, (∑ i, if (∫ u in (0 : ℝ)..1, r (u, x)) i = x.2 i then (1 : ℝ) else 0)
          ∂ν.prod independentExponentials := by
  let p := PosteriorData.ofCompact hY hPcompact hPnonneg hmem
  have hpMem : ∀ h z, p.allocation (h, z) ∈ P := hmem
  have hpCap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i := hcap
  refine ⟨p.initialStage.completionLog id, p.adaptedRate,
    p.initialStage.measurable_completionLog id, p.measurable_adaptedRate,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact p.initialStage.completionLog_labels_distinct id Function.injective_id
  · intro x k hk
    exact p.initialStage.completionLog_empty_after_card id x hk
  · exact p.adaptedRate_measurable_filtration
  · exact p.adaptedRate_feasible hP0 hPc hPcompact.isClosed hPdown hpMem
  · exact p.adaptedService_terminal_feasible hP0 hPc hPcompact hPdown hpMem
  · exact p.continuous_adaptedService hP0 hPc hPcompact hPdown hpMem
  · exact p.monotone_adaptedService hP0 hPc hPcompact hPdown hPnonneg hpMem
  · exact p.adaptedService_bounds_ae hP0 hPc hPcompact hPdown hpMem ν
  · filter_upwards [p.initialStage.completionLog_demands_correct_ae ν,
      p.initialStage.completionLog_times_before_ae id ν,
      PosteriorStage.completionLog_service_frozen_ae p.initialStage hP0 hPc hPcompact hPdown
        (p.initial_feasibleAllocation hpMem) ν,
      p.adaptedService_eq_policyService_ae ν] with x hdem htimes hfrozen heq
    intro k i τ d hentry
    have hd := hdem k i τ d hentry
    have ht := htimes k i τ d hentry
    change d = (0 : ℝ) + x.2 i at hd
    refine ⟨ht.1, ht.2, by simpa only [zero_add] using hd, ?_⟩
    intro t ht
    change p.adaptedService x t i = d
    rw [heq t]
    have hf := hfrozen k i τ d hentry t ht
    change (0 : ℝ) + p.policyService x t i = d at hf
    simpa only [zero_add] using hf
  · exact p.integrable_adaptedWork hP0 hPc hPcompact hPdown hpMem ν
  · exact p.expected_adaptedWork_eq_reward hP0 hPc hPcompact hPdown hpMem ν
  · exact p.posterior_adapted_coordinate_work_guarantee hP0 hPc hPcompact hPdown hpMem hpCap ν
  · exact p.posterior_adapted_work_guarantee hP0 hPc hPcompact hPdown hpMem hpCap ν
  · exact p.posterior_adapted_guarantee hP0 hPc hPcompact hPdown hpMem hpCap ν

end StochasticMatching
