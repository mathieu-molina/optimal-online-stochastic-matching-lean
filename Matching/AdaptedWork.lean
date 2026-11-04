import Matching.WorkExpectation
import Matching.AdaptedRegularity

/-! The observable policy's expected total work equals its expected number of
completions. Consequently the proved competitive lower bound applies to the
paper's integrated-work objective as well as to completion reward.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorData
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : PosteriorData H ι)

theorem integrable_policyWork {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) [IsFiniteMeasure ν] :
    Integrable (fun x => ∑ i, p.policyService x 1 i) (ν.prod independentExponentials) :=
  PosteriorStage.integrable_terminalWork (Fintype.card ι) p.initialStage id Function.injective_id
    hP0 hPc hPcompact hPdown (p.initial_feasibleAllocation hmem) ν

theorem expected_policyWork_eq_reward {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) [IsFiniteMeasure ν] :
    (∫ x, ∑ i, p.policyService x 1 i ∂ν.prod independentExponentials) =
      ∫ x, p.policyReward x ∂ν.prod independentExponentials := by
  rw [integral_congr_ae (p.policyReward_eq_count_ae hP0 hPc hPcompact hPdown hmem ν)]
  exact PosteriorStage.expected_terminalWork_eq_count (Fintype.card ι) p.initialStage id
    Function.injective_id hP0 hPc hPcompact hPdown (p.initial_feasibleAllocation hmem) ν

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem integrable_adaptedWork {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) [IsFiniteMeasure ν] :
    Integrable (fun x => ∑ i, p.adaptedService x 1 i) (ν.prod independentExponentials) := by
  apply (p.integrable_policyWork hP0 hPc hPcompact hPdown hmem ν).congr
  filter_upwards [p.adaptedService_eq_policyService_ae ν] with x hx
  rw [hx 1]

theorem expected_adaptedWork_eq_reward {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) [IsFiniteMeasure ν] :
    (∫ x, ∑ i, p.adaptedService x 1 i ∂ν.prod independentExponentials) =
      ∫ x, p.adaptedReward x ∂ν.prod independentExponentials := by
  have he : (fun x => ∑ i, p.adaptedService x 1 i) =ᵐ[ν.prod independentExponentials]
      fun x => ∑ i, p.policyService x 1 i := by
    filter_upwards [p.adaptedService_eq_policyService_ae ν] with x hx
    rw [hx 1]
  rw [integral_congr_ae he, integral_congr_ae (p.adaptedReward_eq_policyReward_ae ν)]
  exact p.expected_policyWork_eq_reward hP0 hPc hPcompact hPdown hmem ν

theorem posterior_adapted_work_guarantee {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (ν : Measure H) [IsProbabilityMeasure ν] :
    Comparison.ratio * (∫ x, ∑ i, p.allocation x i ∂ν.prod independentExponentials) ≤
      ∫ x, ∑ i, p.adaptedService x 1 i ∂ν.prod independentExponentials := by
  rw [p.expected_adaptedWork_eq_reward hP0 hPc hPcompact hPdown hmem ν]
  exact p.posterior_adapted_guarantee hP0 hPc hPcompact hPdown hmem hcap ν

end StochasticMatching.PosteriorData
