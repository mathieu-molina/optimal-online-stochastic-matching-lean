import Matching.PathCount
import Matching.PolicyGuarantee

/-! The quantitative guarantee expressed directly in terms of the original
coordinates' integrated service. Joint measurability, compact-region rate
feasibility, continuous service, and pathwise demand bounds are proved here.
An observation-adapted version with the same guarantee is constructed and
verified separately in AdaptedPolicy.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorData
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : PosteriorData H ι)

noncomputable def policyRate : ℝ × (H × (ι → ℝ)) → (ι → ℝ) :=
  PosteriorStage.ratePath (Fintype.card ι) p.initialStage id

noncomputable def policyService (x : H × (ι → ℝ)) (t : ℝ) : ι → ℝ :=
  PosteriorStage.cumulativePath (Fintype.card ι) p.initialStage id x t

noncomputable def policyReward (x : H × (ι → ℝ)) : ℝ :=
  ∑ i, if p.policyService x 1 i = x.2 i then 1 else 0

theorem policyService_eq_integral (x : H × (ι → ℝ)) (t : ℝ) :
    p.policyService x t = ∫ u in (0 : ℝ)..t, p.policyRate (u, x) := rfl

theorem measurable_policyRate : Measurable p.policyRate :=
  PosteriorStage.measurable_ratePath (Fintype.card ι) p.initialStage id

theorem initial_feasibleAllocation {P : Set (ι → ℝ)}
    (hmem : ∀ h z, p.allocation (h, z) ∈ P) :
    p.initialStage.data.FeasibleAllocation id P := by
  intro h z
  rw [labelLift_id]
  exact hmem h z

theorem policyRate_feasible {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPclosed : IsClosed P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (q : ℝ × (H × (ι → ℝ))) : p.policyRate q ∈ P :=
  PosteriorStage.ratePath_feasible (Fintype.card ι) p.initialStage id
    hP0 hPc hPclosed hPdown (p.initial_feasibleAllocation hmem) q

theorem continuous_policyService {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (x : H × (ι → ℝ)) : Continuous (p.policyService x) :=
  PosteriorStage.continuous_cumulativePath (Fintype.card ι) p.initialStage id
    hP0 hPc hPcompact hPdown (p.initial_feasibleAllocation hmem) x

theorem policyService_bounds_ae {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
      0 ≤ p.policyService x t i ∧ p.policyService x t i ≤ x.2 i :=
  PosteriorStage.cumulativePath_bounds_ae (Fintype.card ι) p.initialStage id Function.injective_id
    hP0 hPc hPcompact hPdown (p.initial_feasibleAllocation hmem) ν

theorem policyReward_eq_count_ae {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) : p.policyReward =ᵐ[ν.prod independentExponentials]
      fun x => (p.initialStage.completionCount x : ℝ) :=
  PosteriorStage.completedServiceReward_eq_completionCount_ae p.initialStage id Function.injective_id
    hP0 hPc hPcompact hPdown (p.initial_feasibleAllocation hmem) ν

theorem integrable_policyReward {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) [IsFiniteMeasure ν] : Integrable p.policyReward (ν.prod independentExponentials) := by
  exact (PosteriorStage.integrable_countPlan (Fintype.card ι) p.initialStage 0
    (ν.prod independentExponentials)).congr
      (p.policyReward_eq_count_ae hP0 hPc hPcompact hPdown hmem ν).symm

theorem posterior_service_guarantee {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (ν : Measure H) [IsProbabilityMeasure ν] :
    Comparison.ratio * (∫ x, ∑ i, p.allocation x i ∂ν.prod independentExponentials) ≤
      ∫ x, p.policyReward x ∂ν.prod independentExponentials := by
  rw [integral_congr_ae (p.policyReward_eq_count_ae hP0 hPc hPcompact hPdown hmem ν)]
  exact p.posterior_policy_guarantee hcap ν

end StochasticMatching.PosteriorData
