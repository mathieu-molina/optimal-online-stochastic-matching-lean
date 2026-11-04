import Matching.LogRateAgreement
import Matching.PathRegularity
import Matching.ServiceGuarantee

/-! An explicitly observation-adapted implementation of the constructed
service policy. It agrees with the analyzed path simultaneously at all times
outside one null set, so its service bounds and reward guarantee transfer.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
namespace PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace J] [Fintype J] [DecidableEq J] [MeasurableSingletonClass J]

theorem readRate_feasible (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (k : ℕ)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPclosed : IsClosed P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P) (q : RateQuery H J) :
    readRate n s label k q ∈ P := by
  induction n generalizing H ι k with
  | zero => exact hP0
  | succ n ih =>
    classical
    change (if 0 ≤ q.1 - q.2.2.1 ∧ q.1 - q.2.2.1 < s.deadline q.2.1 then
      branchSelect (E := J → ℝ) (readerWinner label k) _ _ q else 0) ∈ P
    split_ifs
    · by_cases hw : ∃ j, q ∈ readerWinner label k j
      · obtain ⟨j, hj⟩ := hw
        rw [branchSelect_of_mem (readerWinner_disjoint label hinj k) _ _ hj]
        exact ih (s.next j) (fun i => label i.1) (hinj.comp Subtype.val_injective) (k + 1)
          (s.next_feasibleAllocation label hPdown hmem j) _
      · rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
        exact s.lifted_rate_mem label hPc hPclosed hmem q.2.1 (q.1 - q.2.2.1)
    · exact hP0

end PosteriorStage
namespace PosteriorData
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : PosteriorData H ι)

noncomputable def adaptedRate (q : ℝ × (H × (ι → ℝ))) : ι → ℝ :=
  PosteriorStage.observedRate (Fintype.card ι) p.initialStage id 0
    (q.1, (q.2.1, (0, p.initialStage.completionLog id q.2)))

noncomputable def adaptedService (x : H × (ι → ℝ)) (t : ℝ) : ι → ℝ :=
  ∫ u in (0 : ℝ)..t, p.adaptedRate (u, x)

noncomputable def adaptedReward (x : H × (ι → ℝ)) : ℝ :=
  ∑ i, if p.adaptedService x 1 i = x.2 i then 1 else 0

theorem measurable_adaptedRate : Measurable p.adaptedRate := by
  apply (PosteriorStage.measurable_observedRate (Fintype.card ι) p.initialStage id
    Function.injective_id 0).comp
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (measurable_const.prodMk ((p.initialStage.measurable_completionLog id).comp measurable_snd)))

theorem adaptedRate_measurable_filtration (t : ℝ) :
    @Measurable (H × (ι → ℝ)) (ι → ℝ) (p.initialStage.observationFiltration id t) inferInstance
      (fun x => p.adaptedRate (t, x)) :=
  PosteriorStage.observedRate_measurable_filtration p.initialStage id Function.injective_id t

theorem adaptedRate_eq_policyRate_ae (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, ∀ t, p.adaptedRate (t, x) = p.policyRate (t, x) :=
  PosteriorStage.observedRate_eq_ratePath_ae p.initialStage id Function.injective_id ν

theorem adaptedRate_feasible {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPclosed : IsClosed P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (q : ℝ × (H × (ι → ℝ))) : p.adaptedRate q ∈ P :=
  PosteriorStage.readRate_feasible (Fintype.card ι) p.initialStage id Function.injective_id 0
    hP0 hPc hPclosed hPdown (p.initial_feasibleAllocation hmem) _

theorem adaptedService_eq_policyService_ae (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, ∀ t, p.adaptedService x t = p.policyService x t := by
  filter_upwards [p.adaptedRate_eq_policyRate_ae ν] with x hx
  intro t
  rw [adaptedService, p.policyService_eq_integral]
  apply intervalIntegral.integral_congr
  intro u _
  exact hx u

theorem adaptedService_bounds_ae {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
      0 ≤ p.adaptedService x t i ∧ p.adaptedService x t i ≤ x.2 i := by
  filter_upwards [p.adaptedService_eq_policyService_ae ν,
    p.policyService_bounds_ae hP0 hPc hPcompact hPdown hmem ν] with x heq hx
  intro t ht i
  rw [heq t]
  exact hx t ht i

theorem adaptedReward_eq_policyReward_ae (ν : Measure H) :
    p.adaptedReward =ᵐ[ν.prod independentExponentials] p.policyReward := by
  filter_upwards [p.adaptedService_eq_policyService_ae ν] with x hx
  simp only [adaptedReward, policyReward, hx 1]

theorem posterior_adapted_guarantee {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (ν : Measure H) [IsProbabilityMeasure ν] :
    Comparison.ratio * (∫ x, ∑ i, p.allocation x i ∂ν.prod independentExponentials) ≤
      ∫ x, p.adaptedReward x ∂ν.prod independentExponentials := by
  rw [integral_congr_ae (p.adaptedReward_eq_policyReward_ae ν)]
  exact p.posterior_service_guarantee hP0 hPc hPcompact hPdown hmem hcap ν

end PosteriorData
end StochasticMatching
