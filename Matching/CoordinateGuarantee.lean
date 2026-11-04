import Matching.CoordinatePayoff
import Matching.CoordinateWork
import Matching.AdaptedWork

/-! The stronger coordinatewise work guarantee for the constructed observable
policy. The induction follows actual marked branches and preserves a separate
comparison certificate for each surviving job.
-/

open MeasureTheory Set
namespace StochasticMatching
namespace PosteriorStage
universe u v w
variable {H : Type u} {ι : Type v} {J : Type w}
  [MeasurableSpace H] [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem coordinateWork_lower_bound_from_certificate (n : ℕ) (s : PosteriorStage H ι)
    (label : ι → J) (hinj : Function.Injective label)
    {P : Set (J → ℝ)} (hP0 : (0 : J → ℝ) ∈ P) (hPc : Convex ℝ P)
    (hPcompact : IsCompact P) (hPdown : NonnegDownwardClosed P)
    (hmem : s.data.FeasibleAllocation label P)
    (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (hn : Fintype.card ι ≤ n) (i : ι) :
    (∫ h, s.coordinateCertificate R.elapsed i h ∂ν) ≤
      ∫ x, coordinateWork n s label i x ∂ν.prod independentExponentials := by
  induction n generalizing H ι with
  | zero =>
    letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
    exact isEmptyElim i
  | succ n ih =>
    apply (s.coordinate_certificate_step R ν hν i).trans
    rw [expected_coordinateWork_step n s label hinj hP0 hPc hPcompact hPdown hmem ν i]
    apply Finset.sum_le_sum
    intro j _
    letI := s.service.finite_markedHistoryMeasure ν j
    unfold coordinateChildCertificate nextCoordinateWork
    by_cases hij : i ≠ j
    · simp only [dif_pos hij]
      have hn' : Fintype.card {k : ι // k ≠ j} ≤ n := by
        have hc := survivor_card j
        omega
      exact ih (s.next j) (fun k => label k.1) (hinj.comp Subtype.val_injective)
        (s.next_feasibleAllocation label hPdown hmem j) (R.next j)
        (s.service.markedHistoryMeasure ν j) (R.next_concentrated ν hν j) hn' ⟨i, hij⟩
    · simp only [dif_neg hij]
      have he := integral_fun_fst (μ := s.service.markedHistoryMeasure ν j)
        (ν := independentExponentials (ι := {k : ι // k ≠ j})) (fun _ : H × ℝ => (1 : ℝ))
      simp only [measureReal_univ_eq_one, one_smul] at he
      exact le_of_eq he.symm

end PosteriorStage
namespace PosteriorData
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : PosteriorData H ι)

theorem initial_coordinateCertificate (h : H) (i : ι) :
    p.initialStage.coordinateCertificate (fun _ => 0) i h =
      Comparison.ratio * (∫ z, p.allocation (h, z) i ∂independentExponentials) := by
  change Comparison.continuation 0 0 - Comparison.continuation 0 0 *
    ((0 : ℝ) + 1 - posteriorRate p.allocation h 0 i) = _
  rw [Comparison.continuation_initial]
  simp only [zero_add, posteriorRate, shiftedMean]
  ring

theorem integrable_allocation_coordinate (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    Integrable (fun x => p.allocation x i) (ν.prod independentExponentials) := by
  apply (integrable_const (p.bound : ℝ)).mono'
    ((measurable_pi_apply i).comp p.measurable_allocation).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖p.allocation (x.1, x.2) i‖ ≤ (p.bound : ℝ)
  rw [Real.norm_of_nonneg (p.allocation_nonneg x.1 x.2 i)]
  exact p.allocation_le x.1 x.2 i

theorem posterior_policy_coordinate_work_guarantee {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    Comparison.ratio * (∫ x, p.allocation x i ∂ν.prod independentExponentials) ≤
      ∫ x, p.policyService x 1 i ∂ν.prod independentExponentials := by
  have h := PosteriorStage.coordinateWork_lower_bound_from_certificate (Fintype.card ι)
    p.initialStage id Function.injective_id hP0 hPc hPcompact hPdown
    (p.initial_feasibleAllocation hmem) (p.initialRegion hcap) ν
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) (le_refl _) i
  change (∫ h, p.initialStage.coordinateCertificate (fun _ => 0) i h ∂ν) ≤ _ at h
  simp_rw [p.initial_coordinateCertificate] at h
  rw [integral_const_mul, ← integral_prod _ (p.integrable_allocation_coordinate ν i)] at h
  exact h

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem integrable_adapted_coordinate_work {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    Integrable (fun x => p.adaptedService x 1 i) (ν.prod independentExponentials) := by
  have hi := PosteriorStage.integrable_coordinateWork (Fintype.card ι) p.initialStage id
    Function.injective_id hP0 hPc hPcompact hPdown (p.initial_feasibleAllocation hmem) ν i
  apply hi.congr
  filter_upwards [p.adaptedService_eq_policyService_ae ν] with x hx
  rw [hx 1]
  rfl

theorem posterior_adapted_coordinate_work_guarantee {P : Set (ι → ℝ)}
    (hP0 : (0 : ι → ℝ) ∈ P) (hPc : Convex ℝ P) (hPcompact : IsCompact P)
    (hPdown : NonnegDownwardClosed P) (hmem : ∀ h z, p.allocation (h, z) ∈ P)
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    Comparison.ratio * (∫ x, p.allocation x i ∂ν.prod independentExponentials) ≤
      ∫ x, p.adaptedService x 1 i ∂ν.prod independentExponentials := by
  have he : (fun x => p.adaptedService x 1 i) =ᵐ[ν.prod independentExponentials]
      fun x => p.policyService x 1 i := by
    filter_upwards [p.adaptedService_eq_policyService_ae ν] with x hx
    rw [hx 1]
  rw [integral_congr_ae he]
  exact p.posterior_policy_coordinate_work_guarantee hP0 hPc hPcompact hPdown hmem hcap ν i

end PosteriorData
end StochasticMatching
