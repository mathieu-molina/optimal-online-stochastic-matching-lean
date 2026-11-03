import Matching.ExecutionDefect
import Matching.BudgetRecurrence

/-! The quantitative guarantee for the constructed finite posterior policy:
its expected completion count is at least the comparison ratio times the
expected total allocation. The separate scheduling-feasibility and matching
reduction obligations of the full paper are not asserted by this theorem.
-/

open MeasureTheory Set
open scoped BigOperators NNReal
namespace StochasticMatching
namespace PosteriorStage
universe u v
variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

theorem totalDefect_le_budget (n : ℕ) (s : PosteriorStage H ι)
    (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    totalDefect n s R.elapsed ν ≤ ∫ h, s.budget R.elapsed h ∂ν := by
  induction n generalizing H ι with
  | zero =>
    apply integral_nonneg_of_ae
    filter_upwards [hν] with h hh
    exact s.budget_nonneg R hh
  | succ n ih =>
    change (∫ h, s.defect R.elapsed h ∂ν) +
      (∑ j, totalDefect n (s.next j) (R.next j).elapsed (s.service.markedHistoryMeasure ν j)) ≤ _
    apply le_trans _ (s.budget_step R ν hν)
    apply add_le_add_left
    apply Finset.sum_le_sum
    intro j _
    letI := s.service.finite_markedHistoryMeasure ν j
    exact ih (s.next j) (R.next j) (s.service.markedHistoryMeasure ν j) (R.next_concentrated ν hν j)

theorem completionCount_lower_bound_from_budget (s : PosteriorStage H ι)
    (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ h, s.potential R.elapsed h ∂ν) - (∫ h, s.budget R.elapsed h ∂ν) ≤
      ∫ x, (s.completionCount x : ℝ) ∂ν.prod independentExponentials := by
  rw [completionCount_expected_eq_potential_sub_defect s R ν hν]
  exact sub_le_sub_left (totalDefect_le_budget (Fintype.card ι) s R ν hν) _

end PosteriorStage
namespace PosteriorData
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : PosteriorData H ι)

noncomputable def initialStage : PosteriorStage H ι where
  data := p
  initial _ := 0
  measurable_initial := measurable_const
  horizon := 1
  horizon_pos := by norm_num
  deadline _ := 1
  measurable_deadline := measurable_const
  deadline_pos _ := by norm_num
  deadline_le _ := by norm_num

noncomputable def initialRegion
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i) : StageRegion p.initialStage where
  domain := univ
  measurable_domain := MeasurableSet.univ
  elapsed _ := 0
  measurable_elapsed := measurable_const
  admissible h _ := ⟨fun _ => le_refl 0, hcap h⟩
  elapsed_nonneg _ _ := le_refl 0
  total_deadline _ _ := by norm_num [initialStage]
  initial_bound _ _ _ := by simp [initialStage]

theorem initial_potential (h : H) :
    p.initialStage.potential (fun _ => 0) h = (Fintype.card ι : ℝ) * Comparison.ratio := by
  simp [PosteriorStage.potential, initialStage, Comparison.continuation_initial]

theorem integrable_total_allocation (ν : Measure H) [IsFiniteMeasure ν] :
    Integrable (fun x : H × (ι → ℝ) => ∑ i, p.allocation x i) (ν.prod independentExponentials) := by
  apply integrable_finset_sum
  intro i _
  apply (integrable_const (p.bound : ℝ)).mono'
    ((measurable_pi_apply i).comp p.measurable_allocation).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖p.allocation x i‖ ≤ (p.bound : ℝ)
  rw [Real.norm_of_nonneg (p.allocation_nonneg x.1 x.2 i)]
  exact p.allocation_le x.1 x.2 i

theorem initial_meanUnallocated (h : H) :
    p.initialStage.meanUnallocated h = (Fintype.card ι : ℝ) -
      ∫ z, ∑ i, p.allocation (h, z) i ∂independentExponentials := by
  have hi : ∀ i, Integrable (fun z => p.allocation (h, z) i) independentExponentials := by
    intro i
    simpa only [zero_add] using p.integrable_shifted_allocation h 0 i
  unfold PosteriorStage.meanUnallocated
  change (∑ i, ((0 : ℝ) + 1 - posteriorRate p.allocation h 0 i)) = _
  simp only [zero_add, Finset.sum_sub_distrib]
  rw [integral_finset_sum _ (fun i _ => hi i)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [posteriorRate, shiftedMean, zero_add]

theorem expected_initial_budget (ν : Measure H) [IsProbabilityMeasure ν] :
    (∫ h, p.initialStage.budget (fun _ => 0) h ∂ν) =
      Comparison.ratio * ((Fintype.card ι : ℝ) -
        ∫ x, ∑ i, p.allocation x i ∂ν.prod independentExponentials) := by
  have hi := p.integrable_total_allocation ν
  simp_rw [PosteriorStage.budget, Comparison.continuation_initial, p.initial_meanUnallocated]
  rw [integral_const_mul, integral_sub (integrable_const _) hi.integral_prod_left,
    ← integral_prod _ hi]
  simp

theorem posterior_policy_guarantee
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (ν : Measure H) [IsProbabilityMeasure ν] :
    Comparison.ratio * (∫ x, ∑ i, p.allocation x i ∂ν.prod independentExponentials) ≤
      ∫ x, (p.initialStage.completionCount x : ℝ) ∂ν.prod independentExponentials := by
  have h := PosteriorStage.completionCount_lower_bound_from_budget
    p.initialStage (p.initialRegion hcap) ν (Filter.Eventually.of_forall (fun _ => mem_univ _))
  change (∫ h, p.initialStage.potential (fun _ => 0) h ∂ν) -
    (∫ h, p.initialStage.budget (fun _ => 0) h ∂ν) ≤ _ at h
  simp_rw [p.initial_potential] at h
  rw [p.expected_initial_budget ν] at h
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at h
  nlinarith

end PosteriorData
end StochasticMatching
