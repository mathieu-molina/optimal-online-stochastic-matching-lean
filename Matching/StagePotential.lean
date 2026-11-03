import Matching.StageRegion
import Matching.ComparisonOutcome

/-! Measurable stage potentials and their actual expected decrement. The
comparison defect is defined from an integrable observable payoff and then
identified with the service-curve drift integral.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
namespace Comparison

theorem measurable_continuation {Ω : Type*} [MeasurableSpace Ω] {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => continuation (a x) (b x)) := by
  unfold continuation
  fun_prop

end Comparison
namespace PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

noncomputable def potential (elapsed : H → ℝ) (h : H) : ℝ :=
  ∑ i, Comparison.continuation (elapsed h) (s.initial h i)

noncomputable def terminalPotential (elapsed : H → ℝ) (h : H) : ℝ :=
  (s.service.curves h).comparisonPotential (elapsed h) (s.initial h) (s.deadline h)

noncomputable def stepOutcome (elapsed : H → ℝ) (x : H × (ι → ℝ)) : ℝ :=
  branchSelect s.service.winner
    (fun j x => 1 + (s.next j).potential (fun h => elapsed h.1 + h.2)
      (x.1, s.service.clock j x))
    (fun x => s.terminalPotential elapsed x.1) x

theorem measurable_potential {elapsed : H → ℝ} (he : Measurable elapsed) :
    Measurable (s.potential elapsed) := by
  apply Finset.measurable_sum
  intro i _
  exact Comparison.measurable_continuation he ((measurable_pi_apply i).comp s.measurable_initial)

theorem measurable_terminalPotential {elapsed : H → ℝ} (he : Measurable elapsed) :
    Measurable (s.terminalPotential elapsed) := by
  apply Finset.measurable_sum
  intro i _
  exact Comparison.measurable_continuation (he.add s.measurable_deadline)
    (((measurable_pi_apply i).comp s.measurable_initial).add
      ((s.service.measurable_service i).comp (measurable_id.prodMk s.measurable_deadline)))

theorem measurable_stepOutcome {elapsed : H → ℝ} (he : Measurable elapsed) :
    Measurable (s.stepOutcome elapsed) :=
  measurable_branchSelect s.service.winner_disjoint s.service.measurable_winner
    (fun j => measurable_const.add (((s.next j).measurable_potential
      ((he.comp measurable_fst).add measurable_snd)).comp
        (measurable_fst.prodMk (s.service.measurable_clock j))))
    ((s.measurable_terminalPotential he).comp measurable_fst)

theorem stepOutcome_eq (elapsed : H → ℝ) (x : H × (ι → ℝ)) :
    s.stepOutcome elapsed x =
      (s.service.curves x.1).comparisonOutcome (elapsed x.1) (s.initial x.1) x.2 := by
  classical
  by_cases hw : ∃ j, x ∈ s.service.winner j
  · obtain ⟨j, hj⟩ := hw
    unfold stepOutcome
    rw [branchSelect_of_mem s.service.winner_disjoint _ _ hj,
      (s.service.curves x.1).comparisonOutcome_winner (elapsed x.1) (s.initial x.1) hj]
    rfl
  · unfold stepOutcome ServiceCurveFamily.comparisonOutcome
    rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
    have hn : ∀ j, x.2 ∉ variableWinner (s.service.curves x.1).service
        (s.service.curves x.1).deadline j := fun j hj => hw ⟨j, hj⟩
    rw [branchSelect_of_not_mem _ _ hn]
    rfl

theorem potential_eq_initial (elapsed : H → ℝ) (h : H) :
    (s.service.curves h).comparisonPotential (elapsed h) (s.initial h) 0 = s.potential elapsed h := by
  simp only [ServiceCurveFamily.comparisonPotential, (s.service.curves h).service_zero,
    add_zero, potential]

noncomputable def defect (elapsed : H → ℝ) (h : H) : ℝ :=
  s.potential elapsed h - ∫ z, s.stepOutcome elapsed (h, z) ∂independentExponentials

theorem measurable_defect {elapsed : H → ℝ} (he : Measurable elapsed) :
    Measurable (s.defect elapsed) :=
  (s.measurable_potential he).sub
    (s.measurable_stepOutcome he).stronglyMeasurable.integral_prod_right'.measurable

theorem defect_eq_integral (elapsed : H → ℝ) (h : H) (ha : s.Admissible h)
    (hT : elapsed h + s.deadline h ≤ 1) :
    s.defect elapsed h = ∫ t in (0 : ℝ)..s.deadline h,
      survivalCurve (fun u i => (s.service.curves h).service i u) t *
        ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 -
          (s.service.curves h).rate i t) *
          Comparison.sensitivity (elapsed h + t) (s.initial h i + (s.service.curves h).service i t) := by
  have hd := (s.service.curves h).comparisonOutcome_expected_drift (elapsed h) (s.initial h) hT ha.1
  have heq : (fun z => s.stepOutcome elapsed (h, z)) =
      (s.service.curves h).comparisonOutcome (elapsed h) (s.initial h) := by
    funext z
    exact s.stepOutcome_eq elapsed (h, z)
  rw [← heq, s.potential_eq_initial] at hd
  unfold defect
  have hneg : -(∫ t in (0 : ℝ)..s.deadline h,
      survivalCurve (fun u i => (s.service.curves h).service i u) t *
        ∑ i, -(s.initial h i + (s.service.curves h).service i t + 1 -
          (s.service.curves h).rate i t) *
          Comparison.sensitivity (elapsed h + t) (s.initial h i + (s.service.curves h).service i t)) =
      ∫ t in (0 : ℝ)..s.deadline h,
      survivalCurve (fun u i => (s.service.curves h).service i u) t *
        ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 -
          (s.service.curves h).rate i t) *
          Comparison.sensitivity (elapsed h + t) (s.initial h i + (s.service.curves h).service i t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    simp only [neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg]
  change (∫ z, s.stepOutcome elapsed (h, z) ∂independentExponentials) -
    s.potential elapsed h = _ at hd
  have hD : (s.service.curves h).deadline = s.deadline h := rfl
  rw [hD] at hd
  linarith

theorem defect_nonneg (elapsed : H → ℝ) (h : H) (ha : s.Admissible h)
    (hT : elapsed h + s.deadline h ≤ 1) : 0 ≤ s.defect elapsed h := by
  rw [s.defect_eq_integral elapsed h ha hT]
  apply intervalIntegral.integral_nonneg (s.deadline_pos h).le
  intro t ht
  apply mul_nonneg (survivalCurve_pos _ _).le
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (s.flow_gap_nonneg_at h ha ht i) (Comparison.sensitivity_pos _ _).le

theorem potential_bounds (R : StageRegion s) {h : H} (hh : h ∈ R.domain) :
    0 ≤ s.potential R.elapsed h ∧ s.potential R.elapsed h ≤ Fintype.card ι := by
  rw [← s.potential_eq_initial]
  exact (s.service.curves h).comparisonPotential_bounds (R.elapsed h) (s.initial h)
    (le_of_eq (R.total_deadline h hh)) (R.admissible h hh).1
    ⟨le_refl _, (s.deadline_pos h).le⟩

theorem stepOutcome_bounds (R : StageRegion s) {x : H × (ι → ℝ)} (hx : x.1 ∈ R.domain) :
    0 ≤ s.stepOutcome R.elapsed x ∧ s.stepOutcome R.elapsed x ≤ Fintype.card ι := by
  rw [s.stepOutcome_eq]
  exact (s.service.curves x.1).comparisonOutcome_bounds (R.elapsed x.1) (s.initial x.1)
    (le_of_eq (R.total_deadline x.1 hx)) (R.admissible x.1 hx).1 x.2

theorem defect_bounds (R : StageRegion s) {h : H} (hh : h ∈ R.domain) :
    0 ≤ s.defect R.elapsed h ∧ s.defect R.elapsed h ≤ Fintype.card ι := by
  refine ⟨s.defect_nonneg R.elapsed h (R.admissible h hh) (le_of_eq (R.total_deadline h hh)), ?_⟩
  have hn : 0 ≤ ∫ z, s.stepOutcome R.elapsed (h, z) ∂independentExponentials :=
    integral_nonneg (fun z => (s.stepOutcome_bounds R hh).1)
  have hp := (s.potential_bounds R hh).2
  unfold defect
  linarith

end PosteriorStage
end StochasticMatching
