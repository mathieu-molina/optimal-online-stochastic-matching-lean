import Matching.SurvivalBudget

/-! Measurable budget quantities on the actual history/sample space, together
with the integrability needed to compose the one-step budget inequality.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
namespace HistoryServiceFamily
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : HistoryServiceFamily H ι)

noncomputable def stopClock (x : H × (ι → ℝ)) : ℝ :=
  branchSelect p.winner p.clock (fun x => (p.curves x.1).deadline) x

theorem measurable_stopClock : Measurable p.stopClock :=
  measurable_branchSelect p.winner_disjoint p.measurable_winner p.measurable_clock
    (p.deadline_measurable.comp measurable_fst)

theorem stopClock_eq (x : H × (ι → ℝ)) : p.stopClock x = (p.curves x.1).stopClock x.2 := by
  classical
  by_cases hw : ∃ j, x ∈ p.winner j
  · obtain ⟨j, hj⟩ := hw
    unfold stopClock
    rw [branchSelect_of_mem p.winner_disjoint _ _ hj, (p.curves x.1).stopClock_winner hj]
    rfl
  · unfold stopClock ServiceCurveFamily.stopClock
    rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
    have hn : ∀ j, x.2 ∉ variableWinner (p.curves x.1).service (p.curves x.1).deadline j :=
      fun j hj => hw ⟨j, hj⟩
    rw [branchSelect_of_not_mem _ _ hn]

theorem stopClock_winner {x : H × (ι → ℝ)} {j : ι} (hx : x ∈ p.winner j) :
    p.stopClock x = p.clock j x := branchSelect_of_mem p.winner_disjoint _ _ hx

theorem stopClock_bounds (x : H × (ι → ℝ)) : p.stopClock x ∈ Icc 0 (p.curves x.1).deadline := by
  rw [p.stopClock_eq]
  exact (p.curves x.1).stopClock_bounds x.2

end HistoryServiceFamily
namespace PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

noncomputable def budget (elapsed : H → ℝ) (h : H) : ℝ :=
  Comparison.continuation (elapsed h) 0 * s.meanUnallocated h

noncomputable def weightedUnallocated (elapsed : H → ℝ) (x : H × (ι → ℝ)) : ℝ :=
  Comparison.continuation (elapsed x.1) 0 * s.unallocated x

noncomputable def remainingBudget (elapsed : H → ℝ) (x : H × (ι → ℝ)) : ℝ :=
  Comparison.continuation (elapsed x.1 + s.service.stopClock x) 0 * s.unallocated x

noncomputable def futureBudget (elapsed : H → ℝ) (x : H × (ι → ℝ)) : ℝ :=
  branchSelect s.service.winner
    (fun j x => (s.next j).weightedUnallocated (fun h => elapsed h.1 + h.2) (s.service.observation j x))
    (fun _ => 0) x

theorem measurable_budget {elapsed : H → ℝ} (he : Measurable elapsed) : Measurable (s.budget elapsed) :=
  (Comparison.measurable_continuation he measurable_const).mul s.measurable_meanUnallocated

theorem measurable_weightedUnallocated {elapsed : H → ℝ} (he : Measurable elapsed) :
    Measurable (s.weightedUnallocated elapsed) :=
  (Comparison.measurable_continuation (he.comp measurable_fst) measurable_const).mul s.measurable_unallocated

theorem measurable_remainingBudget {elapsed : H → ℝ} (he : Measurable elapsed) :
    Measurable (s.remainingBudget elapsed) :=
  (Comparison.measurable_continuation ((he.comp measurable_fst).add s.service.measurable_stopClock)
    measurable_const).mul s.measurable_unallocated

theorem measurable_futureBudget {elapsed : H → ℝ} (he : Measurable elapsed) :
    Measurable (s.futureBudget elapsed) :=
  measurable_branchSelect s.service.winner_disjoint s.service.measurable_winner
    (fun j => ((s.next j).measurable_weightedUnallocated
      ((he.comp measurable_fst).add measurable_snd)).comp (s.service.measurable_observation j)) measurable_const

theorem integrable_initial_coordinate (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) : Integrable (fun h => s.initial h i) ν := by
  apply (integrable_const (s.data.bound : ℝ)).mono'
    ((measurable_pi_apply i).comp s.measurable_initial).aestronglyMeasurable
  filter_upwards [hν] with h hh
  change ‖s.initial h i‖ ≤ (s.data.bound : ℝ)
  rw [Real.norm_of_nonneg ((R.admissible h hh).1 i)]
  exact R.initial_le_bound hh i

theorem integrable_unallocated (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) : Integrable s.unallocated (ν.prod independentExponentials) := by
  apply integrable_finset_sum
  intro i _
  have hm : Measurable (fun x : H × (ι → ℝ) => s.data.allocation (x.1, s.initial x.1 + x.2) i) :=
    (measurable_pi_apply i).comp (s.data.measurable_allocation.comp
      (measurable_fst.prodMk ((s.measurable_initial.comp measurable_fst).add measurable_snd)))
  have ha : Integrable (fun x : H × (ι → ℝ) => s.data.allocation (x.1, s.initial x.1 + x.2) i)
      (ν.prod independentExponentials) := by
    apply (integrable_const (s.data.bound : ℝ)).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (s.data.allocation_nonneg x.1 (s.initial x.1 + x.2) i)]
    exact s.data.allocation_le x.1 (s.initial x.1 + x.2) i
  exact (integrable_history_demand ν s.initial i (s.integrable_initial_coordinate R ν hν i)).sub ha

theorem integrable_weightedUnallocated (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    Integrable (s.weightedUnallocated R.elapsed) (ν.prod independentExponentials) := by
  apply (s.integrable_unallocated R ν hν).bdd_mul' (c := 1)
    (Comparison.measurable_continuation (R.measurable_elapsed.comp measurable_fst)
      measurable_const).aestronglyMeasurable
  filter_upwards [R.incoming_mem_ae ν hν] with x hx
  change ‖Comparison.continuation (R.elapsed x.1) 0‖ ≤ 1
  rw [Real.norm_of_nonneg (Comparison.continuation_nonneg (R.elapsed_le_one hx) (le_refl 0))]
  exact (Comparison.continuation_lt_one _ _).le

theorem integrable_remainingBudget (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    Integrable (s.remainingBudget R.elapsed) (ν.prod independentExponentials) := by
  apply (s.integrable_unallocated R ν hν).bdd_mul' (c := 1)
    (Comparison.measurable_continuation
      ((R.measurable_elapsed.comp measurable_fst).add s.service.measurable_stopClock)
      measurable_const).aestronglyMeasurable
  filter_upwards [R.incoming_mem_ae ν hν] with x hx
  have ht : R.elapsed x.1 + s.service.stopClock x ≤ 1 := by
    have hb := (s.service.stopClock_bounds x).2
    have hT := R.total_deadline x.1 hx
    change s.service.stopClock x ≤ s.deadline x.1 at hb
    linarith
  change ‖Comparison.continuation (R.elapsed x.1 + s.service.stopClock x) 0‖ ≤ 1
  rw [Real.norm_of_nonneg (Comparison.continuation_nonneg ht (le_refl 0))]
  exact (Comparison.continuation_lt_one _ _).le

theorem integral_weightedUnallocated_fiber (elapsed : H → ℝ) (h : H) :
    (∫ z, s.weightedUnallocated elapsed (h, z) ∂independentExponentials) = s.budget elapsed h := by
  unfold weightedUnallocated budget
  dsimp only
  rw [integral_const_mul, ← s.meanUnallocated_eq_integral]

theorem integrable_budget (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) : Integrable (s.budget R.elapsed) ν := by
  have h := (s.integrable_weightedUnallocated R ν hν).integral_prod_left
  simpa only [s.integral_weightedUnallocated_fiber] using h

theorem budget_nonneg (R : StageRegion s) {h : H} (hh : h ∈ R.domain) : 0 ≤ s.budget R.elapsed h :=
  mul_nonneg (Comparison.continuation_nonneg (R.elapsed_le_one hh) (le_refl 0))
    (s.meanUnallocated_nonneg (R.admissible h hh))

theorem futureBudget_bounds (R : StageRegion s) {x : H × (ι → ℝ)}
    (hx : x.1 ∈ R.domain) (hz : ∀ i, 0 < x.2 i) :
    0 ≤ s.futureBudget R.elapsed x ∧ s.futureBudget R.elapsed x ≤ s.remainingBudget R.elapsed x := by
  have ha := R.admissible x.1 hx
  have hT : R.elapsed x.1 + s.service.stopClock x ≤ 1 := by
    have hb := (s.service.stopClock_bounds x).2
    change s.service.stopClock x ≤ s.deadline x.1 at hb
    linarith [R.total_deadline x.1 hx]
  have hq := Comparison.continuation_nonneg hT (le_refl 0)
  classical
  by_cases hw : ∃ j, x ∈ s.service.winner j
  · obtain ⟨j, hj⟩ := hw
    have hn : 0 ≤ (s.next j).unallocated (s.service.observation j x) := by
      rw [s.next_unallocated_eq (hz j) hj]
      apply Finset.sum_nonneg
      intro i _
      exact sub_nonneg.mpr (ha.2 (s.initial x.1 + x.2)
        (fun i => add_nonneg (ha.1 i) (hz i).le) i.1)
    unfold futureBudget
    rw [branchSelect_of_mem s.service.winner_disjoint _ _ hj]
    unfold weightedUnallocated remainingBudget
    rw [s.service.stopClock_winner hj] at hq ⊢
    exact ⟨mul_nonneg hq hn, mul_le_mul_of_nonneg_left (s.next_unallocated_le ha hz hj) hq⟩
  · unfold futureBudget
    rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
    exact ⟨le_refl _, mul_nonneg hq (s.unallocated_nonneg ha (fun i => (hz i).le))⟩

theorem integrable_futureBudget (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    Integrable (s.futureBudget R.elapsed) (ν.prod independentExponentials) := by
  apply (s.integrable_remainingBudget R ν hν).mono'
    (s.measurable_futureBudget R.measurable_elapsed).aestronglyMeasurable
  have hp : ∀ᵐ x ∂ν.prod (independentExponentials (ι := ι)), ∀ i, 0 < x.2 i :=
    goodExecution_ae 0 s ν
  filter_upwards [R.incoming_mem_ae ν hν, hp] with x hx hz
  rw [Real.norm_of_nonneg (s.futureBudget_bounds R hx hz).1]
  exact (s.futureBudget_bounds R hx hz).2

end PosteriorStage
end StochasticMatching
