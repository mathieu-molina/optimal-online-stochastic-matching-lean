import Matching.BudgetFunctions

/-! The comparison budget dominates a stage's defect plus the expected budgets
of all actual restart branches. This is the quantitative recursion needed to
bound the full accumulated defect.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

theorem futureBudget_winner_integral (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (j : ι) :
    (∫ x in s.service.winner j, s.futureBudget R.elapsed x ∂ν.prod independentExponentials) =
    ∫ h, (s.next j).budget (R.next j).elapsed h ∂s.service.markedHistoryMeasure ν j := by
  letI := s.service.finite_markedHistoryMeasure ν j
  have hm := (s.next j).measurable_weightedUnallocated (R.next j).measurable_elapsed
  have hi := (s.next j).integrable_weightedUnallocated (R.next j)
    (s.service.markedHistoryMeasure ν j) (R.next_concentrated ν hν j)
  calc
    _ = ∫ x in s.service.winner j,
        (s.next j).weightedUnallocated (R.next j).elapsed (s.service.observation j x)
          ∂ν.prod independentExponentials := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (s.service.measurable_winner j)] with x hx
      exact branchSelect_of_mem s.service.winner_disjoint _ _ hx
    _ = ∫ x, (s.next j).weightedUnallocated (R.next j).elapsed x
        ∂Measure.map (s.service.observation j)
          ((ν.prod independentExponentials).restrict (s.service.winner j)) :=
      (integral_map_of_stronglyMeasurable (s.service.measurable_observation j) hm.stronglyMeasurable).symm
    _ = _ := by
      rw [s.service.first_completion_factorization, integral_prod _ hi]
      simp only [(s.next j).integral_weightedUnallocated_fiber]

theorem integral_futureBudget (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ x, s.futureBudget R.elapsed x ∂ν.prod independentExponentials) =
    ∑ j, ∫ h, (s.next j).budget (R.next j).elapsed h ∂s.service.markedHistoryMeasure ν j := by
  have hi := s.integrable_futureBudget R ν hν
  rw [s.service.segment_measure_decomposition ν, integrable_add_measure] at hi
  have ht : (∫ x in s.service.terminalEvent, s.futureBudget R.elapsed x
      ∂ν.prod independentExponentials) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem s.service.measurable_terminalEvent] with x hx
    apply branchSelect_of_not_mem
    intro j hj
    exact Set.disjoint_left.mp (s.service.winner_disjoint_terminal j) hx hj
  conv_lhs => rw [s.service.segment_measure_decomposition ν]
  rw [integral_add_measure hi.1 hi.2, ht, zero_add, integral_sum_measure hi.2, tsum_fintype]
  exact Finset.sum_congr rfl (fun j _ => s.futureBudget_winner_integral R ν hν j)

theorem integral_futureBudget_le_remaining (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ x, s.futureBudget R.elapsed x ∂ν.prod independentExponentials) ≤
      ∫ x, s.remainingBudget R.elapsed x ∂ν.prod independentExponentials := by
  apply integral_mono_ae (s.integrable_futureBudget R ν hν) (s.integrable_remainingBudget R ν hν)
  have hp : ∀ᵐ x ∂ν.prod (independentExponentials (ι := ι)), ∀ i, 0 < x.2 i :=
    goodExecution_ae 0 s ν
  filter_upwards [R.incoming_mem_ae ν hν, hp] with x hx hz
  exact (s.futureBudget_bounds R hx hz).2

theorem budget_step (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ h, s.defect R.elapsed h ∂ν) +
      ∑ j, ∫ h, (s.next j).budget (R.next j).elapsed h
        ∂s.service.markedHistoryMeasure ν j ≤
      ∫ h, s.budget R.elapsed h ∂ν := by
  have hpoint : ∀ᵐ h ∂ν,
      s.defect R.elapsed h + (∫ z, s.remainingBudget R.elapsed (h, z) ∂independentExponentials) ≤
        s.budget R.elapsed h := by
    filter_upwards [hν] with h hh
    simpa only [remainingBudget, HistoryServiceFamily.stopClock_eq, budget] using
      s.defect_le_stopped_budget R.elapsed h (R.admissible h hh) (le_of_eq (R.total_deadline h hh))
  have h := integral_mono_ae
    ((s.integrable_defect R ν hν).add (s.integrable_remainingBudget R ν hν).integral_prod_left)
    (s.integrable_budget R ν hν) hpoint
  dsimp only [Pi.add_apply] at h
  rw [integral_add (s.integrable_defect R ν hν)
    (s.integrable_remainingBudget R ν hν).integral_prod_left,
    ← integral_prod _ (s.integrable_remainingBudget R ν hν)] at h
  have hf := s.integral_futureBudget_le_remaining R ν hν
  rw [s.integral_futureBudget R ν hν] at hf
  linarith

end StochasticMatching.PosteriorStage
