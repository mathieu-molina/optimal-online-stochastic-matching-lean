import Matching.StagePotential

/-! Integrate the concrete one-step comparison payoff over incoming histories.
All integrability conditions follow from finite measures and the proved region
bounds. The terminal contribution vanishes at the common absolute deadline.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
namespace StageRegion
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  {s : PosteriorStage H ι} (R : StageRegion s)

theorem incoming_mem_ae (ν : Measure H) (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    ∀ᵐ x ∂ν.prod (independentExponentials (ι := ι)), x.1 ∈ R.domain := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (R.measurable_domain.preimage measurable_fst)).mpr
  filter_upwards [hν] with h hh
  exact Filter.Eventually.of_forall (fun _ => hh)

end StageRegion
namespace PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

theorem integrable_potential (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) : Integrable (s.potential R.elapsed) ν := by
  apply (integrable_const (Fintype.card ι : ℝ)).mono'
    (s.measurable_potential R.measurable_elapsed).aestronglyMeasurable
  filter_upwards [hν] with h hh
  rw [Real.norm_of_nonneg (s.potential_bounds R hh).1]
  exact (s.potential_bounds R hh).2

theorem integrable_stepOutcome (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    Integrable (s.stepOutcome R.elapsed) (ν.prod independentExponentials) := by
  apply (integrable_const (Fintype.card ι : ℝ)).mono'
    (s.measurable_stepOutcome R.measurable_elapsed).aestronglyMeasurable
  filter_upwards [R.incoming_mem_ae ν hν] with x hx
  rw [Real.norm_of_nonneg (s.stepOutcome_bounds R hx).1]
  exact (s.stepOutcome_bounds R hx).2

theorem integrable_defect (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) : Integrable (s.defect R.elapsed) ν := by
  exact (s.integrable_potential R ν hν).sub (s.integrable_stepOutcome R ν hν).integral_prod_left

theorem integral_defect (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ h, s.defect R.elapsed h ∂ν) =
      (∫ h, s.potential R.elapsed h ∂ν) -
        ∫ x, s.stepOutcome R.elapsed x ∂ν.prod independentExponentials := by
  unfold defect
  rw [integral_sub (s.integrable_potential R ν hν)
    (s.integrable_stepOutcome R ν hν).integral_prod_left,
    ← integral_prod _ (s.integrable_stepOutcome R ν hν)]

theorem stepOutcome_winner_integral (elapsed : H → ℝ) (he : Measurable elapsed)
    (ν : Measure H) [IsFiniteMeasure ν] (j : ι) :
    (∫ x in s.service.winner j, s.stepOutcome elapsed x ∂ν.prod independentExponentials) =
    ∫ h, 1 + (s.next j).potential (fun h => elapsed h.1 + h.2) h
      ∂s.service.markedHistoryMeasure ν j := by
  letI := s.service.finite_markedHistoryMeasure ν j
  let g : H × ℝ → ℝ := fun h => 1 + (s.next j).potential (fun h => elapsed h.1 + h.2) h
  have hg : Measurable g := measurable_const.add
    ((s.next j).measurable_potential ((he.comp measurable_fst).add measurable_snd))
  calc
    _ = ∫ x in s.service.winner j, g (s.service.observation j x).1
        ∂ν.prod independentExponentials := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (s.service.measurable_winner j)] with x hx
      exact branchSelect_of_mem s.service.winner_disjoint _ _ hx
    _ = ∫ x, g x.1 ∂Measure.map (s.service.observation j)
        ((ν.prod independentExponentials).restrict (s.service.winner j)) :=
      (integral_map_of_stronglyMeasurable (s.service.measurable_observation j)
        (hg.comp measurable_fst).stronglyMeasurable).symm
    _ = _ := by
      rw [s.service.first_completion_factorization, integral_fun_fst]
      simp only [measureReal_univ_eq_one, one_smul, g]

theorem integral_stepOutcome (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ x, s.stepOutcome R.elapsed x ∂ν.prod independentExponentials) =
    ∑ j, ∫ h, 1 + (s.next j).potential (R.next j).elapsed h
      ∂s.service.markedHistoryMeasure ν j := by
  have hi := s.integrable_stepOutcome R ν hν
  rw [s.service.segment_measure_decomposition ν, integrable_add_measure] at hi
  have ht : (∫ x in s.service.terminalEvent, s.stepOutcome R.elapsed x
      ∂ν.prod independentExponentials) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae (R.incoming_mem_ae ν hν),
      ae_restrict_mem s.service.measurable_terminalEvent] with x hx ht
    rw [s.stepOutcome_eq,
      (s.service.curves x.1).comparisonOutcome_terminal (R.elapsed x.1) (s.initial x.1)
        (mem_univ_pi.mpr ht)]
    exact s.comparison_terminal_zero x.1 (R.total_deadline x.1 hx)
  conv_lhs => rw [s.service.segment_measure_decomposition ν]
  rw [integral_add_measure hi.1 hi.2, ht, zero_add, integral_sum_measure hi.2, tsum_fintype]
  exact Finset.sum_congr rfl (fun j _ =>
    s.stepOutcome_winner_integral R.elapsed R.measurable_elapsed ν j)

theorem potential_defect_recursion (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) :
    (∫ h, s.potential R.elapsed h ∂ν) = (∫ h, s.defect R.elapsed h ∂ν) +
      ∑ j, ∫ h, 1 + (s.next j).potential (R.next j).elapsed h
        ∂s.service.markedHistoryMeasure ν j := by
  rw [s.integral_defect R ν hν, s.integral_stepOutcome R ν hν]
  ring

end PosteriorStage
end StochasticMatching
