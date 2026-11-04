import Matching.ComparisonFlow
import Matching.OneStepLaw

/-! Identify the analytic first-step terms with expectations under the actual
winner and terminal events of the independent exponential demand sample.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

theorem winner_clock_law (j : ι) :
    Measure.map (fun z : ι → ℝ => cappedHit (p.service j) p.deadline (z j))
      (independentExponentials.restrict (variableWinner p.service p.deadline j)) =
      variableMarkedTimeMeasure p.service p.rate p.deadline j := by
  have h := congrArg
    (Measure.map (Prod.fst : ℝ × ({i : ι // i ≠ j} → ℝ) → ℝ))
    (variable_first_completion_marked_law p.service_continuous p.rate_continuous
      p.deadline_pos p.service_monotone p.service_zero p.rate_nonneg p.service_deriv j)
  rw [Measure.map_map measurable_fst (p.measurable_observation j)] at h
  simpa only [Function.comp_def, variableObservation, Measure.map_fst_prod,
    measure_univ, one_smul] using h

theorem winner_clock_integral (j : ι) {g : ℝ → ℝ} (hg : Measurable g) :
    (∫ z in variableWinner p.service p.deadline j,
      g (cappedHit (p.service j) p.deadline (z j)) ∂independentExponentials) =
    ∫ t in (0 : ℝ)..p.deadline,
      p.rate j t * survivalCurve (fun u i => p.service i u) t * g t := by
  have hm : Measurable (fun t => ENNReal.ofReal
      (p.rate j t * Real.exp (-(∑ i, p.service i t)))) := by
    have hs : Continuous (fun t => ∑ i, p.service i t) :=
      continuous_finset_sum _ (fun i _ => p.service_continuous i)
    exact ((p.rate_continuous j).mul (Real.continuous_exp.comp hs.neg)).measurable.ennreal_ofReal
  calc
    _ = ∫ t, g t ∂Measure.map
        (fun z : ι → ℝ => cappedHit (p.service j) p.deadline (z j))
        (independentExponentials.restrict (variableWinner p.service p.deadline j)) :=
      (integral_map_of_stronglyMeasurable (p.measurable_clock j) hg.stronglyMeasurable).symm
    _ = ∫ t in Icc 0 p.deadline,
        (ENNReal.ofReal (p.rate j t * Real.exp (-(∑ i, p.service i t)))).toReal * g t := by
      rw [p.winner_clock_law, variableMarkedTimeMeasure,
        integral_withDensity_eq_integral_toReal_smul hm
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      rfl
    _ = ∫ t in Icc 0 p.deadline,
        p.rate j t * survivalCurve (fun u i => p.service i u) t * g t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [ENNReal.toReal_ofReal (mul_nonneg (p.rate_nonneg j t ht) (Real.exp_pos _).le)]
      rfl
    _ = _ := by rw [intervalIntegral.integral_of_le p.deadline_pos.le, integral_Icc_eq_integral_Ioc]

theorem terminal_constant_integral (c : ℝ) :
    (∫ _ in p.terminalSurvival, c ∂(independentExponentials (ι := ι))) =
      survivalCurve (fun t i => p.service i t) p.deadline * c := by
  rw [setIntegral_const, measureReal_def, p.terminal_survival_probability,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rfl

theorem comparison_marked_expectation (elapsed : ℝ) (initial : ι → ℝ) :
    (∑ j, ∫ z in variableWinner p.service p.deadline j,
      p.comparisonJump elapsed initial j (cappedHit (p.service j) p.deadline (z j))
        ∂independentExponentials) =
    ∫ t in (0 : ℝ)..p.deadline,
      survivalCurve (fun u i => p.service i u) t *
        ∑ j, p.rate j t * p.comparisonJump elapsed initial j t := by
  simp_rw [p.winner_clock_integral _ (p.continuous_comparisonJump elapsed initial _).measurable]
  have hs : Continuous (survivalCurve (fun u i => p.service i u)) :=
    Real.continuous_exp.comp (continuous_finset_sum _ (fun i _ => p.service_continuous i)).neg
  rw [← intervalIntegral.integral_finset_sum]
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j _
    exact (((p.rate_continuous j).mul hs).mul
      (p.continuous_comparisonJump elapsed initial j)).intervalIntegrable 0 p.deadline

theorem comparison_actual_first_step (elapsed : ℝ) (initial : ι → ℝ) :
    (∫ _ in p.terminalSurvival, p.comparisonPotential elapsed initial p.deadline
      ∂(independentExponentials (ι := ι))) +
    (∑ j, ∫ z in variableWinner p.service p.deadline j,
      p.comparisonJump elapsed initial j (cappedHit (p.service j) p.deadline (z j))
        ∂independentExponentials) - p.comparisonPotential elapsed initial 0 =
    ∫ t in (0 : ℝ)..p.deadline, survivalCurve (fun u i => p.service i u) t *
      ∑ i, -(initial i + p.service i t + 1 - p.rate i t) *
        Comparison.sensitivity (elapsed + t) (initial i + p.service i t) := by
  rw [p.terminal_constant_integral, p.comparison_marked_expectation]
  exact p.comparison_first_step_identity elapsed initial

end StochasticMatching.ServiceCurveFamily
