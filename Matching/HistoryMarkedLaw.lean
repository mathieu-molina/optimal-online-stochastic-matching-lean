import Matching.HistoryService

/-! Integrate the marked first-completion law over measurable random histories.
The fresh demand vector has the independent exponential product law, independent
of the incoming history. The output factorization proves that this independence
is preserved for the surviving residuals and the newly extended history.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching.HistoryServiceFamily

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : HistoryServiceFamily H ι)

theorem markedHistoryMeasure_lintegral (ν : Measure H) (j : ι)
    (g : H × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂p.markedHistoryMeasure ν j) =
      ∫⁻ h, (∫⁻ t in Icc 0 (p.curves h).deadline,
        p.markedDensity j (h, t) * g (h, t)) ∂ν := by
  rw [markedHistoryMeasure, lintegral_withDensity_eq_lintegral_mul (ν.prod volume)
    ((p.measurable_markedDensity j).indicator p.measurable_timeWindow) hg]
  have heq : p.timeWindow.indicator (p.markedDensity j) * g =
      p.timeWindow.indicator (fun x => p.markedDensity j x * g x) := by
    funext x
    by_cases hx : x ∈ p.timeWindow <;> simp [hx]
  have hfg : Measurable (fun x => p.markedDensity j x * g x) :=
    (p.measurable_markedDensity j).mul hg
  rw [heq, lintegral_prod _ (hfg.indicator p.measurable_timeWindow).aemeasurable]
  apply lintegral_congr
  intro h
  change (∫⁻ t, (Icc 0 (p.curves h).deadline).indicator
    (fun t => p.markedDensity j (h, t) * g (h, t)) t) = _
  rw [lintegral_indicator measurableSet_Icc]

theorem winner_lintegral (ν : Measure H) (j : ι)
    (f : (H × ℝ) × ({i : ι // i ≠ j} → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in p.winner j, f (p.observation j x) ∂ν.prod independentExponentials) =
      ∫⁻ h, (∫⁻ t in Icc 0 (p.curves h).deadline,
        p.markedDensity j (h, t) * (∫⁻ y, f ((h, t), y) ∂independentExponentials)) ∂ν := by
  have hobs : Measurable (fun x => f (p.observation j x)) :=
    hf.comp (p.measurable_observation j)
  rw [← lintegral_indicator (p.measurable_winner j), lintegral_prod _
    ((hobs.indicator (p.measurable_winner j)).aemeasurable)]
  apply lintegral_congr
  intro h
  let F : ℝ × ({i : ι // i ≠ j} → ℝ) → ℝ≥0∞ := fun q => f ((h, q.1), q.2)
  have hF : Measurable F :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  change (∫⁻ z, (variableWinner (p.curves h).service (p.curves h).deadline j).indicator
    (fun z => F (variableObservation (p.curves h).service (p.curves h).deadline j z)) z
      ∂independentExponentials) = _
  rw [lintegral_indicator ((p.curves h).measurable_winner j),
    ← lintegral_map hF ((p.curves h).measurable_observation j),
    variable_first_completion_marked_law (p.curves h).service_continuous
      (p.curves h).rate_continuous (p.curves h).deadline_pos (p.curves h).service_monotone
      (p.curves h).service_zero (p.curves h).rate_nonneg (p.curves h).service_deriv j,
    lintegral_prod _ hF.aemeasurable, variableMarkedTimeMeasure]
  have hd : Measurable (fun t => p.markedDensity j (h, t)) :=
    (p.measurable_markedDensity j).comp (measurable_const.prodMk measurable_id)
  exact lintegral_withDensity_eq_lintegral_mul (volume.restrict (Icc 0 (p.curves h).deadline))
    hd (hF.lintegral_prod_right' (ν := independentExponentials))

/-- After observing the first completing job and its time, the surviving
residual vector is independent of the extended history and is again a product
of unit exponential laws. Both sides are unnormalized branch measures. -/
theorem first_completion_factorization (ν : Measure H) (j : ι) :
    Measure.map (p.observation j) ((ν.prod independentExponentials).restrict (p.winner j)) =
      (p.markedHistoryMeasure ν j).prod independentExponentials := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (p.measurable_observation j), p.winner_lintegral ν j f hf,
    lintegral_prod _ hf.aemeasurable,
    p.markedHistoryMeasure_lintegral ν j _ hf.lintegral_prod_right']

end StochasticMatching.HistoryServiceFamily
