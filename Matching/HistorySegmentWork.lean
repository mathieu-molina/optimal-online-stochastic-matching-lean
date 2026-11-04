import Matching.FirstSegmentWork
import Matching.BudgetFunctions

/-! The stopped-segment work identity with a random incoming history. All
integrability and product-measure exchanges are proved for finite histories.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

noncomputable def stoppedWork (i : ι) (x : H × (ι → ℝ)) : ℝ :=
  (s.service.curves x.1).service i (s.service.stopClock x)

theorem measurable_stoppedWork (i : ι) : Measurable (s.stoppedWork i) :=
  (s.service.measurable_service i).comp
    (measurable_fst.prodMk s.service.measurable_stopClock)

theorem integrable_stoppedWork (i : ι) (μ : Measure (H × (ι → ℝ))) [IsFiniteMeasure μ] :
    Integrable (s.stoppedWork i) μ := by
  apply (integrable_const ((s.data.bound : ℝ) * s.horizon)).mono'
    (s.measurable_stoppedWork i).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖(s.service.curves x.1).service i (s.service.stopClock x)‖ ≤ _
  rw [Real.norm_of_nonneg ((s.service.curves x.1).service_nonneg
    (s.service.stopClock_bounds x) i)]
  exact (s.service_le_bound x.1 (s.service.stopClock_bounds x) i).trans
    (mul_le_mul_of_nonneg_left
      ((s.service.stopClock_bounds x).2.trans (s.deadline_le x.1)) s.data.bound.coe_nonneg)

theorem stoppedWork_expected_winner (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    (∫ x, s.stoppedWork i x ∂ν.prod independentExponentials) =
      ∫ _ in s.service.winner i, (1 : ℝ) ∂ν.prod independentExponentials := by
  have hw : Integrable ((s.service.winner i).indicator (fun _ => (1 : ℝ)))
      (ν.prod independentExponentials) :=
    (integrable_const 1).indicator (s.service.measurable_winner i)
  rw [← integral_indicator (s.service.measurable_winner i),
    integral_prod _ (s.integrable_stoppedWork i (ν.prod independentExponentials)),
    integral_prod _ hw]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  dsimp only
  have he : (fun z => (s.service.winner i).indicator (fun _ => (1 : ℝ)) (h, z)) =
      (variableWinner (s.service.curves h).service (s.service.curves h).deadline i).indicator
        (fun _ => (1 : ℝ)) := rfl
  rw [he, integral_indicator ((s.service.curves h).measurable_winner i)]
  simpa only [stoppedWork, HistoryServiceFamily.stopClock_eq] using
    (s.service.curves h).stopped_service_expectation i

theorem stoppedWork_expected_marked (ν : Measure H) [IsFiniteMeasure ν] (i : ι) :
    (∫ x, s.stoppedWork i x ∂ν.prod independentExponentials) =
      ∫ _ : (H × ℝ) × ({j : ι // j ≠ i} → ℝ), (1 : ℝ)
        ∂(s.service.markedHistoryMeasure ν i).prod independentExponentials := by
  rw [s.stoppedWork_expected_winner ν i]
  have h := integral_map_of_stronglyMeasurable
    (μ := (ν.prod independentExponentials).restrict (s.service.winner i))
    (s.service.measurable_observation i)
    (f := fun _ => (1 : ℝ)) stronglyMeasurable_const
  rw [s.service.first_completion_factorization] at h
  exact h.symm

end StochasticMatching.PosteriorStage
