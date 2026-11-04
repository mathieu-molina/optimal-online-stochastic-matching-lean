import Matching.StoppingClock
import Matching.StoppedOccupation
import Matching.FirstStepReward

/-! Expected service in an actual stopped segment equals the probability of
the corresponding first completion. The stopping clock is the one selected
from the exponential demands, not an independent auxiliary clock.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

theorem before_stop_probability {t : ℝ} (ht : t ∈ Ico 0 p.deadline) :
    (∫ _ in {z | t < p.stopClock z}, (1 : ℝ)
      ∂(independentExponentials (ι := ι))) =
      survivalCurve (fun u i => p.service i u) t := by
  have he : {z | t < p.stopClock z} =ᵐ[independentExponentials]
      survivalBox (fun i => p.service i t) := by
    filter_upwards [p.survival_iff_before_stopClock_ae] with z hz
    exact propext (hz t ht).symm
  rw [Measure.restrict_congr_set he, setIntegral_const, measureReal_def,
    survivalBox_measure_exp_sum (p.service_nonneg ⟨ht.1, ht.2.le⟩),
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [smul_eq_mul, mul_one, survivalCurve]

theorem stopped_service_expectation (i : ι) :
    (∫ z, p.service i (p.stopClock z) ∂independentExponentials) =
      ∫ _ in variableWinner p.service p.deadline i, (1 : ℝ) ∂independentExponentials := by
  have h := integral_weighted_stopped_interval (independentExponentials (ι := ι))
    p.deadline_pos.le p.stopClock p.measurable_stopClock p.stopClock_bounds
    (fun _ => (1 : ℝ)) (integrable_const 1) (p.rate i) (p.rate_continuous i)
  have he : (fun z => (1 : ℝ) * (∫ t in (0 : ℝ)..p.stopClock z, p.rate i t)) =
      fun z => p.service i (p.stopClock z) := by
    funext z
    rw [one_mul, ← p.service_eq_integral (p.stopClock_bounds z) i]
  rw [he] at h
  rw [h, p.winner_clock_integral i measurable_const]
  rw [intervalIntegral.integral_of_le p.deadline_pos.le,
    intervalIntegral.integral_of_le p.deadline_pos.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [p.before_stop_probability ⟨ht.1.le, ht.2⟩, mul_one]

end StochasticMatching.ServiceCurveFamily
