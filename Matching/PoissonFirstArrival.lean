import Matching.PoissonInputKernel
import Matching.ExponentialScaling

/-! The arrival kernel is the actual first-event law of independent
exponential clocks indexed by arrival type. Zero intensities are allowed.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

def constantRateCurve (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (T : ℝ) (hT : 0 < T) : ServiceCurveFamily σ where
  deadline := T
  deadline_pos := hT
  service := fun s t => capacity s * t
  rate := fun s _ => capacity s
  service_continuous := fun _ => continuous_const.mul continuous_id
  rate_continuous := fun _ => continuous_const
  service_monotone := fun s _ _ _ _ hab => mul_le_mul_of_nonneg_left hab (hc s)
  service_zero := fun s => mul_zero _
  rate_nonneg := fun s _ _ => hc s
  service_deriv := fun s t _ => by simpa using (hasDerivAt_id t).const_mul (capacity s)

theorem poisson_first_arrival_law (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (T : ℝ) (hT : 0 < T) :
    Measure.map (constantRateCurve capacity hc T hT).firstEvent independentExponentials =
      poissonNextArrival capacity T := by
  simpa only [constantRateCurve, variableMarkedTimeMeasure, ← Finset.sum_mul,
    neg_mul, poissonNextArrival] using
    (constantRateCurve capacity hc T hT).firstEvent_distribution

end StochasticMatching
