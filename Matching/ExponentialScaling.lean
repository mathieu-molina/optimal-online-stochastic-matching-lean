import Matching.ExponentialResidual

/-! The candidate completion time for a job served at a positive constant rate. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StochasticMatching

theorem scaled_unitExponential {r : ℝ} (hr : 0 < r) :
    Measure.map (fun z : ℝ => z / r) unitExponential = expMeasure r := by
  letI := isProbabilityMeasureExponential hr
  have hm : Measurable (fun z : ℝ => z / r) := measurable_id.div_const r
  apply Measure.ext_of_Iic
  intro x
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [map_measureReal_apply hm measurableSet_Iic]
  have hset : (fun z : ℝ => z / r) ⁻¹' Iic x = Iic (r * x) := by
    ext z
    simp only [mem_preimage, mem_Iic, div_le_iff₀ hr]
    rw [mul_comm x r]
  rw [hset, unitExponential_real_Iic, ← cdf_eq_real]
  change (if 0 ≤ r * x then 1 - Real.exp (-(r * x)) else 0) = exponentialCDFReal r x
  rw [exponentialCDFReal_eq hr]
  by_cases hx : 0 ≤ x
  · rw [if_pos (mul_nonneg hr.le hx), if_pos hx]
  · rw [if_neg (not_le.mpr (mul_neg_of_pos_of_neg hr (lt_of_not_ge hx))), if_neg hx]

theorem expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (exponentialPDF r) := rfl

theorem scaled_unitExponential_density {r : ℝ} (hr : 0 < r) :
    Measure.map (fun z : ℝ => z / r) unitExponential =
      volume.withDensity (exponentialPDF r) := by
  rw [scaled_unitExponential hr, expMeasure_eq_withDensity]

end StochasticMatching
