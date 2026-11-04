import Matching.ExponentialResidual
import Matching.ComparisonPotential
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Expected capped work for a unit-exponential job and the comparison value. -/

open MeasureTheory ProbabilityTheory Set

namespace StochasticMatching

instance unitExponential_noAtoms : NoAtoms unitExponential := by
  constructor
  intro x
  simp [unitExponential, expMeasure, gammaMeasure, withDensity_apply]

theorem unitExponential_real_Ici {x : ℝ} (hx : 0 ≤ x) :
    unitExponential.real (Ici x) = Real.exp (-x) := by
  rw [← measureReal_congr (Ioi_ae_eq_Ici (μ := unitExponential))]
  exact unitExponential_real_Ioi hx

theorem integrable_capped_work {B : ℝ} (hB : 0 ≤ B) :
    Integrable (fun z => min z B) unitExponential := by
  apply (integrable_const B).mono'
    ((measurable_id.min measurable_const).aestronglyMeasurable)
  filter_upwards [unitExponential_ae_pos] with z hz
  change ‖min z B‖ ≤ B
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_of_lt hz) hB)]
  exact min_le_right _ _

theorem integral_exp_neg_zero_to {B : ℝ} :
    (∫ t in (0 : ℝ)..B, Real.exp (-t)) = 1 - Real.exp (-B) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := B)
    (fun t _ => (show HasDerivAt (fun u : ℝ => -Real.exp (-u)) (Real.exp (-t)) t from
      by simpa using (hasDerivAt_neg_exp_mul_exp (r := 1) (x := t))))
    (hc.intervalIntegrable 0 B)
  simpa only [neg_zero, Real.exp_zero, sub_neg_eq_add, neg_add_eq_sub] using h

theorem expected_capped_work {B : ℝ} (hB : 0 ≤ B) :
    (∫ z, min z B ∂unitExponential) = 1 - Real.exp (-B) := by
  have hnonneg : 0 ≤ᵐ[unitExponential] (fun z => min z B) := by
    filter_upwards [unitExponential_ae_pos] with z hz
    exact le_min (le_of_lt hz) hB
  rw [(integrable_capped_work hB).integral_eq_integral_Ioc_meas_le hnonneg
    (Filter.Eventually.of_forall (fun z => min_le_right z B))]
  calc
    _ = ∫ t in Ioc 0 B, Real.exp (-t) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have hset : {z : ℝ | t ≤ min z B} = Ici t := by
        ext z
        simp only [mem_setOf_eq, le_min_iff, mem_Ici, and_iff_left ht.2]
      change unitExponential.real {z : ℝ | t ≤ min z B} = Real.exp (-t)
      rw [hset, unitExponential_real_Ici (le_of_lt ht.1)]
    _ = 1 - Real.exp (-B) := by
      rw [← intervalIntegral.integral_of_le hB]
      exact integral_exp_neg_zero_to

theorem expected_work_eq_completion_probability {B : ℝ} (hB : 0 ≤ B) :
    (∫ z, min z B ∂unitExponential) = unitExponential.real (Iic B) := by
  rw [expected_capped_work hB, unitExponential_real_Iic, if_pos hB]

theorem continuation_eq_expected_work {t h : ℝ} (ht : t ≤ 1) (hh : 0 ≤ h) :
    Comparison.continuation t h =
      ∫ z, min z ((h + 1) * (Real.exp (1 - t) - 1)) ∂unitExponential := by
  have he : 0 ≤ Real.exp (1 - t) - 1 := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ 1 - t by linarith)
    linarith
  rw [expected_capped_work (mul_nonneg (by linarith) he)]
  rfl

theorem comparison_ratio_eq_expected_work :
    Comparison.ratio = ∫ z, min z (Real.exp 1 - 1) ∂unitExponential := by
  have h := continuation_eq_expected_work (t := 0) (h := 0) (by norm_num) (by norm_num)
  simpa [Comparison.continuation_initial] using h

end StochasticMatching
