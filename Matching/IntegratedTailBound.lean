import Matching.TailDeficiencyBound
import Mathlib.MeasureTheory.Integral.Prod

/-! Fubini turns the pointwise empirical-tail fluctuation estimate into an
integrated error bound of `2 * sqrt m`. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem empiricalTailError_joint_measurable :
    Measurable (fun x : (ι → ℝ) × ℝ => empiricalTailError x.1 x.2) := by
  unfold empiricalTailError empiricalTail tailIndicator
  apply continuous_abs.measurable.comp
  apply Measurable.sub
  · exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
      (measurableSet_lt measurable_snd ((measurable_pi_apply i).comp measurable_fst)) measurable_const)
  · exact measurable_const.mul measurable_snd.neg.exp

theorem empiricalTailError_integrable_sample {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun z : ι → ℝ => empiricalTailError z t) independentExponentials := by
  have he (z : ι → ℝ) : empiricalTail z t - (Fintype.card ι : ℝ) * Real.exp (-t) =
      ∑ i, centeredTail t i z := by
    simp [empiricalTail, centeredTail, Finset.sum_sub_distrib, nsmul_eq_mul]
  simp only [empiricalTailError, he]
  exact (integrable_finset_sum _ (fun (i : ι) _ => centeredTail_integrable ht i)).abs

theorem sqrt_mul_exp_neg (m t : ℝ) (hm : 0 ≤ m) :
    Real.sqrt (m * Real.exp (-t)) = Real.sqrt m * Real.exp ((-1 / 2 : ℝ) * t) := by
  rw [Real.sqrt_mul hm]
  congr 1
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg _) (Real.exp_nonneg _)).mpr
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrable_sqrt_exp_tail (m : ℝ) (hm : 0 ≤ m) :
    IntegrableOn (fun t => Real.sqrt (m * Real.exp (-t))) (Ioi (0 : ℝ)) := by
  simp_rw [sqrt_mul_exp_neg m _ hm]
  exact (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0).const_mul _

theorem integral_sqrt_exp_tail (m : ℝ) (hm : 0 ≤ m) :
    (∫ t in Ioi (0 : ℝ), Real.sqrt (m * Real.exp (-t))) = 2 * Real.sqrt m := by
  simp_rw [sqrt_mul_exp_neg m _ hm]
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0]
  norm_num
  ring

theorem empiricalTailError_integrable_prod :
    Integrable (fun x : (ι → ℝ) × ℝ => empiricalTailError x.1 x.2)
      (independentExponentials.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  apply (integrable_prod_iff' empiricalTailError_joint_measurable.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact empiricalTailError_integrable_sample ht.le
  · have hm : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    apply (integrable_sqrt_exp_tail (Fintype.card ι) hm).mono'
      empiricalTailError_joint_measurable.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.norm_eq_abs, empiricalTailError, abs_abs]
    rw [abs_of_nonneg (integral_nonneg (fun z => abs_nonneg _))]
    exact empiricalTail_mean_abs_bound ht.le

theorem empiricalTailError_integrable_integral :
    Integrable (fun z : ι → ℝ => ∫ t in Ioi (0 : ℝ), empiricalTailError z t)
      independentExponentials :=
  empiricalTailError_integrable_prod.integral_prod_left

theorem expected_integrated_tail_error_le :
    (∫ z : ι → ℝ, (∫ t in Ioi (0 : ℝ), empiricalTailError z t) ∂independentExponentials) ≤
      2 * Real.sqrt (Fintype.card ι) := by
  rw [integral_integral_swap empiricalTailError_integrable_prod]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.sqrt ((Fintype.card ι : ℝ) * Real.exp (-t)) := by
      apply integral_mono_ae empiricalTailError_integrable_prod.integral_prod_right
        (integrable_sqrt_exp_tail _ (Nat.cast_nonneg _))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact empiricalTail_mean_abs_bound ht.le
    _ = 2 * Real.sqrt (Fintype.card ι) := integral_sqrt_exp_tail _ (Nat.cast_nonneg _)

end StochasticMatching
