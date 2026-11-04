import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Full scalar memorylessness at a deterministic nonnegative service threshold.
This is not yet the adaptive-history version required by the posterior policy.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace StochasticMatching

noncomputable def unitExponential : Measure ℝ := expMeasure 1

instance unitExponential_probability : IsProbabilityMeasure unitExponential :=
  isProbabilityMeasureExponential (by norm_num)

theorem unitExponential_real_Iic (x : ℝ) :
    unitExponential.real (Iic x) = if 0 ≤ x then 1 - Real.exp (-x) else 0 := by
  rw [← cdf_eq_real]
  change exponentialCDFReal 1 x = _
  simpa using exponentialCDFReal_eq (r := 1) (by norm_num) x

theorem unitExponential_real_Ioi {x : ℝ} (hx : 0 ≤ x) :
    unitExponential.real (Ioi x) = Real.exp (-x) := by
  have h := measureReal_compl (μ := unitExponential) (s := Iic x) measurableSet_Iic
  simpa [unitExponential_real_Iic, hx] using h

theorem unitExponential_real_Ioc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    unitExponential.real (Ioc a b) = Real.exp (-a) - Real.exp (-b) := by
  have h := measureReal_diff (μ := unitExponential)
    (Iic_subset_Iic.mpr hab) measurableSet_Iic
  rw [Iic_diff_Iic] at h
  rw [h, unitExponential_real_Iic, unitExponential_real_Iic,
    if_pos (ha.trans hab), if_pos ha]
  ring

theorem unitExponential_tail_ratio {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    unitExponential.real (Ioi (a + b)) / unitExponential.real (Ioi a) =
      Real.exp (-b) := by
  rw [unitExponential_real_Ioi (add_nonneg ha hb), unitExponential_real_Ioi ha,
    neg_add, Real.exp_add]
  exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

noncomputable def residualLaw (h : ℝ) : Measure ℝ :=
  Measure.map (fun z : ℝ => z - h) (unitExponential.restrict (Ioi h))

instance residualLaw_finite (h : ℝ) : IsFiniteMeasure (residualLaw h) := by
  unfold residualLaw
  infer_instance

theorem residualLaw_real_Iic {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    (residualLaw h).real (Iic x) =
      Real.exp (-h) * unitExponential.real (Iic x) := by
  have hm : Measurable (fun z : ℝ => z - h) := measurable_id.sub_const h
  rw [residualLaw, map_measureReal_apply hm measurableSet_Iic,
    measureReal_restrict_apply (hm measurableSet_Iic)]
  by_cases hx : 0 ≤ x
  · have hset : (fun z : ℝ => z - h) ⁻¹' Iic x ∩ Ioi h = Ioc h (h + x) := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_Ioc]
      constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
    rw [hset, unitExponential_real_Ioc hh (by linarith),
      unitExponential_real_Iic, if_pos hx, neg_add, Real.exp_add]
    ring
  · have hset : (fun z : ℝ => z - h) ⁻¹' Iic x ∩ Ioi h = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_empty_iff_false,
        iff_false, not_and]
      intro hz
      linarith
    rw [hset, measureReal_empty, unitExponential_real_Iic, if_neg hx, mul_zero]

/-- Unnormalized memorylessness as equality of measures. -/
theorem residualLaw_eq_smul {h : ℝ} (hh : 0 ≤ h) :
    residualLaw h = ENNReal.ofReal (Real.exp (-h)) • unitExponential := by
  apply Measure.ext_of_Iic
  intro x
  have hfin : (ENNReal.ofReal (Real.exp (-h)) • unitExponential) (Iic x) ≠ ⊤ := by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  apply (measureReal_eq_measureReal_iff (by finiteness) hfin).mp
  rw [residualLaw_real_Iic hh, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]

/-- Normalize by the survival probability to obtain the original law again. -/
theorem normalized_residualLaw {h : ℝ} (hh : 0 ≤ h) :
    (ENNReal.ofReal (Real.exp (-h)))⁻¹ • residualLaw h = unitExponential := by
  rw [residualLaw_eq_smul hh, smul_smul,
    ENNReal.inv_mul_cancel (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top, one_smul]

theorem unitExponential_Ioi {h : ℝ} (hh : 0 ≤ h) :
    unitExponential (Ioi h) = ENNReal.ofReal (Real.exp (-h)) := by
  rw [← unitExponential_real_Ioi hh, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem normalized_residualLaw_by_survival {h : ℝ} (hh : 0 ≤ h) :
    (unitExponential (Ioi h))⁻¹ • residualLaw h = unitExponential := by
  rw [unitExponential_Ioi hh]
  exact normalized_residualLaw hh

theorem integral_residual {h : ℝ} (hh : 0 ≤ h) (f : ℝ → ℝ)
    (hf : Measurable f) :
    (∫ z in Ioi h, f (z - h) ∂unitExponential) =
      Real.exp (-h) * ∫ z, f z ∂unitExponential := by
  have hm : Measurable (fun z : ℝ => z - h) := measurable_id.sub_const h
  have hmap := integral_map (μ := unitExponential.restrict (Ioi h))
    hm.aemeasurable hf.aestronglyMeasurable
  change (∫ z, f z ∂residualLaw h) = _ at hmap
  rw [← hmap, residualLaw_eq_smul hh, integral_smul_measure,
    ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _)), smul_eq_mul]

theorem unitExponential_ae_pos : ∀ᵐ z ∂unitExponential, 0 < z := by
  rw [ae_iff]
  have hset : {z : ℝ | ¬0 < z} = Iic 0 := by ext z; simp
  rw [hset]
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  simp [unitExponential_real_Iic]

end StochasticMatching
