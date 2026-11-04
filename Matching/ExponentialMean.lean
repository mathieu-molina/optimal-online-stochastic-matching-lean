import Matching.ExponentialWork
import Matching.MarkedResidual

/-! The unit-exponential mean and integrability, including every coordinate
of the fresh residual product. These are derived from the proved tail law.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StochasticMatching

theorem lintegral_unitExponential_id :
    (∫⁻ z : ℝ, ENNReal.ofReal z ∂unitExponential) = 1 := by
  have hn : 0 ≤ᵐ[unitExponential] (fun z : ℝ => z) :=
    unitExponential_ae_pos.mono (fun _ h => h.le)
  rw [lintegral_eq_lintegral_meas_lt unitExponential hn measurable_id.aemeasurable]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      apply Filter.Eventually.of_forall
      intro t ht
      exact unitExponential_Ioi ht.le
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), Real.exp (-t)) :=
      (ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
        (Filter.Eventually.of_forall (fun t => (Real.exp_pos (-t)).le))).symm
    _ = 1 := by rw [integral_exp_neg_Ioi_zero]; norm_num

theorem integrable_unitExponential_id : Integrable (fun z : ℝ => z) unitExponential := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (unitExponential_ae_pos.mono (fun _ h => h.le)),
    lintegral_unitExponential_id]
  exact ENNReal.one_lt_top

theorem integral_unitExponential_id : (∫ z : ℝ, z ∂unitExponential) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (unitExponential_ae_pos.mono (fun _ h => h.le)) measurable_id.aestronglyMeasurable,
    lintegral_unitExponential_id]
  norm_num

variable {ι : Type*} [Fintype ι]

theorem independentExponentials_coordinate_law (i : ι) :
    Measure.map (fun z : ι → ℝ => z i) independentExponentials = unitExponential := by
  classical
  have h := congrArg (Measure.map (Prod.fst : ℝ × ({j : ι // j ≠ i} → ℝ) → ℝ))
    (splitDemand_preserves_measure i).map_eq
  rw [Measure.map_map measurable_fst (splitDemand i).measurable] at h
  simpa only [Function.comp_def, splitDemand_apply, Measure.map_fst_prod, measure_univ, one_smul] using h

theorem integrable_exponential_coordinate (i : ι) :
    Integrable (fun z : ι → ℝ => z i) independentExponentials := by
  have h : Integrable (fun x : ℝ => x)
      (Measure.map (fun z : ι → ℝ => z i) independentExponentials) := by
    rw [independentExponentials_coordinate_law]
    exact integrable_unitExponential_id
  exact h.comp_measurable (measurable_pi_apply i)

theorem integral_exponential_coordinate (i : ι) :
    (∫ z : ι → ℝ, z i ∂independentExponentials) = 1 := by
  have h := integral_map_of_stronglyMeasurable (μ := independentExponentials)
    (measurable_pi_apply i) (measurable_id.stronglyMeasurable : StronglyMeasurable (fun x : ℝ => x))
  rw [independentExponentials_coordinate_law] at h
  simpa only [id_eq, integral_unitExponential_id] using h.symm

theorem integral_shifted_exponential_coordinate (x : ι → ℝ) (i : ι) :
    (∫ z : ι → ℝ, (x + z) i ∂independentExponentials) = x i + 1 := by
  change (∫ z : ι → ℝ, x i + z i ∂independentExponentials) = _
  rw [integral_add (integrable_const _) (integrable_exponential_coordinate i),
    integral_exponential_coordinate]
  simp

end StochasticMatching
