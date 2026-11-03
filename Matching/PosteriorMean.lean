import Matching.SurvivalCurve
import Mathlib.MeasureTheory.Integral.Prod

/-! Exponential smoothing of bounded measurable allocations. The function
being averaged need not be continuous. Memorylessness controls the change in
its mean when the cumulative-service vector increases.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

variable {ι : Type*} [Fintype ι]

theorem integral_vector_residual {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f) :
    (∫ z in survivalBox h, f (z - h) ∂independentExponentials) =
      independentExponentials.real (survivalBox h) * ∫ z, f z ∂independentExponentials := by
  have hmap := integral_map_of_stronglyMeasurable
    (μ := independentExponentials.restrict (survivalBox h))
    (measurable_subtract_threshold h) hf.stronglyMeasurable
  change (∫ y, f y ∂vectorResidualLaw h) = _ at hmap
  rw [vectorResidualLaw_eq_smul hh, ← survivalBox_measure hh,
    integral_smul_measure, smul_eq_mul] at hmap
  exact hmap.symm

noncomputable def shiftedMean (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ z, f (x + z) ∂independentExponentials

theorem measurable_shiftedMean {f : (ι → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (shiftedMean f) := by
  have hm : Measurable (fun p : (ι → ℝ) × (ι → ℝ) => f (p.1 + p.2)) :=
    hf.comp (measurable_fst.add measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_shiftedMean_integrand {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z, ‖f z‖ ≤ M) (x : ι → ℝ) :
    Integrable (fun z => f (x + z)) independentExponentials := by
  exact (integrable_const M).mono'
    (hf.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => hb (x + z)))

theorem shiftedMean_nonneg {f : (ι → ℝ) → ℝ} (hf : ∀ z, 0 ≤ f z) (x : ι → ℝ) :
    0 ≤ shiftedMean f x := integral_nonneg (fun z => hf (x + z))

theorem shiftedMean_le {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) {M : ℝ} (hM : ∀ z, f z ≤ M) (x : ι → ℝ) :
    shiftedMean f x ≤ M := by
  have hi := integrable_shiftedMean_integrand hf
    (fun z => by rw [Real.norm_of_nonneg (h0 z)]; exact hM z) x
  calc
    shiftedMean f x ≤ ∫ _ : ι → ℝ, M ∂independentExponentials :=
      integral_mono hi (integrable_const M) (fun z => hM (x + z))
    _ = M := by simp

theorem shiftedMean_survival_integral {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (x : ι → ℝ) {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    (∫ z in survivalBox h, f (x + z) ∂independentExponentials) =
      Real.exp (-(∑ i, h i)) * shiftedMean f (x + h) := by
  have hmap := integral_vector_residual hh (fun z => f (x + h + z))
    (hf.comp (measurable_const.add measurable_id))
  have heq : (fun z => f (x + h + (z - h))) = fun z => f (x + z) := by
    funext z
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [heq, survivalBox_real hh] at hmap
  exact hmap

/-- The loss of survival mass bounds the change in a bounded nonnegative
posterior mean, even when the allocation itself is only measurable. -/
theorem shiftedMean_increment_bound {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) {M : ℝ} (hM : ∀ z, f z ≤ M)
    (x : ι → ℝ) {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    |shiftedMean f (x + h) - shiftedMean f x| ≤ M * (1 - Real.exp (-(∑ i, h i))) := by
  have hi := integrable_shiftedMean_integrand hf
    (fun z => by rw [Real.norm_of_nonneg (h0 z)]; exact hM z) x
  let c := ∫ z in (survivalBox h)ᶜ, f (x + z) ∂independentExponentials
  have hc0 : 0 ≤ c := integral_nonneg (fun z => h0 (x + z))
  have hcM : c ≤ (1 - Real.exp (-(∑ i, h i))) * M := by
    calc
      c ≤ ∫ _ : ι → ℝ in (survivalBox h)ᶜ, M ∂independentExponentials :=
        integral_mono hi.restrict (integrable_const M) (fun z => hM (x + z))
      _ = (1 - Real.exp (-(∑ i, h i))) * M := by
        rw [integral_const, measureReal_restrict_apply_univ,
          measureReal_compl (measurableSet_survivalBox h), measureReal_univ_eq_one,
          survivalBox_real hh, smul_eq_mul]
  have heq : Real.exp (-(∑ i, h i)) * shiftedMean f (x + h) + c = shiftedMean f x := by
    rw [← shiftedMean_survival_integral hf x hh]
    exact integral_add_compl (measurableSet_survivalBox h) hi
  have hmass : 0 ≤ 1 - Real.exp (-(∑ i, h i)) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => hh i)))
  have hlower := mul_nonneg hmass (shiftedMean_nonneg h0 (x + h))
  have hupper := mul_le_mul_of_nonneg_left (shiftedMean_le hf h0 hM (x + h)) hmass
  apply abs_le.mpr
  constructor <;> nlinarith

theorem shiftedMean_increment_le {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (h0 : ∀ z, 0 ≤ f z) {M : ℝ} (hM : ∀ z, f z ≤ M)
    (x : ι → ℝ) {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i) :
    |shiftedMean f (x + h) - shiftedMean f x| ≤ M * ∑ i, h i := by
  have hM0 : 0 ≤ M := (h0 0).trans (hM 0)
  apply (shiftedMean_increment_bound hf h0 hM x hh).trans
  apply mul_le_mul_of_nonneg_left _ hM0
  have he := Real.add_one_le_exp (-(∑ i, h i))
  linarith

end StochasticMatching
