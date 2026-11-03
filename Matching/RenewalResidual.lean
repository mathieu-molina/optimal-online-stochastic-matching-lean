import Matching.RenewalCutProbability

/-! A deterministic-time renewal cut leaves a fresh unit exponential.
The unnormalized residual law has exactly the Poisson count mass as weight.
This retains the information needed to advance from one chain time to the next.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching

theorem lintegral_unitExponential_residual {h : ℝ} (hh : 0 ≤ h)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in Ioi h, f (x - h) ∂unitExponential) =
      ENNReal.ofReal (Real.exp (-h)) * ∫⁻ x, f x ∂unitExponential := by
  have hm := lintegral_map (μ := unitExponential.restrict (Ioi h)) hf (measurable_id.sub_const h)
  change (∫⁻ x, f x ∂residualLaw h) = _ at hm
  simp only [id_eq] at hm
  rw [← hm, residualLaw_eq_smul hh, lintegral_smul_measure, smul_eq_mul]

theorem renewal_cut_lintegral_factor (μ : Measure ℝ) (t : ℝ)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p in renewalCut t, f (p.1 + p.2 - t) ∂μ.prod unitExponential) =
      (∫⁻ s in Iic t, ENNReal.ofReal (Real.exp (-(t - s))) ∂μ) *
        ∫⁻ x, f x ∂unitExponential := by
  have hF : Measurable (fun p : ℝ × ℝ => f (p.1 + p.2 - t)) :=
    hf.comp ((measurable_fst.add measurable_snd).sub_const t)
  rw [← lintegral_indicator (measurableSet_renewalCut t),
    lintegral_prod _ (hF.indicator (measurableSet_renewalCut t)).aemeasurable]
  calc
    _ = ∫⁻ s, (Iic t).indicator (fun s => ENNReal.ofReal (Real.exp (-(t - s))) *
        ∫⁻ x, f x ∂unitExponential) s ∂μ := by
      apply lintegral_congr
      intro s
      by_cases hs : s ≤ t
      · rw [Set.indicator_of_mem (show s ∈ Iic t from hs)]
        have he : (fun x : ℝ => (renewalCut t).indicator (fun p => f (p.1 + p.2 - t)) (s, x)) =
            (Ioi (t - s)).indicator (fun x => f (x - (t - s))) := by
          funext x
          have hc : (s, x) ∈ renewalCut t ↔ x ∈ Ioi (t - s) := by
            change (s ≤ t ∧ t < s + x) ↔ t - s < x
            constructor
            · intro h; linarith [h.2]
            · intro h; exact ⟨hs, by linarith⟩
          by_cases hx : x ∈ Ioi (t - s)
          · rw [Set.indicator_of_mem (hc.mpr hx), Set.indicator_of_mem hx]
            congr 1
            ring
          · rw [Set.indicator_of_not_mem (fun h => hx (hc.mp h)), Set.indicator_of_not_mem hx]
        rw [he, lintegral_indicator measurableSet_Ioi]
        exact lintegral_unitExponential_residual (sub_nonneg.mpr hs) f hf
      · rw [Set.indicator_of_not_mem (show s ∉ Iic t from hs)]
        have he : (fun x : ℝ => (renewalCut t).indicator (fun p => f (p.1 + p.2 - t)) (s, x)) = 0 := by
          funext x
          exact Set.indicator_of_not_mem (fun h => hs h.1) _
        rw [he]
        exact lintegral_zero
    _ = _ := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_mul_const]
      exact ((measurable_const.sub measurable_id).neg.exp).ennreal_ofReal

theorem renewal_cut_survival_weight (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ s in Iic t, ENNReal.ofReal (Real.exp (-(t - s))) ∂exponentialSumLaw n) =
      ENNReal.ofReal (poissonWeight t n) := by
  have h := renewal_cut_lintegral_factor (exponentialSumLaw n) t (fun _ => 1) measurable_const
  simp only [lintegral_one, measure_univ, mul_one, Measure.restrict_apply_univ] at h
  rw [← h, ← renewal_cut_probability n ht, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem renewal_cut_residual_law (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Measure.map (fun p : ℝ × ℝ => p.1 + p.2 - t)
      (((exponentialSumLaw n).prod unitExponential).restrict (renewalCut t)) =
      ENNReal.ofReal (poissonWeight t n) • unitExponential := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf ((measurable_fst.add measurable_snd).sub_const t),
    renewal_cut_lintegral_factor _ t f hf, renewal_cut_survival_weight n ht,
    lintegral_smul_measure, smul_eq_mul]

end StochasticMatching
