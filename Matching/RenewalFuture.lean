import Matching.RenewalResidual

/-! Renewal conditioning preserves every independent future variable. This
joint law can be used for many later observation times, rather than only one
remaining waiting-time marginal.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching

theorem scaled_product_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] (c : ℝ≥0∞) :
    (c • μ).prod ν = c • (μ.prod ν) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_prod _ hf.aemeasurable, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_prod _ hf.aemeasurable]

theorem renewal_cut_with_future_law {H : Type*} [MeasurableSpace H]
    (ν : Measure H) [IsFiniteMeasure ν] (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Measure.map (fun p : (ℝ × ℝ) × H => (p.1.1 + p.1.2 - t, p.2))
      ((((exponentialSumLaw n).prod unitExponential).prod ν).restrict
        (renewalCut t ×ˢ Set.univ)) =
      ENNReal.ofReal (poissonWeight t n) • (unitExponential.prod ν) := by
  rw [← Measure.restrict_prod_eq_prod_univ]
  change Measure.map (Prod.map (fun p : ℝ × ℝ => p.1 + p.2 - t) id) _ = _
  rw [← Measure.map_prod_map _ _ ((measurable_fst.add measurable_snd).sub_const t) measurable_id,
    Measure.map_id, renewal_cut_residual_law n ht, scaled_product_left]

theorem renewal_cut_future_sum_law (n m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Measure.map (fun p : (ℝ × ℝ) × ℝ => p.1.1 + p.1.2 - t + p.2)
      ((((exponentialSumLaw n).prod unitExponential).prod (exponentialSumLaw m)).restrict
        (renewalCut t ×ˢ Set.univ)) =
      ENNReal.ofReal (poissonWeight t n) • exponentialSumLaw (m + 1) := by
  have h := congrArg (Measure.map (fun p : ℝ × ℝ => p.1 + p.2))
    (renewal_cut_with_future_law (exponentialSumLaw m) n ht)
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.1 + p.1.2 - t, p.2)) := by fun_prop
  rw [Measure.map_map (measurable_fst.add measurable_snd) hm,
    Measure.map_smul] at h
  exact h

theorem renewal_cut_two_time_probability (n m : ℕ) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    (((exponentialSumLaw n).prod unitExponential).prod (exponentialSumLaw m)).real
      {p : (ℝ × ℝ) × ℝ | p.1.1 ≤ t ∧ t < p.1.1 + p.1.2 ∧ u < p.1.1 + p.1.2 + p.2} =
      poissonWeight t n * poissonLowerTail (u - t) (m + 1) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ => p.1.1 + p.1.2 - t + p.2) := by fun_prop
  have h := congrArg (fun μ : Measure ℝ => μ.real (Ioi (u - t))) (renewal_cut_future_sum_law n m ht)
  dsimp only at h
  rw [map_measureReal_apply hm measurableSet_Ioi, measureReal_restrict_apply (hm measurableSet_Ioi),
    measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (poissonWeight_nonneg ht n),
    exponentialSumLaw_tail_eq_poissonLowerTail (m + 1) (sub_nonneg.mpr htu)] at h
  convert h using 1
  congr 1
  ext p
  simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi, mem_prod, mem_univ, and_true, renewalCut]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, h1, h2⟩
  · rintro ⟨h3, h1, h2⟩
    exact ⟨h1, h2, by linarith⟩

end StochasticMatching
