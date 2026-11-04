import Matching.ExponentialSumLaw
import Matching.PoissonExponentialConvolution

/-! The scalar waiting-time/counting identity for every finite number of
independent unit exponentials, proved from the actual recursive sum law.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching

theorem measurable_shifted_measure_tail (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Measurable (fun x : ℝ => μ.real (Ioi (a - x))) := by
  have h := (measurable_measure_prodMk_left
    (ν := μ)
    (measurableSet_lt measurable_const (measurable_fst.add measurable_snd) :
      MeasurableSet {p : ℝ × ℝ | a < p.1 + p.2})).ennreal_toReal
  convert h using 1
  funext x
  congr 1
  ext y
  change a - x < y ↔ a < x + y
  constructor <;> intro h <;> linarith

theorem integrable_shifted_probability_tail (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν] (a : ℝ) :
    Integrable (fun x => μ.real (Ioi (a - x))) ν := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_shifted_measure_tail μ a).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
  exact (measureReal_mono (subset_univ _)).trans_eq (measureReal_univ_eq_one)

theorem exponentialSumLaw_tail_negative (n : ℕ) {a : ℝ} (ha : a < 0) :
    (exponentialSumLaw n).real (Ioi a) = 1 := by
  have he : Ioi a =ᵐ[exponentialSumLaw n] Set.univ := by
    filter_upwards [exponentialSumLaw_ae_nonneg n] with x hx
    apply propext
    change (a < x ↔ True)
    simp only [mem_Ioi, mem_univ, iff_true]
    exact ha.trans_le hx
  rw [measureReal_congr he, measureReal_univ_eq_one]

theorem exponentialSumLaw_tail_nonnegative_recursion (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (exponentialSumLaw (n + 1)).real (Ioi a) =
      Real.exp (-a) + ∫ x in Ioc 0 a, (exponentialSumLaw n).real (Ioi (a - x)) ∂unitExponential := by
  rw [exponentialSumLaw_tail_recursion]
  have hi := integrable_shifted_probability_tail (exponentialSumLaw n) unitExponential a
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic]
  have hs : Iic a =ᵐ[unitExponential] Ioc 0 a := by
    filter_upwards [unitExponential_ae_pos] with x hx
    apply propext
    change (x ≤ a ↔ 0 < x ∧ x ≤ a)
    simp only [mem_Iic, mem_Ioc, hx, true_and]
  rw [Measure.restrict_congr_set hs]
  have ht : (∫ x in Ioi a, (exponentialSumLaw n).real (Ioi (a - x)) ∂unitExponential) = Real.exp (-a) := by
    calc
      _ = ∫ _x in Ioi a, (1 : ℝ) ∂unitExponential := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact exponentialSumLaw_tail_negative n (sub_neg.mpr hx)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_one, unitExponential_real_Ioi ha]
  rw [ht, add_comm]

theorem exponentialSumLaw_tail_eq_poissonLowerTail (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (exponentialSumLaw n).real (Ioi a) = poissonLowerTail a n := by
  induction n generalizing a with
  | zero => simp [exponentialSumLaw, poissonLowerTail, measureReal_def, not_lt.mpr ha]
  | succ n ih =>
    rw [exponentialSumLaw_tail_nonnegative_recursion n ha,
      ← poissonLowerTail_exponential_recursion ha n]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact ih (sub_nonneg.mpr hx.2)

theorem exponential_subset_sum_poisson_tail {ι : Type*} [Fintype ι]
    (S : Finset ι) (a : ℝ≥0) :
    (independentExponentials (ι := ι)).real {z | (a : ℝ) < ∑ i ∈ S, z i} =
      (poissonMeasure a).real {k : ℕ | k < S.card} := by
  have h := congrArg (fun μ : Measure ℝ => μ.real (Ioi (a : ℝ)))
    (independentExponentials_subset_sum_law S)
  dsimp only at h
  rw [map_measureReal_apply (Finset.measurable_sum S (fun i _ => measurable_pi_apply i)) measurableSet_Ioi,
    exponentialSumLaw_tail_eq_poissonLowerTail S.card a.coe_nonneg, poissonLowerTail_eq_probability] at h
  exact h

end StochasticMatching
