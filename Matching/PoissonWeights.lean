import Matching.SupermodularTail
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum

/-! The Poisson mass functions and their integration in the intensity
parameter. Each fixed-count mass integrates to one, which is the key analytic
identity for converting Poisson-mixture tails into expected deficiencies.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching

noncomputable def poissonWeight (a : ℝ) (n : ℕ) : ℝ := Real.exp (-a) * a ^ n / n.factorial

noncomputable def poissonLowerTail (a : ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, poissonWeight a k

theorem poissonWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : 0 ≤ poissonWeight a n := by
  unfold poissonWeight
  positivity

theorem continuous_poissonWeight (n : ℕ) : Continuous (fun a => poissonWeight a n) :=
  (continuous_id.neg.rexp.mul (continuous_id.pow n)).div_const _

theorem integrable_poissonWeight_intensity (n : ℕ) :
    IntegrableOn (fun a : ℝ => poissonWeight a n) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (show 0 < (n : ℝ) + 1 by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast] at h
  exact h.div_const _

theorem integral_poissonWeight_intensity (n : ℕ) :
    (∫ a : ℝ in Ioi 0, poissonWeight a n) = 1 := by
  have h := Real.Gamma_eq_integral (show 0 < (n : ℝ) + 1 by positivity)
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  unfold poissonWeight
  rw [integral_div, ← h]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

theorem continuous_poissonLowerTail (n : ℕ) : Continuous (fun a => poissonLowerTail a n) :=
  continuous_finset_sum _ (fun k _ => continuous_poissonWeight k)

theorem integrable_poissonLowerTail_intensity (n : ℕ) :
    IntegrableOn (fun a : ℝ => poissonLowerTail a n) (Ioi 0) :=
  integrable_finset_sum _ (fun k _ => integrable_poissonWeight_intensity k)

theorem integral_poissonLowerTail_intensity (n : ℕ) :
    (∫ a : ℝ in Ioi 0, poissonLowerTail a n) = n := by
  unfold poissonLowerTail
  rw [integral_finset_sum _ (fun k _ => integrable_poissonWeight_intensity k)]
  simp only [integral_poissonWeight_intensity, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem poissonWeight_convolution (a b : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), poissonWeight a k * poissonWeight b (n - k)) =
      poissonWeight (a + b) n := by
  have he : Real.exp (-(a + b)) = Real.exp (-a) * Real.exp (-b) := by rw [neg_add, Real.exp_add]
  have hr : poissonWeight (a + b) n =
      ∑ k ∈ Finset.range (n + 1),
        Real.exp (-(a + b)) / (n.factorial : ℝ) * (a ^ k * b ^ (n - k) * (n.choose k : ℝ)) := by
    unfold poissonWeight
    rw [add_pow, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hr]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [Nat.cast_choose ℝ hkn, he]
  unfold poissonWeight
  have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hkf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hdf : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  field_simp
  <;> ring

theorem poissonMeasure_singleton (a : ℝ≥0) (n : ℕ) :
    (ProbabilityTheory.poissonMeasure a) {n} = ENNReal.ofReal (poissonWeight a n) := by
  exact (ProbabilityTheory.poissonPMF a).toMeasure_apply_singleton n (measurableSet_singleton n)

theorem poissonMeasure_real_singleton (a : ℝ≥0) (n : ℕ) :
    (ProbabilityTheory.poissonMeasure a).real {n} = poissonWeight a n := by
  rw [measureReal_def, poissonMeasure_singleton]
  exact ENNReal.toReal_ofReal (poissonWeight_nonneg a.coe_nonneg n)

theorem poissonLowerTail_eq_probability (a : ℝ≥0) (n : ℕ) :
    poissonLowerTail a n = (ProbabilityTheory.poissonMeasure a).real {k : ℕ | k < n} := by
  have he : {k : ℕ | k < n} = (Finset.range n : Set ℕ) := by ext k; simp
  rw [he, measureReal_def, ← sum_measure_singleton]
  simp only [poissonMeasure_singleton]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => poissonWeight_nonneg a.coe_nonneg k),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun k _ => poissonWeight_nonneg a.coe_nonneg k))]
  rfl

end StochasticMatching
