import Matching.PoissonWeights
import Matching.ExponentialScaling
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! The scalar integral identity underlying the exponential waiting-time /
Poisson counting duality. No probability-law identification is assumed here.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching

theorem poissonWeight_shift_integral {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    (∫ x in Ioc 0 a, Real.exp (-x) * poissonWeight (a - x) k) =
      poissonWeight a (k + 1) := by
  have he : ∀ x : ℝ, Real.exp (-x) * poissonWeight (a - x) k =
      Real.exp (-a) * ((a - x) ^ k / (k.factorial : ℝ)) := by
    intro x
    have h : Real.exp (-x) * Real.exp (-(a - x)) = Real.exp (-a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold poissonWeight
    calc
      _ = (Real.exp (-x) * Real.exp (-(a - x))) * ((a - x) ^ k / (k.factorial : ℝ)) := by ring
      _ = _ := by rw [h]
  have hp : (∫ x in (0 : ℝ)..a, (a - x) ^ k) = a ^ (k + 1) / (k + 1) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := a) (fun x : ℝ => x ^ k) a
    simpa only [sub_self, sub_zero, integral_pow, zero_pow (Nat.succ_ne_zero k), sub_zero] using h
  simp_rw [he]
  rw [← intervalIntegral.integral_of_le ha, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div, hp]
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem poissonLowerTail_shift_integral {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.exp (-a) + (∫ x in Ioc 0 a, Real.exp (-x) * poissonLowerTail (a - x) n) =
      poissonLowerTail a (n + 1) := by
  have hi : ∀ k ∈ Finset.range n, IntegrableOn
      (fun x : ℝ => Real.exp (-x) * poissonWeight (a - x) k) (Ioc 0 a) := by
    intro k _
    exact ((Real.continuous_exp.comp continuous_id.neg).mul
      ((continuous_poissonWeight k).comp (continuous_const.sub continuous_id))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  simp only [poissonLowerTail, Finset.mul_sum]
  rw [integral_finset_sum _ hi]
  simp_rw [poissonWeight_shift_integral ha]
  rw [Finset.sum_range_succ', poissonWeight]
  simp [add_comm]

theorem unitExponential_integral_Ioc {a : ℝ} (g : ℝ → ℝ) :
    (∫ x in Ioc 0 a, g x ∂unitExponential) =
      ∫ x in Ioc 0 a, Real.exp (-x) * g x := by
  change (∫ x in Ioc 0 a, g x ∂volume.withDensity (exponentialPDF 1)) = _
  rw [restrict_withDensity measurableSet_Ioc]
  change (∫ x, g x ∂(volume.restrict (Ioc 0 a)).withDensity
    (fun x => ENNReal.ofReal (exponentialPDFReal 1 x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_exponentialPDFReal 1).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change (exponentialPDF 1 x).toReal * g x = _
  rw [exponentialPDF_of_nonneg hx.1.le]
  simp only [one_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

theorem poissonLowerTail_exponential_recursion {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    Real.exp (-a) + (∫ x in Ioc 0 a, poissonLowerTail (a - x) n ∂unitExponential) =
      poissonLowerTail a (n + 1) := by
  rw [unitExponential_integral_Ioc]
  exact poissonLowerTail_shift_integral ha n

end StochasticMatching
