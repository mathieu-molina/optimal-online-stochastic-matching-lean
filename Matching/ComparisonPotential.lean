import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The explicit analytic comparison function in Section 4.2 of arXiv:2610.19866v1.
The calculus and sensitivity bounds are proved here. Identifying this function
with an exponential-service expectation requires a separate probability lemma.
-/

namespace StochasticMatching
namespace Comparison

noncomputable def continuation (t h : ℝ) : ℝ :=
  1 - Real.exp (-((h + 1) * (Real.exp (1 - t) - 1)))

noncomputable def sensitivity (t h : ℝ) : ℝ :=
  Real.exp (1 - t) * Real.exp (-((h + 1) * (Real.exp (1 - t) - 1)))

noncomputable def timeDerivative (t h : ℝ) : ℝ := -(h + 1) * sensitivity t h

noncomputable def workDerivative (t h : ℝ) : ℝ :=
  (Real.exp (1 - t) - 1) * Real.exp (-((h + 1) * (Real.exp (1 - t) - 1)))

noncomputable def ratio : ℝ := 1 - Real.exp (1 - Real.exp 1)

theorem continuation_deadline (h : ℝ) : continuation 1 h = 0 := by
  simp [continuation]

theorem continuation_initial : continuation 0 0 = ratio := by
  simp [continuation, ratio, neg_sub]

theorem ratio_eq_exp_quotient : ratio = 1 - Real.exp 1 / Real.exp (Real.exp 1) := by
  rw [ratio, Real.exp_sub]

theorem ratio_pos : 0 < ratio := by
  have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have h : Real.exp (1 - Real.exp 1) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  dsimp [ratio]
  linarith

theorem ratio_lt_one : ratio < 1 := by
  have h := Real.exp_pos (1 - Real.exp 1)
  dsimp [ratio]
  linarith

theorem hasDerivAt_time (t h : ℝ) :
    HasDerivAt (fun u => continuation u h) (timeDerivative t h) t := by
  have hinner := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).exp.sub_const 1)
  have he := (hinner.const_mul (h + 1)).neg.exp
  convert (hasDerivAt_const t (1 : ℝ)).sub he using 1
  dsimp [continuation, timeDerivative, sensitivity]
  ring

theorem hasDerivAt_work (t h : ℝ) :
    HasDerivAt (continuation t) (workDerivative t h) h := by
  have he := (((hasDerivAt_id h).add_const 1).mul_const
    (Real.exp (1 - t) - 1)).neg.exp
  convert (hasDerivAt_const h (1 : ℝ)).sub he using 1
  dsimp [continuation, workDerivative]
  ring

theorem deriv_time (t h : ℝ) :
    deriv (fun u => continuation u h) t = timeDerivative t h :=
  (hasDerivAt_time t h).deriv

theorem deriv_work (t h : ℝ) : deriv (continuation t) h = workDerivative t h :=
  (hasDerivAt_work t h).deriv

theorem marginal_eq_sensitivity (t h : ℝ) :
    1 + workDerivative t h - continuation t h = sensitivity t h := by
  dsimp [workDerivative, continuation, sensitivity]
  ring

theorem comparison_pde (t h : ℝ) :
    timeDerivative t h + (h + 1) *
      (1 + workDerivative t h - continuation t h) = 0 := by
  rw [marginal_eq_sensitivity]
  dsimp [timeDerivative]
  ring

theorem comparison_pde_deriv (t h : ℝ) :
    deriv (fun u => continuation u h) t + (h + 1) *
      (1 + deriv (continuation t) h - continuation t h) = 0 := by
  rw [deriv_time, deriv_work]
  exact comparison_pde t h

theorem sensitivity_pos (t h : ℝ) : 0 < sensitivity t h :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

theorem sensitivity_le_at_zero {t h : ℝ} (ht : t ≤ 1) (hh : 0 ≤ h) :
    sensitivity t h ≤ sensitivity t 0 := by
  have he : 0 ≤ Real.exp (1 - t) - 1 := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ 1 - t by linarith)
    linarith
  have hexponent : -((h + 1) * (Real.exp (1 - t) - 1)) ≤
      -((0 + 1) * (Real.exp (1 - t) - 1)) := by
    nlinarith [mul_nonneg hh he]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
    (le_of_lt (Real.exp_pos _))

theorem sensitivity_bounds {t h : ℝ} (ht : t ≤ 1) (hh : 0 ≤ h) :
    0 ≤ 1 + deriv (continuation t) h - continuation t h ∧
      1 + deriv (continuation t) h - continuation t h ≤
        -deriv (fun u => continuation u 0) t := by
  rw [deriv_work, marginal_eq_sensitivity, deriv_time]
  constructor
  · exact le_of_lt (sensitivity_pos t h)
  · simpa [timeDerivative] using sensitivity_le_at_zero ht hh

theorem continuation_nonneg {t h : ℝ} (ht : t ≤ 1) (hh : 0 ≤ h) :
    0 ≤ continuation t h := by
  have he : 0 ≤ Real.exp (1 - t) - 1 := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ 1 - t by linarith)
    linarith
  have hexponent : -((h + 1) * (Real.exp (1 - t) - 1)) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg (by linarith) he)
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr hexponent)

theorem continuation_lt_one (t h : ℝ) : continuation t h < 1 := by
  have he := Real.exp_pos (-((h + 1) * (Real.exp (1 - t) - 1)))
  dsimp [continuation]
  linarith

theorem generator_factor (t h s : ℝ) :
    timeDerivative t h + s * (1 + workDerivative t h - continuation t h) =
      -(h + 1 - s) * sensitivity t h := by
  rw [marginal_eq_sensitivity]
  dsimp [timeDerivative]
  ring

theorem generator_lower_bound {t h s : ℝ} (ht : t ≤ 1) (hh : 0 ≤ h)
    (hgap : 0 ≤ h + 1 - s) :
    (h + 1 - s) * timeDerivative t 0 ≤
      timeDerivative t h + s * (1 + workDerivative t h - continuation t h) := by
  rw [generator_factor]
  have h := mul_le_mul_of_nonneg_left (sensitivity_le_at_zero ht hh) hgap
  simp only [timeDerivative, zero_add, neg_one_mul] at *
  nlinarith

end Comparison
end StochasticMatching
