import Matching.SurvivalCurve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The analytic one-segment Dynkin identity, including survival at the deadline.
This uses a survival derivative and an aggregate marked-jump reward density.
Its probabilistic interpretation requires proving that these quantities are
the actual first-completion laws of the scheduling policy.
-/

open MeasureTheory Set
open scoped BigOperators

namespace StochasticMatching

theorem first_step_identity (T : ℝ) (S F D H J : ℝ → ℝ)
    (hS : Continuous S) (hF : Continuous F) (hD : Continuous D)
    (hH : Continuous H) (hJ : Continuous J) (hzero : S 0 = 1)
    (hSd : ∀ t ∈ uIcc 0 T, HasDerivAt S (-H t * S t) t)
    (hFd : ∀ t ∈ uIcc 0 T, HasDerivAt F (D t) t) :
    S T * F T + (∫ t in (0 : ℝ)..T, S t * J t) - F 0 =
      ∫ t in (0 : ℝ)..T, S t * (D t + J t - H t * F t) := by
  have hd : ∀ t ∈ uIcc 0 T,
      HasDerivAt (fun u => S u * F u) (-H t * S t * F t + S t * D t) t := by
    intro t ht
    exact (hSd t ht).mul (hFd t ht)
  have hc : Continuous (fun t => -H t * S t * F t + S t * D t) := by fun_prop
  have hjc : Continuous (fun t => S t * J t) := hS.mul hJ
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 T)
  rw [hzero, one_mul] at hFTC
  have halgebra : (fun t => S t * (D t + J t - H t * F t)) =
      fun t => (-H t * S t * F t + S t * D t) + S t * J t := by
    funext t
    ring
  rw [halgebra, intervalIntegral.integral_add (hc.intervalIntegrable 0 T)
    (hjc.intervalIntegrable 0 T), hFTC]
  ring

theorem first_step_identity_finite {ι : Type*} [Fintype ι]
    (T : ℝ) (S F D : ℝ → ℝ) (r J : ι → ℝ → ℝ)
    (hS : Continuous S) (hF : Continuous F) (hD : Continuous D)
    (hr : ∀ i, Continuous (r i)) (hJ : ∀ i, Continuous (J i)) (hzero : S 0 = 1)
    (hSd : ∀ t ∈ uIcc 0 T, HasDerivAt S (-(∑ i, r i t) * S t) t)
    (hFd : ∀ t ∈ uIcc 0 T, HasDerivAt F (D t) t) :
    S T * F T + (∫ t in (0 : ℝ)..T, S t * ∑ i, r i t * J i t) - F 0 =
      ∫ t in (0 : ℝ)..T, S t * (D t + ∑ i, r i t * (J i t - F t)) := by
  have h := first_step_identity T S F D (fun t => ∑ i, r i t)
    (fun t => ∑ i, r i t * J i t) hS hF hD
    (by fun_prop) (by fun_prop) hzero hSd hFd
  have heq : (fun t => S t * (D t + ∑ i, r i t * (J i t - F t))) =
      fun t => S t * (D t + (∑ i, r i t * J i t) - (∑ i, r i t) * F t) := by
    funext t
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [heq]
  exact h

/-- The event-density and terminal-survival masses sum to one. -/
theorem first_step_mass_conservation (T : ℝ) (S H : ℝ → ℝ)
    (hS : Continuous S) (hH : Continuous H) (hzero : S 0 = 1)
    (hSd : ∀ t ∈ uIcc 0 T, HasDerivAt S (-H t * S t) t) :
    S T + (∫ t in (0 : ℝ)..T, S t * H t) = 1 := by
  have h := first_step_identity T S (fun _ => 1) (fun _ => 0) H H
    hS continuous_const continuous_const hH hH hzero hSd
    (fun t _ => hasDerivAt_const t 1)
  simp only [mul_one, zero_add, sub_self, mul_zero, intervalIntegral.integral_zero] at h
  linarith

end StochasticMatching
