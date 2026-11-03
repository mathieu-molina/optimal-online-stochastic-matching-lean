import Matching.ComparisonFlow
import Matching.PosteriorStage
import Matching.LossBudget

/-! The first-segment comparison inequality for the constructed posterior ODE.
The residual deficit is an actual exponential average of unallocated demand.
-/

open MeasureTheory Set
open scoped BigOperators

namespace StochasticMatching
namespace ServiceCurveFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

theorem comparison_drift_lower_bound (elapsed : ℝ) (initial : ι → ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 p.deadline) (hT : elapsed + p.deadline ≤ 1)
    (hx : ∀ i, 0 ≤ initial i)
    (hgap : ∀ i, 0 ≤ initial i + p.service i t + 1 - p.rate i t) :
    -(Comparison.lossKernel (elapsed + t) *
      ∑ i, (initial i + p.service i t + 1 - p.rate i t)) ≤
      p.comparisonDerivative elapsed initial t +
        ∑ j, p.rate j t * (p.comparisonJump elapsed initial j t -
          p.comparisonPotential elapsed initial t) := by
  rw [p.comparison_drift, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hs := Comparison.sensitivity_le_at_zero (show elapsed + t ≤ 1 by linarith [ht.2])
    (add_nonneg (hx i) (p.service_nonneg ht i))
  rw [Comparison.lossKernel_eq_sensitivity]
  nlinarith [mul_le_mul_of_nonneg_left hs (hgap i)]

theorem comparison_first_step_lower_bound (elapsed : ℝ) (initial : ι → ℝ)
    (hT : elapsed + p.deadline ≤ 1) (hx : ∀ i, 0 ≤ initial i)
    (hgap : ∀ t ∈ Icc 0 p.deadline, ∀ i,
      0 ≤ initial i + p.service i t + 1 - p.rate i t) :
    p.comparisonPotential elapsed initial 0 -
      (∫ t in (0 : ℝ)..p.deadline,
        survivalCurve (fun u i => p.service i u) t * Comparison.lossKernel (elapsed + t) *
          ∑ i, (initial i + p.service i t + 1 - p.rate i t)) ≤
    survivalCurve (fun t i => p.service i t) p.deadline *
      p.comparisonPotential elapsed initial p.deadline +
      (∫ t in (0 : ℝ)..p.deadline, survivalCurve (fun u i => p.service i u) t *
        ∑ j, p.rate j t * p.comparisonJump elapsed initial j t) := by
  have hsurv : Continuous (survivalCurve (fun u i => p.service i u)) :=
    Real.continuous_exp.comp (continuous_finset_sum _ (fun i _ => p.service_continuous i)).neg
  have hc : Continuous (fun t => survivalCurve (fun u i => p.service i u) t *
      Comparison.lossKernel (elapsed + t) *
        ∑ i, (initial i + p.service i t + 1 - p.rate i t)) := by
    apply (hsurv.mul (Comparison.continuous_lossKernel.comp (continuous_const.add continuous_id))).mul
    apply continuous_finset_sum
    intro i _
    have hs := p.service_continuous i
    have hr := p.rate_continuous i
    fun_prop
  have hd : Continuous (fun t => survivalCurve (fun u i => p.service i u) t *
      ∑ i, -(initial i + p.service i t + 1 - p.rate i t) *
        Comparison.sensitivity (elapsed + t) (initial i + p.service i t)) := by
    apply hsurv.mul
    apply continuous_finset_sum
    intro i _
    unfold Comparison.sensitivity
    have hs := p.service_continuous i
    have hr := p.rate_continuous i
    fun_prop
  have hle : ∀ t ∈ Icc 0 p.deadline,
      -(survivalCurve (fun u i => p.service i u) t * Comparison.lossKernel (elapsed + t) *
        ∑ i, (initial i + p.service i t + 1 - p.rate i t)) ≤
      survivalCurve (fun u i => p.service i u) t *
        ∑ i, -(initial i + p.service i t + 1 - p.rate i t) *
          Comparison.sensitivity (elapsed + t) (initial i + p.service i t) := by
    intro t ht
    have h := mul_le_mul_of_nonneg_left
      (p.comparison_drift_lower_bound elapsed initial ht hT hx (hgap t ht))
      (survivalCurve_pos (fun u i => p.service i u) t).le
    rw [p.comparison_drift] at h
    convert h using 1 <;> ring
  have h := intervalIntegral.integral_mono_on (μ := volume) p.deadline_pos.le
    (hc.neg.intervalIntegrable 0 p.deadline) (hd.intervalIntegrable 0 p.deadline) hle
  rw [intervalIntegral.integral_neg, ← p.comparison_first_step_identity elapsed initial] at h
  linarith

end ServiceCurveFamily

namespace PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

theorem cumulative_service_eq_flow (h : H) (t : ℝ) :
    (fun i => s.initial h i + (s.service.curves h).service i t) =
      s.data.flow h (s.initial h) s.horizon t := by
  funext i
  change s.initial h i + (s.data.flow h (s.initial h) s.horizon t i - s.initial h i) = _
  ring

theorem rate_eq_posterior (h : H) (t : ℝ) (i : ι) :
    (s.service.curves h).rate i t = posteriorRate s.data.allocation h
      (fun i => s.initial h i + (s.service.curves h).service i t) i := by
  rw [s.cumulative_service_eq_flow]
  rfl

theorem flow_gap_eq (h : H) (t : ℝ) (i : ι) :
    s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t =
      ∫ z, (s.data.flow h (s.initial h) s.horizon t + z) i -
        s.data.allocation (h, s.data.flow h (s.initial h) s.horizon t + z) i
        ∂independentExponentials := by
  rw [s.rate_eq_posterior, s.cumulative_service_eq_flow]
  have hg := s.data.posterior_gap_eq h (s.data.flow h (s.initial h) s.horizon t) i
  convert hg using 1
  have he := congrFun (s.cumulative_service_eq_flow h t) i
  rw [he]

theorem flow_gap_nonneg
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, s.data.allocation (h, z) i ≤ z i)
    (h : H) (hx : ∀ i, 0 ≤ s.initial h i) {t : ℝ}
    (ht : t ∈ Icc 0 (s.service.curves h).deadline) (i : ι) :
    0 ≤ s.initial h i + (s.service.curves h).service i t + 1 - (s.service.curves h).rate i t := by
  rw [s.rate_eq_posterior]
  exact s.data.posterior_gap_nonneg hcap h _
    (fun i => add_nonneg (hx i) ((s.service.curves h).service_nonneg ht i)) i

theorem comparison_jump_eq_restart (elapsed : ℝ) (h : H) (j : ι) (t : ℝ) :
    (s.service.curves h).comparisonJump elapsed (s.initial h) j t =
      1 + ∑ i : {i : ι // i ≠ j},
        Comparison.continuation (elapsed + t) ((s.next j).initial (h, t) i) := rfl

theorem comparison_terminal_zero {elapsed : ℝ} (h : H)
    (hT : elapsed + s.deadline h = 1) :
    (s.service.curves h).comparisonPotential elapsed (s.initial h) (s.deadline h) = 0 := by
  unfold ServiceCurveFamily.comparisonPotential
  simp only [hT, Comparison.continuation_deadline, Finset.sum_const_zero]

theorem comparison_first_step_bound
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, s.data.allocation (h, z) i ≤ z i)
    (elapsed : ℝ) (h : H) (hx : ∀ i, 0 ≤ s.initial h i)
    (hT : elapsed + s.deadline h = 1) :
    (∑ i, Comparison.continuation elapsed (s.initial h i)) -
      (∫ t in (0 : ℝ)..s.deadline h,
        survivalCurve (fun u i => (s.service.curves h).service i u) t *
          Comparison.lossKernel (elapsed + t) *
            ∑ i, (s.initial h i + (s.service.curves h).service i t + 1 -
              (s.service.curves h).rate i t)) ≤
      ∫ t in (0 : ℝ)..s.deadline h,
        survivalCurve (fun u i => (s.service.curves h).service i u) t *
          ∑ j, (s.service.curves h).rate j t *
            (1 + ∑ i : {i : ι // i ≠ j},
              Comparison.continuation (elapsed + t) ((s.next j).initial (h, t) i)) := by
  have hb := (s.service.curves h).comparison_first_step_lower_bound elapsed (s.initial h)
    (le_of_eq hT) hx (fun t ht i => s.flow_gap_nonneg hcap h hx ht i)
  change (s.service.curves h).comparisonPotential elapsed (s.initial h) 0 - _ ≤
    _ * (s.service.curves h).comparisonPotential elapsed (s.initial h) (s.deadline h) + _ at hb
  rw [s.comparison_terminal_zero h hT, mul_zero, zero_add] at hb
  simpa only [ServiceCurveFamily.comparisonPotential, (s.service.curves h).service_zero,
    add_zero, s.comparison_jump_eq_restart] using hb

end PosteriorStage
end StochasticMatching
