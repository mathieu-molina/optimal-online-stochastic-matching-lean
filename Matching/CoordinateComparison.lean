import Matching.FirstStepReward
import Matching.PosteriorComparison

/-! A comparison potential for one tagged job, while all other jobs retain
their actual rates and can cause restarts. This isolates the analytic step
needed for the stronger coordinatewise guarantee.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

noncomputable def coordinatePotential (elapsed : ℝ) (initial : ι → ℝ) (i : ι) (t : ℝ) : ℝ :=
  Comparison.continuation (elapsed + t) (initial i + p.service i t)

noncomputable def coordinateDerivative (elapsed : ℝ) (initial : ι → ℝ) (i : ι) (t : ℝ) : ℝ :=
  Comparison.timeDerivative (elapsed + t) (initial i + p.service i t) +
    Comparison.workDerivative (elapsed + t) (initial i + p.service i t) * p.rate i t

noncomputable def coordinateJump (elapsed : ℝ) (initial : ι → ℝ) (i j : ι) (t : ℝ) : ℝ :=
  if j = i then 1 else p.coordinatePotential elapsed initial i t

theorem continuous_coordinatePotential (elapsed : ℝ) (initial : ι → ℝ) (i : ι) :
    Continuous (p.coordinatePotential elapsed initial i) := by
  unfold coordinatePotential Comparison.continuation
  have hs := p.service_continuous i
  fun_prop

theorem continuous_coordinateDerivative (elapsed : ℝ) (initial : ι → ℝ) (i : ι) :
    Continuous (p.coordinateDerivative elapsed initial i) := by
  unfold coordinateDerivative Comparison.timeDerivative Comparison.workDerivative Comparison.sensitivity
  have hs := p.service_continuous i
  have hr := p.rate_continuous i
  fun_prop

theorem continuous_coordinateJump (elapsed : ℝ) (initial : ι → ℝ) (i j : ι) :
    Continuous (p.coordinateJump elapsed initial i j) := by
  unfold coordinateJump
  split_ifs
  · exact continuous_const
  · exact p.continuous_coordinatePotential elapsed initial i

theorem hasDerivAt_coordinatePotential (elapsed : ℝ) (initial : ι → ℝ) (i : ι) {t : ℝ}
    (ht : t ∈ Icc 0 p.deadline) :
    HasDerivAt (p.coordinatePotential elapsed initial i) (p.coordinateDerivative elapsed initial i t) t := by
  have h := Comparison.hasDerivAt_comp ((hasDerivAt_id t).const_add elapsed)
    ((p.service_deriv i t ht).const_add (initial i))
  simpa only [mul_one] using h

theorem coordinate_drift (elapsed : ℝ) (initial : ι → ℝ) (i : ι) (t : ℝ) :
    p.coordinateDerivative elapsed initial i t +
      ∑ j, p.rate j t * (p.coordinateJump elapsed initial i j t -
        p.coordinatePotential elapsed initial i t) =
      -(initial i + p.service i t + 1 - p.rate i t) *
        Comparison.sensitivity (elapsed + t) (initial i + p.service i t) := by
  have hs : (∑ j, p.rate j t * (p.coordinateJump elapsed initial i j t -
      p.coordinatePotential elapsed initial i t)) =
      p.rate i t * (1 - p.coordinatePotential elapsed initial i t) := by
    calc
      _ = p.rate i t * (p.coordinateJump elapsed initial i i t -
          p.coordinatePotential elapsed initial i t) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          simp [coordinateJump, hji]
        · simp
      _ = _ := by simp [coordinateJump]
  rw [hs]
  unfold coordinateDerivative coordinatePotential
  convert Comparison.generator_factor (elapsed + t) (initial i + p.service i t) (p.rate i t) using 1 <;> ring

theorem coordinate_first_step_identity (elapsed : ℝ) (initial : ι → ℝ) (i : ι) :
    survivalCurve (fun t j => p.service j t) p.deadline *
        p.coordinatePotential elapsed initial i p.deadline +
      (∫ t in (0 : ℝ)..p.deadline, survivalCurve (fun u j => p.service j u) t *
        ∑ j, p.rate j t * p.coordinateJump elapsed initial i j t) -
      p.coordinatePotential elapsed initial i 0 =
      ∫ t in (0 : ℝ)..p.deadline, survivalCurve (fun u j => p.service j u) t *
        (-(initial i + p.service i t + 1 - p.rate i t) *
          Comparison.sensitivity (elapsed + t) (initial i + p.service i t)) := by
  have hs := p.service_continuous
  have h := first_step_identity_finite p.deadline
    (survivalCurve (fun t j => p.service j t)) (p.coordinatePotential elapsed initial i)
    (p.coordinateDerivative elapsed initial i) p.rate (p.coordinateJump elapsed initial i)
    (by unfold survivalCurve; fun_prop) (p.continuous_coordinatePotential elapsed initial i)
    (p.continuous_coordinateDerivative elapsed initial i) p.rate_continuous
    (p.continuous_coordinateJump elapsed initial i) (survivalCurve_initial p.service_zero)
    (fun t ht => hasDerivAt_survivalCurve (fun j => p.service_deriv j t
      (by simpa only [uIcc_of_le p.deadline_pos.le] using ht)))
    (fun t ht => p.hasDerivAt_coordinatePotential elapsed initial i
      (by simpa only [uIcc_of_le p.deadline_pos.le] using ht))
  simpa only [p.coordinate_drift] using h

theorem coordinate_actual_first_step (elapsed : ℝ) (initial : ι → ℝ) (i : ι) :
    (∫ _ in p.terminalSurvival, p.coordinatePotential elapsed initial i p.deadline
      ∂(independentExponentials (ι := ι))) +
    (∑ j, ∫ z in variableWinner p.service p.deadline j,
      p.coordinateJump elapsed initial i j (cappedHit (p.service j) p.deadline (z j))
        ∂independentExponentials) - p.coordinatePotential elapsed initial i 0 =
    ∫ t in (0 : ℝ)..p.deadline, survivalCurve (fun u j => p.service j u) t *
      (-(initial i + p.service i t + 1 - p.rate i t) *
        Comparison.sensitivity (elapsed + t) (initial i + p.service i t)) := by
  rw [p.terminal_constant_integral]
  simp_rw [p.winner_clock_integral _ (p.continuous_coordinateJump elapsed initial i _).measurable]
  have hs : Continuous (survivalCurve (fun u j => p.service j u)) :=
    Real.continuous_exp.comp (continuous_finset_sum _ (fun j _ => p.service_continuous j)).neg
  rw [← intervalIntegral.integral_finset_sum]
  · convert p.coordinate_first_step_identity elapsed initial i using 2
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j _
    exact (((p.rate_continuous j).mul hs).mul
      (p.continuous_coordinateJump elapsed initial i j)).intervalIntegrable 0 p.deadline

theorem coordinate_first_step_lower_bound (elapsed : ℝ) (initial : ι → ℝ) (i : ι)
    (hT : elapsed + p.deadline ≤ 1) (hx : 0 ≤ initial i)
    (hgap : ∀ t ∈ Icc 0 p.deadline,
      0 ≤ initial i + p.service i t + 1 - p.rate i t) :
    p.coordinatePotential elapsed initial i 0 -
      (∫ t in (0 : ℝ)..p.deadline,
        survivalCurve (fun u j => p.service j u) t * Comparison.lossKernel (elapsed + t) *
          (initial i + p.service i t + 1 - p.rate i t)) ≤
      (∫ _ in p.terminalSurvival, p.coordinatePotential elapsed initial i p.deadline
        ∂(independentExponentials (ι := ι))) +
      ∑ j, ∫ z in variableWinner p.service p.deadline j,
        p.coordinateJump elapsed initial i j (cappedHit (p.service j) p.deadline (z j))
          ∂independentExponentials := by
  have hsurv : Continuous (survivalCurve (fun u j => p.service j u)) :=
    Real.continuous_exp.comp (continuous_finset_sum _ (fun j _ => p.service_continuous j)).neg
  have hs := p.service_continuous i
  have hr := p.rate_continuous i
  have hc : Continuous (fun t => survivalCurve (fun u j => p.service j u) t *
      Comparison.lossKernel (elapsed + t) * (initial i + p.service i t + 1 - p.rate i t)) := by
    apply (hsurv.mul (Comparison.continuous_lossKernel.comp (continuous_const.add continuous_id))).mul
    fun_prop
  have hd : Continuous (fun t => survivalCurve (fun u j => p.service j u) t *
      (-(initial i + p.service i t + 1 - p.rate i t) *
        Comparison.sensitivity (elapsed + t) (initial i + p.service i t))) := by
    apply hsurv.mul
    unfold Comparison.sensitivity
    fun_prop
  have hle : ∀ t ∈ Icc 0 p.deadline,
      -(survivalCurve (fun u j => p.service j u) t * Comparison.lossKernel (elapsed + t) *
        (initial i + p.service i t + 1 - p.rate i t)) ≤
      survivalCurve (fun u j => p.service j u) t *
        (-(initial i + p.service i t + 1 - p.rate i t) *
          Comparison.sensitivity (elapsed + t) (initial i + p.service i t)) := by
    intro t ht
    have hb := Comparison.sensitivity_le_at_zero (show elapsed + t ≤ 1 by linarith [ht.2])
      (add_nonneg hx (p.service_nonneg ht i))
    have hmul := mul_le_mul_of_nonneg_left hb (hgap t ht)
    have hsurvpos := (survivalCurve_pos (fun u j => p.service j u) t).le
    rw [Comparison.lossKernel_eq_sensitivity]
    nlinarith [mul_le_mul_of_nonneg_left hmul hsurvpos]
  have h := intervalIntegral.integral_mono_on (μ := volume) p.deadline_pos.le
    (hc.neg.intervalIntegrable 0 p.deadline) (hd.intervalIntegrable 0 p.deadline) hle
  rw [intervalIntegral.integral_neg, ← p.coordinate_actual_first_step elapsed initial i] at h
  linarith

end StochasticMatching.ServiceCurveFamily
