import Matching.ComparisonPotential
import Matching.ExpectedTelescope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
The deterministic comparison loss budget and its conditional-expectation
integral. Product integrability is explicitly required for Fubini.
-/

open MeasureTheory

namespace StochasticMatching
namespace Comparison

noncomputable def lossKernel (t : ℝ) : ℝ := -timeDerivative t 0

theorem lossKernel_eq_sensitivity (t : ℝ) : lossKernel t = sensitivity t 0 := by
  simp [lossKernel, timeDerivative]

theorem lossKernel_pos (t : ℝ) : 0 < lossKernel t := by
  rw [lossKernel_eq_sensitivity]
  exact sensitivity_pos t 0

theorem continuous_lossKernel : Continuous lossKernel := by
  unfold lossKernel timeDerivative sensitivity
  fun_prop

theorem integral_lossKernel : (∫ t in (0 : ℝ)..1, lossKernel t) = ratio := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun t _ => (hasDerivAt_time t 0).neg)
    (show IntervalIntegrable lossKernel volume 0 1 from
      continuous_lossKernel.intervalIntegrable 0 1)
  simpa only [continuation_deadline, continuation_initial, neg_zero,
    zero_sub, neg_neg] using h

theorem setIntegral_lossKernel :
    (∫ t in Set.Ioc (0 : ℝ) 1, lossKernel t) = ratio := by
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact integral_lossKernel

end Comparison

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- For a nonnegative residual, joint measurability suffices for the weighted
conditional budget to be product-integrable. This discharges the Fubini
integrability requirement without assuming a uniform bound on the residual. -/
theorem integrable_conditional_loss_budget [IsFiniteMeasure μ]
    (R : Ω → ℝ) (m : ℝ → MeasurableSpace Ω) (hm : ∀ t, m t ≤ mΩ)
    (hR : 0 ≤ᵐ[μ] R)
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ × Ω => Comparison.lossKernel p.1 * (μ[R | m p.1]) p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ)) :
    Integrable
      (fun p : ℝ × Ω => Comparison.lossKernel p.1 * (μ[R | m p.1]) p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ) := by
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t =>
      (show Integrable (μ[R | m t]) μ from integrable_condExp).const_mul
        (Comparison.lossKernel t))
  · have hnorm : (fun t => ∫ ω,
        ‖Comparison.lossKernel t * (μ[R | m t]) ω‖ ∂μ) =
        fun t => Comparison.lossKernel t * ∫ ω, R ω ∂μ := by
      funext t
      calc
        _ = ∫ ω, Comparison.lossKernel t * (μ[R | m t]) ω ∂μ := by
          apply integral_congr_ae
          filter_upwards [condExp_nonneg (m := m t) hR] with ω hω
          exact Real.norm_of_nonneg
            (mul_nonneg (le_of_lt (Comparison.lossKernel_pos t)) hω)
        _ = _ := by rw [integral_const_mul, integral_condExp (hm t)]
    rw [hnorm]
    have hK : Integrable Comparison.lossKernel
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (Comparison.continuous_lossKernel.intervalIntegrable 0 1).1
    exact hK.mul_const _

/-- Integrate the conditional residual budget over the deterministic time
interval. This does not assert measurability of a time-indexed conditional
expectation: that requirement is contained in the explicit `hprod` hypothesis. -/
theorem expected_conditional_loss_budget [IsFiniteMeasure μ]
    (R : Ω → ℝ) (m : ℝ → MeasurableSpace Ω) (hm : ∀ t, m t ≤ mΩ)
    (hprod : Integrable
      (fun p : ℝ × Ω => Comparison.lossKernel p.1 * (μ[R | m p.1]) p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ)) :
    (∫ ω, (∫ t in Set.Ioc (0 : ℝ) 1,
      Comparison.lossKernel t * (μ[R | m t]) ω) ∂μ) =
        Comparison.ratio * ∫ ω, R ω ∂μ := by
  rw [← integral_integral_swap hprod]
  have hinner : ∀ t,
      (∫ ω, Comparison.lossKernel t * (μ[R | m t]) ω ∂μ) =
        Comparison.lossKernel t * ∫ ω, R ω ∂μ := by
    intro t
    rw [integral_const_mul, integral_condExp (hm t)]
  simp_rw [hinner]
  rw [integral_mul_const, Comparison.setIntegral_lossKernel]

theorem expected_conditional_loss_budget_of_measurable [IsFiniteMeasure μ]
    (R : Ω → ℝ) (m : ℝ → MeasurableSpace Ω) (hm : ∀ t, m t ≤ mΩ)
    (hR : 0 ≤ᵐ[μ] R)
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ × Ω => Comparison.lossKernel p.1 * (μ[R | m p.1]) p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ)) :
    (∫ ω, (∫ t in Set.Ioc (0 : ℝ) 1,
      Comparison.lossKernel t * (μ[R | m t]) ω) ∂μ) =
        Comparison.ratio * ∫ ω, R ω ∂μ :=
  expected_conditional_loss_budget R m hm
    (integrable_conditional_loss_budget R m hm hR hmeas)

/-- The final algebraic implication once the process-specific loss inequality
has been proved. Its hypotheses are exposed; this is not an unconditional
competitive theorem for a constructed policy. -/
theorem guarantee_of_conditional_loss [IsProbabilityMeasure μ]
    (X Y Z : Ω → ℝ) (m : ℝ → MeasurableSpace Ω) (hm : ∀ t, m t ≤ mΩ)
    (_hX : Integrable X μ) (hY : Integrable Y μ) (hZ : Integrable Z μ)
    (hmean : (∫ ω, Z ω ∂μ) = 1)
    (hprod : Integrable
      (fun p : ℝ × Ω => Comparison.lossKernel p.1 * (μ[(Z - Y) | m p.1]) p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod μ))
    (hloss : Comparison.ratio - (∫ ω, X ω ∂μ) ≤
      ∫ ω, (∫ t in Set.Ioc (0 : ℝ) 1,
        Comparison.lossKernel t * (μ[(Z - Y) | m t]) ω) ∂μ) :
    Comparison.ratio * (∫ ω, Y ω ∂μ) ≤ ∫ ω, X ω ∂μ := by
  rw [expected_conditional_loss_budget (Z - Y) m hm hprod,
    integral_sub' hZ hY, hmean] at hloss
  nlinarith

end StochasticMatching
