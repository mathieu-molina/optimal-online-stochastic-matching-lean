import Matching.PoissonInputKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Integrating a payoff against the actual next-arrival measure, including
its no-arrival atom. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem poissonNextArrival_integral (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    {T : ℝ} (hT : 0 ≤ T) (f : Unit ⊕ (ℝ × σ) → ℝ) (hf : Measurable f)
    (hi : Integrable f (poissonNextArrival capacity T)) :
    (∫ e, f e ∂poissonNextArrival capacity T) =
      Real.exp (-((∑ s, capacity s) * T)) * f (Sum.inl ()) +
        ∑ s, ∫ t in (0 : ℝ)..T, capacity s * Real.exp (-(∑ u, capacity u) * t) *
          f (Sum.inr (t, s)) := by
  rw [poissonNextArrival, integrable_add_measure] at hi
  rw [poissonNextArrival, integral_add_measure hi.1 hi.2, integral_sum_measure hi.2, tsum_fintype,
    integral_smul_measure, integral_dirac' f _ hf.stronglyMeasurable, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have hm : Measurable (fun t : ℝ => (Sum.inr (t, s) : Unit ⊕ (ℝ × σ))) :=
    measurable_inr.comp (measurable_id.prodMk measurable_const)
  rw [integral_map_of_stronglyMeasurable hm hf.stronglyMeasurable]
  have hd : Measurable (fun t : ℝ => ENNReal.ofReal
      (capacity s * Real.exp (-(∑ u, capacity u) * t))) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (mul_nonneg (hc s) (Real.exp_nonneg _)), smul_eq_mul]
  rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

end StochasticMatching
