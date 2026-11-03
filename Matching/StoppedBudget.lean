import Matching.StoppedOccupation

/-! Splitting a fixed sample budget between the time spent before a stopping
clock and its remaining comparison weight at that clock.
-/

open MeasureTheory Set
namespace StochasticMatching
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integrable_remaining_weight {D elapsed : ℝ} (hT : elapsed + D ≤ 1)
    (τ : Ω → ℝ) (hτ : Measurable τ) (hτbounds : ∀ ω, τ ω ∈ Icc 0 D)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    Integrable (fun ω => Comparison.continuation (elapsed + τ ω) 0 * f ω) μ := by
  have hm : Measurable (fun ω => Comparison.continuation (elapsed + τ ω) 0) := by
    unfold Comparison.continuation
    fun_prop
  apply hf.bdd_mul hm.aestronglyMeasurable
  refine ⟨1, ?_⟩
  intro ω
  rw [Real.norm_of_nonneg (Comparison.continuation_nonneg
    (by linarith [(hτbounds ω).2]) (le_refl 0))]
  exact (Comparison.continuation_lt_one _ _).le

theorem stopped_budget_identity {D elapsed : ℝ} (hD : 0 ≤ D) (hT : elapsed + D ≤ 1)
    (τ : Ω → ℝ) (hτ : Measurable τ) (hτbounds : ∀ ω, τ ω ∈ Icc 0 D)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ t in (0 : ℝ)..D, Comparison.lossKernel (elapsed + t) *
      (∫ ω in {ω | t < τ ω}, f ω ∂μ)) +
    (∫ ω, Comparison.continuation (elapsed + τ ω) 0 * f ω ∂μ) =
      Comparison.continuation elapsed 0 * (∫ ω, f ω ∂μ) := by
  have hq := integrable_remaining_weight μ hT τ hτ hτbounds f hf
  have he : (fun ω => f ω * (∫ t in (0 : ℝ)..τ ω, Comparison.lossKernel (elapsed + t))) =
      fun ω => Comparison.continuation elapsed 0 * f ω -
        Comparison.continuation (elapsed + τ ω) 0 * f ω := by
    funext ω
    rw [Comparison.integral_lossKernel_shift]
    ring
  have hc : Integrable
      (fun ω => f ω * (∫ t in (0 : ℝ)..τ ω, Comparison.lossKernel (elapsed + t))) μ := by
    rw [he]
    exact (hf.const_mul _).sub hq
  rw [← integral_weighted_stopped_interval μ hD τ hτ hτbounds f hf
      (fun t => Comparison.lossKernel (elapsed + t))
      (Comparison.continuous_lossKernel.comp (continuous_const.add continuous_id)),
    he, integral_sub (hf.const_mul _) hq, integral_const_mul]
  ring

end StochasticMatching
