import Matching.PoissonMixture
import Mathlib.MeasureTheory.Integral.Prod

/-! A random count compared with an independent Poisson threshold. Its event
probability is the lower-tail mixture used by the offline comparison.
-/

open MeasureTheory Set
open scoped BigOperators NNReal
namespace StochasticMatching
variable {Ω : Type*} [MeasurableSpace Ω]

theorem poisson_product_threshold_probability (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Ω → ℕ) (hD : Measurable D) (a : ℝ≥0) :
    (μ.prod (ProbabilityTheory.poissonMeasure a)).real {p : Ω × ℕ | p.2 < D p.1} =
      ∫ ω, poissonLowerTail a (D ω) ∂μ := by
  classical
  let E : Set (Ω × ℕ) := {p | p.2 < D p.1}
  have hE : MeasurableSet E := measurableSet_lt measurable_snd (hD.comp measurable_fst)
  have hi : Integrable (fun p : Ω × ℕ => if p ∈ E then (1 : ℝ) else 0)
      (μ.prod (ProbabilityTheory.poissonMeasure a)) :=
    integrable_event_constant _ E hE 1
  have he := integral_event_constant (μ.prod (ProbabilityTheory.poissonMeasure a)) E hE 1
  rw [mul_one] at he
  rw [← he, integral_prod _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hk : MeasurableSet {k : ℕ | k < D ω} := Set.to_countable _ |>.measurableSet
  have h := integral_event_constant (ProbabilityTheory.poissonMeasure a) {k : ℕ | k < D ω} hk 1
  rw [mul_one, ← poissonLowerTail_eq_probability] at h
  exact h

end StochasticMatching
