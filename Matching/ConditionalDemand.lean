import Matching.PosteriorGap
import Matching.ConditionalTransport

/-! Conditional demand means and residual loss budgets under the transported
history/residual product law. The initial-service coordinate is required to
be integrable under the incoming history measure.
-/

open MeasureTheory Set

namespace StochasticMatching

variable {H ι Ω : Type*} [MeasurableSpace H] [Fintype ι] [MeasurableSpace Ω]

theorem integrable_history_demand (ν : Measure H) [IsFiniteMeasure ν]
    (ξ : H → (ι → ℝ)) (i : ι) (hξi : Integrable (fun h => ξ h i) ν) :
    Integrable (fun x : H × (ι → ℝ) => (ξ x.1 + x.2) i) (ν.prod independentExponentials) := by
  have h1 : Integrable (fun x : H × (ι → ℝ) => ξ x.1 i) (ν.prod independentExponentials) := by
    simpa only [mul_one] using hξi.mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : ι → ℝ => (1 : ℝ)) independentExponentials)
  have h2 : Integrable (fun x : H × (ι → ℝ) => x.2 i) (ν.prod independentExponentials) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : H => (1 : ℝ)) ν).mul_prod
        (integrable_exponential_coordinate i)
  exact h1.add h2

theorem demand_conditionalExpectation (ν : Measure H) [IsFiniteMeasure ν]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → H × (ι → ℝ)) (hX : Measurable X)
    (hLaw : Measure.map X μ = ν.prod independentExponentials)
    {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (i : ι)
    (hξi : Integrable (fun h => ξ h i) ν) :
    (fun ω => ξ (X ω).1 i + 1) =ᵐ[μ]
      μ[fun ω => (ξ (X ω).1 + (X ω).2) i |
        (‹MeasurableSpace H›).comap (fun ω => (X ω).1)] := by
  have hf : Measurable (fun x : H × (ι → ℝ) => (ξ x.1 + x.2) i) :=
    (measurable_pi_apply i).comp ((hξ.comp measurable_fst).add measurable_snd)
  have h := conditionalExpectation_history_transport ν μ X hX hLaw
    (fun x : H × (ι → ℝ) => (ξ x.1 + x.2) i) hf (integrable_history_demand ν ξ i hξi)
  simpa only [integral_shifted_exponential_coordinate] using h

theorem posterior_gap_conditionalExpectation (p : PosteriorData H ι)
    (ν : Measure H) [IsFiniteMeasure ν] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → H × (ι → ℝ)) (hX : Measurable X)
    (hLaw : Measure.map X μ = ν.prod independentExponentials)
    {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (i : ι)
    (hξi : Integrable (fun h => ξ h i) ν) :
    (fun ω => ξ (X ω).1 i + 1 - posteriorRate p.allocation (X ω).1 (ξ (X ω).1) i) =ᵐ[μ]
      μ[fun ω => (ξ (X ω).1 + (X ω).2) i -
        p.allocation ((X ω).1, ξ (X ω).1 + (X ω).2) i |
        (‹MeasurableSpace H›).comap (fun ω => (X ω).1)] := by
  let F : H × (ι → ℝ) → ℝ := fun x => (ξ x.1 + x.2) i - p.allocation (x.1, ξ x.1 + x.2) i
  have hd : Measurable (fun x : H × (ι → ℝ) => ξ x.1 + x.2) :=
    (hξ.comp measurable_fst).add measurable_snd
  have hy : Measurable (fun x : H × (ι → ℝ) => p.allocation (x.1, ξ x.1 + x.2) i) :=
    (measurable_pi_apply i).comp (p.measurable_allocation.comp (measurable_fst.prodMk hd))
  have hyi : Integrable (fun x : H × (ι → ℝ) => p.allocation (x.1, ξ x.1 + x.2) i)
      (ν.prod independentExponentials) := by
    apply (integrable_const (p.bound : ℝ)).mono' hy.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (p.allocation_nonneg x.1 (ξ x.1 + x.2) i)]
    exact p.allocation_le x.1 (ξ x.1 + x.2) i
  have hf : Measurable F := ((measurable_pi_apply i).comp hd).sub hy
  have hfi : Integrable F (ν.prod independentExponentials) :=
    (integrable_history_demand ν ξ i hξi).sub hyi
  have h := conditionalExpectation_history_transport ν μ X hX hLaw F hf hfi
  have heq : (fun ω => ∫ z, F ((X ω).1, z) ∂independentExponentials) =
      (fun ω => ξ (X ω).1 i + 1 - posteriorRate p.allocation (X ω).1 (ξ (X ω).1) i) := by
    funext ω
    exact (p.posterior_gap_eq (X ω).1 (ξ (X ω).1) i).symm
  rw [heq] at h
  exact h

end StochasticMatching
