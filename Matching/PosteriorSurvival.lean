import Matching.PosteriorService
import Matching.ConditionalTransport

/-! Conditional rates after a no-completion observation along the constructed
posterior flow. The inspection time may depend measurably on the incoming
history, but not on unobserved fresh residual demands.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι]

theorem posterior_rate_after_survival (p : PosteriorData H ι)
    (ν : Measure H) [IsFiniteMeasure ν]
    {ξ a : H → (ι → ℝ)} (hξ : Measurable ξ) (ha : Measurable a)
    (ha0 : ∀ h i, 0 ≤ a h i) (i : ι) :
    (fun x : H × (ι → ℝ) => posteriorRate p.allocation x.1 (ξ x.1 + a x.1) i)
      =ᵐ[(ν.prod independentExponentials).restrict (historySurvival a)]
    ((ν.prod independentExponentials).restrict (historySurvival a))[
      fun x => p.allocation (x.1, ξ x.1 + x.2) i |
      (‹MeasurableSpace H›).comap Prod.fst] := by
  let μ := (ν.prod (independentExponentials (ι := ι))).restrict (historySurvival a)
  let ν' := ν.withDensity (fun h => independentExponentials (survivalBox (a h)))
  have hLaw : Measure.map (residualObservation a) μ = ν'.prod independentExponentials :=
    history_survival_factorization ha ha0 ν
  have hfst : Measure.map (Prod.fst : H × (ι → ℝ) → H)
      (Measure.map (residualObservation a) μ) = ν' := by
    rw [hLaw]
    simp
  letI : IsFiniteMeasure ν' := by
    rw [← hfst]
    infer_instance
  have hid := posterior_rate_conditionalExpectation p ν' μ (residualObservation a)
    (measurable_residualObservation ha) hLaw (hξ.add ha) i
  have heq : (fun x : H × (ι → ℝ) =>
      p.allocation ((residualObservation a x).1,
        ξ (residualObservation a x).1 + a (residualObservation a x).1 +
          (residualObservation a x).2) i) =
      (fun x => p.allocation (x.1, ξ x.1 + x.2) i) := by
    funext x
    congr 2
    funext j
    simp only [residualObservation, Pi.add_apply]
    ring
  rw [heq] at hid
  exact hid

namespace PosteriorData

variable (p : PosteriorData H ι)

theorem measurable_flow_increment {ξ : H → (ι → ℝ)} (hξ : Measurable ξ)
    (T : ℝ≥0) {τ : H → ℝ} (hτ : Measurable τ) :
    Measurable (fun h => p.flow h (ξ h) T (τ h) - ξ h) := by
  exact ((p.measurable_flow hξ T).comp (measurable_id.prodMk hτ)).sub hξ

theorem flow_rate_conditionalExpectation (ν : Measure H) [IsFiniteMeasure ν]
    {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (T : ℝ≥0)
    {τ : H → ℝ} (hτ : Measurable τ) (hτT : ∀ h, τ h ∈ Icc 0 (T : ℝ)) (i : ι) :
    let a := fun h => p.flow h (ξ h) T (τ h) - ξ h
    (fun x : H × (ι → ℝ) => posteriorRate p.allocation x.1
      (p.flow x.1 (ξ x.1) T (τ x.1)) i)
      =ᵐ[(ν.prod independentExponentials).restrict (historySurvival a)]
    ((ν.prod independentExponentials).restrict (historySurvival a))[
      fun x => p.allocation (x.1, ξ x.1 + x.2) i |
      (‹MeasurableSpace H›).comap Prod.fst] := by
  dsimp only
  have ha0 : ∀ h i, 0 ≤ (p.flow h (ξ h) T (τ h) - ξ h) i := by
    intro h j
    exact sub_nonneg.mpr (p.flow_above_initial h (ξ h) T (hτT h) j)
  have hid := posterior_rate_after_survival p ν hξ
    (p.measurable_flow_increment hξ T hτ) ha0 i
  simpa only [add_sub_cancel] using hid

end PosteriorData
end StochasticMatching
