import Matching.HistoryOneStep

/-! Transport the one-step laws to any sample space with the required incoming
joint law, and compose two actual completion observations. This exposes the
residual-product invariant required for repeated adaptive stages.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching.HistoryServiceFamily

variable {H ι Ω : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] (p : HistoryServiceFamily H ι)

theorem first_completion_transport (ν : Measure H) (j : ι) (μ : Measure Ω)
    (X : Ω → H × (ι → ℝ)) (hX : Measurable X)
    (hLaw : Measure.map X μ = ν.prod independentExponentials) :
    Measure.map (p.observation j ∘ X) (μ.restrict (X ⁻¹' p.winner j)) =
      (p.markedHistoryMeasure ν j).prod independentExponentials := by
  rw [← Measure.map_map (p.measurable_observation j) hX,
    ← Measure.restrict_map hX (p.measurable_winner j), hLaw,
    p.first_completion_factorization ν j]

theorem terminal_transport (ν : Measure H) (μ : Measure Ω)
    (X : Ω → H × (ι → ℝ)) (hX : Measurable X)
    (hLaw : Measure.map X μ = ν.prod independentExponentials) :
    Measure.map (residualObservation p.terminalThreshold ∘ X)
      (μ.restrict (X ⁻¹' p.terminalEvent)) =
      (p.terminalHistoryMeasure ν).prod independentExponentials := by
  rw [← Measure.map_map (measurable_residualObservation p.measurable_terminalThreshold) hX,
    ← Measure.restrict_map hX p.measurable_terminalEvent, hLaw, p.terminal_factorization ν]

/-- The second service family may depend on the incoming history and the
first completion time. Surviving demands remain independent exponentials
after both observations, on the specified ordered pair of winner branches. -/
theorem two_completion_factorization (ν : Measure H) (j : ι)
    (q : HistoryServiceFamily (H × ℝ) {i : ι // i ≠ j}) (k : {i : ι // i ≠ j}) :
    Measure.map (q.observation k ∘ p.observation j)
      ((ν.prod independentExponentials).restrict
        (p.observation j ⁻¹' q.winner k ∩ p.winner j)) =
      (q.markedHistoryMeasure (p.markedHistoryMeasure ν j) k).prod independentExponentials := by
  have h := q.first_completion_transport (p.markedHistoryMeasure ν j) k
    ((ν.prod independentExponentials).restrict (p.winner j)) (p.observation j)
    (p.measurable_observation j) (p.first_completion_factorization ν j)
  rw [Measure.restrict_restrict ((q.measurable_winner k).preimage (p.measurable_observation j))] at h
  exact h

end StochasticMatching.HistoryServiceFamily
