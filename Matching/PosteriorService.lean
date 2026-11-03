import Matching.MeasurablePosteriorFlow
import Matching.HistoryTransport
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Instantiate the measurable-history service interface with the constructed
posterior ODE. A measurable remaining deadline may vary with history, provided
it is positive and bounded by the common finite construction horizon.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching.PosteriorData

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] (p : PosteriorData H ι)

theorem flow_monotone (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) (i : ι) :
    MonotoneOn (fun t => p.flow h x₀ T t i) (Icc 0 (T : ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (T : ℝ))
    (((continuous_apply i).comp (p.continuous_flow h x₀ T)).continuousOn)
  · intro t ht
    exact ((hasDerivAt_pi.mp (p.flow_hasDerivAt h x₀ T (interior_subset ht))) i).hasDerivWithinAt
  · intro t _
    exact posteriorRate_nonneg p.allocation_nonneg h (p.flow h x₀ T t) i

theorem flow_above_initial (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) {t : ℝ}
    (ht : t ∈ Icc 0 (T : ℝ)) (i : ι) : x₀ i ≤ p.flow h x₀ T t i := by
  calc
    x₀ i = p.flow h x₀ T 0 i := by rw [p.flow_initial]
    _ ≤ p.flow h x₀ T t i :=
      p.flow_monotone h x₀ T i ⟨le_refl _, T.coe_nonneg⟩ ht ht.1

noncomputable def serviceCurves (h : H) (x₀ : ι → ℝ) (T : ℝ≥0)
    (D : ℝ) (hD : 0 < D) (hDT : D ≤ T) : ServiceCurveFamily ι where
  deadline := D
  deadline_pos := hD
  service i t := p.flow h x₀ T t i - x₀ i
  rate i t := posteriorRate p.allocation h (p.flow h x₀ T t) i
  service_continuous i := ((continuous_apply i).comp (p.continuous_flow h x₀ T)).sub continuous_const
  rate_continuous i := (continuous_apply i).comp
    ((posteriorRate_lipschitz p.measurable_allocation p.allocation_nonneg p.allocation_le h).continuous.comp
      (p.continuous_flow h x₀ T))
  service_monotone i := by
    intro s hs t ht hst
    exact sub_le_sub_right (p.flow_monotone h x₀ T i
      ⟨hs.1, hs.2.trans hDT⟩ ⟨ht.1, ht.2.trans hDT⟩ hst) _
  service_zero i := by rw [p.flow_initial]; exact sub_self _
  rate_nonneg i t _ := posteriorRate_nonneg p.allocation_nonneg h (p.flow h x₀ T t) i
  service_deriv i t ht :=
    ((hasDerivAt_pi.mp (p.flow_hasDerivAt h x₀ T ⟨ht.1, ht.2.trans hDT⟩)) i).sub_const _

noncomputable def historyService {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (T : ℝ≥0)
    {D : H → ℝ} (hD : Measurable D) (hD0 : ∀ h, 0 < D h) (hDT : ∀ h, D h ≤ T) :
    HistoryServiceFamily H ι where
  curves h := p.serviceCurves h (ξ h) T (D h) (hD0 h) (hDT h)
  deadline_measurable := hD
  service_at_measurable i t := by
    exact ((measurable_pi_apply i).comp ((p.measurable_flow hξ T).comp
      (measurable_id.prodMk measurable_const))).sub ((measurable_pi_apply i).comp hξ)
  rate_at_measurable i t := by
    have hm : Measurable (fun h => p.flow h (ξ h) T t) :=
      (p.measurable_flow hξ T).comp (measurable_id.prodMk measurable_const)
    exact (measurable_pi_apply i).comp
      ((measurable_posteriorRate p.measurable_allocation).comp (measurable_id.prodMk hm))

end StochasticMatching.PosteriorData
