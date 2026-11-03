import Matching.PosteriorTrajectory
import Matching.ActiveCoordinates
import Mathlib.Analysis.Convex.Integral

/-! Feasibility of posterior rates. Compact feasible allocation regions supply
the uniform bound needed by the ODE construction. Convexity and closedness
preserve feasibility under averaging; downward closure permits completed
coordinates to be set to zero.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching.PosteriorData

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] (p : PosteriorData H ι)

theorem allocation_integrable (h : H) (x : ι → ℝ) :
    Integrable (fun z => p.allocation (h, x + z)) independentExponentials := by
  have hm : Measurable (fun z => p.allocation (h, x + z)) :=
    p.measurable_allocation.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  apply (integrable_const (p.bound : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  apply (pi_norm_le_iff_of_nonneg p.bound.coe_nonneg).mpr
  intro i
  rw [Real.norm_of_nonneg (p.allocation_nonneg h (x + z) i)]
  exact p.allocation_le h (x + z) i

theorem posteriorRate_eq_integral (h : H) (x : ι → ℝ) :
    posteriorRate p.allocation h x = ∫ z, p.allocation (h, x + z) ∂independentExponentials := by
  ext i
  exact (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).integral_comp_comm
    (p.allocation_integrable h x)

theorem posteriorRate_mem {P : Set (ι → ℝ)} (hPc : Convex ℝ P) (hPclosed : IsClosed P)
    (hmem : ∀ h z, p.allocation (h, z) ∈ P) (h : H) (x : ι → ℝ) :
    posteriorRate p.allocation h x ∈ P := by
  rw [p.posteriorRate_eq_integral]
  exact hPc.integral_mem hPclosed (Filter.Eventually.of_forall (fun z => hmem h (x + z)))
    (p.allocation_integrable h x)

theorem masked_posteriorRate_mem [DecidableEq ι] {P : Set (ι → ℝ)}
    (hPc : Convex ℝ P) (hPclosed : IsClosed P) (hPdown : NonnegDownwardClosed P)
    (hmem : ∀ h z, p.allocation (h, z) ∈ P) (D : Finset ι) (h : H) (x : ι → ℝ) :
    maskCompleted D (posteriorRate p.allocation h x) ∈ P :=
  maskCompleted_mem hPdown D (p.posteriorRate_mem hPc hPclosed hmem h x)
    (posteriorRate_nonneg p.allocation_nonneg h x)

/-- Compactness provides the uniform coordinate bound used in all posterior
regularity and flow theorems. No continuity of the allocation is required. -/
noncomputable def ofCompact {Y : H × (ι → ℝ) → (ι → ℝ)} (hY : Measurable Y)
    {P : Set (ι → ℝ)} (hP : IsCompact P) (hP0 : ∀ x ∈ P, ∀ i, 0 ≤ x i)
    (hmem : ∀ h z, Y (h, z) ∈ P) : PosteriorData H ι := by
  let C := Classical.choose hP.isBounded.exists_norm_le
  have hC := Classical.choose_spec hP.isBounded.exists_norm_le
  exact {
    allocation := Y
    measurable_allocation := hY
    bound := ⟨max C 0, le_max_right _ _⟩
    allocation_nonneg := fun h z => hP0 _ (hmem h z)
    allocation_le := fun h z i => by
      calc
        Y (h, z) i ≤ ‖Y (h, z) i‖ := le_abs_self _
        _ ≤ ‖Y (h, z)‖ := norm_le_pi_norm _ i
        _ ≤ C := hC _ (hmem h z)
        _ ≤ max C 0 := le_max_left _ _ }

end StochasticMatching.PosteriorData
