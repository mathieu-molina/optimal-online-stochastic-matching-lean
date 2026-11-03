import Matching.PosteriorTrajectory

/-! Extend allocation data from nonnegative demands to all real vectors, as
required by the global posterior ODE. The extension agrees on its original
domain and preserves the same nonnegative uniform bound.
-/

open MeasureTheory Set
open scoped NNReal

namespace StochasticMatching

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι]

def nonnegativeDemand (z : ι → ℝ) : {y : ι → ℝ // ∀ i, 0 ≤ y i} :=
  ⟨fun i => max (z i) 0, fun _ => le_max_right _ _⟩

theorem measurable_nonnegativeDemand : Measurable (nonnegativeDemand (ι := ι)) := by
  apply Measurable.subtype_mk
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i).max measurable_const)

theorem nonnegativeDemand_eq {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    nonnegativeDemand z = ⟨z, hz⟩ := by
  apply Subtype.ext
  funext i
  exact max_eq_left (hz i)

namespace PosteriorData

noncomputable def ofNonnegative
    (Y : H × {z : ι → ℝ // ∀ i, 0 ≤ z i} → (ι → ℝ)) (hY : Measurable Y)
    (M : ℝ≥0) (hY0 : ∀ h z i, 0 ≤ Y (h, z) i)
    (hYM : ∀ h z i, Y (h, z) i ≤ M) : PosteriorData H ι where
  allocation x := Y (x.1, nonnegativeDemand x.2)
  measurable_allocation := hY.comp (measurable_fst.prodMk
    (measurable_nonnegativeDemand.comp measurable_snd))
  bound := M
  allocation_nonneg h z i := hY0 h (nonnegativeDemand z) i
  allocation_le h z i := hYM h (nonnegativeDemand z) i

theorem ofNonnegative_agrees
    (Y : H × {z : ι → ℝ // ∀ i, 0 ≤ z i} → (ι → ℝ)) (hY : Measurable Y)
    (M : ℝ≥0) (hY0 : ∀ h z i, 0 ≤ Y (h, z) i)
    (hYM : ∀ h z i, Y (h, z) i ≤ M) (h : H) (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (ofNonnegative Y hY M hY0 hYM).allocation (h, z) = Y (h, ⟨z, hz⟩) := by
  change Y (h, nonnegativeDemand z) = _
  rw [nonnegativeDemand_eq hz]

end PosteriorData
end StochasticMatching
