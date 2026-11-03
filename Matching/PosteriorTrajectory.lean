import Matching.PosteriorFlow

/-! A chosen posterior trajectory for bounded nonnegative allocation data.
The field is averaged only over active coordinates; known completed demands
can be included in the history parameter of the allocation function.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching

structure PosteriorData (H ι : Type*) [MeasurableSpace H] where
  allocation : H × (ι → ℝ) → (ι → ℝ)
  measurable_allocation : Measurable allocation
  bound : ℝ≥0
  allocation_nonneg : ∀ h z i, 0 ≤ allocation (h, z) i
  allocation_le : ∀ h z i, allocation (h, z) i ≤ bound

namespace PosteriorData

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] (p : PosteriorData H ι)

noncomputable def picard (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) : PicardLindelof (ι → ℝ) :=
  posteriorPicard p.measurable_allocation p.allocation_nonneg p.allocation_le h x₀ T T.coe_nonneg

noncomputable def fixedCurve (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) : (p.picard h x₀ T).FunSpace :=
  Classical.choose (p.picard h x₀ T).exists_fixed

theorem fixedCurve_next (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) :
    (p.fixedCurve h x₀ T).next = p.fixedCurve h x₀ T :=
  Classical.choose_spec (p.picard h x₀ T).exists_fixed

noncomputable def flow (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) (t : ℝ) : ι → ℝ :=
  p.fixedCurve h x₀ T ((p.picard h x₀ T).proj t)

theorem continuous_flow (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) : Continuous (p.flow h x₀ T) :=
  (p.fixedCurve h x₀ T).continuous.comp (p.picard h x₀ T).continuous_proj

theorem flow_initial (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) : p.flow h x₀ T 0 = x₀ := by
  change p.fixedCurve h x₀ T ((p.picard h x₀ T).proj ((p.picard h x₀ T).t₀ : ℝ)) =
    (p.picard h x₀ T).x₀
  rw [PicardLindelof.proj_coe, PicardLindelof.FunSpace.map_t₀]

theorem flow_hasDerivAt (h : H) (x₀ : ι → ℝ) (T : ℝ≥0) {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ)) :
    HasDerivAt (p.flow h x₀ T) (posteriorRate p.allocation h (p.flow h x₀ T t)) t := by
  let v := p.picard h x₀ T
  let f := p.fixedCurve h x₀ T
  have hf : f.next = f := p.fixedCurve_next h x₀ T
  have ht' : t ∈ Icc v.tMin v.tMax := by
    change t ∈ Icc (-1) ((T : ℝ) + 1)
    constructor <;> linarith [ht.1, ht.2]
  have hp : v.proj t = ⟨t, ht'⟩ := v.proj_coe ⟨t, ht'⟩
  have hd : HasDerivWithinAt (f ∘ v.proj) (v t ((f ∘ v.proj) t))
      (Icc v.tMin v.tMax) t := by
    simpa only [hf, Function.comp_def, hp] using f.hasDerivWithinAt_next ⟨t, ht'⟩
  apply hd.hasDerivAt
  apply Icc_mem_nhds
  · change -1 < t
    linarith [ht.1]
  · change t < (T : ℝ) + 1
    linarith [ht.2]

end PosteriorData
end StochasticMatching
