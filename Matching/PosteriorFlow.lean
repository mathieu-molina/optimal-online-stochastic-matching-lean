import Matching.PosteriorRegularity
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

/-! Existence and uniqueness of the posterior-rate ODE on a finite horizon,
for each fixed history. Joint measurability of the chosen trajectories in
history remains a separate obligation.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι]

noncomputable def posteriorPicard {Y : H × (ι → ℝ) → (ι → ℝ)} (hY : Measurable Y)
    (h0 : ∀ h z i, 0 ≤ Y (h, z) i) {M : ℝ≥0} (hM : ∀ h z i, Y (h, z) i ≤ M)
    (h : H) (x₀ : ι → ℝ) (T : ℝ) (hT : 0 ≤ T) : PicardLindelof (ι → ℝ) where
  toFun := fun _ => posteriorRate Y h
  tMin := -1
  tMax := T + 1
  t₀ := ⟨0, by constructor <;> linarith⟩
  x₀ := x₀
  C := M
  R := ⟨(M : ℝ) * (T + 1), mul_nonneg M.coe_nonneg (by linarith)⟩
  L := M * (Fintype.card ι : ℝ≥0)
  isPicardLindelof := {
    ht₀ := by
      change (0 : ℝ) ∈ Icc (-1) (T + 1)
      constructor <;> linarith
    hR := mul_nonneg M.coe_nonneg (by linarith)
    lipschitz := fun _ _ => (posteriorRate_lipschitz hY h0 hM h).lipschitzOnWith
    cont := fun _ _ => continuousOn_const
    norm_le := fun _ _ x _ => posteriorRate_norm_le hY h0 hM h x
    C_mul_le_R := by
      change (M : ℝ) * max (T + 1 - 0) (0 - (-1)) ≤ (M : ℝ) * (T + 1)
      simp only [sub_zero, sub_neg_eq_add, zero_add]
      rw [max_eq_left (by linarith : (1 : ℝ) ≤ T + 1)] }

/-- A continuous trajectory exists through every initial state on every
finite nonnegative time horizon. The ODE holds with ordinary derivatives,
including at the horizon endpoints. -/
theorem exists_posterior_trajectory {Y : H × (ι → ℝ) → (ι → ℝ)} (hY : Measurable Y)
    (h0 : ∀ h z i, 0 ≤ Y (h, z) i) {M : ℝ≥0} (hM : ∀ h z i, Y (h, z) i ≤ M)
    (h : H) (x₀ : ι → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ x : ℝ → (ι → ℝ), Continuous x ∧ x 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivAt x (posteriorRate Y h (x t)) t := by
  let v := posteriorPicard hY h0 hM h x₀ T hT
  obtain ⟨f, hf⟩ := v.exists_fixed
  refine ⟨f ∘ v.proj, f.continuous.comp v.continuous_proj, ?_, ?_⟩
  · change f (v.proj (v.t₀ : ℝ)) = v.x₀
    rw [v.proj_coe, f.map_t₀]
  · intro t ht
    have ht' : t ∈ Icc v.tMin v.tMax := by
      change t ∈ Icc (-1) (T + 1)
      constructor <;> linarith [ht.1, ht.2]
    have hp : v.proj t = ⟨t, ht'⟩ := v.proj_coe ⟨t, ht'⟩
    have hd : HasDerivWithinAt (f ∘ v.proj) (v t ((f ∘ v.proj) t))
        (Icc v.tMin v.tMax) t := by
      simpa only [hf, Function.comp_def, hp] using f.hasDerivWithinAt_next ⟨t, ht'⟩
    apply hd.hasDerivAt
    apply Icc_mem_nhds
    · change -1 < t
      linarith [ht.1]
    · change t < T + 1
      linarith [ht.2]

theorem posterior_trajectory_unique {Y : H × (ι → ℝ) → (ι → ℝ)} (hY : Measurable Y)
    (h0 : ∀ h z i, 0 ≤ Y (h, z) i) {M : ℝ≥0} (hM : ∀ h z i, Y (h, z) i ≤ M)
    (h : H) {T : ℝ} {f g : ℝ → (ι → ℝ)}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (posteriorRate Y h (f t)) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (posteriorRate Y h (g t)) t)
    (hinit : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  exact ODE_solution_unique (fun _ => posteriorRate_lipschitz hY h0 hM h)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) hinit

end StochasticMatching
