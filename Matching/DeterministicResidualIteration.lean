import Matching.NoiseKernelFactorization

/-! A deterministic transition can consume a single initially sampled
infinite stream. A one-step fresh-residual law yields every finite iteration
law, without resampling the latent stream between steps. -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A R : Type*} [MeasurableSpace A] [MeasurableSpace R]

theorem iterateKernel_deterministic (F : A → A) (hF : Measurable F) (n : ℕ) :
    iterateKernel (Kernel.deterministic F hF) n =
      Kernel.deterministic (F^[n]) (hF.iterate n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterateKernel_succ, ih, Kernel.deterministic_comp_deterministic]
    congr 1
    funext x
    exact (Function.iterate_succ_apply' F n x).symm

theorem deterministicResidual_intertwining (ρ : Measure R) [IsProbabilityMeasure ρ]
    (F : A × R → A × R) (hF : Measurable F) (L : Kernel A A)
    (hlaw : ∀ a, Measure.map (fun r => F (a, r)) ρ = (L a).prod ρ) :
    Kernel.deterministic F hF ∘ₖ freshResidualKernel ρ = freshResidualKernel ρ ∘ₖ L := by
  rw [Kernel.deterministic_comp_eq_map]
  ext a : 1
  rw [Kernel.map_apply _ hF, freshResidualKernel_apply, Measure.dirac_prod,
    Measure.map_map hF measurable_prodMk_left, freshResidualKernel_comp_apply]
  exact hlaw a

theorem deterministicResidual_iterate_law (ρ : Measure R) [IsProbabilityMeasure ρ]
    (F : A × R → A × R) (hF : Measurable F) (L : Kernel A A)
    (hlaw : ∀ a, Measure.map (fun r => F (a, r)) ρ = (L a).prod ρ)
    (n : ℕ) (a : A) :
    Measure.map (fun r => F^[n] (a, r)) ρ = (iterateKernel L n a).prod ρ := by
  have h := congrArg (fun K : Kernel A (A × R) => K a)
    (iterateKernel_intertwining _ _ _ (deterministicResidual_intertwining ρ F hF L hlaw) n)
  rw [iterateKernel_deterministic, Kernel.deterministic_comp_eq_map] at h
  dsimp only at h
  rw [Kernel.map_apply _ (hF.iterate n), freshResidualKernel_apply, Measure.dirac_prod,
    Measure.map_map (hF.iterate n) measurable_prodMk_left, freshResidualKernel_comp_apply] at h
  exact h

theorem deterministicResidual_observed_iterate_law (ρ : Measure R) [IsProbabilityMeasure ρ]
    (F : A × R → A × R) (hF : Measurable F) (L : Kernel A A)
    (hlaw : ∀ a, Measure.map (fun r => F (a, r)) ρ = (L a).prod ρ)
    (n : ℕ) (a : A) :
    Measure.map (fun r => (F^[n] (a, r)).1) ρ = iterateKernel L n a := by
  have h := congrArg (Measure.map (Prod.fst : A × R → A))
    (deterministicResidual_iterate_law ρ F hF L hlaw n a)
  have hm : Measurable (fun r : R => F^[n] (a, r)) := (hF.iterate n).comp measurable_prodMk_left
  rw [Measure.map_map measurable_fst hm,
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

end StochasticMatching
