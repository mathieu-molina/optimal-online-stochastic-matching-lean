import Matching.FiniteKernelIteration
import Mathlib.Probability.Kernel.Composition.Prod

/-! Iteration with latent randomness: a kernel inserts fresh residuals, and
a transition preserves their conditional distribution given the history.
-/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A B R : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace R]

theorem iterateKernel_intertwining (K : Kernel A A) (L : Kernel B B) (J : Kernel B A)
    (hstep : K ∘ₖ J = J ∘ₖ L) (n : ℕ) :
    iterateKernel K n ∘ₖ J = J ∘ₖ iterateKernel L n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iterateKernel_succ, Kernel.comp_assoc, ih, ← Kernel.comp_assoc, hstep,
        Kernel.comp_assoc, ← iterateKernel_succ]

noncomputable def freshResidualKernel (ρ : Measure R) : Kernel A (A × R) :=
  Kernel.id ×ₖ Kernel.const A ρ

theorem freshResidualKernel_apply (ρ : Measure R) [SFinite ρ] (a : A) :
    freshResidualKernel ρ a = (Measure.dirac a).prod ρ := by
  rw [freshResidualKernel, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]

instance freshResidualKernel_markov (ρ : Measure R) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (freshResidualKernel (A := A) ρ) := by unfold freshResidualKernel; infer_instance

theorem freshResidualKernel_fst (ρ : Measure R) [IsProbabilityMeasure ρ] :
    (freshResidualKernel (A := A) ρ).map Prod.fst = Kernel.id := by
  rw [← Kernel.fst_eq, freshResidualKernel, Kernel.fst_prod]

theorem latent_iterate_history_law (ρ : Measure R) [IsProbabilityMeasure ρ]
    (K : Kernel (A × R) (A × R)) (L : Kernel A A)
    (hstep : K ∘ₖ freshResidualKernel ρ = freshResidualKernel ρ ∘ₖ L) (n : ℕ) :
    (iterateKernel K n ∘ₖ freshResidualKernel ρ).map Prod.fst = iterateKernel L n := by
  rw [iterateKernel_intertwining K L _ hstep n, Kernel.map_comp,
    freshResidualKernel_fst, Kernel.id_comp]

end StochasticMatching
