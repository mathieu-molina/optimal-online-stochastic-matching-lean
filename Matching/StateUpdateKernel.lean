import Matching.FiniteKernelIteration
import Mathlib.Probability.Kernel.Composition.Prod

/-! Updating a remembered state with a sampled event, together with its
projection law. The state may contain an entire finite history.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A B E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace E] [MeasurableSpace F]

noncomputable def stateUpdateKernel (K : Kernel A E) [IsSFiniteKernel K]
    (U : A × E → A) : Kernel A A := (Kernel.id ×ₖ K).map U

theorem stateUpdateKernel_apply (K : Kernel A E) [IsSFiniteKernel K]
    (U : A × E → A) (hU : Measurable U) (a : A) :
    stateUpdateKernel K U a = Measure.map (fun e => U (a, e)) (K a) := by
  unfold stateUpdateKernel
  rw [Kernel.map_apply _ hU, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map hU measurable_prodMk_left]
  rfl

theorem stateUpdateKernel_markov (K : Kernel A E) [IsMarkovKernel K]
    (U : A × E → A) (hU : Measurable U) : IsMarkovKernel (stateUpdateKernel K U) := by
  apply Kernel.IsMarkovKernel.map _ hU

theorem stateUpdateKernel_projection (K : Kernel A E) [IsSFiniteKernel K]
    (L : Kernel B F) [IsSFiniteKernel L]
    (U : A × E → A) (hU : Measurable U) (V : B × F → B) (hV : Measurable V)
    (f : A → B) (hf : Measurable f) (g : E → F) (hg : Measurable g)
    (hK : ∀ a, Measure.map g (K a) = L (f a))
    (hUV : ∀ a e, f (U (a, e)) = V (f a, g e)) (a : A) :
    Measure.map f (stateUpdateKernel K U a) = stateUpdateKernel L V (f a) := by
  have hu : Measurable (fun e => U (a, e)) := hU.comp measurable_prodMk_left
  have hv : Measurable (fun e => V (f a, e)) := hV.comp measurable_prodMk_left
  rw [stateUpdateKernel_apply K U hU, Measure.map_map hf hu,
    stateUpdateKernel_apply L V hV, ← hK a,
    Measure.map_map hv hg]
  congr 1
  funext e
  exact hUV a e

theorem stateUpdateKernel_iterate_projection (K : Kernel A E) [IsSFiniteKernel K]
    (L : Kernel B F) [IsSFiniteKernel L]
    (U : A × E → A) (hU : Measurable U) (V : B × F → B) (hV : Measurable V)
    (f : A → B) (hf : Measurable f) (g : E → F) (hg : Measurable g)
    (hK : ∀ a, Measure.map g (K a) = L (f a))
    (hUV : ∀ a e, f (U (a, e)) = V (f a, g e)) (n : ℕ) (a : A) :
    Measure.map f (iterateKernel (stateUpdateKernel K U) n a) =
      iterateKernel (stateUpdateKernel L V) n (f a) :=
  iterateKernel_projection _ _ f hf
    (stateUpdateKernel_projection K L U hU V hV f hf g hg hK hUV) n a

end StochasticMatching
