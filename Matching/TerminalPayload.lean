import Matching.MeasurableCursorBranches
import Matching.NoiseKernelFactorization

/-! Preserve an algorithm's actual output when it terminates, and expose a
general observation kernel for independently sampled residual coordinates.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A B C E R : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace E] [MeasurableSpace R]

def fillTerminal (x : E × (Unit ⊕ A)) : E ⊕ A :=
  Sum.elim (fun _ => .inl x.1) Sum.inr x.2

theorem measurable_fillTerminal : Measurable (fillTerminal (E := E) (A := A)) :=
  measurable_prod_sum_elim (fun x : E × Unit => (Sum.inl x.1 : E ⊕ A))
    (fun x : E × A => Sum.inr x.2) (measurable_inl.comp measurable_fst) (measurable_inr.comp measurable_snd)

def freezeTerminalUpdate (U : A × B → E ⊕ A) (x : (E ⊕ A) × B) : E ⊕ A :=
  Sum.elim Sum.inl (fun a => U (a, x.2)) x.1

theorem measurable_freezeTerminalUpdate (U : A × B → E ⊕ A) (hU : Measurable U) :
    Measurable (freezeTerminalUpdate U) :=
  measurable_sum_prod_elim (fun x : E × B => Sum.inl x.1) U (measurable_inl.comp measurable_fst) hU

def terminalObservation (F : A × R → E) (x : (E ⊕ A) × R) : E :=
  Sum.elim id (fun a => F (a, x.2)) x.1

theorem measurable_terminalObservation (F : A × R → E) (hF : Measurable F) :
    Measurable (terminalObservation F) :=
  measurable_sum_prod_elim (Prod.fst : E × R → E) F measurable_fst hF

theorem terminalObservation_filled (F : A × R → E) (e : E) (u : Unit ⊕ A) (r : R) :
    terminalObservation F (fillTerminal (e, u), r) = Sum.elim (fun _ => e) (fun a => F (a, r)) u := by
  cases u <;> rfl

theorem freshResidualKernel_comp_apply_general (ρ : Measure R) [SFinite ρ]
    (L : Kernel A B) (a : A) :
    (freshResidualKernel ρ ∘ₖ L) a = (L a).prod ρ := by
  ext S hS
  rw [Kernel.comp_apply' _ _ _ hS, Measure.prod_apply hS]
  apply lintegral_congr
  intro b
  rw [freshResidualKernel_apply, Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hS]

noncomputable def residualObservationKernel (ρ : Measure R) [SFinite ρ]
    (F : A × R → E) : Kernel A E := (freshResidualKernel ρ).map F

theorem residualObservationKernel_apply (ρ : Measure R) [SFinite ρ]
    (F : A × R → E) (hF : Measurable F) (a : A) :
    residualObservationKernel ρ F a = Measure.map (fun r => F (a, r)) ρ := by
  rw [residualObservationKernel, Kernel.map_apply _ hF, freshResidualKernel_apply,
    Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left]
  rfl

theorem residualObservationKernel_comp_apply (ρ : Measure R) [SFinite ρ]
    (F : B × R → E) (hF : Measurable F) (K : Kernel A B) (a : A) :
    (residualObservationKernel ρ F ∘ₖ K) a = Measure.map F ((K a).prod ρ) := by
  rw [residualObservationKernel, ← Kernel.map_comp, Kernel.map_apply _ hF,
    freshResidualKernel_comp_apply_general]

theorem kernel_harmonic_iterate (K : Kernel A A) (J : Kernel A E) (h : J ∘ₖ K = J) (n : ℕ) :
    J ∘ₖ iterateKernel K n = J := by
  induction n with
  | zero => rw [iterateKernel_zero, Kernel.comp_id]
  | succ n ih => rw [iterateKernel_succ, ← Kernel.comp_assoc, h, ih]

end StochasticMatching
