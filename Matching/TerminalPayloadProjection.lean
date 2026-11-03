import Matching.TerminalPayload
import Matching.StoppedKernel

/-! Retaining a terminal output does not change the underlying stopped state
trajectory when the output is forgotten. -/
open MeasureTheory Set ProbabilityTheory
namespace StochasticMatching
variable {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]

def forgetTerminal : E ⊕ A → Unit ⊕ A := Sum.map (fun _ => ()) id

theorem measurable_forgetTerminal : Measurable (forgetTerminal (E := E) (A := A)) :=
  measurable_const.sumMap measurable_id

theorem forgetTerminal_fill (e : E) (u : Unit ⊕ A) :
    forgetTerminal (fillTerminal (e, u)) = u := by
  cases u with
  | inl u => cases u; rfl
  | inr _ => rfl

theorem terminalPayload_kernel_projection (K : Kernel (E ⊕ A) (E ⊕ A))
    (L : Kernel A (Unit ⊕ A)) (O : A → E)
    (hterminal : ∀ e, K (.inl e) = Measure.dirac (.inl e))
    (hlive : ∀ a, K (.inr a) = Measure.map (fun u => fillTerminal (O a, u)) (L a))
    (b : E ⊕ A) :
    Measure.map forgetTerminal (K b) = absorbingKernel L (forgetTerminal b) := by
  cases b with
  | inl e =>
    rw [hterminal e, Measure.map_dirac measurable_forgetTerminal]
    rfl
  | inr a =>
    have hm : Measurable (fun u : Unit ⊕ A => fillTerminal (O a, u)) :=
      measurable_fillTerminal.comp (measurable_const.prodMk measurable_id)
    rw [hlive a, Measure.map_map measurable_forgetTerminal hm]
    change Measure.map (fun u => forgetTerminal (fillTerminal (O a, u))) (L a) = L a
    simp only [forgetTerminal_fill]
    exact Measure.map_id

theorem terminalPayload_trajectory_projection (K : Kernel (E ⊕ A) (E ⊕ A)) [IsMarkovKernel K]
    (L : Kernel A (Unit ⊕ A)) [IsMarkovKernel L] (O : A → E)
    (hterminal : ∀ e, K (.inl e) = Measure.dirac (.inl e))
    (hlive : ∀ a, K (.inr a) = Measure.map (fun u => fillTerminal (O a, u)) (L a))
    (b : E ⊕ A) :
    Measure.map (fun z : ℕ → E ⊕ A => fun k => forgetTerminal (z k)) (markovTrajectory K b) =
      markovTrajectory (absorbingKernel L) (forgetTerminal b) :=
  markovTrajectory_projection K (absorbingKernel L) forgetTerminal measurable_forgetTerminal
    (terminalPayload_kernel_projection K L O hterminal hlive) b

end StochasticMatching
