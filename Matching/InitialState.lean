import Matching.ExponentialResidual
import Matching.VectorResidual
import Matching.CompletionState

namespace StochasticMatching

variable {ι : Type*} [Fintype ι]

theorem independentExponentials_ae_pos :
    ∀ᵐ z ∂(independentExponentials (ι := ι)), ∀ i, 0 < z i := by
  apply Filter.eventually_all.mpr
  intro i
  exact (MeasureTheory.Measure.tendsto_eval_ae_ae
    (μ := fun _ : ι => unitExponential) (i := i)).eventually
    unitExponential_ae_pos

theorem initial_state_valid_ae :
    ∀ᵐ z ∂(independentExponentials (ι := ι)),
      CompletionState.Valid z CompletionState.initial := by
  filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
  exact CompletionState.initial_valid hz

end StochasticMatching
