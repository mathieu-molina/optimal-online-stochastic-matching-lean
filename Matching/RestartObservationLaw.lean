import Matching.TerminalPayload
import Matching.HistoryFirstEventRestart

/-! A pathwise conserved observation of a residual restart gives a harmonic
observation kernel, hence an invariant law through every finite iteration.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching
variable {H E J : Type*} [MeasurableSpace H] [MeasurableSpace E]
  [Fintype J] [DecidableEq J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem restart_observation_harmonic (p : HistoryServiceFamily H (Option J))
    (U : H × (Unit ⊕ (ℝ × Option J)) → H) (hU : Measurable U)
    (F : H × (J → ℝ) → E) (hF : Measurable F)
    (hpres : ∀ h, ∀ᵐ z ∂(independentExponentials (ι := Option J)),
      F (U (h, (historyRestart p (h, z)).1), (historyRestart p (h, z)).2) =
        F (h, fun j => z (some j))) :
    residualObservationKernel (independentExponentials (ι := J)) F ∘ₖ
      eventUpdateKernel (historyEventKernel p) U =
        residualObservationKernel (independentExponentials (ι := J)) F := by
  ext h : 1
  rw [residualObservationKernel_comp_apply _ F hF, residualObservationKernel_apply _ F hF]
  have hp : Measurable (fun z : Option J → ℝ => historyRestart p (h, z)) :=
    (measurable_historyRestart p).comp measurable_prodMk_left
  have hu : Measurable (fun z : Option J → ℝ =>
      (U (h, (historyRestart p (h, z)).1), (historyRestart p (h, z)).2)) :=
    (hU.comp (measurable_const.prodMk hp.fst)).prodMk hp.snd
  rw [← historyRestart_update_law p U hU h, Measure.map_map hF hu]
  have he : F ∘ (fun z : Option J → ℝ =>
      (U (h, (historyRestart p (h, z)).1), (historyRestart p (h, z)).2)) =ᵐ[independentExponentials]
      (fun z : Option J → ℝ => F (h, fun j => z (some j))) := hpres h
  rw [Measure.map_congr he]
  have hr : Measurable (fun z : Option J → ℝ => fun j : J => z (some j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (some j))
  have hfh : Measurable (fun r : J → ℝ => F (h, r)) := hF.comp measurable_prodMk_left
  change Measure.map ((fun r : J → ℝ => F (h, r)) ∘ (fun z : Option J → ℝ => fun j : J => z (some j)))
    independentExponentials = _
  rw [← Measure.map_map hfh hr, independentExponentials_injective_coordinates Option.some (Option.some_injective J)]

theorem restart_observation_iterate (p : HistoryServiceFamily H (Option J))
    (U : H × (Unit ⊕ (ℝ × Option J)) → H) (hU : Measurable U)
    (F : H × (J → ℝ) → E) (hF : Measurable F)
    (hpres : ∀ h, ∀ᵐ z ∂(independentExponentials (ι := Option J)),
      F (U (h, (historyRestart p (h, z)).1), (historyRestart p (h, z)).2) =
        F (h, fun j => z (some j))) (n : ℕ) :
    residualObservationKernel (independentExponentials (ι := J)) F ∘ₖ
      iterateKernel (eventUpdateKernel (historyEventKernel p) U) n =
        residualObservationKernel (independentExponentials (ι := J)) F :=
  kernel_harmonic_iterate _ _ (restart_observation_harmonic p U hU F hF hpres) n

end StochasticMatching
