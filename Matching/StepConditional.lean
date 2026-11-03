import Matching.StepObservation
import Matching.TerminalConditional
import Matching.ConditionalObservation

/-! A single conditional-expectation identity on the original sample space
after the full tagged first-step observation. Terminal and completion branches
are combined, rather than conditioned on separately in the final statement.
-/

open MeasureTheory Set

namespace StochasticMatching.HistoryServiceFamily

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : HistoryServiceFamily H ι)

noncomputable def posteriorValue (f : H × (ι → ℝ) → ℝ)
    (x : (H × ℝ) × StepTag ι) : ℝ :=
  match x.2 with
  | none => 0
  | some none => ∫ z, f (reconstructDemands p.terminalThreshold (x.1.1, z)) ∂independentExponentials
  | some (some j) => ∫ z, f (p.reconstructMarked j (x.1, z)) ∂independentExponentials

theorem measurable_posteriorValue {f : H × (ι → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (p.posteriorValue f) := by
  apply measurable_from_prod_countable
  intro tag
  cases tag with
  | none => exact measurable_const
  | some b =>
    cases b with
    | none =>
      exact ((hf.comp (measurable_reconstructDemands p.measurable_terminalThreshold)).stronglyMeasurable.integral_prod_right').measurable.comp measurable_fst
    | some j =>
      exact ((hf.comp (p.measurable_reconstructMarked j)).stronglyMeasurable.integral_prod_right').measurable

theorem observed_conditionalExpectation (ν : Measure H) [IsFiniteMeasure ν]
    (f : H × (ι → ℝ) → ℝ) (hf : Measurable f) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (p.posteriorValue f ∘ p.observedHistory) =ᵐ[ν.prod independentExponentials]
      (ν.prod independentExponentials)[f |
        (inferInstance : MeasurableSpace ((H × ℝ) × StepTag ι)).comap p.observedHistory] := by
  have hfi : Integrable f (ν.prod independentExponentials) := by
    exact (integrable_const B).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  apply conditionalExpectation_of_branch_cover (ν.prod independentExponentials)
    p.measurable_observedHistory.comap_le p.branchEvent p.branchEvent_observable
    (p.branchEvent_cover ν) hfi
  intro b
  cases b with
  | none =>
    let q : H → (H × ℝ) × StepTag ι := fun h => ((h, (p.curves h).deadline), some none)
    have hq : Measurable q := (measurable_id.prodMk p.deadline_measurable).prodMk measurable_const
    have hrel : p.observedHistory =ᵐ[(ν.prod independentExponentials).restrict p.terminalEvent]
        q ∘ Prod.fst := by
      filter_upwards [ae_restrict_mem p.measurable_terminalEvent] with x hx
      exact p.observedHistory_of_event (b := none) hx
    have hc : (p.posteriorValue f ∘ p.observedHistory) =ᵐ[
        (ν.prod independentExponentials).restrict p.terminalEvent]
        (fun x => ∫ z, f (reconstructDemands p.terminalThreshold (x.1, z)) ∂independentExponentials) := by
      filter_upwards [hrel] with x hx
      change p.posteriorValue f (p.observedHistory x) = _
      rw [hx]
      rfl
    exact conditionalExpectation_of_observation
      ((ν.prod independentExponentials).restrict p.terminalEvent)
      Prod.fst measurable_fst p.observedHistory p.measurable_observedHistory q hq hrel
      (p.posteriorValue f) (p.measurable_posteriorValue hf) hfi.restrict
      (hc.trans (p.terminal_conditionalExpectation ν f hf hB))
  | some j =>
    let X : H × (ι → ℝ) → H × ℝ := fun x => (x.1, p.clock j x)
    have hX : Measurable X := measurable_fst.prodMk (p.measurable_clock j)
    let q : H × ℝ → (H × ℝ) × StepTag ι := fun h => (h, some (some j))
    have hq : Measurable q := measurable_id.prodMk measurable_const
    have hrel : p.observedHistory =ᵐ[(ν.prod independentExponentials).restrict (p.winner j)]
        q ∘ X := by
      filter_upwards [ae_restrict_mem (p.measurable_winner j)] with x hx
      exact p.observedHistory_of_event (b := some j) hx
    have hc : (p.posteriorValue f ∘ p.observedHistory) =ᵐ[
        (ν.prod independentExponentials).restrict (p.winner j)]
        (fun x => ∫ z, f (p.reconstructMarked j ((x.1, p.clock j x), z)) ∂independentExponentials) := by
      filter_upwards [hrel] with x hx
      change p.posteriorValue f (p.observedHistory x) = _
      rw [hx]
      rfl
    exact conditionalExpectation_of_observation
      ((ν.prod independentExponentials).restrict (p.winner j))
      X hX p.observedHistory p.measurable_observedHistory q hq hrel
      (p.posteriorValue f) (p.measurable_posteriorValue hf) hfi.restrict
      (hc.trans (p.completion_conditionalExpectation ν j f hf hB))

end StochasticMatching.HistoryServiceFamily
