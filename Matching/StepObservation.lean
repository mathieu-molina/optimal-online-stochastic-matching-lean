import Matching.MeasurableBranching

/-! A full one-step observed history, including the branch label. A separate
exceptional tag makes the observation total and keeps every actual branch
observable; exceptional samples have measure zero by the established partition.
-/

open MeasureTheory Set

namespace StochasticMatching

def StepTag (ι : Type*) := Option (Option ι)

instance stepTagMeasurableSpace {ι : Type*} : MeasurableSpace (StepTag ι) := ⊤

instance stepTagMeasurableSingleton {ι : Type*} : MeasurableSingletonClass (StepTag ι) :=
  ⟨fun _ => trivial⟩

instance stepTagFintype {ι : Type*} [Fintype ι] : Fintype (StepTag ι) :=
  inferInstanceAs (Fintype (Option (Option ι)))

namespace HistoryServiceFamily

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : HistoryServiceFamily H ι)

def branchEvent : Option ι → Set (H × (ι → ℝ))
  | none => p.terminalEvent
  | some j => p.winner j

theorem measurable_branchEvent (b : Option ι) : MeasurableSet (p.branchEvent b) := by
  cases b with
  | none => exact p.measurable_terminalEvent
  | some j => exact p.measurable_winner j

theorem branchEvent_disjoint : Pairwise (fun a b => Disjoint (p.branchEvent a) (p.branchEvent b)) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => exact (hab rfl).elim
    | some j => exact p.winner_disjoint_terminal j
  | some i =>
    cases b with
    | none => exact (p.winner_disjoint_terminal i).symm
    | some j => exact p.winner_disjoint (fun h => hab (congrArg some h))

noncomputable def branchObservation (b : Option ι) (x : H × (ι → ℝ)) :
    (H × ℝ) × StepTag ι :=
  ((x.1, b.elim (p.curves x.1).deadline (fun j => p.clock j x)), some b)

theorem measurable_branchObservation (b : Option ι) : Measurable (p.branchObservation b) := by
  cases b with
  | none => exact (measurable_fst.prodMk (p.deadline_measurable.comp measurable_fst)).prodMk measurable_const
  | some j => exact (measurable_fst.prodMk (p.measurable_clock j)).prodMk measurable_const

noncomputable def observedHistory : H × (ι → ℝ) → (H × ℝ) × StepTag ι :=
  branchSelect p.branchEvent p.branchObservation (fun x => ((x.1, 0), none))

theorem measurable_observedHistory : Measurable p.observedHistory :=
  measurable_branchSelect p.branchEvent_disjoint p.measurable_branchEvent
    p.measurable_branchObservation ((measurable_fst.prodMk measurable_const).prodMk measurable_const)

theorem observedHistory_of_event {b : Option ι} {x : H × (ι → ℝ)} (hx : x ∈ p.branchEvent b) :
    p.observedHistory x = p.branchObservation b x :=
  branchSelect_of_mem p.branchEvent_disjoint _ _ hx

theorem observedHistory_tag_iff (b : Option ι) (x : H × (ι → ℝ)) :
    (p.observedHistory x).2 = (some b : StepTag ι) ↔ x ∈ p.branchEvent b := by
  classical
  constructor
  · intro ht
    by_cases he : ∃ c, x ∈ p.branchEvent c
    · obtain ⟨c, hc⟩ := he
      rw [p.observedHistory_of_event hc] at ht
      have hcb : c = b := Option.some.inj ht
      simpa only [hcb] using hc
    · have hobs : p.observedHistory x = ((x.1, 0), none) :=
        branchSelect_of_not_mem _ _ (not_exists.mp he)
      rw [hobs] at ht
      cases ht
  · intro hx
    rw [p.observedHistory_of_event hx]
    rfl

theorem branchEvent_observable (b : Option ι) :
    MeasurableSet[(inferInstance : MeasurableSpace ((H × ℝ) × StepTag ι)).comap p.observedHistory]
      (p.branchEvent b) := by
  have heq : p.branchEvent b = p.observedHistory ⁻¹'
      {y : (H × ℝ) × StepTag ι | y.2 = some b} := by
    ext x
    exact (p.observedHistory_tag_iff b x).symm
  rw [heq]
  exact (comap_measurable p.observedHistory) (measurable_snd (measurableSet_singleton _))

theorem branchEvent_cover (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, ∃ b, x ∈ p.branchEvent b := by
  filter_upwards [p.no_completion_or_unique_ae ν] with x hx
  rcases hx with ht | ⟨j, hj, _⟩
  · exact ⟨none, ht⟩
  · exact ⟨some j, hj⟩

end HistoryServiceFamily
end StochasticMatching
