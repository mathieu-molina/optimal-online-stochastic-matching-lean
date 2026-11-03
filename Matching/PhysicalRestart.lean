import Matching.FirstEventRestart
import Matching.ResidualStateBookkeeping
import Matching.InitialState

/-! The fixed-coordinate restart preserves the original job demands and
produces a valid service/completion state. The rejection clock is auxiliary;
its recycling into a completed coordinate cannot alter any unfinished job.
-/
open MeasureTheory Set
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def physicalAfterEvent (p : ServiceCurveFamily (Option ι)) (s : CompletionState ι) :
    Unit ⊕ (ℝ × Option ι) → CompletionState ι
  | .inl _ => s.afterService (fun i => p.service (some i) p.deadline)
  | .inr (t, none) => s.afterService (fun i => p.service (some i) t)
  | .inr (t, some j) => s.afterCompletion (fun i => p.service (some i) t) j

theorem recycledObservation_pos (p : ServiceCurveFamily (Option ι)) (j : Option ι)
    {z : Option ι → ℝ} (hw : z ∈ variableWinner p.service p.deadline j) (i : ι) :
    0 < (recycledObservation p j z).2 i :=
  sub_pos.mpr (p.winner_other_service_lt hw (survivorSlot j i).property)

theorem physical_winner_preserves_demands (p : ServiceCurveFamily (Option ι))
    (s : CompletionState ι) (z : Option ι → ℝ) (j : Option ι)
    (hz : ∀ i, 0 < z i)
    (hfrozen : ∀ i ∈ s.completed, ∀ t ∈ Icc 0 p.deadline, p.service (some i) t = 0)
    (hw : z ∈ variableWinner p.service p.deadline j) :
    (physicalAfterEvent p s (.inr ((recycledObservation p j z).1, j))).originalDemands
        (recycledObservation p j z).2 = s.originalDemands (fun i => z (some i)) := by
  have ht := cappedHit_bounds (z := z j) (p.service_continuous j) p.deadline_pos.le
  cases j with
  | none =>
    apply CompletionState.afterService_originalDemands
    · intro i hi
      exact hfrozen i hi _ ht
    · intro i _
      simp [recycledObservation]
  | some j =>
    have hj : j ∉ s.completed := by
      intro hj
      have he := p.winner_service_eq (hz (some j)) hw
      rw [hfrozen j hj _ ht] at he
      exact (hz (some j)).ne he
    apply CompletionState.afterCompletion_originalDemands _ _ _ _ j hj
    · intro i hi
      exact hfrozen i hi _ ht
    · exact p.winner_service_eq (hz (some j)) hw
    · intro i hi
      have hij : i ≠ j := by
        intro he
        subst i
        exact hi (Finset.mem_insert_self _ _)
      simp [recycledObservation, survivorSlot_other j i hij]

theorem physical_winner_valid (p : ServiceCurveFamily (Option ι))
    (s : CompletionState ι) (z : Option ι → ℝ) (j : Option ι)
    (hs : ∀ i, 0 ≤ s.served i) (hz : ∀ i, 0 < z i)
    (hfrozen : ∀ i ∈ s.completed, ∀ t ∈ Icc 0 p.deadline, p.service (some i) t = 0)
    (hw : z ∈ variableWinner p.service p.deadline j) :
    CompletionState.Valid (s.originalDemands (fun i => z (some i)))
      (physicalAfterEvent p s (.inr ((recycledObservation p j z).1, j))) := by
  rw [← physical_winner_preserves_demands p s z j hz hfrozen hw]
  apply CompletionState.valid_originalDemands
  · intro i
    have ht := cappedHit_bounds (z := z j) (p.service_continuous j) p.deadline_pos.le
    have hn := add_nonneg (hs i) (p.service_nonneg ht (some i))
    cases j <;> exact hn
  · intro i _
    exact recycledObservation_pos p j hw i

variable [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]

theorem physical_terminal_preserves_demands (p : ServiceCurveFamily (Option ι))
    (s : CompletionState ι) (z : Option ι → ℝ)
    (hfrozen : ∀ i ∈ s.completed, ∀ t ∈ Icc 0 p.deadline, p.service (some i) t = 0) :
    (physicalAfterEvent p s (.inl ())).originalDemands (terminalResidual p z) =
      s.originalDemands (fun i => z (some i)) := by
  apply CompletionState.afterService_originalDemands
  · intro i hi
    exact hfrozen i hi _ ⟨p.deadline_pos.le, le_rfl⟩
  · intro i _
    rfl

theorem physical_terminal_valid (p : ServiceCurveFamily (Option ι))
    (s : CompletionState ι) (z : Option ι → ℝ) (hs : ∀ i, 0 ≤ s.served i)
    (hfrozen : ∀ i ∈ s.completed, ∀ t ∈ Icc 0 p.deadline, p.service (some i) t = 0)
    (hz : z ∈ p.terminalSurvival) :
    CompletionState.Valid (s.originalDemands (fun i => z (some i)))
      (physicalAfterEvent p s (.inl ())) := by
  rw [← physical_terminal_preserves_demands p s z hfrozen]
  apply CompletionState.valid_originalDemands
  · intro i
    exact add_nonneg (hs i) (p.service_nonneg ⟨p.deadline_pos.le, le_rfl⟩ (some i))
  · intro i _
    exact sub_pos.mpr (mem_univ_pi.mp hz (some i))

theorem physical_restart_valid_ae (p : ServiceCurveFamily (Option ι))
    (s : CompletionState ι) (hs : ∀ i, 0 ≤ s.served i)
    (hfrozen : ∀ i ∈ s.completed, ∀ t ∈ Icc 0 p.deadline, p.service (some i) t = 0) :
    ∀ᵐ z ∂(independentExponentials (ι := Option ι)),
      let e := firstEventRestart p z
      let s' := physicalAfterEvent p s e.1
      s'.originalDemands e.2 = s.originalDemands (fun i => z (some i)) ∧
      CompletionState.Valid (s.originalDemands (fun i => z (some i))) s' := by
  filter_upwards [p.no_completion_or_unique_ae, independentExponentials_ae_pos (ι := Option ι)] with z hw hz
  rcases hw with ht | ⟨j, hj, _⟩
  · rw [firstEventRestart_of_terminal p ht]
    exact ⟨physical_terminal_preserves_demands p s z hfrozen,
      physical_terminal_valid p s z hs hfrozen ht⟩
  · rw [firstEventRestart_of_winner p j hj]
    exact ⟨physical_winner_preserves_demands p s z j hz hfrozen hj,
      physical_winner_valid p s z j hs hz hfrozen hj⟩

end StochasticMatching
