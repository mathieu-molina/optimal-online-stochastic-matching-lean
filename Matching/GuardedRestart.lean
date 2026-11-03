import Matching.GuardedArrivalUpdate
import Matching.FirstEventRestart

/-! The totality guard never changes an actual first-event restart, even on
the default terminal branch. -/
open MeasureTheory Set
namespace StochasticMatching
variable {H J : Type*} [MeasurableSpace H] [Fintype J] [DecidableEq J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem guardedEventUpdate_restart (D : H → ℝ)
    (U : H × (Unit ⊕ (ℝ × Option J)) → Unit ⊕ H) (h : H)
    (hterm : U (h, .inl ()) = .inl ()) (p : ServiceCurveFamily (Option J))
    (hD : D h = p.deadline) (z : Option J → ℝ) :
    guardedEventUpdate D U (h, (firstEventRestart p z).1) = U (h, (firstEventRestart p z).1) := by
  classical
  by_cases hw : ∃ a, z ∈ variableWinner p.service p.deadline a
  · obtain ⟨a, ha⟩ := hw
    rw [firstEventRestart_of_winner p a ha]
    apply guardedEventUpdate_of_valid
    · exact (cappedHit_bounds (p.service_continuous a) p.deadline_pos.le).1
    · rw [hD]
      exact ha.1
  · have hn := not_exists.mp hw
    rw [firstEventRestart, branchSelect_of_not_mem _ _ hn]
    exact hterm.symm

end StochasticMatching
