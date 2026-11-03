import Matching.VariableRacePartition
import Matching.ActiveCoordinates
import Matching.IntegratedSegment

/-! Convert a first-completion event of concrete service curves into the
valid, bounded state transitions used by the finite-execution bookkeeping.
Original job labels are retained and completed coordinates stay frozen.
-/

open MeasureTheory Set
open scoped BigOperators

namespace StochasticMatching

instance activeFintype {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Finset ι) :
    Fintype (Active D) := inferInstanceAs (Fintype {i : ι // i ∉ D})

instance activeDecidableEq {ι : Type*} [DecidableEq ι] (D : Finset ι) :
    DecidableEq (Active D) := inferInstanceAs (DecidableEq {i : ι // i ∉ D})

namespace ServiceCurveFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

theorem service_nonneg {t : ℝ} (ht : t ∈ Icc 0 p.deadline) (i : ι) : 0 ≤ p.service i t := by
  rw [← p.service_zero i]
  exact p.service_monotone i ⟨le_refl _, p.deadline_pos.le⟩ ht ht.1

theorem service_eq_integral {t : ℝ} (ht : t ∈ Icc 0 p.deadline) (i : ι) :
    p.service i t = ∫ u in (0 : ℝ)..t, p.rate i u := by
  have hd : ∀ u ∈ uIcc 0 t, HasDerivAt (p.service i) (p.rate i u) u := by
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact p.service_deriv i u ⟨hu.1, hu.2.trans ht.2⟩
  simpa only [p.service_zero, sub_zero] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((p.rate_continuous i).intervalIntegrable 0 t)).symm

theorem service_le {M t : ℝ} (ht : t ∈ Icc 0 p.deadline)
    (hM : ∀ i u, u ∈ Icc 0 p.deadline → p.rate i u ≤ M) (i : ι) :
    p.service i t ≤ M * t := by
  rw [p.service_eq_integral ht i]
  have h := segmentWork_le (r := fun u i => p.rate i u) ht.1
    (fun i => (p.rate_continuous i).intervalIntegrable 0 t)
    (fun i u hu => hM i u ⟨hu.1, hu.2.trans ht.2⟩) i
  simpa only [segmentWork, sub_zero] using h

theorem winner_service_eq {z : ι → ℝ} {j : ι} (hz : 0 < z j)
    (hj : z ∈ variableWinner p.service p.deadline j) :
    p.service j (cappedHit (p.service j) p.deadline (z j)) = z j := by
  have ht := cappedHit_bounds (z := z j) (p.service_continuous j) p.deadline_pos.le
  have hd := (cappedHit_le_iff (p.service_continuous j) p.deadline_pos.le
    (p.service_monotone j) ht.1 hj.1).mp (le_refl _)
  apply service_at_cappedHit (p.service_continuous j) p.deadline_pos.le (p.service_monotone j)
  · rw [p.service_zero]; exact hz.le
  · exact hd.trans (p.service_monotone j ht ⟨p.deadline_pos.le, le_refl _⟩ ht.2)

theorem winner_other_service_lt {z : ι → ℝ} {j i : ι}
    (hj : z ∈ variableWinner p.service p.deadline j) (hij : i ≠ j) :
    p.service i (cappedHit (p.service j) p.deadline (z j)) < z i :=
  service_below_demand_before_hit (p.service_continuous i) p.deadline_pos.le
    (p.service_monotone i) (cappedHit_bounds (p.service_continuous j) p.deadline_pos.le).1
    (hj.2 i hij)

end ServiceCurveFamily

namespace CompletionState

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def activeResidual (s : CompletionState ι) (z : ι → ℝ) (i : Active s.completed) : ℝ :=
  z i.1 - s.served i.1

noncomputable def curveClock (s : CompletionState ι) (z : ι → ℝ)
    (p : ServiceCurveFamily (Active s.completed)) (j : Active s.completed) : ℝ :=
  cappedHit (p.service j) p.deadline (s.activeResidual z j)

noncomputable def afterCurveCompletion (s : CompletionState ι) (z : ι → ℝ)
    (p : ServiceCurveFamily (Active s.completed)) (j : Active s.completed) : CompletionState ι :=
  s.afterCompletion (liftActive s.completed (fun i => p.service i (s.curveClock z p j))) j.1

theorem afterCurveCompletion_valid {z : ι → ℝ} {s : CompletionState ι} (hs : Valid z s)
    (p : ServiceCurveFamily (Active s.completed)) (j : Active s.completed)
    (hw : s.activeResidual z ∈ variableWinner p.service p.deadline j) :
    Valid z (s.afterCurveCompletion z p j) := by
  have ht := cappedHit_bounds (z := s.activeResidual z j) (p.service_continuous j) p.deadline_pos.le
  apply afterCompletion_valid hs _ j.1
  · exact liftActive_nonneg _ _ (p.service_nonneg ht)
  · intro i hi
    exact liftActive_of_completed _ _ hi
  · rw [liftActive_of_active]
    have h := p.winner_service_eq (sub_pos.mpr (valid_unfinished_lt hs j.2)) hw
    change p.service j (s.curveClock z p j) = z j.1 - s.served j.1 at h
    linarith
  · intro i hi
    have hiD : i ∉ s.completed := fun h => hi (Finset.mem_insert_of_mem h)
    let a : Active s.completed := ⟨i, hiD⟩
    have haj : a ≠ j := by
      intro heq
      exact hi (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val heq)))
    have h := p.winner_other_service_lt hw haj
    change p.service a (s.curveClock z p j) < z i - s.served i at h
    have heq : liftActive s.completed (fun k => p.service k (s.curveClock z p j)) i =
        p.service a (s.curveClock z p j) := liftActive_of_active _ _ a
    rw [heq]
    linarith

theorem afterCurveCompletion_step (s : CompletionState ι) (z : ι → ℝ)
    (p : ServiceCurveFamily (Active s.completed)) (j : Active s.completed) :
    CompletionStep s (s.afterCurveCompletion z p j) := by
  have ht := cappedHit_bounds (z := s.activeResidual z j) (p.service_continuous j) p.deadline_pos.le
  exact afterCompletion_step s _ j.1 j.2 (liftActive_nonneg _ _ (p.service_nonneg ht))
    (fun _ hi => liftActive_of_completed _ _ hi)

theorem curveClock_pos {z : ι → ℝ} {s : CompletionState ι} (hs : Valid z s)
    (p : ServiceCurveFamily (Active s.completed)) (j : Active s.completed) :
    0 < s.curveClock z p j := by
  apply cappedHit_pos (p.service_continuous j) p.deadline_pos
  rw [p.service_zero]
  exact sub_pos.mpr (valid_unfinished_lt hs j.2)

theorem afterCurveCompletion_bounded (s : CompletionState ι) (z : ι → ℝ)
    (p : ServiceCurveFamily (Active s.completed)) (j : Active s.completed)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i t, t ∈ Icc 0 p.deadline → p.rate i t ≤ M) :
    BoundedCompletionStep M (s.curveClock z p j) s (s.afterCurveCompletion z p j) := by
  have ht := cappedHit_bounds (z := s.activeResidual z j) (p.service_continuous j) p.deadline_pos.le
  refine ⟨s.afterCurveCompletion_step z p j, ht.1, ?_⟩
  intro i
  change s.served i + liftActive s.completed (fun k => p.service k (s.curveClock z p j)) i -
    s.served i ≤ M * s.curveClock z p j
  rw [add_sub_cancel_left]
  by_cases hi : i ∈ s.completed
  · rw [liftActive_of_completed _ _ hi]
    exact mul_nonneg hM0 ht.1
  · let a : Active s.completed := ⟨i, hi⟩
    have heq : liftActive s.completed (fun k => p.service k (s.curveClock z p j)) i =
        p.service a (s.curveClock z p j) := liftActive_of_active _ _ a
    rw [heq]
    exact p.service_le ht hM a

end CompletionState
end StochasticMatching
