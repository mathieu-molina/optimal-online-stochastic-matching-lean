import Matching.ShiftedService
import Matching.FirstEventDistribution
import Matching.RejectionClockService

/-! Pathwise removal of rejected arrivals: shifting an unfinished service
segment preserves the next genuine job event and its absolute time.
-/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.ServiceCurveFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem afterTime_winner_iff (p : ServiceCurveFamily ι) (s : ℝ) (hs0 : 0 ≤ s)
    (hsT : s < p.deadline) (z : ι → ℝ) (hz : ∀ i, p.service i s < z i) (j : ι) :
    (fun i => z i - p.service i s) ∈ variableWinner (p.afterTime s hs0 hsT).service
      (p.afterTime s hs0 hsT).deadline j ↔ z ∈ variableWinner p.service p.deadline j := by
  have hc : ∀ i, cappedHit ((p.afterTime s hs0 hsT).service i) (p.afterTime s hs0 hsT).deadline
      (z i - p.service i s) = cappedHit (p.service i) p.deadline (z i) - s :=
    fun i => p.afterTime_clock s hs0 hsT i (hz i)
  have hc' : ∀ i, cappedHit (fun u => p.service i (s + u) - p.service i s)
      (p.deadline - s) (z i - p.service i s) = cappedHit (p.service i) p.deadline (z i) - s := hc
  simp only [variableWinner, mem_setOf_eq, afterTime]
  simp only [hc', sub_lt_sub_iff_right]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem afterTime_firstEvent (p : ServiceCurveFamily ι) (s : ℝ) (hs0 : 0 ≤ s)
    (hsT : s < p.deadline) (z : ι → ℝ) (hz : ∀ i, p.service i s < z i) :
    (p.afterTime s hs0 hsT).firstEvent (fun i => z i - p.service i s) =
      Sum.map id (Prod.map (fun t => t - s) id) (p.firstEvent z) := by
  classical
  by_cases hw : ∃ j, z ∈ variableWinner p.service p.deadline j
  · obtain ⟨j, hj⟩ := hw
    have hj' := (p.afterTime_winner_iff s hs0 hsT z hz j).mpr hj
    rw [(p.afterTime s hs0 hsT).firstEvent_of_winner j hj', p.firstEvent_of_winner j hj,
      p.afterTime_clock s hs0 hsT j (hz j)]
    rfl
  · have hn : ∀ j, z ∉ variableWinner p.service p.deadline j := not_exists.mp hw
    have hn' : ∀ j, (fun i => z i - p.service i s) ∉ variableWinner
        (p.afterTime s hs0 hsT).service (p.afterTime s hs0 hsT).deadline j :=
      fun j h => hn j ((p.afterTime_winner_iff s hs0 hsT z hz j).mp h)
    rw [firstEvent, firstEvent, branchSelect_of_not_mem _ _ hn', branchSelect_of_not_mem _ _ hn]
    rfl

theorem rejection_preserves_first_job (p : ServiceCurveFamily ι) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 p.deadline, ∑ i, p.rate i t ≤ Λ)
    (z : Option ι → ℝ)
    (hw : z ∈ variableWinner (p.withRejectionClock Λ hΛ).service p.deadline none) :
    let t := cappedHit ((p.withRejectionClock Λ hΛ).service none) p.deadline (z none)
    ∃ ht0 : 0 ≤ t, ∃ htT : t < p.deadline,
      (p.afterTime t ht0 htT).firstEvent (fun i => z (some i) - p.service i t) =
        Sum.map id (Prod.map (fun u => u - t) id) (p.firstEvent (fun i => z (some i))) := by
  intro t
  let q := p.withRejectionClock Λ hΛ
  have ht0 : 0 ≤ t := (cappedHit_bounds (q.service_continuous none) p.deadline_pos.le).1
  have htT : t < p.deadline := hw.1
  refine ⟨ht0, htT, p.afterTime_firstEvent t ht0 htT (fun i => z (some i)) ?_⟩
  intro i
  exact q.winner_other_service_lt hw (by simp : some i ≠ none)

end StochasticMatching.ServiceCurveFamily
