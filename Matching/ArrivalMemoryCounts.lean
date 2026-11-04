import Matching.LoggedRoutingLaw

/-! Type counts read only the meaningful prefix of the retained arrival log. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

def arrivalTypeIndicator (s : σ) : Unit ⊕ (ℝ × σ) → ℕ :=
  Sum.elim (fun _ => 0) (fun e => if e.2 = s then 1 else 0)

theorem measurable_arrivalTypeIndicator (s : σ) : Measurable (arrivalTypeIndicator s) :=
  measurable_const.sumElim ((measurable_of_countable (fun a : σ => if a = s then 1 else 0)).comp measurable_snd)

def arrivalMemoryCounts (m : ArrivalMemory σ) (s : σ) : ℕ :=
  ∑ k ∈ Finset.range m.1, arrivalTypeIndicator s (m.2 k)

theorem measurable_arrivalMemoryCounts : Measurable (arrivalMemoryCounts (σ := σ)) := by
  apply measurable_pi_lambda
  intro s
  have hm : Measurable (fun x : ArrivalMemory σ × ℕ =>
      ∑ k ∈ Finset.range x.2, arrivalTypeIndicator s (x.1.2 k)) :=
    measurable_from_prod_countable (fun n => Finset.measurable_sum (Finset.range n) (fun k _ =>
      (measurable_arrivalTypeIndicator s).comp ((measurable_pi_apply k).comp measurable_snd)))
  exact hm.comp (measurable_id.prodMk measurable_fst)

theorem arrivalMemoryCounts_empty : arrivalMemoryCounts (emptyArrivalMemory σ) = 0 := by
  funext s
  simp [arrivalMemoryCounts, emptyArrivalMemory]

theorem arrivalMemoryCounts_append (m : ArrivalMemory σ) (e : Unit ⊕ (ℝ × σ)) (s : σ) :
    arrivalMemoryCounts (appendEvent (m, e)) s = arrivalMemoryCounts m s + arrivalTypeIndicator s e := by
  change (∑ k ∈ Finset.range (m.1 + 1), arrivalTypeIndicator s ((appendEvent (m, e)).2 k)) = _
  rw [Finset.sum_range_succ, appendEvent_at_last]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [appendEvent_preserves_prefix m e k (Finset.mem_range.mp hk)]

theorem arrivalMemoryCounts_append_arrival (m : ArrivalMemory σ) (t : ℝ) (j : σ) :
    arrivalMemoryCounts (appendEvent (m, .inr (t, j))) =
      Function.update (arrivalMemoryCounts m) j (arrivalMemoryCounts m j + 1) := by
  funext s
  rw [arrivalMemoryCounts_append]
  by_cases hs : s = j
  · subst s
    simp [arrivalTypeIndicator]
  · simp [arrivalTypeIndicator, hs, Ne.symm hs, Function.update_of_ne hs]

theorem arrivalMemoryCounts_append_total (m : ArrivalMemory σ) (t : ℝ) (j : σ) :
    (∑ s, arrivalMemoryCounts (appendEvent (m, .inr (t, j))) s) =
      (∑ s, arrivalMemoryCounts m s) + 1 := by
  simp_rw [arrivalMemoryCounts_append, arrivalTypeIndicator, Sum.elim_inr]
  rw [Finset.sum_add_distrib]
  simp

end StochasticMatching
