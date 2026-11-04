import Matching.ArrivalMemoryCounts
import Matching.StoppedOutput

/-! Read the final live arrival log immediately before absorbing termination.
This reader uses only the observed trajectory, with no access to latent streams. -/
open MeasureTheory Set
namespace StochasticMatching
variable {A B σ : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def lastArrivalMemory (z : ℕ → Unit ⊕ (A × ArrivalMemory σ)) : ArrivalMemory σ :=
  Sum.elim (fun _ => emptyArrivalMemory σ) Prod.snd
    (z (firstEntryTime {a | a = .inl ()} z - 1))

theorem measurable_lastArrivalMemory : Measurable (lastArrivalMemory (A := A) (σ := σ)) := by
  have hS : MeasurableSet {a : Unit ⊕ (A × ArrivalMemory σ) | a = .inl ()} := by
    have he : {a : Unit ⊕ (A × ArrivalMemory σ) | a = .inl ()} =
        Set.range (Sum.inl : Unit → Unit ⊕ (A × ArrivalMemory σ)) := by
      ext a
      cases a with
      | inl u => cases u; simp
      | inr y => simp
    rw [he]
    exact measurableSet_range_inl
  have hm : Measurable (fun x : (ℕ → Unit ⊕ (A × ArrivalMemory σ)) × ℕ => x.1 x.2) :=
    measurable_from_prod_countable (fun n => measurable_pi_apply n)
  exact (measurable_const.sumElim measurable_snd).comp
    (hm.comp (measurable_id.prodMk ((measurable_of_countable (fun n : ℕ => n - 1)).comp
      (measurable_firstEntryTime _ hS))))

noncomputable def lastArrivalCounts (z : ℕ → Unit ⊕ (A × ArrivalMemory σ)) : σ → ℕ :=
  arrivalMemoryCounts (lastArrivalMemory z)

theorem measurable_lastArrivalCounts : Measurable (lastArrivalCounts (A := A) (σ := σ)) :=
  measurable_arrivalMemoryCounts.comp measurable_lastArrivalMemory

theorem firstEntryTime_eq_of_membership {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (S : Set X) (R : Set Y)
    (z : ℕ → X) (w : ℕ → Y) (h : ∀ n, z n ∈ S ↔ w n ∈ R) :
    firstEntryTime S z = firstEntryTime R w := by
  classical
  have he : firstEntryPredicate S z = firstEntryPredicate R w := by
    funext n
    apply propext
    simp only [firstEntryPredicate, h]
  unfold firstEntryTime
  exact Nat.find_congr' (fun {n} => iff_of_eq (congrFun he n))

theorem lastArrivalMemory_map (f : A → B) (z : ℕ → Unit ⊕ (A × ArrivalMemory σ)) :
    lastArrivalMemory (fun n => Sum.map id (fun x : A × ArrivalMemory σ => (f x.1, x.2)) (z n)) =
      lastArrivalMemory z := by
  have he := firstEntryTime_eq_of_membership {a : Unit ⊕ (A × ArrivalMemory σ) | a = .inl ()}
    {a : Unit ⊕ (B × ArrivalMemory σ) | a = .inl ()}
    z (fun n => Sum.map id (fun x => (f x.1, x.2)) (z n)) (fun n => by cases hn : z n <;> simp [hn])
  unfold lastArrivalMemory
  rw [← he]
  dsimp only
  cases z (firstEntryTime {a | a = .inl ()} z - 1) <;> rfl

theorem lastArrivalCounts_map (f : A → B) (z : ℕ → Unit ⊕ (A × ArrivalMemory σ)) :
    lastArrivalCounts (fun n => Sum.map id (fun x : A × ArrivalMemory σ => (f x.1, x.2)) (z n)) =
      lastArrivalCounts z := by
  unfold lastArrivalCounts
  rw [lastArrivalMemory_map]

end StochasticMatching
