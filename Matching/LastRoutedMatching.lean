import Matching.LastLiveObservation
import Matching.RoutedMemoryMatching
import Matching.RoutedMemoryMeasurable

/-! Extract a genuine finite matching from a stopped marked trajectory.
Malformed paths use the empty matching; almost-sure validity is proved
separately for the concrete policy. -/
open MeasureTheory Set
open scoped Classical
namespace StochasticMatching
variable {A ι σ : Type*} [MeasurableSpace A]
  [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def lastRoutedMemory (z : ℕ → Unit ⊕ (A × RoutedMemory σ ι)) : RoutedMemory σ ι :=
  lastLiveObservation Prod.snd emptyRoutedMemory z

theorem measurable_lastRoutedMemory : Measurable (lastRoutedMemory (A := A) (ι := ι) (σ := σ)) :=
  measurable_lastLiveObservation _ measurable_snd _

noncomputable def lastRoutedCounts (z : ℕ → Unit ⊕ (A × RoutedMemory σ ι)) : σ → ℕ :=
  arrivalMemoryCounts (routedMemoryInput (lastRoutedMemory z))

theorem measurable_lastRoutedCounts : Measurable (lastRoutedCounts (A := A) (ι := ι) (σ := σ)) :=
  measurable_arrivalMemoryCounts.comp (measurable_routedMemoryInput.comp measurable_lastRoutedMemory)

theorem lastRoutedMemory_erase_marks (z : ℕ → Unit ⊕ (A × RoutedMemory σ ι)) :
    lastArrivalMemory (fun k => Sum.map id (fun y : A × RoutedMemory σ ι =>
      (y.1, routedMemoryInput y.2)) (z k)) = routedMemoryInput (lastRoutedMemory z) := by
  change lastLiveObservation (Prod.snd : A × ArrivalMemory σ → ArrivalMemory σ) (emptyArrivalMemory σ)
    (fun k => Sum.map id (fun y : A × RoutedMemory σ ι => (y.1, routedMemoryInput y.2)) (z k)) =
      routedMemoryInput (lastRoutedMemory z)
  rw [lastLiveObservation_map, lastRoutedMemory, lastLiveObservation_comp routedMemoryInput]
  rfl

theorem lastRoutedCounts_erase_marks (z : ℕ → Unit ⊕ (A × RoutedMemory σ ι)) :
    lastArrivalCounts (fun k => Sum.map id (fun y : A × RoutedMemory σ ι =>
      (y.1, routedMemoryInput y.2)) (z k)) = lastRoutedCounts z := by
  unfold lastArrivalCounts lastRoutedCounts
  rw [lastRoutedMemory_erase_marks]

def FiniteMatching.empty {α : Type*} [DecidableEq α] (t : ι → Finset α) : FiniteMatching t where
  unmatched := Finset.univ
  assign := fun i => False.elim (i.2 (Finset.mem_univ i.1))
  injective := fun i _ _ => False.elim (i.2 (Finset.mem_univ i.1))
  supported := fun i => False.elim (i.2 (Finset.mem_univ i.1))

theorem FiniteMatching.empty_size {α : Type*} [DecidableEq α] (t : ι → Finset α) :
    (FiniteMatching.empty t).size = 0 := by simp [FiniteMatching.size, FiniteMatching.empty]

noncomputable def observedRoutingMatching (N : σ → Finset ι)
    (z : ℕ → Unit ⊕ (A × RoutedMemory σ ι)) : FiniteMatching (arrivalNeighbors N (lastRoutedCounts z)) := by
  classical
  exact if h : RoutedMemoryValid N (lastRoutedMemory z) then
    routedMemoryMatching N (lastRoutedMemory z) h else FiniteMatching.empty _

theorem observedRoutingMatching_size (N : σ → Finset ι)
    (z : ℕ → Unit ⊕ (A × RoutedMemory σ ι)) :
    (observedRoutingMatching N z).size =
      if RoutedMemoryValid N (lastRoutedMemory z) then routedMemoryAccepted (lastRoutedMemory z) else 0 := by
  classical
  unfold observedRoutingMatching
  split_ifs with h
  · exact routedMemoryMatching_size N _ h
  · exact FiniteMatching.empty_size _

theorem observedRoutingMatching_size_of_valid (N : σ → Finset ι)
    (z : ℕ → Unit ⊕ (A × RoutedMemory σ ι)) (h : RoutedMemoryValid N (lastRoutedMemory z)) :
    (observedRoutingMatching N z).size = routedMemoryAccepted (lastRoutedMemory z) := by
  classical
  rw [observedRoutingMatching_size, if_pos h]

theorem measurable_observedRoutingMatching_size (N : σ → Finset ι) :
    Measurable (fun z : ℕ → Unit ⊕ (A × RoutedMemory σ ι) => (observedRoutingMatching N z).size) := by
  classical
  simp_rw [observedRoutingMatching_size]
  exact Measurable.ite (measurable_lastRoutedMemory (A := A) (measurableSet_routedMemoryValid N))
    (measurable_routedMemoryAccepted.comp measurable_lastRoutedMemory) measurable_const

theorem observedRoutingMatching_size_le (N : σ → Finset ι)
    (z : ℕ → Unit ⊕ (A × RoutedMemory σ ι)) : (observedRoutingMatching N z).size ≤ Fintype.card ι :=
  Nat.sub_le _ _

end StochasticMatching
