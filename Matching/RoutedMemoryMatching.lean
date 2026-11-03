import Matching.RoutedMemory
import Matching.FiniteArrivalMatching

/-! A valid finite routing log determines a matching on exactly the
individual arrival copies counted by its input projection. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def routedMemoryRecord (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) (k : Fin m.1) : ℝ × (σ × Option ι) :=
  Classical.choose (h.genuine k.1 k.2)

theorem routedMemoryRecord_spec (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) (k : Fin m.1) :
    m.2 k.1 = .inr (routedMemoryRecord N m h k) := Classical.choose_spec (h.genuine k.1 k.2)

theorem routedMemoryRecord_job (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) (k : Fin m.1) :
    (routedMemoryRecord N m h k).2.2 = routedEventJob (m.2 k.1) := by
  rw [routedMemoryRecord_spec N m h k]
  rfl

theorem routedMemoryRecord_supported (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) (k : Fin m.1) (j : ι)
    (hj : (routedMemoryRecord N m h k).2.2 = some j) :
    j ∈ N (routedMemoryRecord N m h k).2.1 := by
  apply h.supported k.1 k.2 (routedMemoryRecord N m h k).1 _ j
  rw [routedMemoryRecord_spec N m h k]
  apply congrArg Sum.inr
  exact Prod.ext rfl (Prod.ext rfl hj)

theorem routedMemoryRecord_unique (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) (k l : Fin m.1) (j : ι)
    (hk : (routedMemoryRecord N m h k).2.2 = some j)
    (hl : (routedMemoryRecord N m h l).2.2 = some j) : k = l := by
  rw [routedMemoryRecord_job] at hk hl
  exact Fin.ext (h.unique k.1 l.1 k.2 l.2 j hk hl)

theorem routedMemoryRecord_counts (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) :
    finiteTypeCounts (fun k => (routedMemoryRecord N m h k).2.1) =
      arrivalMemoryCounts (routedMemoryInput m) := by
  funext s
  unfold finiteTypeCounts
  rw [Fintype.card_subtype, Finset.card_filter]
  change (∑ k : Fin m.1, if (routedMemoryRecord N m h k).2.1 = s then 1 else 0) =
    ∑ k ∈ Finset.range m.1, arrivalTypeIndicator s (arrivalTypeProjection (m.2 k))
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [routedMemoryRecord_spec N m h k]
  rfl

theorem routedMemoryRecord_accepted (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) :
    (routedArrivals (fun k => (routedMemoryRecord N m h k).2.2)).card = routedMemoryAccepted m := by
  rw [routedArrivals, Finset.card_filter]
  unfold routedMemoryAccepted
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [routedMemoryRecord_job]
  rfl

noncomputable def routedMemoryMatching (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) : FiniteMatching (arrivalNeighbors N (arrivalMemoryCounts (routedMemoryInput m))) :=
  (routedMemoryRecord_counts N m h) ▸ routingMatching N
    (fun k => (routedMemoryRecord N m h k).2.1) (fun k => (routedMemoryRecord N m h k).2.2)
    (routedMemoryRecord_supported N m h)

theorem arrivalMatching_size_cast (N : σ → Finset ι) {c d : σ → ℕ} (h : c = d)
    (m : FiniteMatching (arrivalNeighbors N c)) : (h ▸ m).size = m.size := by
  subst d
  rfl

theorem routedMemoryMatching_size (N : σ → Finset ι) (m : RoutedMemory σ ι)
    (h : RoutedMemoryValid N m) : (routedMemoryMatching N m h).size = routedMemoryAccepted m := by
  have hsize := routingMatching_size_eq_accepted N
    (fun k => (routedMemoryRecord N m h k).2.1) (fun k => (routedMemoryRecord N m h k).2.2)
    (routedMemoryRecord_supported N m h) (routedMemoryRecord_unique N m h)
  rw [routedMemoryRecord_accepted] at hsize
  rw [routedMemoryMatching, arrivalMatching_size_cast]
  exact hsize

end StochasticMatching
