import Matching.OfflineTightSets
import Mathlib.Topology.Order.Lattice

/-! A continuous greedy coordinate extension inside a coverage region. Each
extension reaches its demand cap or a tight capacity constraint, and earlier
settled coordinates stay settled under further feasible increases.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

noncomputable def containingSets (i : ι) : Finset (Finset ι) :=
  Finset.univ.filter (fun A => i ∈ A)

theorem containingSets_nonempty (i : ι) : (containingSets i).Nonempty := by
  refine ⟨{i}, ?_⟩
  simp [containingSets]

theorem mem_containingSets (i : ι) (A : Finset ι) : A ∈ containingSets i ↔ i ∈ A := by
  simp [containingSets]

noncomputable def coordinateRoom (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  (containingSets i).inf' (containingSets_nonempty i)
    (fun A => supplyCoverage N capacity A - ∑ j ∈ A, x j)

noncomputable def greedyIncrement (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (i : ι) : ℝ := min (max (z i) 0 - x i) (coordinateRoom N capacity x i)

noncomputable def greedyGrow (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (i : ι) : ι → ℝ :=
  Function.update x i (x i + greedyIncrement N capacity z x i)

def CoordinateSettled (N : σ → Finset ι) (capacity : σ → ℝ) (z x : ι → ℝ) (i : ι) : Prop :=
  x i = max (z i) 0 ∨ ∃ A : Finset ι, i ∈ A ∧ (∑ j ∈ A, x j) = supplyCoverage N capacity A

theorem coordinateRoom_nonneg (N : σ → Finset ι) (capacity : σ → ℝ)
    {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) (i : ι) : 0 ≤ coordinateRoom N capacity x i := by
  apply Finset.le_inf'
  intro A _
  exact sub_nonneg.mpr (hx.2 A)

theorem coordinateRoom_le (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ)
    (i : ι) (A : Finset ι) (hiA : i ∈ A) :
    coordinateRoom N capacity x i ≤ supplyCoverage N capacity A - ∑ j ∈ A, x j :=
  Finset.inf'_le _ ((mem_containingSets i A).mpr hiA)

theorem greedyIncrement_nonneg (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (hxz : x ≤ fun i => max (z i) 0) (i : ι) :
    0 ≤ greedyIncrement N capacity z x i :=
  le_min (sub_nonneg.mpr (hxz i)) (coordinateRoom_nonneg N capacity hx i)

theorem greedyGrow_ge (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (hxz : x ≤ fun i => max (z i) 0) (i : ι) :
    x ≤ greedyGrow N capacity z x i := by
  intro j
  by_cases hj : j = i
  · subst j
    simp only [greedyGrow, Function.update_self]
    exact le_add_of_nonneg_right (greedyIncrement_nonneg N capacity z x hx hxz i)
  · simp only [greedyGrow, Function.update_of_ne hj, le_refl]

theorem greedyGrow_feasible (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (hxz : x ≤ fun i => max (z i) 0) (i : ι) :
    greedyGrow N capacity z x i ∈ supplyRegion N capacity := by
  refine ⟨fun j => (hx.1 j).trans (greedyGrow_ge N capacity z x hx hxz i j), ?_⟩
  intro A
  unfold greedyGrow
  rw [sum_update_add]
  by_cases hiA : i ∈ A
  · rw [if_pos hiA]
    have he := (min_le_right (max (z i) 0 - x i) (coordinateRoom N capacity x i)).trans
      (coordinateRoom_le N capacity x i A hiA)
    change greedyIncrement N capacity z x i ≤ _ at he
    linarith
  · rw [if_neg hiA, add_zero]
    exact hx.2 A

theorem greedyGrow_cap (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (hxz : x ≤ fun i => max (z i) 0) (i : ι) :
    greedyGrow N capacity z x i ≤ fun j => max (z j) 0 := by
  intro j
  by_cases hj : j = i
  · subst j
    simp only [greedyGrow, Function.update_self]
    have h := min_le_left (max (z i) 0 - x i) (coordinateRoom N capacity x i)
    change greedyIncrement N capacity z x i ≤ _ at h
    linarith
  · simpa only [greedyGrow, Function.update_of_ne hj] using hxz j

theorem greedyGrow_settled (N : σ → Finset ι) (capacity : σ → ℝ) (z x : ι → ℝ) (i : ι) :
    CoordinateSettled N capacity z (greedyGrow N capacity z x i) i := by
  classical
  by_cases h : max (z i) 0 - x i ≤ coordinateRoom N capacity x i
  · left
    simp only [greedyGrow, greedyIncrement, min_eq_left h, Function.update_self]
    ring
  · right
    obtain ⟨A, hA, he⟩ := Finset.exists_mem_eq_inf' (containingSets_nonempty i)
      (fun A => supplyCoverage N capacity A - ∑ j ∈ A, x j)
    have hiA := (mem_containingSets i A).mp hA
    refine ⟨A, hiA, ?_⟩
    unfold greedyGrow
    rw [sum_update_add, if_pos hiA]
    unfold greedyIncrement
    rw [min_eq_right (le_of_not_ge h)]
    change (∑ j ∈ A, x j) + (containingSets i).inf' _ _ = _
    rw [he]
    ring

theorem coordinateSettled_mono (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x y : ι → ℝ) (hxy : x ≤ y) (hy : y ∈ supplyRegion N capacity)
    (hyz : y ≤ fun i => max (z i) 0) (i : ι) (hi : CoordinateSettled N capacity z x i) :
    CoordinateSettled N capacity z y i := by
  rcases hi with hi | ⟨A, hiA, hA⟩
  · left
    exact le_antisymm (hyz i) (hi ▸ hxy i)
  · right
    refine ⟨A, hiA, le_antisymm (hy.2 A) ?_⟩
    rw [← hA]
    exact Finset.sum_le_sum (fun j _ => hxy j)

theorem continuous_coordinateRoom (N : σ → Finset ι) (capacity : σ → ℝ) (i : ι) :
    Continuous (fun x => coordinateRoom N capacity x i) := by
  apply Continuous.finset_inf'_apply
  intro A _
  exact continuous_const.sub (continuous_finset_sum A (fun j _ => continuous_apply j))

theorem continuous_greedyIncrement (N : σ → Finset ι) (capacity : σ → ℝ) (i : ι) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => greedyIncrement N capacity p.1 p.2 i) := by
  exact (((continuous_apply i).comp continuous_fst).max continuous_const |>.sub
    ((continuous_apply i).comp continuous_snd)).min ((continuous_coordinateRoom N capacity i).comp continuous_snd)

theorem continuous_greedyGrow (N : σ → Finset ι) (capacity : σ → ℝ) (i : ι) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => greedyGrow N capacity p.1 p.2 i) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j
    simp only [greedyGrow, Function.update_self]
    exact ((continuous_apply i).comp continuous_snd).add (continuous_greedyIncrement N capacity i)
  · simp only [greedyGrow, Function.update_of_ne hj]
    exact (continuous_apply j).comp continuous_snd

end StochasticMatching
