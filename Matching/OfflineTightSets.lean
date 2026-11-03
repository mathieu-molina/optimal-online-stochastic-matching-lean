import Matching.OfflineValue
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Tight constraints at an offline optimum of the coverage region. Every
coordinate below its demand belongs to a tight set; tight sets are closed
under unions by submodularity. These facts give an elementary dual certificate.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

theorem finite_positive_lower_bound {β : Type*} (S : Finset β) (b : β → ℝ)
    (hb : ∀ j ∈ S, 0 < b j) : ∃ ε : ℝ, 0 < ε ∧ ∀ j ∈ S, ε ≤ b j := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert j S hj ih =>
    obtain ⟨ε, hε, hbound⟩ := ih (fun k hk => hb k (Finset.mem_insert_of_mem hk))
    refine ⟨min (b j) ε, lt_min (hb j (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound k hk)

theorem sum_update_add (x : ι → ℝ) (i : ι) (ε : ℝ) (A : Finset ι) :
    (∑ j ∈ A, Function.update x i (x i + ε) j) =
      (∑ j ∈ A, x j) + if i ∈ A then ε else 0 := by
  have hy : Function.update x i (x i + ε) = fun j => x j + if j = i then ε else 0 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, if_pos rfl, ite_true]
    · simp only [Function.update_of_ne hj, if_neg hj, add_zero]
  rw [hy, Finset.sum_add_distrib]
  simp

theorem optimizer_has_tight_set (N : σ → Finset ι) (capacity : σ → ℝ)
    (z x : ι → ℝ) (hx : x ∈ supplyRegion N capacity) (hxz : x ≤ z)
    (hmax : ∀ y ∈ supplyRegion N capacity, y ≤ z → (∑ i, y i) ≤ ∑ i, x i)
    (i : ι) (hi : x i < z i) :
    ∃ A : Finset ι, i ∈ A ∧ (∑ j ∈ A, x j) = supplyCoverage N capacity A := by
  classical
  by_contra hnone
  have hstrict : ∀ A : Finset ι, i ∈ A → (∑ j ∈ A, x j) < supplyCoverage N capacity A := by
    intro A hiA
    apply lt_of_le_of_ne (hx.2 A)
    intro he
    exact hnone ⟨A, hiA, he⟩
  let b : Finset ι → ℝ := fun A => if i ∈ A then supplyCoverage N capacity A - ∑ j ∈ A, x j else 1
  have hb : ∀ A ∈ (Finset.univ : Finset (Finset ι)), 0 < b A := by
    intro A _
    dsimp [b]
    split_ifs with hiA
    · exact sub_pos.mpr (hstrict A hiA)
    · exact zero_lt_one
  obtain ⟨δ, hδ, hbound⟩ := finite_positive_lower_bound Finset.univ b hb
  let ε : ℝ := min δ (z i - x i)
  have hε : 0 < ε := lt_min hδ (sub_pos.mpr hi)
  let y := Function.update x i (x i + ε)
  have hy : y ∈ supplyRegion N capacity := by
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hj : j = i
      · subst j
        simpa [y] using add_nonneg (hx.1 i) hε.le
      · simpa [y, hj] using hx.1 j
    · intro A
      rw [sum_update_add]
      by_cases hiA : i ∈ A
      · rw [if_pos hiA]
        have he : ε ≤ supplyCoverage N capacity A - ∑ j ∈ A, x j := by
          apply (min_le_left δ (z i - x i)).trans
          simpa only [b, if_pos hiA] using hbound A (Finset.mem_univ A)
        linarith
      · rw [if_neg hiA, add_zero]
        exact hx.2 A
  have hyz : y ≤ z := by
    intro j
    by_cases hj : j = i
    · subst j
      have he : ε ≤ z i - x i := min_le_right δ (z i - x i)
      simp only [y, Function.update_same]
      linarith
    · simpa [y, hj] using hxz j
  have hm := hmax y hy hyz
  rw [sum_update_add, if_pos (Finset.mem_univ i)] at hm
  linarith

theorem tight_set_union (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    {A B : Finset ι} (hA : (∑ i ∈ A, x i) = supplyCoverage N capacity A)
    (hB : (∑ i ∈ B, x i) = supplyCoverage N capacity B) :
    (∑ i ∈ A ∪ B, x i) = supplyCoverage N capacity (A ∪ B) := by
  have hsub := supplyCoverage_submodular N capacity hcapacity A B
  have hu := hx.2 (A ∪ B)
  have hi := hx.2 (A ∩ B)
  have hm : (∑ i ∈ A ∪ B, x i) + (∑ i ∈ A ∩ B, x i) =
      (∑ i ∈ A, x i) + (∑ i ∈ B, x i) := Finset.sum_union_inter
  linarith

theorem tight_set_biUnion (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity)
    (F : Finset (Finset ι)) (hF : ∀ A ∈ F, (∑ i ∈ A, x i) = supplyCoverage N capacity A) :
    (∑ i ∈ F.biUnion id, x i) = supplyCoverage N capacity (F.biUnion id) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [supplyCoverage_empty]
  | @insert A F hAF ih =>
    rw [Finset.biUnion_insert]
    exact tight_set_union N capacity hcapacity hx (hF A (Finset.mem_insert_self _ _))
      (ih (fun B hB => hF B (Finset.mem_insert_of_mem hB)))

theorem optimizer_tight_certificate (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (z x : ι → ℝ)
    (hx : x ∈ supplyRegion N capacity) (hxz : x ≤ z)
    (hmax : ∀ y ∈ supplyRegion N capacity, y ≤ z → (∑ i, y i) ≤ ∑ i, x i) :
    ∃ A : Finset ι, (∑ i ∈ A, x i) = supplyCoverage N capacity A ∧
      ∀ i, i ∉ A → x i = z i := by
  classical
  let F : Finset (Finset ι) := Finset.univ.filter
    (fun A => (∑ i ∈ A, x i) = supplyCoverage N capacity A)
  refine ⟨F.biUnion id, tight_set_biUnion N capacity hcapacity hx F
    (fun A hA => (Finset.mem_filter.mp hA).2), ?_⟩
  intro i hi
  apply le_antisymm (hxz i)
  by_contra hnot
  have hlt : x i < z i := lt_of_not_ge hnot
  obtain ⟨A, hiA, hA⟩ := optimizer_has_tight_set N capacity z x hx hxz hmax i hlt
  exact hi (Finset.mem_biUnion.mpr ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩, hiA⟩)

end StochasticMatching
