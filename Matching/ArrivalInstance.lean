import Matching.MatchingRealDeficiency
import Matching.OfflineDeficiency
import Mathlib.Data.Fintype.Sigma

/-! Realizing finite type counts as an actual bipartite matching instance.
The right vertices are individual arrival copies. Its neighborhood cardinality
is exactly the coverage count, connecting Hall's formula to the paper's model.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

abbrev ArrivalCopies (counts : σ → ℕ) := Σ s : σ, Fin (counts s)

noncomputable def arrivalNeighbors (N : σ → Finset ι) (counts : σ → ℕ) (i : ι) : Finset (ArrivalCopies counts) :=
  Finset.univ.filter (fun a => i ∈ N a.1)

noncomputable def arrivalCoverageCount (N : σ → Finset ι) (counts : σ → ℕ) (A : Finset ι) : ℕ :=
  ∑ s, if (N s ∩ A).Nonempty then counts s else 0

theorem arrival_neighbors_union (N : σ → Finset ι) (counts : σ → ℕ) (A : Finset ι) :
    A.biUnion (arrivalNeighbors N counts) = Finset.univ.sigma
      (fun s => if (N s ∩ A).Nonempty then (Finset.univ : Finset (Fin (counts s))) else ∅) := by
  ext a
  constructor
  · intro ha
    obtain ⟨i, hiA, hai⟩ := Finset.mem_biUnion.mp ha
    have hiN := (Finset.mem_filter.mp hai).2
    have ht : (N a.1 ∩ A).Nonempty := ⟨i, Finset.mem_inter.mpr ⟨hiN, hiA⟩⟩
    simp only [Finset.mem_sigma, Finset.mem_univ, if_pos ht, and_self]
  · intro ha
    have ht : (N a.1 ∩ A).Nonempty := by
      by_contra h
      simp [h] at ha
    obtain ⟨i, hi⟩ := ht
    exact Finset.mem_biUnion.mpr ⟨i, (Finset.mem_inter.mp hi).2,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_inter.mp hi).1⟩⟩

theorem arrival_neighbors_card (N : σ → Finset ι) (counts : σ → ℕ) (A : Finset ι) :
    (A.biUnion (arrivalNeighbors N counts)).card = arrivalCoverageCount N counts A := by
  rw [arrival_neighbors_union, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

theorem arrivalCoverageCount_cast (N : σ → Finset ι) (counts : σ → ℕ) (A : Finset ι) :
    (arrivalCoverageCount N counts A : ℝ) = supplyCoverage N (fun s => (counts s : ℝ)) A := by
  unfold arrivalCoverageCount supplyCoverage
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

theorem arrival_matchingDeficiency_eq (N : σ → Finset ι) (counts : σ → ℕ) (A : Finset ι) :
    matchingDeficiency (arrivalNeighbors N counts) A =
      supplyDeficiency N (fun s => (counts s : ℝ)) (fun _ => 1) A := by
  rw [matchingDeficiency, arrival_neighbors_card, arrivalCoverageCount_cast]
  simp [supplyDeficiency]

theorem arrival_max_deficiency_eq_hall (N : σ → Finset ι) (counts : σ → ℕ) :
    maxSupplyDeficiency N (fun s => (counts s : ℝ)) (fun _ => 1) =
      (hallDeficiency (arrivalNeighbors N counts) : ℝ) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro A _
    rw [← arrival_matchingDeficiency_eq]
    exact matchingDeficiency_le_hall _ A
  · obtain ⟨A, hA⟩ := exists_matchingDeficiency_eq_hall (arrivalNeighbors N counts)
    rw [← hA, arrival_matchingDeficiency_eq]
    exact supplyDeficiency_le_max _ _ _ A

noncomputable def arrivalOfflineValue (N : σ → Finset ι) (counts : σ → ℕ) : ℝ :=
  (Fintype.card ι : ℝ) - (hallDeficiency (arrivalNeighbors N counts) : ℝ)

theorem arrivalOfflineValue_realized (N : σ → Finset ι) (counts : σ → ℕ) :
    ∃ m : FiniteMatching (arrivalNeighbors N counts), (m.size : ℝ) = arrivalOfflineValue N counts ∧
      ∀ m' : FiniteMatching (arrivalNeighbors N counts), m'.size ≤ m.size :=
  exists_maximum_matching_real (arrivalNeighbors N counts)

theorem arrivalOfflineValue_deficiency_formula (N : σ → Finset ι) (counts : σ → ℕ) :
    arrivalOfflineValue N counts = (Fintype.card ι : ℝ) -
      maxSupplyDeficiency N (fun s => (counts s : ℝ)) (fun _ => 1) := by
  rw [arrival_max_deficiency_eq_hall]
  rfl

theorem arrivalOfflineValue_nonneg (N : σ → Finset ι) (counts : σ → ℕ) :
    0 ≤ arrivalOfflineValue N counts := by
  obtain ⟨m, hm, _⟩ := arrivalOfflineValue_realized N counts
  rw [← hm]
  exact Nat.cast_nonneg _

theorem arrivalOfflineValue_le_card (N : σ → Finset ι) (counts : σ → ℕ) :
    arrivalOfflineValue N counts ≤ (Fintype.card ι : ℝ) := by
  unfold arrivalOfflineValue
  exact sub_le_self _ (Nat.cast_nonneg _)

end StochasticMatching
