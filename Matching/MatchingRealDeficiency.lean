import Matching.MatchingDeficiency
import Matching.SupermodularTail

/-! Real-valued deficiency for finite bipartite graphs, linked to the exact
maximum matching theorem and the supermodular chain formula.
-/

open scoped BigOperators
namespace StochasticMatching
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

noncomputable def matchingDeficiency (t : ι → Finset α) (A : Finset ι) : ℝ :=
  (A.card : ℝ) - (A.biUnion t).card

theorem matchingDeficiency_empty (t : ι → Finset α) : matchingDeficiency t ∅ = 0 := by
  simp [matchingDeficiency]

theorem neighbors_inter_subset (t : ι → Finset α) (A B : Finset ι) :
    (A ∩ B).biUnion t ⊆ (A.biUnion t) ∩ (B.biUnion t) := by
  intro a ha
  obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨hiA, hiB⟩ := Finset.mem_inter.mp hi
  exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, hiA, hai⟩,
    Finset.mem_biUnion.mpr ⟨i, hiB, hai⟩⟩

theorem neighbor_card_submodular (t : ι → Finset α) (A B : Finset ι) :
    ((A ∪ B).biUnion t).card + ((A ∩ B).biUnion t).card ≤
      (A.biUnion t).card + (B.biUnion t).card := by
  have hu : (A ∪ B).biUnion t = (A.biUnion t) ∪ (B.biUnion t) := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_union, or_and_right, exists_or]
  rw [hu]
  have hm := Finset.card_union_add_card_inter (A.biUnion t) (B.biUnion t)
  have hi := Finset.card_le_card (neighbors_inter_subset t A B)
  omega

theorem matchingDeficiency_supermodular (t : ι → Finset α) :
    SupermodularFinset (matchingDeficiency t) := by
  intro A B
  have hm : ((A ∪ B).card : ℝ) + (A ∩ B).card = (A.card : ℝ) + B.card := by
    exact_mod_cast Finset.card_union_add_card_inter A B
  have hn : (((A ∪ B).biUnion t).card : ℝ) + ((A ∩ B).biUnion t).card ≤
      ((A.biUnion t).card : ℝ) + (B.biUnion t).card := by
    exact_mod_cast neighbor_card_submodular t A B
  unfold matchingDeficiency
  linarith

theorem matchingDeficiency_le_hall (t : ι → Finset α) (A : Finset ι) :
    matchingDeficiency t A ≤ (hallDeficiency t : ℝ) := by
  have h := subset_deficiency_le t A
  unfold matchingDeficiency
  by_cases hA : (A.biUnion t).card ≤ A.card
  · have hc : ((A.card - (A.biUnion t).card : ℕ) : ℝ) ≤ (hallDeficiency t : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_sub hA] using hc
  · have hc : (A.card : ℝ) ≤ ((A.biUnion t).card : ℝ) := by exact_mod_cast le_of_not_ge hA
    have hn : (0 : ℝ) ≤ hallDeficiency t := Nat.cast_nonneg _
    linarith

theorem exists_matchingDeficiency_eq_hall (t : ι → Finset α) :
    ∃ A : Finset ι, matchingDeficiency t A = (hallDeficiency t : ℝ) := by
  by_cases hd : hallDeficiency t = 0
  · exact ⟨∅, by simp [matchingDeficiency_empty, hd]⟩
  · obtain ⟨A, _, hA⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset ι))
      Finset.univ_nonempty (fun A => A.card - (A.biUnion t).card)
    have he : hallDeficiency t = A.card - (A.biUnion t).card := hA
    have hle : (A.biUnion t).card ≤ A.card := by
      have hpos : 0 < hallDeficiency t := Nat.pos_of_ne_zero hd
      omega
    refine ⟨A, ?_⟩
    rw [he, Nat.cast_sub hle]
    rfl

theorem hallDeficiency_gt_iff (t : ι → Finset α) (a : ℝ) :
    a < (hallDeficiency t : ℝ) ↔ ∃ A, a < matchingDeficiency t A := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := exists_matchingDeficiency_eq_hall t
    exact ⟨A, by rwa [hA]⟩
  · rintro ⟨A, hA⟩
    exact hA.trans_le (matchingDeficiency_le_hall t A)

theorem exists_maximum_matching_real (t : ι → Finset α) :
    ∃ m : FiniteMatching t,
      (m.size : ℝ) = (Fintype.card ι : ℝ) - (hallDeficiency t : ℝ) ∧
      ∀ m' : FiniteMatching t, m'.size ≤ m.size := by
  obtain ⟨m, _, hm, hmax⟩ := exists_maximum_matching t
  exact ⟨m, by rw [hm, Nat.cast_sub (hallDeficiency_le_card t)], hmax⟩

end StochasticMatching
