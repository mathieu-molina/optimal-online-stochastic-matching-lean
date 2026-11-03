import Matching.ChainCancellation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max

/-! The chain formula for a supermodular maximum, proved by finite sign
cancellation. A maximizing set supplies the union closure used to delete
dominated vertices, leaving a family with a common apex.
-/

open scoped BigOperators
namespace StochasticMatching
variable {ι : Type*} [DecidableEq ι]

theorem reducedChainSum_union_closed (Q : Finset (Finset ι)) (B : Finset ι)
    (hBQ : B ∈ Q) (hclosed : ∀ A ∈ Q, A ∪ B ∈ Q) : reducedChainSum Q = 0 := by
  classical
  induction Q using Finset.strongInduction generalizing B with
  | H Q ih =>
    by_cases hall : ∀ A ∈ Q, B ⊆ A
    · exact reducedChainSum_apex Q B hBQ (fun A hA => Or.inr (hall A hA))
    · have hbad : (Q.filter (fun A => ¬ B ⊆ A)).Nonempty := by
        push_neg at hall
        obtain ⟨A, hA, hBA⟩ := hall
        exact ⟨A, Finset.mem_filter.mpr ⟨hA, hBA⟩⟩
      obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image
        (Q.filter (fun A => ¬ B ⊆ A)) Finset.card hbad
      obtain ⟨hAQ, hBA⟩ := Finset.mem_filter.mp hA
      have hAC : A ≠ A ∪ B := by
        intro he
        apply hBA
        rw [he]
        exact Finset.subset_union_right
      have hdom : ∀ C ∈ finiteChains Q, A ∈ C → ∀ U ∈ C,
          U ⊆ A ∪ B ∨ A ∪ B ⊆ U := by
        intro C hC hAC' U hUC
        obtain ⟨hCQ, hn⟩ := mem_finiteChains.mp hC
        rcases hn A hAC' U hUC with hAU | hUA
        · by_cases hBU : B ⊆ U
          · exact Or.inr (Finset.union_subset hAU hBU)
          · have hcard : U.card ≤ A.card := hmax U (Finset.mem_filter.mpr ⟨hCQ hUC, hBU⟩)
            have he : A = U := Finset.eq_of_subset_of_card_le hAU hcard
            exact Or.inl (he ▸ Finset.subset_union_left)
        · exact Or.inl (hUA.trans Finset.subset_union_left)
      rw [reducedChainSum_delete_dominated Q A (A ∪ B) hAC (hclosed A hAQ) hdom]
      apply ih (Q.erase A) (Finset.erase_ssubset hAQ) B
      · apply Finset.mem_erase.mpr
        refine ⟨?_, hBQ⟩
        intro he
        apply hBA
        rw [← he]
      · intro U hU
        apply Finset.mem_erase.mpr
        refine ⟨?_, hclosed U (Finset.mem_of_mem_erase hU)⟩
        intro he
        apply hBA
        rw [← he]
        exact Finset.subset_union_right

noncomputable def chainEuler {α : Type*} [DecidableEq α] [PartialOrder α] (Q : Finset α) : ℝ :=
  ∑ C ∈ (finiteChains Q).erase ∅, -chainWeight C

theorem chainEuler_eq_one_sub {α : Type*} [DecidableEq α] [PartialOrder α] (Q : Finset α) :
    chainEuler Q = 1 - reducedChainSum Q := by
  have he : (∅ : Finset α) ∈ finiteChains Q :=
    mem_finiteChains.mpr ⟨Finset.empty_subset _, by simp [NestedFamily]⟩
  have hs := Finset.sum_erase_add (s := finiteChains Q) chainWeight he
  have hw : chainWeight (∅ : Finset α) = 1 := by simp [chainWeight]
  rw [hw] at hs
  unfold chainEuler reducedChainSum
  rw [Finset.sum_neg_distrib]
  linarith

theorem chainEuler_empty {α : Type*} [DecidableEq α] [PartialOrder α] :
    chainEuler (∅ : Finset α) = 0 := by
  classical
  have hn : NestedFamily (∅ : Finset α) := by simp [NestedFamily]
  have he : finiteChains (∅ : Finset α) = {∅} := by
    simp only [finiteChains, Finset.powerset_empty, Finset.filter_singleton, if_pos hn]
  rw [chainEuler, he]
  simp

def SupermodularFinset (d : Finset ι → ℝ) : Prop :=
  ∀ A B, d A + d B ≤ d (A ∪ B) + d (A ∩ B)

theorem supermodular_union_maximizer {d : Finset ι → ℝ} (hd : SupermodularFinset d)
    (B : Finset ι) (hB : ∀ U, d U ≤ d B) (A : Finset ι) : d A ≤ d (A ∪ B) := by
  have hs := hd A B
  have hm := hB (A ∩ B)
  linarith

variable [Fintype ι]

noncomputable def thresholdFamily (d : Finset ι → ℝ) (a : ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun A => a < d A)

theorem mem_thresholdFamily (d : Finset ι → ℝ) (a : ℝ) (A : Finset ι) :
    A ∈ thresholdFamily d a ↔ a < d A := by
  classical
  simp [thresholdFamily]

theorem chainEuler_threshold_nonempty {d : Finset ι → ℝ} (hd : SupermodularFinset d)
    (a : ℝ) (hne : ∃ A, a < d A) : chainEuler (thresholdFamily d a) = 1 := by
  classical
  obtain ⟨B, _, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset ι)) d Finset.univ_nonempty
  have hB : ∀ U, d U ≤ d B := fun U => hm U (Finset.mem_univ U)
  have hBQ : B ∈ thresholdFamily d a := by
    obtain ⟨A, hA⟩ := hne
    exact (mem_thresholdFamily d a B).mpr (hA.trans_le (hB A))
  have hclosed : ∀ A ∈ thresholdFamily d a, A ∪ B ∈ thresholdFamily d a := by
    intro A hA
    exact (mem_thresholdFamily d a _).mpr
      (((mem_thresholdFamily d a A).mp hA).trans_le (supermodular_union_maximizer hd B hB A))
  rw [chainEuler_eq_one_sub, reducedChainSum_union_closed _ B hBQ hclosed, sub_zero]

theorem finiteChains_threshold (d : Finset ι → ℝ) (a : ℝ) :
    finiteChains (thresholdFamily d a) =
      (finiteChains (Finset.univ : Finset (Finset ι))).filter (fun C => ∀ A ∈ C, a < d A) := by
  classical
  ext C
  rw [mem_finiteChains, Finset.mem_filter, mem_finiteChains]
  constructor
  · rintro ⟨hsub, hn⟩
    exact ⟨⟨Finset.subset_univ _, hn⟩, fun A hA => (mem_thresholdFamily d a A).mp (hsub hA)⟩
  · rintro ⟨⟨_, hn⟩, hex⟩
    exact ⟨fun A hA => (mem_thresholdFamily d a A).mpr (hex A hA), hn⟩

theorem chainEuler_threshold_expansion (d : Finset ι → ℝ) (a : ℝ) :
    chainEuler (thresholdFamily d a) =
      ∑ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
        if ∀ A ∈ C, a < d A then -chainWeight C else 0 := by
  classical
  unfold chainEuler
  rw [finiteChains_threshold]
  have he : ((finiteChains (Finset.univ : Finset (Finset ι))).filter
      (fun C => ∀ A ∈ C, a < d A)).erase ∅ =
      ((finiteChains (Finset.univ : Finset (Finset ι))).erase ∅).filter
        (fun C => ∀ A ∈ C, a < d A) := by
    ext C
    simp only [Finset.mem_erase, Finset.mem_filter, and_assoc, and_left_comm]
  rw [he, Finset.sum_filter]

theorem supermodular_max_chain_identity {d : Finset ι → ℝ} (hd : SupermodularFinset d) (a : ℝ) :
    (if ∃ A, a < d A then (1 : ℝ) else 0) =
      ∑ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
        if ∀ A ∈ C, a < d A then -chainWeight C else 0 := by
  classical
  rw [← chainEuler_threshold_expansion]
  by_cases h : ∃ A, a < d A
  · rw [if_pos h, chainEuler_threshold_nonempty hd a h]
  · have he : thresholdFamily d a = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro A hA
      exact h ⟨A, (mem_thresholdFamily d a A).mp hA⟩
    rw [if_neg h, he, chainEuler_empty]

end StochasticMatching
