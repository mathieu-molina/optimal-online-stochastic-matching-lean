import Matching.CompletionState
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! Elementary cancellation for finite order complexes. Chains include the
empty chain, so their alternating sum is the reduced Euler sum. Toggling a
compatible vertex pairs terms with opposite signs, without topological axioms.
-/

open scoped BigOperators
namespace StochasticMatching
variable {α : Type*} [DecidableEq α] [PartialOrder α]

def NestedFamily (C : Finset α) : Prop := ∀ a ∈ C, ∀ b ∈ C, a ≤ b ∨ b ≤ a

noncomputable def finiteChains (Q : Finset α) : Finset (Finset α) := by
  classical
  exact Q.powerset.filter NestedFamily

noncomputable def chainWeight (C : Finset α) : ℝ := (-1 : ℝ) ^ C.card

noncomputable def reducedChainSum (Q : Finset α) : ℝ := ∑ C ∈ finiteChains Q, chainWeight C

def toggleVertex (c : α) (C : Finset α) : Finset α :=
  if c ∈ C then C.erase c else insert c C

theorem mem_finiteChains {Q C : Finset α} : C ∈ finiteChains Q ↔ C ⊆ Q ∧ NestedFamily C := by
  classical
  simp only [finiteChains, Finset.mem_filter, Finset.mem_powerset]

theorem nested_subset {C D : Finset α} (hC : NestedFamily C) (hDC : D ⊆ C) : NestedFamily D :=
  fun a ha b hb => hC a (hDC ha) b (hDC hb)

theorem nested_insert {C : Finset α} {c : α} (hC : NestedFamily C)
    (hc : ∀ a ∈ C, a ≤ c ∨ c ≤ a) : NestedFamily (insert c C) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with hac | haC
  · subst a
    rcases Finset.mem_insert.mp hb with hbc | hbC
    · subst b
      exact Or.inl (le_refl _)
    · exact (hc b hbC).symm
  · rcases Finset.mem_insert.mp hb with hbc | hbC
    · subst b
      exact hc a haC
    · exact hC a haC b hbC

theorem toggleVertex_involution (c : α) (C : Finset α) : toggleVertex c (toggleVertex c C) = C := by
  by_cases hc : c ∈ C
  · simp [toggleVertex, hc, Finset.insert_erase hc]
  · simp [toggleVertex, hc]

theorem toggleVertex_ne (c : α) (C : Finset α) : toggleVertex c C ≠ C := by
  intro he
  by_cases hc : c ∈ C
  · have ht : c ∉ toggleVertex c C := by simp [toggleVertex, hc]
    exact ht (he.symm ▸ hc)
  · apply hc
    rw [← he]
    simp [toggleVertex, hc]

theorem mem_toggleVertex_other {a c : α} (hac : a ≠ c) (C : Finset α) :
    a ∈ toggleVertex c C ↔ a ∈ C := by
  unfold toggleVertex
  split_ifs <;> simp [hac]

theorem chainWeight_toggle (c : α) (C : Finset α) :
    chainWeight C + chainWeight (toggleVertex c C) = 0 := by
  by_cases hc : c ∈ C
  · change (-1 : ℝ) ^ C.card + (-1 : ℝ) ^ (toggleVertex c C).card = 0
    rw [toggleVertex, if_pos hc, ← Finset.card_erase_add_one hc, pow_succ]
    ring
  · change (-1 : ℝ) ^ C.card + (-1 : ℝ) ^ (toggleVertex c C).card = 0
    rw [toggleVertex, if_neg hc, Finset.card_insert_of_not_mem hc, pow_succ]
    ring

theorem toggleVertex_mem_chains {Q C : Finset α} {c : α}
    (hC : C ∈ finiteChains Q) (hcQ : c ∈ Q) (hc : ∀ a ∈ C, a ≤ c ∨ c ≤ a) :
    toggleVertex c C ∈ finiteChains Q := by
  obtain ⟨hsub, hnest⟩ := mem_finiteChains.mp hC
  apply mem_finiteChains.mpr
  unfold toggleVertex
  split_ifs with hcC
  · exact ⟨(Finset.erase_subset c C).trans hsub, nested_subset hnest (Finset.erase_subset c C)⟩
  · exact ⟨Finset.insert_subset hcQ hsub, nested_insert hnest hc⟩

theorem chainWeight_sum_cancel (S : Finset (Finset α)) (c : α)
    (hS : ∀ C ∈ S, toggleVertex c C ∈ S) : (∑ C ∈ S, chainWeight C) = 0 := by
  exact Finset.sum_involution (fun C _ => toggleVertex c C)
    (fun C _ => chainWeight_toggle c C) (fun C _ _ => toggleVertex_ne c C)
    hS (fun C _ => toggleVertex_involution c C)

theorem reducedChainSum_apex (Q : Finset α) (c : α) (hcQ : c ∈ Q)
    (hc : ∀ a ∈ Q, a ≤ c ∨ c ≤ a) : reducedChainSum Q = 0 := by
  apply chainWeight_sum_cancel (finiteChains Q) c
  intro C hC
  exact toggleVertex_mem_chains hC hcQ (fun a ha => hc a ((mem_finiteChains.mp hC).1 ha))

theorem finiteChains_erase (Q : Finset α) (a : α) :
    finiteChains (Q.erase a) = (finiteChains Q).filter (fun C => a ∉ C) := by
  classical
  ext C
  rw [mem_finiteChains, Finset.mem_filter, mem_finiteChains]
  constructor
  · rintro ⟨hsub, hn⟩
    exact ⟨⟨fun b hb => Finset.mem_of_mem_erase (hsub hb), hn⟩,
      fun ha => (Finset.mem_erase.mp (hsub ha)).1 rfl⟩
  · rintro ⟨⟨hsub, hn⟩, ha⟩
    refine ⟨?_, hn⟩
    intro b hb
    exact Finset.mem_erase.mpr ⟨fun hba => ha (hba ▸ hb), hsub hb⟩

theorem reducedChainSum_delete_dominated (Q : Finset α) (a c : α)
    (hac : a ≠ c) (hcQ : c ∈ Q)
    (hdom : ∀ C ∈ finiteChains Q, a ∈ C → ∀ b ∈ C, b ≤ c ∨ c ≤ b) :
    reducedChainSum Q = reducedChainSum (Q.erase a) := by
  classical
  have hz : (∑ C ∈ (finiteChains Q).filter (fun C => a ∈ C), chainWeight C) = 0 := by
    apply chainWeight_sum_cancel _ c
    intro C hC
    obtain ⟨hchain, haC⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨toggleVertex_mem_chains hchain hcQ (hdom C hchain haC),
      (mem_toggleVertex_other hac C).mpr haC⟩
  have hs := Finset.sum_filter_add_sum_filter_not (finiteChains Q) (fun C => a ∈ C) chainWeight
  rw [hz, zero_add, ← finiteChains_erase] at hs
  exact hs.symm

end StochasticMatching
