import Matching.HistoryTransport

/-! Measurable selection among pairwise disjoint observed event branches.
The fallback defines the function even on exceptional samples.
-/

open MeasureTheory Set

namespace StochasticMatching

variable {Ω κ E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Countable κ]

noncomputable def branchSelect (s : κ → Set Ω) (f : κ → Ω → E) (g : Ω → E) (x : Ω) : E := by
  classical
  exact if h : ∃ j, x ∈ s j then f (Classical.choose h) x else g x

theorem branchSelect_of_mem {s : κ → Set Ω}
    (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : κ → Ω → E) (g : Ω → E) {j : κ} {x : Ω} (hx : x ∈ s j) :
    branchSelect s f g x = f j x := by
  classical
  have hex : ∃ k, x ∈ s k := ⟨j, hx⟩
  have heq : Classical.choose hex = j := by
    by_contra hn
    exact Set.disjoint_left.mp (hs hn) (Classical.choose_spec hex) hx
  simp only [branchSelect, dif_pos hex, heq]

theorem branchSelect_of_not_mem {s : κ → Set Ω}
    (f : κ → Ω → E) (g : Ω → E) {x : Ω} (hx : ∀ j, x ∉ s j) :
    branchSelect s f g x = g x := by
  classical
  simp only [branchSelect, not_exists.mpr hx, dite_false]

theorem branchSelect_preimage {s : κ → Set Ω}
    (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : κ → Ω → E) (g : Ω → E) (A : Set E) :
    branchSelect s f g ⁻¹' A =
      ((⋃ j, s j)ᶜ ∩ g ⁻¹' A) ∪ ⋃ j, s j ∩ f j ⁻¹' A := by
  classical
  ext x
  by_cases hx : ∃ j, x ∈ s j
  · obtain ⟨j, hj⟩ := hx
    rw [mem_preimage, branchSelect_of_mem hs f g hj]
    constructor
    · intro hf
      exact Or.inr (mem_iUnion.mpr ⟨j, hj, hf⟩)
    · rintro (hg | hf)
      · exact False.elim (hg.1 (mem_iUnion.mpr ⟨j, hj⟩))
      · obtain ⟨k, hk, hf⟩ := mem_iUnion.mp hf
        have heq : k = j := by
          by_contra hn
          exact Set.disjoint_left.mp (hs hn) hk hj
        simpa only [heq] using hf
  · have hn : ∀ j, x ∉ s j := not_exists.mp hx
    rw [mem_preimage, branchSelect_of_not_mem f g hn]
    constructor
    · intro hg
      exact Or.inl ⟨by simpa using hx, hg⟩
    · rintro (hg | hf)
      · exact hg.2
      · obtain ⟨j, hj, _⟩ := mem_iUnion.mp hf
        exact False.elim (hn j hj)

theorem measurable_branchSelect {s : κ → Set Ω}
    (hs : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hsm : ∀ j, MeasurableSet (s j)) {f : κ → Ω → E} (hf : ∀ j, Measurable (f j))
    {g : Ω → E} (hg : Measurable g) : Measurable (branchSelect s f g) := by
  intro A hA
  rw [branchSelect_preimage hs]
  exact (((MeasurableSet.iUnion hsm).compl).inter (hg hA)).union
    (MeasurableSet.iUnion (fun j => (hsm j).inter (hf j hA)))

end StochasticMatching
