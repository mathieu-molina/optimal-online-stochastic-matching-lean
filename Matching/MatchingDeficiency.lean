import Matching.SupermodularChains
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Sum

/-! The finite bipartite matching deficiency formula. The lower bound uses
Hall's theorem after adding universal dummy neighbors. A matching is recorded
by its unmatched left vertices and an injective supported assignment elsewhere.
-/

open scoped BigOperators
namespace StochasticMatching
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

structure FiniteMatching (t : ι → Finset α) where
  unmatched : Finset ι
  assign : {i // i ∉ unmatched} → α
  injective : Function.Injective assign
  supported : ∀ i : {i // i ∉ unmatched}, assign i ∈ t i.val

def FiniteMatching.size {t : ι → Finset α} (m : FiniteMatching t) : ℕ :=
  Fintype.card ι - m.unmatched.card

noncomputable def hallDeficiency (t : ι → Finset α) : ℕ :=
  Finset.univ.sup (fun A : Finset ι => A.card - (A.biUnion t).card)

theorem subset_deficiency_le (t : ι → Finset α) (A : Finset ι) :
    A.card - (A.biUnion t).card ≤ hallDeficiency t := by
  exact Finset.le_sup (f := fun A : Finset ι => A.card - (A.biUnion t).card) (Finset.mem_univ A)

theorem hallDeficiency_le_card (t : ι → Finset α) : hallDeficiency t ≤ Fintype.card ι := by
  apply Finset.sup_le
  intro A hA
  exact (Nat.sub_le _ _).trans (Finset.card_le_univ A)

theorem neighbor_card_add_deficiency (t : ι → Finset α) (A : Finset ι) :
    A.card ≤ (A.biUnion t).card + hallDeficiency t := by
  have h := subset_deficiency_le t A
  omega

theorem dummy_neighbors_union (t : ι → Finset α) (d : ℕ) (A : Finset ι) (hA : A.Nonempty) :
    (A.biUnion (fun i => (t i).disjSum (Finset.univ : Finset (Fin d)))) =
      (A.biUnion t).disjSum (Finset.univ : Finset (Fin d)) := by
  ext v
  cases v with
  | inl a => simp
  | inr b => simpa using hA

theorem exists_matching_of_hall_slack (t : ι → Finset α) (d : ℕ)
    (hd : ∀ A : Finset ι, A.card ≤ (A.biUnion t).card + d) :
    ∃ m : FiniteMatching t, m.unmatched.card ≤ d := by
  classical
  let u : ι → Finset (α ⊕ Fin d) := fun i => (t i).disjSum Finset.univ
  have hh : ∀ A : Finset ι, A.card ≤ (A.biUnion u).card := by
    intro A
    by_cases hA : A.Nonempty
    · dsimp [u]
      rw [dummy_neighbors_union t d A hA, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
      exact hd A
    · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      simp [he]
  obtain ⟨f, hfi, hfs⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' u).mp hh
  let U : Finset ι := Finset.univ.filter (fun i => ∃ b : Fin d, f i = Sum.inr b)
  have hright : ∀ i : U, ∃ b : Fin d, f i = Sum.inr b := by
    intro i
    exact (Finset.mem_filter.mp i.property).2
  choose r hr using hright
  have hri : Function.Injective r := by
    intro i j hij
    apply Subtype.ext
    apply hfi
    rw [hr i, hr j, hij]
  have hcard : U.card ≤ d := by
    have h := Fintype.card_le_of_injective r hri
    simpa only [Fintype.card_coe, Fintype.card_fin] using h
  have hleft : ∀ i : {i // i ∉ U}, ∃ a : α, f i = Sum.inl a := by
    intro i
    cases hf : f i with
    | inl a => exact ⟨a, rfl⟩
    | inr b =>
      exfalso
      apply i.property
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, hf⟩⟩
  choose g hg using hleft
  have hgi : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply hfi
    rw [hg i, hg j, hij]
  have hgs : ∀ i : {i // i ∉ U}, g i ∈ t i := by
    intro i
    have h := hfs i.val
    rw [hg i] at h
    exact Finset.inl_mem_disjSum.mp h
  exact ⟨⟨U, g, hgi, hgs⟩, hcard⟩

theorem matching_hall_slack {t : ι → Finset α} (m : FiniteMatching t) (A : Finset ι) :
    A.card ≤ (A.biUnion t).card + m.unmatched.card := by
  let f : {i // i ∈ A \ m.unmatched} → {a // a ∈ A.biUnion t} := fun i =>
    ⟨m.assign ⟨i.val, (Finset.mem_sdiff.mp i.property).2⟩,
      Finset.mem_biUnion.mpr ⟨i.val, (Finset.mem_sdiff.mp i.property).1,
        m.supported ⟨i.val, (Finset.mem_sdiff.mp i.property).2⟩⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h := m.injective (congrArg Subtype.val hij)
    exact Subtype.ext (congrArg (fun k : {i // i ∉ m.unmatched} => k.val) h)
  have hcard : (A \ m.unmatched).card ≤ (A.biUnion t).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hsum := Finset.card_sdiff_add_card_inter A m.unmatched
  have hi := Finset.card_le_card (Finset.inter_subset_right : A ∩ m.unmatched ⊆ m.unmatched)
  omega

theorem hallDeficiency_le_unmatched {t : ι → Finset α} (m : FiniteMatching t) :
    hallDeficiency t ≤ m.unmatched.card := by
  apply Finset.sup_le
  intro A hA
  have h := matching_hall_slack m A
  omega

theorem exists_maximum_matching (t : ι → Finset α) :
    ∃ m : FiniteMatching t,
      m.unmatched.card = hallDeficiency t ∧
      m.size = Fintype.card ι - hallDeficiency t ∧
      ∀ m' : FiniteMatching t, m'.size ≤ m.size := by
  obtain ⟨m, hm⟩ := exists_matching_of_hall_slack t (hallDeficiency t) (neighbor_card_add_deficiency t)
  have he : m.unmatched.card = hallDeficiency t := le_antisymm hm (hallDeficiency_le_unmatched m)
  refine ⟨m, he, ?_, ?_⟩
  · simp only [FiniteMatching.size, he]
  · intro m'
    have h := hallDeficiency_le_unmatched m'
    dsimp [FiniteMatching.size]
    rw [he]
    omega

end StochasticMatching
