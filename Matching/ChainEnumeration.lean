import Matching.ChainCancellation
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Basic

/-! A finite nested family can be enumerated in inclusion order. -/

namespace StochasticMatching
variable {α : Type*} [DecidableEq α] [PartialOrder α]

theorem nested_family_enumeration (C : Finset α) (hC : NestedFamily C) :
    ∃ e : Fin C.card → α, Monotone e ∧ ∀ a, a ∈ C ↔ ∃ k, e k = a := by
  classical
  letI : IsTotal C (· ≤ ·) := ⟨fun a b => hC a a.2 b b.2⟩
  letI : LinearOrder C := (inferInstance : LinearOrder (AsLinearOrder C))
  let e : Fin C.card ≃o C := Fintype.orderIsoFinOfCardEq C (Fintype.card_coe C)
  refine ⟨fun k => (e k : α), ?_, ?_⟩
  · exact e.monotone
  · intro a
    constructor
    · intro ha
      exact ⟨e.symm ⟨a, ha⟩, congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)⟩
    · rintro ⟨k, rfl⟩
      exact (e k).2

theorem forall_mem_iff_forall_enumeration {n : ℕ} (C : Finset α) (e : Fin n → α)
    (he : ∀ a, a ∈ C ↔ ∃ k, e k = a) (P : α → Prop) :
    (∀ a ∈ C, P a) ↔ ∀ k, P (e k) := by
  constructor
  · intro h k
    exact h (e k) ((he (e k)).mpr ⟨k, rfl⟩)
  · intro h a ha
    obtain ⟨k, rfl⟩ := (he a).mp ha
    exact h k

end StochasticMatching
