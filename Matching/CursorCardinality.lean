import Matching.CursorDecisionStep
import Matching.AdaptiveBudget

/-! With a full recursion budget, the cursor loses exactly one available
vertex at each acceptance. Its depth is the actual matched cardinality. -/
open MeasureTheory Set
namespace StochasticMatching
variable {H ι J : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J]

theorem cursorAvailable_card_add_depth (n : ℕ) (label : ι → J) (hinj : Function.Injective label)
    (hn : Fintype.card ι ≤ n) (x : RoutingCursor n H ι) :
    (cursorAvailable n label x).card + cursorDepth n x = Fintype.card ι := by
  induction n generalizing H ι with
  | zero => simpa [cursorAvailable, cursorDepth] using Nat.eq_zero_of_le_zero hn |>.symm
  | succ n ih =>
      cases x with
      | inl x => simp [cursorAvailable, cursorDepth, Finset.card_image_of_injective _ hinj]
      | inr x =>
          have hc := survivor_card x.1
          have hbound : Fintype.card {i : ι // i ≠ x.1} ≤ n := by omega
          have h := ih (fun i : {i : ι // i ≠ x.1} => label i.1)
            (hinj.comp Subtype.val_injective) hbound x.2
          change (cursorAvailable n (fun i : {i : ι // i ≠ x.1} => label i.1) x.2).card +
            (cursorDepth n x.2 + 1) = _
          omega

theorem cursorAvailable_initial_full (n : ℕ) (label : ι → J) (hn : Fintype.card ι ≤ n) (h : H) :
    cursorAvailable n label (initialRoutingCursor n h) = Finset.univ.image label := by
  cases n with
  | zero =>
      have hi : IsEmpty ι := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
      letI := hi
      simp [cursorAvailable]
  | succ n => rfl

namespace PosteriorStage
variable [MeasurableSpace J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem cursorUpdate_accepted_exact (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (hn : Fintype.card ι ≤ n)
    (x : RoutingCursor n H ι) (t : ℝ) (a : J) (ha : a ∈ cursorAvailable n label x) :
    ∃ y, s.cursorUpdate n label (x, .inr (t, some a)) = .inr y ∧
      cursorAvailable n label y = (cursorAvailable n label x).erase a := by
  obtain ⟨y, hy, hd, hs⟩ := s.cursorUpdate_accepted n label hinj x t a ha
  refine ⟨y, hy, Finset.eq_of_subset_of_card_le hs ?_⟩
  have hx := cursorAvailable_card_add_depth n label hinj hn x
  have hh := cursorAvailable_card_add_depth n label hinj hn y
  rw [Finset.card_erase_of_mem ha]
  omega

end PosteriorStage
end StochasticMatching
