import Matching.CursorCombinatorics

/-! Rejecting an arrival preserves the combinatorial cursor. Accepting an
available job increments its completion count and removes that label. -/
open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
variable {H ι J : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem cursorUpdate_rejected (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι) (t : ℝ) :
    ∃ y, s.cursorUpdate n label (x, .inr (t, none)) = .inr y ∧
      cursorDepth n y = cursorDepth n x ∧ cursorAvailable n label y = cursorAvailable n label x := by
  induction n generalizing H ι with
  | zero => exact ⟨_, rfl, rfl, rfl⟩
  | succ n ih =>
    cases x with
    | inl x => exact ⟨_, rfl, rfl, rfl⟩
    | inr x =>
      obtain ⟨y, hy, hd, ha⟩ := ih (s.next x.1) (fun i => label i.1) x.2
      refine ⟨.inr ⟨x.1, y⟩, ?_, congrArg (fun k => k + 1) hd, ha⟩
      change Sum.map id _ ((s.next x.1).cursorUpdate n (fun i => label i.1) (x.2, .inr (t, none))) = _
      rw [hy]
      rfl

theorem cursorUpdate_accepted (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : RoutingCursor n H ι) (t : ℝ) (a : J)
    (ha : a ∈ cursorAvailable n label x) :
    ∃ y, s.cursorUpdate n label (x, .inr (t, some a)) = .inr y ∧
      cursorDepth n y = cursorDepth n x + 1 ∧
      cursorAvailable n label y ⊆ (cursorAvailable n label x).erase a := by
  induction n generalizing H ι with
  | zero => simp [cursorAvailable] at ha
  | succ n ih =>
    cases x with
    | inl x =>
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha
      subst a
      let v := s.advanceRoutingTime label (x, t)
      refine ⟨.inr ⟨j, initialRoutingCursor n v⟩, ?_, ?_, ?_⟩
      · change Sum.inr (acceptedRoutingCursor n label (label j) v) = _
        rw [acceptedRoutingCursor_at_label n label hinj]
      · change cursorDepth n (initialRoutingCursor n v) + 1 = 0 + 1
        rw [cursorDepth_initial]
      · intro b hb
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp
          (cursorAvailable_subset_labels n (fun i : {i : ι // i ≠ j} => label i.1)
            (initialRoutingCursor n v) hb)
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_image.mpr ⟨i.1, Finset.mem_univ _, hi⟩⟩
        intro he
        exact i.2 (hinj (hi.trans he))
    | inr x =>
      obtain ⟨y, hy, hd, ha'⟩ := ih (s.next x.1) (fun i => label i.1)
        (hinj.comp Subtype.val_injective) x.2 ha
      refine ⟨.inr ⟨x.1, y⟩, ?_, ?_, ha'⟩
      · change Sum.map id _ ((s.next x.1).cursorUpdate n (fun i => label i.1) (x.2, .inr (t, some a))) = _
        rw [hy]
        rfl
      · change cursorDepth n y + 1 = (cursorDepth n x.2 + 1) + 1
        rw [hd]

end StochasticMatching.PosteriorStage
