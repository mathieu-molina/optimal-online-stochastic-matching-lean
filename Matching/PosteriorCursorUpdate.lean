import Matching.PosteriorRoutingCursor
import Matching.MeasurableCursorBranches

/-! The actual arrival-driven posterior-policy update: rejected arrivals
advance within a segment, accepted jobs select its posterior child, and a
terminal event stops the execution.
-/
open MeasureTheory Set
namespace StochasticMatching
variable {H ι J : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J]

noncomputable def acceptedRoutingCursor (n : ℕ) (label : ι → J) (a : J) (x : H × ℝ) :
    RoutingCursor (n + 1) H ι := by
  classical
  exact if h : ∃ j, label j = a then
    Sum.inr ⟨h.choose, initialRoutingCursor n x⟩ else Sum.inl x

theorem measurable_acceptedRoutingCursor (n : ℕ) (label : ι → J) (a : J) :
    Measurable (acceptedRoutingCursor (H := H) n label a) := by
  classical
  unfold acceptedRoutingCursor
  split_ifs with h
  · exact measurable_inr.comp ((measurable_sigma_injection h.choose).comp (measurable_initialRoutingCursor n))
  · exact measurable_inl

theorem acceptedRoutingCursor_at_label (n : ℕ) (label : ι → J) (hinj : Function.Injective label)
    (j : ι) (x : H × ℝ) : acceptedRoutingCursor n label (label j) x =
      Sum.inr ⟨j, initialRoutingCursor n x⟩ := by
  classical
  have h : ∃ i, label i = label j := ⟨j, rfl⟩
  have he : h.choose = j := hinj h.choose_spec
  simp only [acceptedRoutingCursor, dif_pos h]
  apply congrArg Sum.inr
  exact congrArg (fun k : ι => (⟨k, initialRoutingCursor n x⟩ :
    (k : ι) × RoutingCursor n (H × ℝ) {i : ι // i ≠ k})) he

namespace PosteriorStage

noncomputable def advanceRoutingTime (s : PosteriorStage H ι) (label : ι → J)
    (x : (H × ℝ) × ℝ) : H × ℝ :=
  (x.1.1, (s.service.labelled label).shiftOffset x.1 + x.2)

theorem measurable_advanceRoutingTime (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.advanceRoutingTime label) :=
  (measurable_fst.comp measurable_fst).prodMk
    (((s.service.labelled label).measurable_shiftOffset.comp measurable_fst).add measurable_snd)

noncomputable def currentRoutingStep (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : (H × ℝ) × (Unit ⊕ (ℝ × Option J))) : Unit ⊕ RoutingCursor (n + 1) H ι :=
  Sum.elim (fun _ => Sum.inl ()) (fun e =>
    let y := s.advanceRoutingTime label (x.1, e.1)
    Sum.inr (e.2.elim (Sum.inl y) (fun a => acceptedRoutingCursor n label a y))) x.2

variable [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem measurable_currentRoutingStep (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.currentRoutingStep n label) := by
  have hchoice : Measurable (fun x : (H × ℝ) × Option J =>
      Sum.inr (x.2.elim (Sum.inl x.1) (fun a => acceptedRoutingCursor n label a x.1)) :
        (H × ℝ) × Option J → Unit ⊕ RoutingCursor (n + 1) H ι) := by
    apply measurable_from_prod_countable
    intro a
    cases a with
    | none => exact measurable_inr.comp measurable_inl
    | some a => exact measurable_inr.comp (measurable_acceptedRoutingCursor n label a)
  refine measurable_prod_sum_elim (fun _ : (H × ℝ) × Unit => Sum.inl ())
    (fun y : (H × ℝ) × (ℝ × Option J) => Sum.inr (y.2.2.elim (Sum.inl (s.advanceRoutingTime label (y.1, y.2.1)))
      (fun a => acceptedRoutingCursor n label a (s.advanceRoutingTime label (y.1, y.2.1)))))
    measurable_const ?_
  exact hchoice.comp
      (((s.measurable_advanceRoutingTime label).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))

noncomputable def cursorUpdate : (n : ℕ) → {H ι : Type} → [MeasurableSpace H] →
    [Fintype ι] → [DecidableEq ι] → PosteriorStage H ι → (ι → J) →
    RoutingCursor n H ι × (Unit ⊕ (ℝ × Option J)) → Unit ⊕ RoutingCursor n H ι
  | 0, _, _, _, _, _, s, label, x =>
      Sum.elim (fun _ => Sum.inl ())
        (fun e => Sum.inr (s.advanceRoutingTime label (x.1, e.1))) x.2
  | n + 1, _, _, _, _, _, s, label, x =>
      Sum.elim (fun y => s.currentRoutingStep n label (y, x.2))
        (fun y => Sum.map id (fun z => Sum.inr ⟨y.1, z⟩)
          (cursorUpdate n (s.next y.1) (fun i => label i.1) (y.2, x.2))) x.1

theorem measurable_cursorUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.cursorUpdate n label) := by
  induction n generalizing H ι with
  | zero =>
    refine measurable_prod_sum_elim (fun _ : (H × ℝ) × Unit => Sum.inl ())
      (fun y : (H × ℝ) × (ℝ × Option J) => Sum.inr (s.advanceRoutingTime label (y.1, y.2.1))) measurable_const ?_
    exact measurable_inr.comp ((s.measurable_advanceRoutingTime label).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  | succ n ih =>
    refine measurable_sum_prod_elim (s.currentRoutingStep n label)
      (fun y : ((j : ι) × RoutingCursor n (H × ℝ) {i : ι // i ≠ j}) × (Unit ⊕ (ℝ × Option J)) =>
        Sum.map id (fun z => Sum.inr ⟨y.1.1, z⟩)
        ((s.next y.1.1).cursorUpdate n (fun i => label i.1) (y.1.2, y.2)))
      (s.measurable_currentRoutingStep n label) ?_
    refine measurable_sigma_prod_elim
      (fun (j : ι) (y : RoutingCursor n (H × ℝ) {i : ι // i ≠ j} × (Unit ⊕ (ℝ × Option J))) =>
        Sum.map id (fun z => (Sum.inr ⟨j, z⟩ : RoutingCursor (n + 1) H ι))
          ((s.next j).cursorUpdate n (fun i => label i.1) y)) ?_
    intro j
    exact (measurable_id.sumMap (measurable_inr.comp (measurable_sigma_injection j))).comp
      (ih (s.next j) (fun i => label i.1))

theorem cursorUpdate_terminal (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι) : s.cursorUpdate n label (x, .inl ()) = .inl () := by
  induction n generalizing H ι with
  | zero => rfl
  | succ n ih =>
    cases x with
    | inl x => rfl
    | inr x =>
      change Sum.map id _ ((s.next x.1).cursorUpdate n (fun i => label i.1) (x.2, .inl ())) = _
      rw [ih]
      rfl

end PosteriorStage
end StochasticMatching
