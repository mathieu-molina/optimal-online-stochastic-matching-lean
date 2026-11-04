import Matching.CursorAcceptance

/-! The complete scheduling continuation log is preserved by each actual
residual restart, including adaptive posterior changes and terminal output.
-/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
variable {J : Type} [Fintype J] [DecidableEq J] [MeasurableSpace J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
variable {H ι : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

noncomputable def cursorRestartValue (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (x : RoutingCursor n H ι) (e : (Unit ⊕ (ℝ × Option J)) × (J → ℝ)) : CompletionLog J :=
  Sum.elim (fun _ => s.cursorLog n label L elapsed k x)
    (fun y => s.cursorContinuation n label L hL elapsed he k (y, e.2))
    (s.cursorUpdate n label (x, e.1))

theorem currentRestart_terminal (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) (x : H × ℝ)
    (Λ : ℝ) (hΛ : ∀ t ∈ Icc 0 ((s.routingService label).curves x).deadline,
      ∑ a, ((s.routingService label).curves x).rate a t ≤ Λ) (z : Option J → ℝ)
    (ht : z ∈ (((s.routingService label).curves x).withRejectionClock Λ hΛ).terminalSurvival) :
    s.cursorRestartValue (n + 1) label L hL elapsed he k (.inl x)
      (firstEventRestart (((s.routingService label).curves x).withRejectionClock Λ hΛ) z) =
      s.cursorContinuation (n + 1) label L hL elapsed he k (.inl x, fun a => z (some a)) := by
  rw [firstEventRestart_of_terminal _ ht]
  change L x.1 = _
  symm
  apply s.cursorContinuation_terminal n label hinj L hL elapsed he k x
  intro a
  exact mem_univ_pi.mp ht (some a)

theorem currentRestart_winner (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) (x : H × ℝ)
    (Λ : ℝ) (hΛ : ∀ t ∈ Icc 0 ((s.routingService label).curves x).deadline,
      ∑ a, ((s.routingService label).curves x).rate a t ≤ Λ) (z : Option J → ℝ)
    (hz : ∀ a, 0 < z a) (a : Option J)
    (hw : z ∈ variableWinner (((s.routingService label).curves x).withRejectionClock Λ hΛ).service
      ((s.routingService label).curves x).deadline a) :
    s.cursorRestartValue (n + 1) label L hL elapsed he k (.inl x)
      (firstEventRestart (((s.routingService label).curves x).withRejectionClock Λ hΛ) z) =
      s.cursorContinuation (n + 1) label L hL elapsed he k (.inl x, fun a => z (some a)) := by
  let p := (s.routingService label).curves x
  let q := p.withRejectionClock Λ hΛ
  rw [firstEventRestart_of_winner _ a hw]
  cases a with
  | none =>
    let t := cappedHit (q.service none) q.deadline (z none)
    have ht0 : 0 ≤ t := (cappedHit_bounds (q.service_continuous none) q.deadline_pos.le).1
    have htT : t < p.deadline := hw.1
    have hr : (recycledObservation q none z).2 = fun a => z (some a) - p.service a t := by
      funext a
      simp only [recycledObservation, survivorSlot_none]
      rfl
    change s.cursorContinuation (n + 1) label L hL elapsed he k
      (.inl (s.advanceRoutingTime label (x, t)), (recycledObservation q none z).2) = _
    rw [hr]
    exact s.cursorContinuation_rejected n label hinj L hL elapsed he k x (fun a => z (some a)) t ht0 htT
  | some a =>
    have hw' := p.rejectionClock_job_winner Λ hΛ z a hw
    obtain ⟨j, rfl⟩ := s.routingService_winner_has_label label x (fun a => z (some a))
      (fun a => hz (some a)) a hw'
    exact s.cursorContinuation_accepted n label hinj L hL elapsed he k x
      (fun a => z (some a)) (recycledObservation q (some (label j)) z).2
      (fun i => hz (some (label i))) j hw'
      (s.recycled_active_residual label hinj x Λ hΛ z j)

theorem cursorRestartValue_descend (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (L : H → CompletionLog J) (hL : Measurable L) (elapsed : H → ℝ) (he : Measurable elapsed)
    (k : ℕ) (j : ι) (x : RoutingCursor n (H × ℝ) {i : ι // i ≠ j})
    (e : (Unit ⊕ (ℝ × Option J)) × (J → ℝ)) :
    s.cursorRestartValue (n + 1) label L hL elapsed he k (.inr ⟨j, x⟩) e =
      (s.next j).cursorRestartValue n (fun i => label i.1)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1) x e := by
  unfold cursorRestartValue
  change Sum.elim _ _ (Sum.map id _ ((s.next j).cursorUpdate n (fun i => label i.1) (x, e.1))) = _
  cases hu : (s.next j).cursorUpdate n (fun i => label i.1) (x, e.1) <;> rfl

theorem cursorRestartValue_preserved (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) (x : RoutingCursor n H ι)
    (Λ : ℝ) (hΛ : ∀ t ∈ Icc 0 ((s.cursorService n label).curves x).deadline,
      ∑ a, ((s.cursorService n label).curves x).rate a t ≤ Λ) (z : Option J → ℝ) (hz : ∀ a, 0 < z a) :
    let q := ((s.cursorService n label).curves x).withRejectionClock Λ hΛ
    z ∈ q.terminalSurvival ∨ (∃ a, z ∈ variableWinner q.service q.deadline a) →
    s.cursorRestartValue n label L hL elapsed he k x (firstEventRestart q z) =
      s.cursorContinuation n label L hL elapsed he k (x, fun a => z (some a)) := by
  induction n generalizing H ι k with
  | zero =>
    intro q _
    generalize firstEventRestart q z = e
    rcases e with ⟨e, r⟩
    cases e <;> rfl
  | succ n ih =>
    intro q hpart
    cases x with
    | inl x =>
      rcases hpart with ht | ⟨a, ha⟩
      · exact s.currentRestart_terminal n label hinj L hL elapsed he k x Λ hΛ z ht
      · exact s.currentRestart_winner n label hinj L hL elapsed he k x Λ hΛ z hz a ha
    | inr x =>
      obtain ⟨j, x⟩ := x
      rw [s.cursorRestartValue_descend n label L hL elapsed he k j x]
      exact ih (s.next j) (fun i => label i.1) (hinj.comp Subtype.val_injective)
        (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
        (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1)
        x hΛ hpart

theorem cursorRestartValue_preserved_ae (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) (x : RoutingCursor n H ι)
    (Λ : ℝ) (hΛ : ∀ t ∈ Icc 0 ((s.cursorService n label).curves x).deadline,
      ∑ a, ((s.cursorService n label).curves x).rate a t ≤ Λ) :
    let q := ((s.cursorService n label).curves x).withRejectionClock Λ hΛ
    ∀ᵐ z ∂(independentExponentials (ι := Option J)),
      s.cursorRestartValue n label L hL elapsed he k x (firstEventRestart q z) =
        s.cursorContinuation n label L hL elapsed he k (x, fun a => z (some a)) := by
  intro q
  filter_upwards [q.no_completion_or_unique_ae, independentExponentials_ae_pos (ι := Option J)] with z hw hz
  apply s.cursorRestartValue_preserved n label hinj L hL elapsed he k x Λ hΛ z hz
  rcases hw with ht | ⟨a, ha, _⟩
  · exact Or.inl ht
  · exact Or.inr ⟨a, ha⟩

end StochasticMatching.PosteriorStage
