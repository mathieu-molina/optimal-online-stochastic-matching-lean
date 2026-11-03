import Matching.MeasurableCursorBranches

/-! Total, measurable event updates with exact remaining-time projection.
The guard acts only outside the valid arrival-time window.
-/
open MeasureTheory Set
namespace StochasticMatching
abbrev PositiveHorizon := {t : ℝ // 0 < t}

noncomputable def remainingTimeAfter (x : PositiveHorizon × ℝ) : PositiveHorizon := by
  classical
  exact ⟨if 0 ≤ x.2 ∧ x.2 < x.1.1 then x.1.1 - x.2 else x.1.1, by
    split_ifs with hx
    · exact sub_pos.mpr hx.2
    · exact x.1.2⟩

theorem measurable_remainingTimeAfter : Measurable remainingTimeAfter := by
  apply Measurable.subtype_mk
  exact Measurable.ite ((measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (measurable_subtype_coe.comp measurable_fst)))
    ((measurable_subtype_coe.comp measurable_fst).sub measurable_snd)
    (measurable_subtype_coe.comp measurable_fst)

noncomputable def remainingTimeUpdate {E : Type*} (x : PositiveHorizon × (Unit ⊕ (ℝ × E))) :
    Unit ⊕ PositiveHorizon :=
  Sum.elim (fun _ => .inl ()) (fun e => .inr (remainingTimeAfter (x.1, e.1))) x.2

theorem measurable_remainingTimeUpdate {E : Type*} [MeasurableSpace E] :
    Measurable (remainingTimeUpdate (E := E)) := by
  refine measurable_prod_sum_elim (fun _ : PositiveHorizon × Unit => (Sum.inl () : Unit ⊕ PositiveHorizon))
    (fun x : PositiveHorizon × (ℝ × E) => Sum.inr (remainingTimeAfter (x.1, x.2.1))) measurable_const ?_
  exact measurable_inr.comp (measurable_remainingTimeAfter.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))

variable {H E : Type*} [MeasurableSpace H] [MeasurableSpace E]

noncomputable def guardedEventUpdate (D : H → ℝ)
    (U : H × (Unit ⊕ (ℝ × E)) → Unit ⊕ H) (x : H × (Unit ⊕ (ℝ × E))) : Unit ⊕ H :=
  Sum.elim (fun _ => .inl ())
    (fun e => if 0 ≤ e.1 ∧ e.1 < D x.1 then U (x.1, .inr e) else .inr x.1) x.2

theorem measurable_guardedEventUpdate (D : H → ℝ) (hD : Measurable D)
    (U : H × (Unit ⊕ (ℝ × E)) → Unit ⊕ H) (hU : Measurable U) :
    Measurable (guardedEventUpdate D U) := by
  refine measurable_prod_sum_elim (fun _ : H × Unit => .inl ())
    (fun x : H × (ℝ × E) => if 0 ≤ x.2.1 ∧ x.2.1 < D x.1
      then U (x.1, .inr x.2) else .inr x.1) measurable_const ?_
  exact Measurable.ite
    ((measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_lt (measurable_fst.comp measurable_snd) (hD.comp measurable_fst)))
    (hU.comp (measurable_fst.prodMk (measurable_inr.comp measurable_snd)))
    (measurable_inr.comp measurable_fst)

theorem guardedEventUpdate_of_valid (D : H → ℝ)
    (U : H × (Unit ⊕ (ℝ × E)) → Unit ⊕ H) (h : H) (t : ℝ) (e : E)
    (ht0 : 0 ≤ t) (htD : t < D h) :
    guardedEventUpdate D U (h, .inr (t, e)) = U (h, .inr (t, e)) := if_pos ⟨ht0, htD⟩

theorem guardedEventUpdate_time_projection (D : H → ℝ) (hpos : ∀ h, 0 < D h)
    (U : H × (Unit ⊕ (ℝ × E)) → Unit ⊕ H)
    (hstep : ∀ h t e, 0 ≤ t → t < D h → ∃ y, U (h, .inr (t, e)) = .inr y ∧ D y = D h - t)
    (h : H) (e : Unit ⊕ (ℝ × E)) :
    Sum.map id (fun a => (⟨D a, hpos a⟩ : PositiveHorizon)) (guardedEventUpdate D U (h, e)) =
      remainingTimeUpdate ((⟨D h, hpos h⟩ : PositiveHorizon), e) := by
  classical
  cases e with
  | inl _ => rfl
  | inr e =>
    by_cases ht : 0 ≤ e.1 ∧ e.1 < D h
    · obtain ⟨y, hy, hD⟩ := hstep h e.1 e.2 ht.1 ht.2
      simp only [guardedEventUpdate, Sum.elim_inr, if_pos ht, hy, Sum.map_inr,
        remainingTimeUpdate]
      apply congrArg Sum.inr
      apply Subtype.ext
      simpa only [remainingTimeAfter, if_pos ht] using hD
    · simp only [guardedEventUpdate, Sum.elim_inr, if_neg ht, Sum.map_inr,
        remainingTimeUpdate]
      apply congrArg Sum.inr
      apply Subtype.ext
      simp only [remainingTimeAfter, if_neg ht]

end StochasticMatching
