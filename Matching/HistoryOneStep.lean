import Matching.HistoryMarkedLaw

/-! The no-completion branch and the exhaustive one-step law for random
histories. The initial joint law is a history measure times fresh exponentials.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching.HistoryServiceFamily

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : HistoryServiceFamily H ι)

def terminalThreshold (h : H) (i : ι) : ℝ :=
  (p.curves h).service i (p.curves h).deadline

theorem measurable_terminalThreshold : Measurable p.terminalThreshold := by
  apply measurable_pi_lambda
  intro i
  exact (p.measurable_service i).comp (measurable_id.prodMk p.deadline_measurable)

theorem terminalThreshold_nonneg (h : H) (i : ι) : 0 ≤ p.terminalThreshold h i := by
  change 0 ≤ (p.curves h).service i (p.curves h).deadline
  rw [← (p.curves h).service_zero i]
  exact (p.curves h).service_monotone i ⟨le_refl _, (p.curves h).deadline_pos.le⟩
    ⟨(p.curves h).deadline_pos.le, le_refl _⟩ (p.curves h).deadline_pos.le

def terminalEvent : Set (H × (ι → ℝ)) := historySurvival p.terminalThreshold

theorem measurable_terminalEvent : MeasurableSet p.terminalEvent :=
  measurable_historySurvival p.measurable_terminalThreshold

noncomputable def terminalHistoryMeasure (ν : Measure H) : Measure H :=
  ν.withDensity (fun h => independentExponentials (survivalBox (p.terminalThreshold h)))

theorem terminal_factorization (ν : Measure H) :
    Measure.map (residualObservation p.terminalThreshold)
      ((ν.prod independentExponentials).restrict p.terminalEvent) =
      (p.terminalHistoryMeasure ν).prod independentExponentials :=
  history_survival_factorization p.measurable_terminalThreshold p.terminalThreshold_nonneg ν

theorem winner_disjoint : Pairwise (fun i j => Disjoint (p.winner i) (p.winner j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact Set.disjoint_left.mp ((p.curves x.1).winner_disjoint hij) hi hj

theorem winner_disjoint_terminal (j : ι) : Disjoint p.terminalEvent (p.winner j) := by
  apply Set.disjoint_left.mpr
  intro x ht hj
  exact (p.curves x.1).winner_subset_completion j hj (mem_univ_pi.mpr ht)

theorem no_completion_or_unique_ae (ν : Measure H) :
    ∀ᵐ x ∂ν.prod independentExponentials, x ∈ p.terminalEvent ∨ ∃! j, x ∈ p.winner j := by
  have hm : MeasurableSet (p.terminalEvent ∪ ⋃ j, p.winner j) :=
    p.measurable_terminalEvent.union (MeasurableSet.iUnion p.measurable_winner)
  have hcover : ∀ᵐ x ∂ν.prod independentExponentials,
      x ∈ p.terminalEvent ∪ ⋃ j, p.winner j := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem hm).mpr
    apply Filter.Eventually.of_forall
    intro h
    filter_upwards [(p.curves h).no_completion_or_unique_ae] with z hz
    rcases hz with hs | ⟨j, hj, _⟩
    · exact Or.inl (mem_univ_pi.mp hs)
    · exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
  filter_upwards [hcover] with x hx
  rcases hx with ht | hw
  · exact Or.inl ht
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    right
    refine ⟨j, hj, ?_⟩
    intro i hi
    by_cases hij : i = j
    · exact hij
    · exact False.elim (Set.disjoint_left.mp (p.winner_disjoint hij) hi hj)

theorem segment_measure_decomposition (ν : Measure H) :
    ν.prod independentExponentials =
      (ν.prod independentExponentials).restrict p.terminalEvent +
        Measure.sum (fun j => (ν.prod independentExponentials).restrict (p.winner j)) := by
  have hcover : (p.terminalEvent ∪ ⋃ j, p.winner j : Set (H × (ι → ℝ))) =ᵐ[
      ν.prod independentExponentials] (univ : Set (H × (ι → ℝ))) := by
    filter_upwards [p.no_completion_or_unique_ae ν] with x hx
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      rcases hx with ht | ⟨j, hj, _⟩
      · exact Or.inl ht
      · exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
  have hd : Disjoint p.terminalEvent (⋃ j, p.winner j) := by
    apply Set.disjoint_left.mpr
    intro x ht hw
    obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    exact Set.disjoint_left.mp (p.winner_disjoint_terminal j) ht hj
  have h := Measure.restrict_congr_set (μ := ν.prod independentExponentials) hcover
  rw [Measure.restrict_univ, Measure.restrict_union hd (MeasurableSet.iUnion p.measurable_winner),
    Measure.restrict_iUnion p.winner_disjoint p.measurable_winner] at h
  exact h.symm

/-- A full one-step formula for functions that can depend on both the incoming
history and the complete fresh demand vector. -/
theorem one_step_original_sample_lintegral (ν : Measure H)
    (f : H × (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂ν.prod independentExponentials) =
      ∫⁻ h, (ENNReal.ofReal (Real.exp (-(∑ i, p.terminalThreshold h i))) *
        (∫⁻ y, f (h, fun i => y i + p.terminalThreshold h i) ∂independentExponentials) +
      ∑ j, ∫⁻ t in Icc 0 (p.curves h).deadline,
        p.markedDensity j (h, t) *
          (∫⁻ y, f (h, (p.curves h).reconstructMarked j (t, y)) ∂independentExponentials)) ∂ν := by
  rw [lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro h
  exact (p.curves h).one_step_original_sample_lintegral (fun z => f (h, z))
    (hf.comp (measurable_const.prodMk measurable_id))

end StochasticMatching.HistoryServiceFamily
