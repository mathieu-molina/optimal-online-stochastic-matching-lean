import Matching.OneStepLaw

/-! Measurable service curves selected by an observed history, with a
history-dependent positive deadline. The history is not assumed independent
of any particular original sample; independence of fresh residuals will be
an explicit hypothesis when applying the product-measure laws.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

theorem measurable_cappedHit_variableDeadline {Ω : Type*} [MeasurableSpace Ω]
    {a : Ω → ℝ → ℝ} {z T : Ω → ℝ} (hT : ∀ ω, 0 ≤ T ω)
    (hTm : Measurable T) (ha : ∀ ω, Continuous (a ω))
    (hm : ∀ ω, MonotoneOn (a ω) (Icc 0 (T ω)))
    (ham : ∀ t, Measurable (fun ω => a ω t)) (hz : Measurable z) :
    Measurable (fun ω => cappedHit (a ω) (T ω) (z ω)) := by
  apply measurable_of_Iic
  intro t
  by_cases ht0 : 0 ≤ t
  · have heq : (fun ω => cappedHit (a ω) (T ω) (z ω)) ⁻¹' Iic t =
        {ω | T ω ≤ t} ∪ {ω | z ω ≤ a ω t} := by
      ext ω
      change cappedHit (a ω) (T ω) (z ω) ≤ t ↔ T ω ≤ t ∨ z ω ≤ a ω t
      by_cases ht : T ω ≤ t
      · exact ⟨fun _ => Or.inl ht, fun _ => (cappedHit_bounds (ha ω) (hT ω)).2.trans ht⟩
      · rw [or_iff_right ht]
        exact cappedHit_le_iff (ha ω) (hT ω) (hm ω) ht0 (lt_of_not_ge ht)
    rw [heq]
    exact (measurableSet_le hTm measurable_const).union (measurableSet_le hz (ham t))
  · have heq : (fun ω => cappedHit (a ω) (T ω) (z ω)) ⁻¹' Iic t = ∅ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le (lt_of_not_ge ht0) (cappedHit_bounds (ha ω) (hT ω)).1)
    rw [heq]
    exact MeasurableSet.empty

structure HistoryServiceFamily (H ι : Type*) [MeasurableSpace H] where
  curves : H → ServiceCurveFamily ι
  deadline_measurable : Measurable (fun h => (curves h).deadline)
  service_at_measurable : ∀ i t, Measurable (fun h => (curves h).service i t)
  rate_at_measurable : ∀ i t, Measurable (fun h => (curves h).rate i t)

namespace HistoryServiceFamily

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : HistoryServiceFamily H ι)

theorem measurable_service (i : ι) :
    Measurable (fun x : H × ℝ => (p.curves x.1).service i x.2) :=
  (measurable_uncurry_of_continuous_of_measurable
    (fun h => (p.curves h).service_continuous i) (p.service_at_measurable i)).comp measurable_swap

theorem measurable_rate (i : ι) :
    Measurable (fun x : H × ℝ => (p.curves x.1).rate i x.2) :=
  (measurable_uncurry_of_continuous_of_measurable
    (fun h => (p.curves h).rate_continuous i) (p.rate_at_measurable i)).comp measurable_swap

noncomputable def clock (j : ι) (x : H × (ι → ℝ)) : ℝ :=
  cappedHit ((p.curves x.1).service j) (p.curves x.1).deadline (x.2 j)

theorem measurable_clock (j : ι) : Measurable (p.clock j) := by
  exact measurable_cappedHit_variableDeadline
    (fun x => (p.curves x.1).deadline_pos.le)
    (p.deadline_measurable.comp measurable_fst)
    (fun x => (p.curves x.1).service_continuous j)
    (fun x => (p.curves x.1).service_monotone j)
    (fun t => (p.service_at_measurable j t).comp measurable_fst)
    ((measurable_pi_apply j).comp measurable_snd)

def winner (j : ι) : Set (H × (ι → ℝ)) :=
  {x | x.2 ∈ variableWinner (p.curves x.1).service (p.curves x.1).deadline j}

theorem measurable_winner (j : ι) : MeasurableSet (p.winner j) := by
  have heq : p.winner j = {x | p.clock j x < (p.curves x.1).deadline} ∩
      ⋂ i : {i : ι // i ≠ j}, {x | p.clock j x < p.clock i.1 x} := by
    ext x
    simp [winner, variableWinner, clock]
  rw [heq]
  exact (measurableSet_lt (p.measurable_clock j)
    (p.deadline_measurable.comp measurable_fst)).inter
    (MeasurableSet.iInter (fun i => measurableSet_lt (p.measurable_clock j) (p.measurable_clock i.1)))

noncomputable def observation (j : ι) (x : H × (ι → ℝ)) :
    (H × ℝ) × ({i : ι // i ≠ j} → ℝ) :=
  ((x.1, p.clock j x), fun i => x.2 i.1 - (p.curves x.1).service i.1 (p.clock j x))

theorem measurable_observation (j : ι) : Measurable (p.observation j) := by
  apply Measurable.prodMk (measurable_fst.prodMk (p.measurable_clock j))
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i.1).comp measurable_snd).sub
    ((p.measurable_service i.1).comp (measurable_fst.prodMk (p.measurable_clock j)))

def timeWindow : Set (H × ℝ) := {x | x.2 ∈ Icc 0 (p.curves x.1).deadline}

theorem measurable_timeWindow : MeasurableSet p.timeWindow :=
  (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (p.deadline_measurable.comp measurable_fst))

noncomputable def markedDensity (j : ι) (x : H × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((p.curves x.1).rate j x.2 * Real.exp (-(∑ i, (p.curves x.1).service i x.2)))

theorem measurable_markedDensity (j : ι) : Measurable (p.markedDensity j) := by
  have hs : Measurable (fun x : H × ℝ => ∑ i, (p.curves x.1).service i x.2) :=
    Finset.measurable_sum _ (fun i _ => p.measurable_service i)
  exact ((p.measurable_rate j).mul (Real.measurable_exp.comp hs.neg)).ennreal_ofReal

noncomputable def markedHistoryMeasure (ν : Measure H) (j : ι) : Measure (H × ℝ) :=
  (ν.prod volume).withDensity (p.timeWindow.indicator (p.markedDensity j))

end HistoryServiceFamily
end StochasticMatching
