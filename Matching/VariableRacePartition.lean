import Matching.VariableRateRace

/-! Almost-sure exhaustion of a variable-rate segment by its marked completion
branches and its no-completion branch. The hypotheses are collected in a
record so a later adaptive-flow construction has one explicit interface.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

structure ServiceCurveFamily (ι : Type*) where
  deadline : ℝ
  deadline_pos : 0 < deadline
  service : ι → ℝ → ℝ
  rate : ι → ℝ → ℝ
  service_continuous : ∀ i, Continuous (service i)
  rate_continuous : ∀ i, Continuous (rate i)
  service_monotone : ∀ i, MonotoneOn (service i) (Icc 0 deadline)
  service_zero : ∀ i, service i 0 = 0
  rate_nonneg : ∀ i t, t ∈ Icc 0 deadline → 0 ≤ rate i t
  service_deriv : ∀ i t, t ∈ Icc 0 deadline → HasDerivAt (service i) (rate i t) t

namespace ServiceCurveFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

theorem measurable_clock (j : ι) :
    Measurable (fun z : ι → ℝ => cappedHit (p.service j) p.deadline (z j)) :=
  (measurable_cappedHit (p.service_continuous j) p.deadline_pos.le
    (p.service_monotone j)).comp (measurable_pi_apply j)

theorem measurable_observation (j : ι) :
    Measurable (variableObservation p.service p.deadline j) := by
  unfold variableObservation
  apply Measurable.prodMk (p.measurable_clock j)
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.1).sub
    ((p.service_continuous i.1).measurable.comp (p.measurable_clock j))

theorem measurable_winner (j : ι) :
    MeasurableSet (variableWinner p.service p.deadline j) := by
  have hs : variableWinner p.service p.deadline j =
      {z : ι → ℝ | cappedHit (p.service j) p.deadline (z j) < p.deadline} ∩
      ⋂ i : {i : ι // i ≠ j}, {z : ι → ℝ |
        cappedHit (p.service j) p.deadline (z j) < cappedHit (p.service i.1) p.deadline (z i.1)} := by
    ext z
    simp [variableWinner]
  rw [hs]
  exact (measurableSet_lt (p.measurable_clock j) measurable_const).inter
    (MeasurableSet.iInter (fun i => measurableSet_lt (p.measurable_clock j) (p.measurable_clock i.1)))

theorem winner_disjoint : Pairwise (fun i j =>
    Disjoint (variableWinner p.service p.deadline i) (variableWinner p.service p.deadline j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  exact lt_asymm (hi.2 j (Ne.symm hij)) (hj.2 i hij)

theorem winner_mass (j : ι) :
    independentExponentials (variableWinner p.service p.deadline j) =
      ∫⁻ t in Icc 0 p.deadline,
        ENNReal.ofReal (p.rate j t * Real.exp (-(∑ i, p.service i t))) := by
  have h := congrArg (fun μ : Measure (ℝ × ({i : ι // i ≠ j} → ℝ)) => μ univ)
    (variable_first_completion_marked_law p.service_continuous p.rate_continuous p.deadline_pos
      p.service_monotone p.service_zero p.rate_nonneg p.service_deriv j)
  dsimp only at h
  rw [Measure.map_apply (p.measurable_observation j) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    ← univ_prod_univ, Measure.prod_prod] at h
  simp only [measure_univ, mul_one] at h
  rw [variableMarkedTimeMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  exact h

theorem total_winner_mass :
    ∑ j, independentExponentials (variableWinner p.service p.deadline j) =
      ENNReal.ofReal (1 - Real.exp (-(∑ i, p.service i p.deadline))) := by
  simp_rw [p.winner_mass]
  have hsum : Continuous (fun t => ∑ i, p.service i t) :=
    continuous_finset_sum _ (fun i _ => p.service_continuous i)
  have hmeas : ∀ j, Measurable (fun t =>
      ENNReal.ofReal (p.rate j t * Real.exp (-(∑ i, p.service i t)))) := by
    intro j
    exact ((p.rate_continuous j).mul (Real.continuous_exp.comp hsum.neg)).measurable.ennreal_ofReal
  rw [← lintegral_finset_sum (μ := volume.restrict (Icc 0 p.deadline)) Finset.univ
    (fun j _ => hmeas j)]
  have heq : (∫⁻ t in Icc 0 p.deadline,
      ∑ j, ENNReal.ofReal (p.rate j t * Real.exp (-(∑ i, p.service i t)))) =
      ∫⁻ t in Icc 0 p.deadline,
        ENNReal.ofReal ((∑ j, p.rate j t) * Real.exp (-(∑ i, p.service i t))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      mul_nonneg (p.rate_nonneg j t ht) (Real.exp_pos _).le), Finset.sum_mul]
  rw [heq]
  have ha : Continuous (fun t => ∑ i, p.service i t) := by
    exact continuous_finset_sum _ (fun i _ => p.service_continuous i)
  have hr : Continuous (fun t => ∑ i, p.rate i t) := by
    exact continuous_finset_sum _ (fun i _ => p.rate_continuous i)
  apply integrated_hitting_density ha hr p.deadline_pos.le le_rfl
  · simp [p.service_zero]
  · intro t ht
    exact Finset.sum_nonneg (fun i _ => p.rate_nonneg i t ht)
  · intro t ht
    exact HasDerivAt.sum (u := Finset.univ) (fun i _ => p.service_deriv i t ht)

theorem winner_union_mass :
    independentExponentials (⋃ j, variableWinner p.service p.deadline j) =
      ENNReal.ofReal (1 - Real.exp (-(∑ i, p.service i p.deadline))) := by
  rw [measure_iUnion p.winner_disjoint p.measurable_winner, tsum_fintype, p.total_winner_mass]

def terminalSurvival : Set (ι → ℝ) := survivalBox (fun i => p.service i p.deadline)

theorem terminal_survival_probability :
    independentExponentials p.terminalSurvival =
      ENNReal.ofReal (Real.exp (-(∑ i, p.service i p.deadline))) := by
  apply survivalBox_measure_exp_sum
  intro i
  rw [← p.service_zero i]
  exact p.service_monotone i ⟨le_refl _, p.deadline_pos.le⟩
    ⟨p.deadline_pos.le, le_refl _⟩ p.deadline_pos.le

theorem winner_subset_completion (j : ι) :
    variableWinner p.service p.deadline j ⊆ p.terminalSurvivalᶜ := by
  intro z hz hs
  have htime := cappedHit_bounds (z := z j) (p.service_continuous j) p.deadline_pos.le
  have hdem := (cappedHit_le_iff (p.service_continuous j) p.deadline_pos.le
    (p.service_monotone j) htime.1 hz.1).mp (le_refl _)
  have hend : z j ≤ p.service j p.deadline :=
    hdem.trans (p.service_monotone j htime ⟨p.deadline_pos.le, le_refl _⟩ htime.2)
  have hs' : p.service j p.deadline < z j := mem_univ_pi.mp hs j
  exact (not_lt.mpr hend) hs'

/-- Up to a null set, either all demands survive to the deadline, or one and
only one job completes first strictly before it. -/
theorem no_completion_or_unique_ae :
    ∀ᵐ z ∂independentExponentials,
      z ∈ p.terminalSurvival ∨ ∃! j, z ∈ variableWinner p.service p.deadline j := by
  have hsurv : MeasurableSet p.terminalSurvival := measurableSet_survivalBox _
  have hunion : MeasurableSet (⋃ j, variableWinner p.service p.deadline j) :=
    MeasurableSet.iUnion p.measurable_winner
  have hsub : (⋃ j, variableWinner p.service p.deadline j) ⊆ p.terminalSurvivalᶜ :=
    iUnion_subset (fun j => p.winner_subset_completion j)
  have hmass : independentExponentials p.terminalSurvivalᶜ =
      independentExponentials (⋃ j, variableWinner p.service p.deadline j) := by
    rw [measure_compl hsurv (measure_ne_top _ _), measure_univ,
      p.terminal_survival_probability, p.winner_union_mass,
      ENNReal.ofReal_sub 1 (Real.exp_pos _).le, ENNReal.ofReal_one]
  have hzero : independentExponentials
      (p.terminalSurvivalᶜ \ ⋃ j, variableWinner p.service p.deadline j) = 0 := by
    rw [measure_diff hsub hunion.nullMeasurableSet (measure_ne_top _ _), hmass, tsub_self]
  have hcover : ∀ᵐ z ∂independentExponentials,
      z ∈ p.terminalSurvival ∨ z ∈ ⋃ j, variableWinner p.service p.deadline j := by
    rw [ae_iff]
    have hs : {z | ¬(z ∈ p.terminalSurvival ∨ z ∈ ⋃ j, variableWinner p.service p.deadline j)} =
        p.terminalSurvivalᶜ \ ⋃ j, variableWinner p.service p.deadline j := by
      ext z
      simp
    rw [hs]
    exact hzero
  filter_upwards [hcover] with z hz
  rcases hz with hs | hw
  · exact Or.inl hs
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    right
    refine ⟨j, hj, ?_⟩
    intro i hi
    by_cases hij : i = j
    · exact hij
    · exact False.elim (Set.disjoint_left.mp (p.winner_disjoint hij) hi hj)

end ServiceCurveFamily
end StochasticMatching
