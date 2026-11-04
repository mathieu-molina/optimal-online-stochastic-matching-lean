import Matching.VectorResidual
import Mathlib.MeasureTheory.Integral.Prod

/-!
History-dependent thresholds independent of the fresh residual vector.
This proves the no-completion observation identity. Histories that also reveal
newly completed coordinates need an additional marked-completion argument.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching

variable {ι H : Type*} [Fintype ι] [MeasurableSpace H]

theorem lintegral_vector_residual {h : ι → ℝ} (hh : ∀ i, 0 ≤ h i)
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in survivalBox h, f (fun i => z i - h i) ∂independentExponentials) =
      independentExponentials (survivalBox h) * ∫⁻ z, f z ∂independentExponentials := by
  have hmap := lintegral_map (μ := independentExponentials.restrict (survivalBox h))
    hf (measurable_subtract_threshold h)
  change (∫⁻ z, f z ∂vectorResidualLaw h) = _ at hmap
  rw [← hmap, vectorResidualLaw_eq_smul hh, lintegral_smul_measure,
    smul_eq_mul, survivalBox_measure hh]

def historySurvival (h : H → ι → ℝ) : Set (H × (ι → ℝ)) :=
  {p | ∀ i, h p.1 i < p.2 i}

def residualObservation (h : H → ι → ℝ) (p : H × (ι → ℝ)) : H × (ι → ℝ) :=
  (p.1, fun i => p.2 i - h p.1 i)

theorem measurable_historySurvival {h : H → ι → ℝ} (hh : Measurable h) :
    MeasurableSet (historySurvival h) := by
  have heq : historySurvival h = ⋂ i, {p : H × (ι → ℝ) | h p.1 i < p.2 i} := by
    ext p
    simp [historySurvival]
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_lt (((measurable_pi_apply i).comp hh).comp measurable_fst)
    ((measurable_pi_apply i).comp measurable_snd)

omit [Fintype ι] in
theorem measurable_residualObservation {h : H → ι → ℝ} (hh : Measurable h) :
    Measurable (residualObservation h) := by
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).sub
    (((measurable_pi_apply i).comp hh).comp measurable_fst)

theorem history_survival_lintegral {h : H → ι → ℝ} (hh : Measurable h)
    (hnonneg : ∀ u i, 0 ≤ h u i) (ν : Measure H)
    (f : H × (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p in historySurvival h, f (residualObservation h p)
      ∂ν.prod (independentExponentials (ι := ι))) =
      ∫⁻ u, independentExponentials (survivalBox (h u)) *
        (∫⁻ z, f (u, z) ∂independentExponentials) ∂ν := by
  have hS := measurable_historySurvival hh
  have hF : Measurable (fun p => f (residualObservation h p)) :=
    hf.comp (measurable_residualObservation hh)
  rw [← lintegral_indicator hS]
  rw [lintegral_prod _ ((hF.indicator hS).aemeasurable)]
  apply lintegral_congr
  intro u
  have heq : (fun z => (historySurvival h).indicator
        (fun p => f (residualObservation h p)) (u, z)) =
      (survivalBox (h u)).indicator (fun z => f (u, fun i => z i - h u i)) := by
    funext z
    by_cases hz : z ∈ survivalBox (h u)
    · have hp : (u, z) ∈ historySurvival h := by
        simpa [historySurvival, survivalBox] using hz
      simp [Set.indicator_of_mem, hp, hz, residualObservation]
    · have hp : (u, z) ∉ historySurvival h := by
        simpa [historySurvival, survivalBox] using hz
      simp [Set.indicator_of_not_mem, hp, hz]
  rw [heq, lintegral_indicator (measurableSet_survivalBox (h u))]
  exact lintegral_vector_residual (hnonneg u) (fun z => f (u, z))
    (hf.comp (measurable_const.prodMk measurable_id))

def reconstructDemands (h : H → ι → ℝ) (p : H × (ι → ℝ)) : H × (ι → ℝ) :=
  (p.1, fun i => p.2 i + h p.1 i)

omit [Fintype ι] in
theorem measurable_reconstructDemands {h : H → ι → ℝ} (hh : Measurable h) :
    Measurable (reconstructDemands h) := by
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).add
    (((measurable_pi_apply i).comp hh).comp measurable_fst)

omit [Fintype ι] [MeasurableSpace H] in
theorem reconstruct_after_observation (h : H → ι → ℝ) (p : H × (ι → ℝ)) :
    reconstructDemands h (residualObservation h p) = p := by
  rcases p with ⟨u, z⟩
  simp [reconstructDemands, residualObservation]

omit [Fintype ι] [MeasurableSpace H] in
theorem observation_after_reconstruct (h : H → ι → ℝ) (p : H × (ι → ℝ)) :
    residualObservation h (reconstructDemands h p) = p := by
  rcases p with ⟨u, z⟩
  simp [reconstructDemands, residualObservation]

theorem history_original_demands_lintegral {h : H → ι → ℝ} (hh : Measurable h)
    (hnonneg : ∀ u i, 0 ≤ h u i) (ν : Measure H)
    (f : H × (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p in historySurvival h, f p ∂ν.prod (independentExponentials (ι := ι))) =
      ∫⁻ u, independentExponentials (survivalBox (h u)) *
        (∫⁻ z, f (u, fun i => z i + h u i) ∂independentExponentials) ∂ν := by
  have h := history_survival_lintegral hh hnonneg ν
    (fun p => f (reconstructDemands h p)) (hf.comp (measurable_reconstructDemands hh))
  simpa [reconstructDemands, residualObservation] using h

theorem measurable_survival_weight {h : H → ι → ℝ} (hh : Measurable h)
    (hnonneg : ∀ u i, 0 ≤ h u i) :
    Measurable (fun u => independentExponentials (survivalBox (h u))) := by
  simp_rw [survivalBox_measure (hnonneg _)]
  fun_prop

/-- The residual vector is independent of the surviving history after the
history measure has been reweighted by its survival probability. -/
theorem history_survival_factorization {h : H → ι → ℝ} (hh : Measurable h)
    (hnonneg : ∀ u i, 0 ≤ h u i) (ν : Measure H) :
    Measure.map (residualObservation h)
      ((ν.prod (independentExponentials (ι := ι))).restrict (historySurvival h)) =
      (ν.withDensity (fun u => independentExponentials (survivalBox (h u)))).prod
        (independentExponentials (ι := ι)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_residualObservation hh),
    history_survival_lintegral hh hnonneg ν f hf,
    lintegral_prod _ hf.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul ν
    (measurable_survival_weight hh hnonneg) hf.lintegral_prod_right']
  rfl

end StochasticMatching
