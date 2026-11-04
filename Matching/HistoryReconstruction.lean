import Matching.ConditionalTransport

/-! Recover original demands after a marked completion, and identify
conditional expectations of bounded functions of that original sample.
All branch measures are unnormalized.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching.HistoryServiceFamily

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (p : HistoryServiceFamily H ι)

noncomputable def reconstructMarked (j : ι)
    (x : (H × ℝ) × ({i : ι // i ≠ j} → ℝ)) : H × (ι → ℝ) :=
  (x.1.1, (p.curves x.1.1).reconstructMarked j (x.1.2, x.2))

theorem measurable_reconstructMarked (j : ι) : Measurable (p.reconstructMarked j) := by
  apply Measurable.prodMk (measurable_fst.comp measurable_fst)
  apply (splitDemand j).symm.measurable.comp
  apply Measurable.prodMk ((p.measurable_service j).comp measurable_fst)
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).add
    ((p.measurable_service i.1).comp measurable_fst)

theorem reconstruct_observation_ae (ν : Measure H) (j : ι) :
    (fun x => p.reconstructMarked j (p.observation j x)) =ᵐ[
      (ν.prod independentExponentials).restrict (p.winner j)] id := by
  have hm : MeasurableSet {x : H × (ι → ℝ) | ∀ i, 0 < x.2 i} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const
      ((measurable_pi_apply i).comp measurable_snd))
  have hpos : ∀ᵐ x ∂ν.prod (independentExponentials (ι := ι)), ∀ i, 0 < x.2 i := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem hm).mpr
    exact Filter.Eventually.of_forall (fun _ => independentExponentials_ae_pos)
  filter_upwards [ae_restrict_mem (p.measurable_winner j), ae_restrict_of_ae hpos] with x hx hz
  apply Prod.ext
  · rfl
  · exact (p.curves x.1).reconstruct_first_observation (hz j) hx

theorem finite_markedHistoryMeasure (ν : Measure H) [IsFiniteMeasure ν] (j : ι) :
    IsFiniteMeasure (p.markedHistoryMeasure ν j) := by
  have hfst : Measure.map (Prod.fst : (H × ℝ) × ({i : ι // i ≠ j} → ℝ) → H × ℝ)
      (Measure.map (p.observation j) ((ν.prod independentExponentials).restrict (p.winner j))) =
      p.markedHistoryMeasure ν j := by
    rw [p.first_completion_factorization]
    simp
  rw [← hfst]
  infer_instance

theorem completion_conditionalExpectation (ν : Measure H) [IsFiniteMeasure ν]
    (j : ι) (f : H × (ι → ℝ) → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (fun x : H × (ι → ℝ) => ∫ z,
      f (p.reconstructMarked j ((x.1, p.clock j x), z)) ∂independentExponentials)
      =ᵐ[(ν.prod independentExponentials).restrict (p.winner j)]
    ((ν.prod independentExponentials).restrict (p.winner j))[
      f | (inferInstance : MeasurableSpace (H × ℝ)).comap (fun x => (x.1, p.clock j x))] := by
  letI := p.finite_markedHistoryMeasure ν j
  have hf' : Measurable (fun x => f (p.reconstructMarked j x)) :=
    hf.comp (p.measurable_reconstructMarked j)
  have hfi : Integrable (fun x => f (p.reconstructMarked j x))
      ((p.markedHistoryMeasure ν j).prod independentExponentials) := by
    apply (integrable_const B).mono' hf'.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => hB (p.reconstructMarked j x))
  have hid := conditionalExpectation_history_transport (p.markedHistoryMeasure ν j)
    ((ν.prod independentExponentials).restrict (p.winner j)) (p.observation j)
    (p.measurable_observation j) (p.first_completion_factorization ν j)
    (fun x => f (p.reconstructMarked j x)) hf' hfi
  have heq : (fun x => f (p.reconstructMarked j (p.observation j x))) =ᵐ[
      (ν.prod independentExponentials).restrict (p.winner j)] f := by
    filter_upwards [p.reconstruct_observation_ae ν j] with x hx
    exact congrArg f hx
  exact hid.trans (condExp_congr_ae heq)

end StochasticMatching.HistoryServiceFamily
