import Matching.HistoryRoutingKernel

/-! The arrival-only kernel is measurable in the remaining deadline and is
normalized for every positive horizon, including zero total arrival rate.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {B σ : Type*} [MeasurableSpace B] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

def idleServiceCurve (ι : Type*) (T : ℝ) (hT : 0 < T) : ServiceCurveFamily ι where
  deadline := T
  deadline_pos := hT
  service := fun _ _ => 0
  rate := fun _ _ => 0
  service_continuous := fun _ => continuous_const
  rate_continuous := fun _ => continuous_const
  service_monotone := fun _ _ _ _ _ _ => le_rfl
  service_zero := fun _ => rfl
  rate_nonneg := fun _ _ _ => le_rfl
  service_deriv := fun _ _ _ => hasDerivAt_const _ _

theorem poissonNextArrival_probability (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (T : ℝ) (hT : 0 < T) : IsProbabilityMeasure (poissonNextArrival capacity T) := by
  letI : MeasurableSpace (Option Unit) := ⊤
  letI : MeasurableSingletonClass (Option Unit) := ⟨fun _ => trivial⟩
  let N : σ → Finset Unit := fun _ => ∅
  let p := idleServiceCurve Unit T hT
  have hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity :=
    fun _ _ => zero_mem_supplyRegion N capacity hc
  letI := routingNextArrival_probability N capacity hc p hp
  have he := routingNextArrival_type_law N capacity hc p hp
  change IsProbabilityMeasure (poissonNextArrival capacity p.deadline)
  rw [← he]
  exact isProbabilityMeasure_map measurable_arrivalTypeProjection.aemeasurable

theorem measurable_poissonNextArrival (capacity : σ → ℝ) (D : B → ℝ) (hD : Measurable D) :
    Measurable (fun b => poissonNextArrival capacity (D b)) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [poissonNextArrival, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.sum_apply _ hE]
  apply Measurable.add
  · exact ((measurable_const.mul hD).neg.exp.ennreal_ofReal).mul_const _
  · apply Measurable.ennreal_tsum
    intro s
    have hf : Measurable (fun t : ℝ => (Sum.inr (t, s) : Unit ⊕ (ℝ × σ))) :=
      measurable_inr.comp (measurable_id.prodMk measurable_const)
    have hd : Measurable (fun x : B × ℝ => ENNReal.ofReal
        (capacity s * Real.exp (-(∑ u, capacity u) * x.2))) := by fun_prop
    have hw : MeasurableSet {x : B × ℝ | x.2 ∈ Icc 0 (D x.1)} :=
      (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (hD.comp measurable_fst))
    have hm := (hd.indicator hw).lintegral_prod_right' (ν := volume.restrict ((fun t : ℝ => (Sum.inr (t, s) : Unit ⊕ (ℝ × σ))) ⁻¹' E))
    convert hm using 1
    funext b
    rw [Measure.map_apply hf hE, ← withDensity_indicator measurableSet_Icc,
      withDensity_apply _ (hf hE)]
    rfl

noncomputable def poissonInputKernel (capacity : σ → ℝ) (D : B → ℝ) (hD : Measurable D) :
    Kernel B (Unit ⊕ (ℝ × σ)) where
  toFun b := poissonNextArrival capacity (D b)
  measurable' := measurable_poissonNextArrival capacity D hD

theorem poissonInputKernel_markov (capacity : σ → ℝ) (hc : ∀ s, 0 ≤ capacity s)
    (D : B → ℝ) (hD : Measurable D) (hpos : ∀ b, 0 < D b) :
    IsMarkovKernel (poissonInputKernel capacity D hD) :=
  ⟨fun b => poissonNextArrival_probability capacity hc (D b) (hpos b)⟩

end StochasticMatching
