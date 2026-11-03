import Matching.MarkedArrivalCoupling
import Matching.FirstEventDistribution

/-! The complete one-step routing distribution, with a terminal outcome.
Its arrival-time/type marginal is independent of the service decision, and
its time/job marginal is exactly the augmented exponential scheduling race.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def routingNextArrival (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : ServiceCurveFamily ι) : Measure (Unit ⊕ (ℝ × (σ × Option ι))) :=
  ENNReal.ofReal (Real.exp (-((∑ s, capacity s) * p.deadline))) • Measure.dirac (Sum.inl ()) +
    Measure.sum (fun s => Measure.sum (fun j =>
      Measure.map (fun t => Sum.inr (t, (s, j))) (routingArrivalMeasure N capacity p s j)))

noncomputable def poissonNextArrival (capacity : σ → ℝ) (T : ℝ) : Measure (Unit ⊕ (ℝ × σ)) :=
  ENNReal.ofReal (Real.exp (-((∑ s, capacity s) * T))) • Measure.dirac (Sum.inl ()) +
    Measure.sum (fun s => Measure.map (fun t => Sum.inr (t, s))
      ((volume.restrict (Icc 0 T)).withDensity
        (fun t => ENNReal.ofReal (capacity s * Real.exp (-(∑ u, capacity u) * t)))))

def arrivalTypeProjection : Unit ⊕ (ℝ × (σ × Option ι)) → Unit ⊕ (ℝ × σ) :=
  Sum.map id (Prod.map id Prod.fst)

def arrivalJobProjection : Unit ⊕ (ℝ × (σ × Option ι)) → Unit ⊕ (ℝ × Option ι) :=
  Sum.map id (Prod.map id Prod.snd)

theorem measurable_arrivalTypeProjection : Measurable (arrivalTypeProjection (ι := ι) (σ := σ)) :=
  measurable_id.sumMap (measurable_id.prodMap measurable_fst)

theorem measurable_arrivalJobProjection : Measurable (arrivalJobProjection (ι := ι) (σ := σ)) :=
  measurable_id.sumMap (measurable_id.prodMap measurable_snd)

theorem routingNextArrival_type_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity) :
    Measure.map arrivalTypeProjection (routingNextArrival N capacity p) = poissonNextArrival capacity p.deadline := by
  have hg := measurable_arrivalTypeProjection (ι := ι) (σ := σ)
  unfold routingNextArrival poissonNextArrival
  rw [Measure.map_add _ _ hg, Measure.map_smul, Measure.map_dirac hg]
  congr 1
  rw [Measure.map_sum hg.aemeasurable]
  congr 1
  funext s
  rw [Measure.map_sum hg.aemeasurable]
  have hf : Measurable (fun t : ℝ => (Sum.inr (t, s) : Unit ⊕ (ℝ × σ))) :=
    measurable_inr.comp (measurable_id.prodMk measurable_const)
  have he : (fun j => Measure.map arrivalTypeProjection
      (Measure.map (fun t => Sum.inr (t, (s, j))) (routingArrivalMeasure N capacity p s j))) =
      (fun j => Measure.map (fun t => Sum.inr (t, s)) (routingArrivalMeasure N capacity p s j)) := by
    funext j
    have hm : Measurable (fun t : ℝ => (Sum.inr (t, (s, j)) : Unit ⊕ (ℝ × (σ × Option ι)))) :=
      measurable_inr.comp (measurable_id.prodMk measurable_const)
    rw [Measure.map_map hg hm]
    rfl
  rw [he, ← Measure.map_sum hf.aemeasurable, routingArrivalMeasure_type_marginal N capacity hc p hp s]

theorem routingNextArrival_job_law (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity) :
    let q := p.withRejectionClock (∑ s, capacity s)
      (fun t ht => supplyRegion_total_rate_le N capacity hc (hp t ht))
    Measure.map arrivalJobProjection (routingNextArrival N capacity p) =
      Measure.map q.firstEvent independentExponentials := by
  intro q
  have hg := measurable_arrivalJobProjection (ι := ι) (σ := σ)
  rw [q.firstEvent_distribution]
  have htotal : (∑ i, q.service i q.deadline) = (∑ s, capacity s) * p.deadline :=
    p.withRejectionClock_total_service _ _ _
  rw [htotal]
  unfold routingNextArrival
  rw [Measure.map_add _ _ hg, Measure.map_smul, Measure.map_dirac hg]
  congr 1
  rw [Measure.map_sum hg.aemeasurable]
  have hmaps : ∀ (s : σ) (j : Option ι), Measure.map arrivalJobProjection
      (Measure.map (fun t => Sum.inr (t, (s, j))) (routingArrivalMeasure N capacity p s j)) =
      Measure.map (fun t => (Sum.inr (t, j) : Unit ⊕ (ℝ × Option ι))) (routingArrivalMeasure N capacity p s j) := by
    intro s j
    have hm : Measurable (fun t : ℝ => (Sum.inr (t, (s, j)) : Unit ⊕ (ℝ × (σ × Option ι)))) :=
      measurable_inr.comp (measurable_id.prodMk measurable_const)
    rw [Measure.map_map hg hm]
    rfl
  simp_rw [Measure.map_sum hg.aemeasurable, hmaps]
  change (Measure.sum fun s => Measure.sum fun j =>
    Measure.map (fun t => (Sum.inr (t, j) : Unit ⊕ (ℝ × Option ι))) (routingArrivalMeasure N capacity p s j)) = _
  rw [Measure.sum_comm]
  congr 1
  funext j
  have hf : Measurable (fun t : ℝ => (Sum.inr (t, j) : Unit ⊕ (ℝ × Option ι))) :=
    measurable_inr.comp (measurable_id.prodMk measurable_const)
  rw [← Measure.map_sum hf.aemeasurable, routingArrivalMeasure_job_marginal N capacity hc p hp j]
  rfl

theorem routingNextArrival_probability (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity) :
    IsProbabilityMeasure (routingNextArrival N capacity p) := by
  have h := congrArg (fun μ : Measure (Unit ⊕ (ℝ × Option ι)) => μ Set.univ)
    (routingNextArrival_job_law N capacity hc p hp)
  dsimp only at h
  rw [Measure.map_apply measurable_arrivalJobProjection MeasurableSet.univ, Set.preimage_univ,
    Measure.map_apply (ServiceCurveFamily.measurable_firstEvent _) MeasurableSet.univ,
    Set.preimage_univ] at h
  exact ⟨h.trans measure_univ⟩

end StochasticMatching
