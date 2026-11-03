import Matching.HistoryRoutingKernel

/-! The routing kernel assigns only available neighbors and makes strictly
positive time progress. These are the invariants needed to build valid
matching traces from successive arrival decisions.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

theorem routingArrivalMeasure_eq_zero_of_rate (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : ServiceCurveFamily ι) (s : σ) (j : Option ι)
    (hz : ∀ t ∈ Icc 0 p.deadline, arrivalRoutingRate N capacity (fun i => p.rate i t) s j = 0) :
    routingArrivalMeasure N capacity p s j = 0 := by
  unfold routingArrivalMeasure
  have he : (fun t => ENNReal.ofReal (arrivalRoutingRate N capacity (fun i => p.rate i t) s j *
      Real.exp (-(∑ u, capacity u) * t))) =ᵐ[volume.restrict (Icc 0 p.deadline)] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [hz t ht, zero_mul, ENNReal.ofReal_zero]
  rw [withDensity_congr_ae he]
  exact withDensity_zero

theorem routingArrivalMeasure_unsupported (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity)
    (s : σ) (i : ι) (hi : i ∉ N s) : routingArrivalMeasure N capacity p s (some i) = 0 :=
  routingArrivalMeasure_eq_zero_of_rate N capacity p s (some i)
    (fun t ht => arrivalRoutingRate_supported N capacity hc (hp t ht) s i hi)

theorem routingArrivalMeasure_inactive (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity)
    (s : σ) (i : ι) (hi : ∀ t ∈ Icc 0 p.deadline, p.rate i t = 0) :
    routingArrivalMeasure N capacity p s (some i) = 0 :=
  routingArrivalMeasure_eq_zero_of_rate N capacity p s (some i)
    (fun t ht => arrivalRoutingRate_zero_job N capacity hc (hp t ht) i (hi t ht) s)

theorem routingArrivalMeasure_time_support (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : ServiceCurveFamily ι) (s : σ) (j : Option ι) :
    ∀ᵐ t ∂routingArrivalMeasure N capacity p s j, t ∈ Ioo 0 p.deadline := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  have h0 := (Set.countable_singleton (0 : ℝ)).ae_not_mem (volume.restrict (Icc 0 p.deadline))
  have hT := (Set.countable_singleton p.deadline).ae_not_mem (volume.restrict (Icc 0 p.deadline))
  filter_upwards [ae_restrict_mem measurableSet_Icc, h0, hT] with t ht h0t hTt
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm h0t), lt_of_le_of_ne ht.2 hTt⟩

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

def admissibleArrival (N : σ → Finset ι) (D : Finset ι) (T : ℝ) :
    Set (Unit ⊕ (ℝ × (σ × Option ι))) :=
  Sum.inl '' Set.univ ∪ Sum.inr '' (Ioo 0 T ×ˢ
    {q : σ × Option ι | ∀ i, q.2 = some i → i ∈ N q.1 ∧ i ∉ D})

theorem measurableSet_admissibleArrival (N : σ → Finset ι) (D : Finset ι) (T : ℝ) :
    MeasurableSet (admissibleArrival N D T) :=
  MeasurableSet.univ.inl_image.union
    (measurableSet_Ioo.prod (Set.to_countable _).measurableSet).inr_image

theorem routingNextArrival_admissible (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity)
    (D : Finset ι) (hD : ∀ i ∈ D, ∀ t ∈ Icc 0 p.deadline, p.rate i t = 0) :
    ∀ᵐ e ∂routingNextArrival N capacity p, e ∈ admissibleArrival N D p.deadline := by
  unfold routingNextArrival
  rw [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (measurableSet_admissibleArrival N D p.deadline)).mpr
    change Sum.inl () ∈ admissibleArrival N D p.deadline
    exact Or.inl ⟨(), Set.mem_univ _, rfl⟩
  · rw [Measure.ae_sum_iff]
    intro s
    rw [Measure.ae_sum_iff]
    intro j
    have hf : Measurable (fun t : ℝ => (Sum.inr (t, (s, j)) : Unit ⊕ (ℝ × (σ × Option ι)))) :=
      measurable_inr.comp (measurable_id.prodMk measurable_const)
    apply (ae_map_iff hf.aemeasurable (measurableSet_admissibleArrival N D p.deadline)).mpr
    cases j with
    | none =>
        filter_upwards [routingArrivalMeasure_time_support N capacity p s none] with t ht
        change Sum.inr (t, (s, none)) ∈ admissibleArrival N D p.deadline
        exact Or.inr ⟨(t, (s, none)), ⟨ht, by simp⟩, rfl⟩
    | some i =>
        by_cases hiN : i ∈ N s
        · by_cases hiD : i ∈ D
          · rw [routingArrivalMeasure_inactive N capacity hc p hp s i (hD i hiD)]
            simp
          · filter_upwards [routingArrivalMeasure_time_support N capacity p s (some i)] with t ht
            change Sum.inr (t, (s, some i)) ∈ admissibleArrival N D p.deadline
            exact Or.inr ⟨(t, (s, some i)), ⟨ht, by simpa using And.intro hiN hiD⟩, rfl⟩
        · rw [routingArrivalMeasure_unsupported N capacity hc p hp s i hiN]
          simp

end StochasticMatching
