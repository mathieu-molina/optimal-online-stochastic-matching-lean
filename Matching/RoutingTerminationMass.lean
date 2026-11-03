import Matching.RoutingSupport

/-! The exact terminal mass of the routing distribution and the uniform
continuation bound used to rule out infinitely many rejected arrivals.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem routingNextArrival_terminal_mass (N : σ → Finset ι) (capacity : σ → ℝ)
    (p : ServiceCurveFamily ι) :
    routingNextArrival N capacity p (Set.range Sum.inl) =
      ENNReal.ofReal (Real.exp (-((∑ s, capacity s) * p.deadline))) := by
  unfold routingNextArrival
  rw [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_range_inl]
  simp only [Set.mem_range_self, Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  have hz : (Measure.sum fun s => Measure.sum fun j =>
      Measure.map (fun t => (Sum.inr (t, (s, j)) : Unit ⊕ (ℝ × (σ × Option ι))))
        (routingArrivalMeasure N capacity p s j)) (Set.range Sum.inl) = 0 := by
    rw [Measure.sum_apply _ measurableSet_range_inl]
    apply ENNReal.tsum_eq_zero.mpr
    intro s
    rw [Measure.sum_apply _ measurableSet_range_inl]
    apply ENNReal.tsum_eq_zero.mpr
    intro j
    have hf : Measurable (fun t : ℝ => (Sum.inr (t, (s, j)) : Unit ⊕ (ℝ × (σ × Option ι)))) :=
      measurable_inr.comp (measurable_id.prodMk measurable_const)
    rw [Measure.map_apply hf measurableSet_range_inl]
    have he : (fun t : ℝ => (Sum.inr (t, (s, j)) : Unit ⊕ (ℝ × (σ × Option ι)))) ⁻¹'
        Set.range Sum.inl = ∅ := by ext t; simp
    rw [he, measure_empty]
  rw [hz, add_zero]

theorem routingNextArrival_continuation_mass (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity) :
    routingNextArrival N capacity p (Set.range Sum.inr) =
      1 - ENNReal.ofReal (Real.exp (-((∑ s, capacity s) * p.deadline))) := by
  letI := routingNextArrival_probability N capacity hc p hp
  have he : (Set.range (Sum.inl : Unit → Unit ⊕ (ℝ × (σ × Option ι))))ᶜ = Set.range Sum.inr := by
    ext e
    cases e <;> simp
  rw [← he, measure_compl measurableSet_range_inl (measure_ne_top _ _), measure_univ,
    routingNextArrival_terminal_mass]

theorem routingNextArrival_continuation_bound (N : σ → Finset ι) (capacity : σ → ℝ)
    (hc : ∀ s, 0 ≤ capacity s) (p : ServiceCurveFamily ι)
    (hp : ∀ t ∈ Icc 0 p.deadline, (fun i => p.rate i t) ∈ supplyRegion N capacity)
    (T : ℝ) (hT : p.deadline ≤ T) :
    routingNextArrival N capacity p (Set.range Sum.inr) ≤
      1 - ENNReal.ofReal (Real.exp (-((∑ s, capacity s) * T))) := by
  rw [routingNextArrival_continuation_mass N capacity hc p hp]
  apply tsub_le_tsub_left
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_left hT (Finset.sum_nonneg (fun s _ => hc s)))

theorem routing_continuation_bound_lt_one (capacity : σ → ℝ) (T : ℝ) :
    1 - ENNReal.ofReal (Real.exp (-((∑ s, capacity s) * T))) < 1 :=
  ENNReal.sub_lt_self (by simp) (by simp) (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))

end StochasticMatching
