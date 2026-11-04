import Matching.CoordinateOutcome
import Matching.CoordinateBudget

/-! Measurable tagged-job potentials, sample budgets, and the local certificate
inequality on valid incoming histories.
-/

open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

noncomputable def coordinatePotential (elapsed : H → ℝ) (i : ι) (h : H) : ℝ :=
  Comparison.continuation (elapsed h) (s.initial h i)

noncomputable def coordinateStep (elapsed : H → ℝ) (i : ι) (x : H × (ι → ℝ)) : ℝ :=
  branchSelect s.service.winner
    (fun j x => if j = i then 1 else Comparison.continuation (elapsed x.1 + s.service.clock j x)
      (s.initial x.1 i + (s.service.curves x.1).service i (s.service.clock j x)))
    (fun x => Comparison.continuation (elapsed x.1 + s.deadline x.1)
      (s.initial x.1 i + (s.service.curves x.1).service i (s.deadline x.1))) x

noncomputable def coordinateRemaining (elapsed : H → ℝ) (i : ι) (x : H × (ι → ℝ)) : ℝ :=
  Comparison.continuation (elapsed x.1 + s.service.stopClock x) 0 * s.unallocatedCoordinate i x

noncomputable def coordinateCertificate (elapsed : H → ℝ) (i : ι) (h : H) : ℝ :=
  s.coordinatePotential elapsed i h - Comparison.continuation (elapsed h) 0 *
    s.meanUnallocatedCoordinate i h

noncomputable def coordinateSampleCertificate (elapsed : H → ℝ) (i : ι)
    (x : H × (ι → ℝ)) : ℝ :=
  s.coordinatePotential elapsed i x.1 - Comparison.continuation (elapsed x.1) 0 *
    s.unallocatedCoordinate i x

theorem measurable_coordinatePotential {elapsed : H → ℝ} (he : Measurable elapsed) (i : ι) :
    Measurable (s.coordinatePotential elapsed i) :=
  Comparison.measurable_continuation he ((measurable_pi_apply i).comp s.measurable_initial)

theorem measurable_coordinateStep {elapsed : H → ℝ} (he : Measurable elapsed) (i : ι) :
    Measurable (s.coordinateStep elapsed i) := by
  apply measurable_branchSelect s.service.winner_disjoint s.service.measurable_winner
  · intro j
    by_cases hji : j = i
    · simp only [if_pos hji]
      exact measurable_const
    · simp only [if_neg hji]
      exact Comparison.measurable_continuation ((he.comp measurable_fst).add (s.service.measurable_clock j))
        (((measurable_pi_apply i).comp (s.measurable_initial.comp measurable_fst)).add
          ((s.service.measurable_service i).comp (measurable_fst.prodMk (s.service.measurable_clock j))))
  · exact Comparison.measurable_continuation ((he.add s.measurable_deadline).comp measurable_fst)
      (((measurable_pi_apply i).comp (s.measurable_initial.comp measurable_fst)).add
        ((s.service.measurable_service i).comp
          (measurable_fst.prodMk (s.measurable_deadline.comp measurable_fst))))

theorem measurable_coordinateRemaining {elapsed : H → ℝ} (he : Measurable elapsed) (i : ι) :
    Measurable (s.coordinateRemaining elapsed i) :=
  (Comparison.measurable_continuation ((he.comp measurable_fst).add s.service.measurable_stopClock)
    measurable_const).mul (s.measurable_unallocatedCoordinate i)

theorem measurable_coordinateCertificate {elapsed : H → ℝ} (he : Measurable elapsed) (i : ι) :
    Measurable (s.coordinateCertificate elapsed i) :=
  (s.measurable_coordinatePotential he i).sub
    ((Comparison.measurable_continuation he measurable_const).mul
      (s.measurable_meanUnallocatedCoordinate i))

theorem measurable_coordinateSampleCertificate {elapsed : H → ℝ} (he : Measurable elapsed) (i : ι) :
    Measurable (s.coordinateSampleCertificate elapsed i) :=
  ((s.measurable_coordinatePotential he i).comp measurable_fst).sub
    ((Comparison.measurable_continuation (he.comp measurable_fst) measurable_const).mul
      (s.measurable_unallocatedCoordinate i))

theorem coordinateStep_eq (elapsed : H → ℝ) (i : ι) (x : H × (ι → ℝ)) :
    s.coordinateStep elapsed i x =
      (s.service.curves x.1).coordinateOutcome (elapsed x.1) (s.initial x.1) i x.2 := by
  classical
  by_cases hw : ∃ j, x ∈ s.service.winner j
  · obtain ⟨j, hj⟩ := hw
    unfold coordinateStep
    rw [branchSelect_of_mem s.service.winner_disjoint _ _ hj,
      (s.service.curves x.1).coordinateOutcome_winner (elapsed x.1) (s.initial x.1) i hj]
    rfl
  · unfold coordinateStep ServiceCurveFamily.coordinateOutcome
    rw [branchSelect_of_not_mem _ _ (not_exists.mp hw)]
    have hn : ∀ j, x.2 ∉ variableWinner (s.service.curves x.1).service
        (s.service.curves x.1).deadline j := fun j hj => hw ⟨j, hj⟩
    rw [branchSelect_of_not_mem _ _ hn]
    rfl

theorem coordinatePotential_bounds (R : StageRegion s) {h : H} (hh : h ∈ R.domain) (i : ι) :
    0 ≤ s.coordinatePotential R.elapsed i h ∧ s.coordinatePotential R.elapsed i h ≤ 1 :=
  ⟨Comparison.continuation_nonneg (R.elapsed_le_one hh) ((R.admissible h hh).1 i),
    (Comparison.continuation_lt_one _ _).le⟩

theorem coordinateStep_bounds (R : StageRegion s) {x : H × (ι → ℝ)}
    (hx : x.1 ∈ R.domain) (i : ι) :
    0 ≤ s.coordinateStep R.elapsed i x ∧ s.coordinateStep R.elapsed i x ≤ 1 := by
  rw [s.coordinateStep_eq]
  exact (s.service.curves x.1).coordinateOutcome_bounds (R.elapsed x.1) (s.initial x.1) i
    (le_of_eq (R.total_deadline x.1 hx)) ((R.admissible x.1 hx).1 i) x.2

theorem coordinateRemaining_nonneg (R : StageRegion s) {x : H × (ι → ℝ)}
    (hx : x.1 ∈ R.domain) (hz : ∀ j, 0 ≤ x.2 j) (i : ι) :
    0 ≤ s.coordinateRemaining R.elapsed i x := by
  have ht : R.elapsed x.1 + s.service.stopClock x ≤ 1 := by
    have hb := (s.service.stopClock_bounds x).2
    change s.service.stopClock x ≤ s.deadline x.1 at hb
    linarith [R.total_deadline x.1 hx]
  exact mul_nonneg (Comparison.continuation_nonneg ht (le_refl 0))
    (s.unallocatedCoordinate_nonneg (R.admissible x.1 hx) hz i)

theorem integrable_coordinatePotential (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) : Integrable (s.coordinatePotential R.elapsed i) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (s.measurable_coordinatePotential R.measurable_elapsed i).aestronglyMeasurable
  filter_upwards [hν] with h hh
  rw [Real.norm_of_nonneg (s.coordinatePotential_bounds R hh i).1]
  exact (s.coordinatePotential_bounds R hh i).2

theorem integrable_coordinateStep (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) :
    Integrable (s.coordinateStep R.elapsed i) (ν.prod independentExponentials) := by
  apply (integrable_const (1 : ℝ)).mono'
    (s.measurable_coordinateStep R.measurable_elapsed i).aestronglyMeasurable
  filter_upwards [R.incoming_mem_ae ν hν] with x hx
  rw [Real.norm_of_nonneg (s.coordinateStep_bounds R hx i).1]
  exact (s.coordinateStep_bounds R hx i).2

theorem integrable_coordinateRemaining (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) :
    Integrable (s.coordinateRemaining R.elapsed i) (ν.prod independentExponentials) := by
  apply (s.integrable_unallocatedCoordinate R ν hν i).bdd_mul' (c := 1)
    (Comparison.measurable_continuation
      ((R.measurable_elapsed.comp measurable_fst).add s.service.measurable_stopClock)
      measurable_const).aestronglyMeasurable
  filter_upwards [R.incoming_mem_ae ν hν] with x hx
  have ht : R.elapsed x.1 + s.service.stopClock x ≤ 1 := by
    have hb := (s.service.stopClock_bounds x).2
    change s.service.stopClock x ≤ s.deadline x.1 at hb
    linarith [R.total_deadline x.1 hx]
  change ‖Comparison.continuation (R.elapsed x.1 + s.service.stopClock x) 0‖ ≤ 1
  rw [Real.norm_of_nonneg (Comparison.continuation_nonneg ht (le_refl 0))]
  exact (Comparison.continuation_lt_one _ _).le

theorem coordinateSampleCertificate_integral (elapsed : H → ℝ) (h : H) (i : ι) :
    (∫ z, s.coordinateSampleCertificate elapsed i (h, z) ∂independentExponentials) =
      s.coordinateCertificate elapsed i h := by
  unfold coordinateSampleCertificate coordinateCertificate
  dsimp only
  rw [integral_sub (integrable_const _) ((s.integrable_unallocatedCoordinate_fiber h i).const_mul _),
    integral_const_mul, ← s.meanUnallocatedCoordinate_eq_integral]
  simp

theorem integrable_coordinateSampleCertificate (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) :
    Integrable (s.coordinateSampleCertificate R.elapsed i) (ν.prod independentExponentials) := by
  have hp : Integrable (fun x : H × (ι → ℝ) => s.coordinatePotential R.elapsed i x.1)
      (ν.prod independentExponentials) := by
    simpa only [mul_one] using (s.integrable_coordinatePotential R ν hν i).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : ι → ℝ => (1 : ℝ)) independentExponentials)
  apply hp.sub
  apply (s.integrable_unallocatedCoordinate R ν hν i).bdd_mul' (c := 1)
    (Comparison.measurable_continuation (R.measurable_elapsed.comp measurable_fst)
      measurable_const).aestronglyMeasurable
  filter_upwards [R.incoming_mem_ae ν hν] with x hx
  change ‖Comparison.continuation (R.elapsed x.1) 0‖ ≤ 1
  rw [Real.norm_of_nonneg (Comparison.continuation_nonneg (R.elapsed_le_one hx) (le_refl 0))]
  exact (Comparison.continuation_lt_one _ _).le

theorem integrable_coordinateCertificate (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) : Integrable (s.coordinateCertificate R.elapsed i) ν := by
  have h := (s.integrable_coordinateSampleCertificate R ν hν i).integral_prod_left
  simpa only [s.coordinateSampleCertificate_integral] using h

theorem coordinate_certificate_step_fiber (elapsed : H → ℝ) (h : H) (i : ι)
    (ha : s.Admissible h) (hT : elapsed h + s.deadline h ≤ 1) :
    s.coordinateCertificate elapsed i h ≤
      (∫ z, s.coordinateStep elapsed i (h, z) ∂independentExponentials) -
      ∫ z, s.coordinateRemaining elapsed i (h, z) ∂independentExponentials := by
  have hp := (s.service.curves h).coordinateOutcome_expected_lower_bound
    (elapsed h) (s.initial h) i hT (ha.1 i) (fun t ht => s.flow_gap_nonneg_at h ha ht i)
  have he : (fun z => s.coordinateStep elapsed i (h, z)) =
      (s.service.curves h).coordinateOutcome (elapsed h) (s.initial h) i :=
    funext (fun z => s.coordinateStep_eq elapsed i (h, z))
  rw [← he] at hp
  have hinit : (s.service.curves h).coordinatePotential (elapsed h) (s.initial h) i 0 =
      s.coordinatePotential elapsed i h := by
    simp only [ServiceCurveFamily.coordinatePotential, (s.service.curves h).service_zero,
      add_zero, coordinatePotential]
  rw [hinit] at hp
  have hb := s.stopped_coordinate_budget_identity (elapsed h) h i hT
  have hrem : (fun z => s.coordinateRemaining elapsed i (h, z)) =
      fun z => Comparison.continuation (elapsed h + (s.service.curves h).stopClock z) 0 *
        s.unallocatedCoordinate i (h, z) := by
    funext z
    simp only [coordinateRemaining, HistoryServiceFamily.stopClock_eq]
  rw [hrem]
  unfold coordinateCertificate
  change s.coordinatePotential elapsed i h - _ ≤ _
  have hD : (s.service.curves h).deadline = s.deadline h := rfl
  rw [hD] at hp
  linarith

end StochasticMatching.PosteriorStage
