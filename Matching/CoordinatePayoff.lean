import Matching.CoordinateStage
import Matching.PathBounds

/-! Transport the tagged-job certificate through the actual restart law.
The first completion of the tagged job pays one and removes its remaining
nonnegative budget; other completions preserve that job's sample budget.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching.PosteriorStage
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  (s : PosteriorStage H ι)

noncomputable def coordinateChildPayoff (elapsed : H → ℝ) (i j : ι)
    (x : (H × ℝ) × ({k : ι // k ≠ j} → ℝ)) : ℝ :=
  if hij : i ≠ j then (s.next j).coordinateSampleCertificate
    (fun h => elapsed h.1 + h.2) ⟨i, hij⟩ x else 1

noncomputable def coordinateChildCertificate (elapsed : H → ℝ) (i j : ι) (h : H × ℝ) : ℝ :=
  if hij : i ≠ j then (s.next j).coordinateCertificate
    (fun h => elapsed h.1 + h.2) ⟨i, hij⟩ h else 1

noncomputable def coordinatePayoff (elapsed : H → ℝ) (i : ι) (x : H × (ι → ℝ)) : ℝ :=
  branchSelect s.service.winner
    (fun j x => s.coordinateChildPayoff elapsed i j (s.service.observation j x)) (fun _ => 0) x

theorem measurable_coordinateChildPayoff {elapsed : H → ℝ} (he : Measurable elapsed) (i j : ι) :
    Measurable (s.coordinateChildPayoff elapsed i j) := by
  unfold coordinateChildPayoff
  split_ifs
  · exact (s.next j).measurable_coordinateSampleCertificate
      ((he.comp measurable_fst).add measurable_snd) _
  · exact measurable_const

theorem measurable_coordinatePayoff {elapsed : H → ℝ} (he : Measurable elapsed) (i : ι) :
    Measurable (s.coordinatePayoff elapsed i) :=
  measurable_branchSelect s.service.winner_disjoint s.service.measurable_winner
    (fun j => (s.measurable_coordinateChildPayoff he i j).comp (s.service.measurable_observation j))
    measurable_const

theorem coordinatePayoff_terminal (elapsed : H → ℝ) (i : ι) {x : H × (ι → ℝ)}
    (hx : x ∈ s.service.terminalEvent) : s.coordinatePayoff elapsed i x = 0 := by
  apply branchSelect_of_not_mem
  intro j hj
  exact Set.disjoint_left.mp (s.service.winner_disjoint_terminal j) hx hj

theorem coordinatePayoff_winner (elapsed : H → ℝ) (i : ι) {x : H × (ι → ℝ)} {j : ι}
    (hx : x ∈ s.service.winner j) :
    s.coordinatePayoff elapsed i x = s.coordinateChildPayoff elapsed i j (s.service.observation j x) :=
  branchSelect_of_mem s.service.winner_disjoint _ _ hx

theorem coordinateStep_sub_remaining_le_payoff (R : StageRegion s) (i : ι)
    {x : H × (ι → ℝ)} (hx : x.1 ∈ R.domain) (hg : GoodExecution 1 s x) :
    s.coordinateStep R.elapsed i x - s.coordinateRemaining R.elapsed i x ≤
      s.coordinatePayoff R.elapsed i x := by
  rcases hg with ⟨hz, hterm | ⟨j, hj, _⟩⟩
  · rw [s.coordinatePayoff_terminal R.elapsed i hterm, s.coordinateStep_eq,
      (s.service.curves x.1).coordinateOutcome_terminal (R.elapsed x.1) (s.initial x.1) i
        (mem_univ_pi.mpr hterm)]
    unfold ServiceCurveFamily.coordinatePotential coordinateRemaining
    rw [s.stopClock_terminal x hterm]
    change Comparison.continuation (R.elapsed x.1 + s.deadline x.1) _ -
      Comparison.continuation (R.elapsed x.1 + s.deadline x.1) 0 * _ ≤ 0
    simp only [R.total_deadline x.1 hx, Comparison.continuation_deadline, zero_mul, sub_self, le_refl]
  · rw [s.coordinatePayoff_winner R.elapsed i hj]
    unfold coordinateStep
    rw [branchSelect_of_mem s.service.winner_disjoint _ _ hj]
    by_cases hij : i ≠ j
    · rw [if_neg (Ne.symm hij)]
      unfold coordinateChildPayoff
      rw [dif_pos hij]
      unfold coordinateSampleCertificate coordinatePotential coordinateRemaining
      rw [s.service.stopClock_winner hj, s.next_unallocatedCoordinate_eq (hz j) hj]
      exact le_refl _
    · have he : i = j := not_ne_iff.mp hij
      subst j
      simp only [if_pos rfl, coordinateChildPayoff, ne_eq, not_true_eq_false, dite_false]
      exact sub_le_self _ (s.coordinateRemaining_nonneg R hx (fun j => (hz j).le) i)

theorem integrable_coordinateChildPayoff (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i j : ι) :
    Integrable (s.coordinateChildPayoff R.elapsed i j)
      ((s.service.markedHistoryMeasure ν j).prod independentExponentials) := by
  letI := s.service.finite_markedHistoryMeasure ν j
  unfold coordinateChildPayoff
  split_ifs
  · exact (s.next j).integrable_coordinateSampleCertificate (R.next j)
      (s.service.markedHistoryMeasure ν j) (R.next_concentrated ν hν j) _
  · exact integrable_const 1

theorem integrable_coordinatePayoff (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) :
    Integrable (s.coordinatePayoff R.elapsed i) (ν.prod independentExponentials) := by
  have ht : Integrable (s.coordinatePayoff R.elapsed i)
      ((ν.prod independentExponentials).restrict s.service.terminalEvent) := by
    apply (integrable_const (0 : ℝ)).congr
    filter_upwards [ae_restrict_mem s.service.measurable_terminalEvent] with x hx
    exact (s.coordinatePayoff_terminal R.elapsed i hx).symm
  have hw : ∀ j, Integrable (s.coordinatePayoff R.elapsed i)
      ((ν.prod independentExponentials).restrict (s.service.winner j)) := by
    intro j
    have hc := s.integrable_coordinateChildPayoff R ν hν i j
    rw [← s.service.first_completion_factorization ν j] at hc
    apply (hc.comp_measurable (s.service.measurable_observation j)).congr
    filter_upwards [ae_restrict_mem (s.service.measurable_winner j)] with x hx
    exact (s.coordinatePayoff_winner R.elapsed i hx).symm
  rw [s.service.segment_measure_decomposition ν, integrable_add_measure, Measure.sum_fintype,
    integrable_finset_sum_measure]
  exact ⟨ht, fun j _ => hw j⟩

theorem coordinateChildPayoff_integral (elapsed : H → ℝ) (i j : ι) (h : H × ℝ) :
    (∫ z, s.coordinateChildPayoff elapsed i j (h, z) ∂independentExponentials) =
      s.coordinateChildCertificate elapsed i j h := by
  unfold coordinateChildPayoff coordinateChildCertificate
  split_ifs
  · exact (s.next j).coordinateSampleCertificate_integral _ h _
  · simp

theorem coordinatePayoff_winner_integral (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i j : ι) :
    (∫ x in s.service.winner j, s.coordinatePayoff R.elapsed i x ∂ν.prod independentExponentials) =
      ∫ h, s.coordinateChildCertificate R.elapsed i j h ∂s.service.markedHistoryMeasure ν j := by
  letI := s.service.finite_markedHistoryMeasure ν j
  calc
    _ = ∫ x in s.service.winner j,
        s.coordinateChildPayoff R.elapsed i j (s.service.observation j x)
          ∂ν.prod independentExponentials := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (s.service.measurable_winner j)] with x hx
      exact s.coordinatePayoff_winner R.elapsed i hx
    _ = ∫ x, s.coordinateChildPayoff R.elapsed i j x
        ∂Measure.map (s.service.observation j)
          ((ν.prod independentExponentials).restrict (s.service.winner j)) :=
      (integral_map_of_stronglyMeasurable (s.service.measurable_observation j)
        (s.measurable_coordinateChildPayoff R.measurable_elapsed i j).stronglyMeasurable).symm
    _ = _ := by
      rw [s.service.first_completion_factorization,
        integral_prod _ (s.integrable_coordinateChildPayoff R ν hν i j)]
      simp only [s.coordinateChildPayoff_integral]

theorem integral_coordinatePayoff (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) :
    (∫ x, s.coordinatePayoff R.elapsed i x ∂ν.prod independentExponentials) =
      ∑ j, ∫ h, s.coordinateChildCertificate R.elapsed i j h ∂s.service.markedHistoryMeasure ν j := by
  have hi := s.integrable_coordinatePayoff R ν hν i
  rw [s.service.segment_measure_decomposition ν, integrable_add_measure] at hi
  have ht : (∫ x in s.service.terminalEvent, s.coordinatePayoff R.elapsed i x
      ∂ν.prod independentExponentials) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem s.service.measurable_terminalEvent] with x hx
    exact s.coordinatePayoff_terminal R.elapsed i hx
  conv_lhs => rw [s.service.segment_measure_decomposition ν]
  rw [integral_add_measure hi.1 hi.2, ht, zero_add, integral_sum_measure hi.2, tsum_fintype]
  exact Finset.sum_congr rfl (fun j _ => s.coordinatePayoff_winner_integral R ν hν i j)

theorem coordinate_certificate_step (R : StageRegion s) (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ h ∂ν, h ∈ R.domain) (i : ι) :
    (∫ h, s.coordinateCertificate R.elapsed i h ∂ν) ≤
      ∑ j, ∫ h, s.coordinateChildCertificate R.elapsed i j h ∂s.service.markedHistoryMeasure ν j := by
  have hs := s.integrable_coordinateStep R ν hν i
  have hr := s.integrable_coordinateRemaining R ν hν i
  have hl := integral_mono_ae (s.integrable_coordinateCertificate R ν hν i)
    (hs.integral_prod_left.sub hr.integral_prod_left)
    (show ∀ᵐ h ∂ν, s.coordinateCertificate R.elapsed i h ≤
      (∫ z, s.coordinateStep R.elapsed i (h, z) ∂independentExponentials) -
      ∫ z, s.coordinateRemaining R.elapsed i (h, z) ∂independentExponentials from by
      filter_upwards [hν] with h hh
      exact s.coordinate_certificate_step_fiber R.elapsed h i (R.admissible h hh)
        (le_of_eq (R.total_deadline h hh)))
  simp only [Pi.sub_apply] at hl
  rw [integral_sub hs.integral_prod_left hr.integral_prod_left,
    ← integral_prod _ hs, ← integral_prod _ hr, ← integral_sub hs hr] at hl
  apply hl.trans
  rw [← s.integral_coordinatePayoff R ν hν i]
  apply integral_mono_ae (hs.sub hr) (s.integrable_coordinatePayoff R ν hν i)
  filter_upwards [R.incoming_mem_ae ν hν, goodExecution_ae 1 s ν] with x hx hg
  exact s.coordinateStep_sub_remaining_le_payoff R i hx hg

end StochasticMatching.PosteriorStage
