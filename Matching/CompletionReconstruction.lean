import Matching.VariableRacePartition
import Matching.InitialState

/-! The first-completion observation retains enough information to reconstruct
the original demand vector almost surely. This supports later segment
concatenation and expectations of functions of the original sample.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StochasticMatching.ServiceCurveFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ServiceCurveFamily ι)

noncomputable def reconstructMarked (j : ι) (x : ℝ × ({i : ι // i ≠ j} → ℝ)) : ι → ℝ :=
  (splitDemand j).symm (p.service j x.1, fun i => x.2 i + p.service i.1 x.1)

theorem measurable_reconstructMarked (j : ι) : Measurable (p.reconstructMarked j) := by
  apply (splitDemand j).symm.measurable.comp
  apply Measurable.prodMk ((p.service_continuous j).measurable.comp measurable_fst)
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).add
    ((p.service_continuous i.1).measurable.comp measurable_fst)

theorem reconstruct_first_observation {z : ι → ℝ} {j : ι}
    (hz : 0 < z j) (hj : z ∈ variableWinner p.service p.deadline j) :
    p.reconstructMarked j (variableObservation p.service p.deadline j z) = z := by
  have htime := cappedHit_bounds (z := z j) (p.service_continuous j) p.deadline_pos.le
  have hdem := (cappedHit_le_iff (p.service_continuous j) p.deadline_pos.le
    (p.service_monotone j) htime.1 hj.1).mp (le_refl _)
  have hend : z j ≤ p.service j p.deadline :=
    hdem.trans (p.service_monotone j htime ⟨p.deadline_pos.le, le_refl _⟩ htime.2)
  have hexact := service_at_cappedHit (p.service_continuous j) p.deadline_pos.le
    (p.service_monotone j) (show p.service j 0 ≤ z j by rw [p.service_zero]; exact hz.le) hend
  unfold reconstructMarked variableObservation
  simp only [hexact, sub_add_cancel]
  exact (splitDemand j).symm_apply_apply z

theorem reconstruct_first_observation_ae (j : ι) :
    (fun z => p.reconstructMarked j (variableObservation p.service p.deadline j z)) =ᵐ[
      independentExponentials.restrict (variableWinner p.service p.deadline j)] id := by
  filter_upwards [ae_restrict_mem (p.measurable_winner j),
    ae_restrict_of_ae (independentExponentials_ae_pos (ι := ι))] with z hj hz
  exact p.reconstruct_first_observation (hz j) hj

/-- A marked-branch formula for arbitrary nonnegative measurable functions of
the original demand sample, including dependence on the completed coordinate. -/
theorem original_sample_branch_lintegral (j : ι) (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in variableWinner p.service p.deadline j, f z ∂independentExponentials) =
      ∫⁻ t in Icc 0 p.deadline,
        ENNReal.ofReal (p.rate j t * Real.exp (-(∑ i, p.service i t))) *
          (∫⁻ y, f (p.reconstructMarked j (t, y)) ∂independentExponentials) := by
  have hf' : Measurable (fun x => f (p.reconstructMarked j x)) :=
    hf.comp (p.measurable_reconstructMarked j)
  have hsum : Continuous (fun t => ∑ i, p.service i t) :=
    continuous_finset_sum _ (fun i _ => p.service_continuous i)
  have hdens : Measurable (fun t =>
      ENNReal.ofReal (p.rate j t * Real.exp (-(∑ i, p.service i t)))) :=
    ((p.rate_continuous j).mul (Real.continuous_exp.comp hsum.neg)).measurable.ennreal_ofReal
  calc
    _ = ∫⁻ z in variableWinner p.service p.deadline j,
        f (p.reconstructMarked j (variableObservation p.service p.deadline j z))
          ∂independentExponentials := by
      apply lintegral_congr_ae
      filter_upwards [p.reconstruct_first_observation_ae j] with z hz
      exact congrArg f hz.symm
    _ = ∫⁻ x, f (p.reconstructMarked j x) ∂
        Measure.map (variableObservation p.service p.deadline j)
          (independentExponentials.restrict (variableWinner p.service p.deadline j)) :=
      (lintegral_map hf' (p.measurable_observation j)).symm
    _ = _ := by
      rw [variable_first_completion_marked_law p.service_continuous p.rate_continuous
        p.deadline_pos p.service_monotone p.service_zero p.rate_nonneg p.service_deriv j,
        lintegral_prod _ hf'.aemeasurable, variableMarkedTimeMeasure,
        lintegral_withDensity_eq_lintegral_mul (volume.restrict (Icc 0 p.deadline))
          hdens hf'.lintegral_prod_right']
      rfl

end StochasticMatching.ServiceCurveFamily
