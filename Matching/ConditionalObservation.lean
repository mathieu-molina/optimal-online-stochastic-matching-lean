import Matching.BranchConditional

/-! Transfer a conditional identity to an observation that, almost surely,
is a measurable function of the local history. The candidate must itself be
a measurable function of the new observation. This handles tagged branches
without pretending that their events are measurable in the untagged history.
-/

open MeasureTheory Set

namespace StochasticMatching

variable {Ω H G : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace G]

theorem conditionalExpectation_of_observation (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → H) (hX : Measurable X) (O : Ω → G) (hO : Measurable O)
    (q : H → G) (hq : Measurable q) (hrel : O =ᵐ[μ] q ∘ X)
    (r : G → ℝ) (hr : Measurable r) {f : Ω → ℝ} (hf : Integrable f μ)
    (hlocal : (r ∘ O) =ᵐ[μ] μ[f | (‹MeasurableSpace H›).comap X]) :
    (r ∘ O) =ᵐ[μ] μ[f | (‹MeasurableSpace G›).comap O] := by
  have hri : Integrable (r ∘ O) μ := integrable_condExp.congr hlocal.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hO.comap_le hf
    (fun _ _ _ => hri.integrableOn)
  · rintro _ ⟨A, hA, rfl⟩ _
    have hset : (O ⁻¹' A : Set Ω) =ᵐ[μ] X ⁻¹' (q ⁻¹' A) := by
      filter_upwards [hrel] with x hx
      exact congrArg (fun y => y ∈ A) hx
    have hrestrict := Measure.restrict_congr_set hset
    rw [hrestrict]
    calc
      (∫ x in X ⁻¹' (q ⁻¹' A), (r ∘ O) x ∂μ) =
          ∫ x in X ⁻¹' (q ⁻¹' A), (μ[f | (‹MeasurableSpace H›).comap X]) x ∂μ :=
        by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae hlocal] with x hx
          exact hx
      _ = ∫ x in X ⁻¹' (q ⁻¹' A), f x ∂μ :=
        setIntegral_condExp hX.comap_le hf ⟨q ⁻¹' A, hq hA, rfl⟩
  · exact (hr.stronglyMeasurable.comp_measurable (comap_measurable O)).aestronglyMeasurable

end StochasticMatching
