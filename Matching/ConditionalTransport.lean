import Matching.HistoryConditionalExpectation
import Matching.PosteriorTrajectory

/-! Conditional-expectation identification on an arbitrary original sample
space, assuming its observed-history and residual map has the product law.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StochasticMatching

variable {H ι Ω : Type*} [MeasurableSpace H] [Fintype ι] [MeasurableSpace Ω]

theorem conditionalExpectation_history_transport (ν : Measure H) [IsFiniteMeasure ν]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → H × (ι → ℝ)) (hX : Measurable X)
    (hLaw : Measure.map X μ = ν.prod independentExponentials)
    (f : H × (ι → ℝ) → ℝ) (hf : Measurable f)
    (hfi : Integrable f (ν.prod independentExponentials)) :
    (fun ω => ∫ z, f ((X ω).1, z) ∂independentExponentials) =ᵐ[μ]
      μ[fun ω => f (X ω) | (‹MeasurableSpace H›).comap (fun ω => (X ω).1)] := by
  let b : Ω → H := fun ω => (X ω).1
  let g : H → ℝ := fun h => ∫ z, f (h, z) ∂independentExponentials
  have hb : Measurable b := measurable_fst.comp hX
  have hg : StronglyMeasurable g := hf.stronglyMeasurable.integral_prod_right'
  have hbLaw : Measure.map b μ = ν := by
    change Measure.map (Prod.fst ∘ X) μ = ν
    rw [← Measure.map_map measurable_fst hX, hLaw]
    simp
  have hFi : Integrable (fun ω => f (X ω)) μ := by
    have h : Integrable f (Measure.map X μ) := by rw [hLaw]; exact hfi
    exact h.comp_measurable hX
  have hgi : Integrable (fun ω => g (b ω)) μ := by
    have h : Integrable g (Measure.map b μ) := by rw [hbLaw]; exact hfi.integral_prod_left
    exact h.comp_measurable hb
  apply ae_eq_condExp_of_forall_setIntegral_eq hb.comap_le hFi
    (fun _ _ _ => hgi.integrableOn)
  · rintro _ ⟨s, hs, rfl⟩ _
    have hrestrict : Measure.map X (μ.restrict (b ⁻¹' s)) =
        (ν.restrict s).prod independentExponentials := by
      change Measure.map X (μ.restrict (X ⁻¹' (Prod.fst ⁻¹' s))) = _
      rw [← Measure.restrict_map hX (measurable_fst hs), hLaw,
        Measure.restrict_prod_eq_prod_univ]
      congr 1
      ext x
      simp
    have hfir : Integrable f ((ν.restrict s).prod independentExponentials) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hfi.restrict
    calc
      (∫ ω in b ⁻¹' s, g (b ω) ∂μ) =
          ∫ x : H × (ι → ℝ), g x.1 ∂(ν.restrict s).prod independentExponentials := by
        rw [← hrestrict]
        have hgf : StronglyMeasurable (fun x : H × (ι → ℝ) => g x.1) :=
          hg.comp_measurable measurable_fst
        exact (integral_map_of_stronglyMeasurable hX hgf).symm
      _ = ∫ x, f x ∂(ν.restrict s).prod independentExponentials := by
        rw [integral_fun_fst, measureReal_univ_eq_one, one_smul, integral_prod _ hfir]
      _ = ∫ ω in b ⁻¹' s, f (X ω) ∂μ := by
        rw [← hrestrict, integral_map_of_stronglyMeasurable hX hf.stronglyMeasurable]
  · exact (hg.comp_measurable (comap_measurable b)).aestronglyMeasurable

theorem posterior_rate_conditionalExpectation (p : PosteriorData H ι)
    (ν : Measure H) [IsFiniteMeasure ν] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → H × (ι → ℝ)) (hX : Measurable X)
    (hLaw : Measure.map X μ = ν.prod independentExponentials)
    {ξ : H → (ι → ℝ)} (hξ : Measurable ξ) (i : ι) :
    (fun ω => posteriorRate p.allocation (X ω).1 (ξ (X ω).1) i) =ᵐ[μ]
      μ[fun ω => p.allocation ((X ω).1, ξ (X ω).1 + (X ω).2) i |
        (‹MeasurableSpace H›).comap (fun ω => (X ω).1)] := by
  let f : H × (ι → ℝ) → ℝ := fun x => p.allocation (x.1, ξ x.1 + x.2) i
  have hf : Measurable f := (measurable_pi_apply i).comp
    (p.measurable_allocation.comp (measurable_fst.prodMk ((hξ.comp measurable_fst).add measurable_snd)))
  have hfi : Integrable f (ν.prod independentExponentials) := by
    apply (integrable_const (p.bound : ℝ)).mono' hf.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (p.allocation_nonneg x.1 (ξ x.1 + x.2) i)]
    exact p.allocation_le x.1 (ξ x.1 + x.2) i
  exact conditionalExpectation_history_transport ν μ X hX hLaw f hf hfi

end StochasticMatching
