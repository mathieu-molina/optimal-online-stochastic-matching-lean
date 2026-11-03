import Matching.TerminalPayload

/-! Two observations that agree outside a small exceptional set have close
event probabilities. No metric or countability assumption on outputs is needed.
-/
open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory
namespace StochasticMatching
variable {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]

theorem measure_event_le_of_agree (μ : Measure A) (f g : A → E) (S : Set A) (B : Set E)
    (h : ∀ᵐ a ∂μ, a ∉ S → (f a ∈ B ↔ g a ∈ B)) :
    μ (f ⁻¹' B) ≤ μ (g ⁻¹' B) + μ S := by
  apply le_trans (measure_mono_ae ?_) (measure_union_le (g ⁻¹' B) S)
  filter_upwards [h] with a ha
  intro hfa
  by_cases hs : a ∈ S
  · exact Or.inr hs
  · exact Or.inl ((ha hs).mp hfa)

theorem map_measure_le_of_agree (μ : Measure A) (f g : A → E) (hf : Measurable f) (hg : Measurable g)
    (S : Set A) (B : Set E) (hB : MeasurableSet B)
    (h : ∀ᵐ a ∂μ, a ∉ S → (f a ∈ B ↔ g a ∈ B)) :
    Measure.map f μ B ≤ Measure.map g μ B + μ S := by
  rw [Measure.map_apply hf hB, Measure.map_apply hg hB]
  exact measure_event_le_of_agree μ f g S B h

theorem residualObservation_approximation {R : Type*} [MeasurableSpace R]
    (ρ : Measure R) [IsProbabilityMeasure ρ] (μ : Measure A) [SFinite μ]
    (F : A × R → E) (hF : Measurable F) (O : A → E) (hO : Measurable O)
    (S : Set A) (hS : MeasurableSet S) (hagree : ∀ a ∉ S, ∀ r, F (a, r) = O a)
    (B : Set E) (hB : MeasurableSet B) :
    Measure.map F (μ.prod ρ) B ≤ Measure.map O μ B + μ S ∧
      Measure.map O μ B ≤ Measure.map F (μ.prod ρ) B + μ S := by
  have hg : Measurable (O ∘ Prod.fst : A × R → E) := hO.comp measurable_fst
  have heq : Measure.map (O ∘ Prod.fst) (μ.prod ρ) = Measure.map O μ := by
    rw [← Measure.map_map hO measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have hmass : μ.prod ρ (S ×ˢ (univ : Set R)) = μ S := by
    rw [Measure.prod_prod, measure_univ, mul_one]
  have he : ∀ᵐ x ∂μ.prod ρ, x ∉ S ×ˢ (univ : Set R) → (F x ∈ B ↔ O x.1 ∈ B) :=
    Filter.Eventually.of_forall (fun x hx => by
      have hn : x.1 ∉ S := fun hs => hx ⟨hs, mem_univ _⟩
      rw [hagree x.1 hn x.2])
  have h1 := map_measure_le_of_agree (μ.prod ρ) F (O ∘ Prod.fst) hF hg _ B hB he
  have h2 := map_measure_le_of_agree (μ.prod ρ) (O ∘ Prod.fst) F hg hF _ B hB
    (he.mono (fun x hx hs => (hx hs).symm))
  rw [heq, hmass] at h1 h2
  exact ⟨h1, h2⟩

end StochasticMatching
