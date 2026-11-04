import Matching.PoissonOnlineController
import Matching.HardStatePotential

/-! Every admissible Poisson online controller on the hard instance has a
bounded supersolution with initial value `m * (1 - e / e^e)`. -/
open MeasureTheory ProbabilityTheory Set
namespace StochasticMatching
variable {H ι : Type*} [MeasurableSpace H]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

theorem hardPoisson_joint_routing_step_upper_bound {Ω : Type*} [MeasurableSpace Ω]
    {T : ℝ} (hT : 0 < T) (A : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (event : Ω → ControllerEvent (Finset ι) ι) (hm : Measurable event)
    (hinput : Measure.map (fun y => arrivalTypeProjection (event y)) μ =
      poissonNextArrival (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) T)
    (hvalid : ∀ᵐ y ∂μ, match event y with
      | .inl _ => True
      | .inr p => ∀ i, p.2.2 = some i → i ∈ p.2.1 ∩ A) :
    (∫ y, hardMarkedUpperPayoff T A (event y) ∂μ) ≤ hardUpperPotential T (hardUnmatchedFraction A) := by
  have hi : Integrable (fun y => hardMarkedUpperPayoff T A (event y)) μ :=
    integrable_of_abs_bounded _ ((hardMarkedUpperPayoff_measurable T A).comp hm) 1 (fun y => by
      rw [abs_of_nonneg (hardMarkedUpperPayoff_bounds T A _).1]
      exact (hardMarkedUpperPayoff_bounds T A _).2)
  have hj : Integrable (fun y => hardArrivalUpperPayoff T A (arrivalTypeProjection (event y))) μ :=
    integrable_of_abs_bounded _
      ((hardArrivalUpperPayoff_measurable T A).comp (measurable_arrivalTypeProjection.comp hm)) 1 (fun y => by
        rw [abs_of_nonneg (hardArrivalUpperPayoff_bounds T A _).1]
        exact (hardArrivalUpperPayoff_bounds T A _).2)
  calc
    _ ≤ ∫ y, hardArrivalUpperPayoff T A (arrivalTypeProjection (event y)) ∂μ :=
      integral_mono_ae hi hj (hvalid.mono (fun y hy => hardMarkedUpperPayoff_le T A _ hy))
    _ = ∫ e, hardArrivalUpperPayoff T A e
        ∂poissonNextArrival (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) T := by
      rw [← hinput]
      exact (integral_map_of_stronglyMeasurable (measurable_arrivalTypeProjection.comp hm)
        (hardArrivalUpperPayoff_measurable T A).stronglyMeasurable).symm
    _ ≤ _ := hardPoisson_first_arrival_upper_bound hT A

namespace PoissonOnlineController
variable (P : PoissonOnlineController (H := H) (id : Finset ι → Finset ι) hardPoissonIntensity)

noncomputable def hardPotential : ControllerState H ι → ℝ :=
  hardStatePotential P.horizon P.available

theorem hardPotential_measurable : Measurable P.hardPotential :=
  measurable_hardStatePotential P.horizon P.available P.horizon_measurable P.available_measurable

theorem hardPotential_bounds (x : ControllerState H ι) : 0 ≤ P.hardPotential x ∧ P.hardPotential x ≤ 1 := by
  cases x with
  | inl A => exact ⟨sub_nonneg.mpr (hardUnmatchedFraction_bounds A).2,
      sub_le_self _ (hardUnmatchedFraction_bounds A).1⟩
  | inr h => exact hardUpperPotential_bounds (P.horizon_pos h).le (hardUnmatchedFraction_bounds (P.available h))

theorem hardPotential_step_pointwise (h : H)
    (y : ControllerEvent (Finset ι) ι × ControllerState H ι)
    (hy : ControllerStepValid id P.horizon P.available h y) :
    P.hardPotential y.2 ≤ hardMarkedUpperPayoff (P.horizon h) (P.available h) y.1 := by
  rcases y with ⟨e, x⟩
  cases e with
  | inl _ =>
      change x = .inl (P.available h) at hy
      rw [hy]
      exact le_rfl
  | inr p =>
      cases x with
      | inl A =>
          change _ ∧ A = unmatchedAfterMark (P.available h) p.2.2 at hy
          change 1 - hardUnmatchedFraction A ≤ _
          rw [hy.2]
          exact hardUpperPotential_ge_matched (le_max_left _ _)
            (hardUnmatchedFraction_bounds (unmatchedAfterMark (P.available h) p.2.2))
      | inr h' =>
          change _ ∧ P.available h' = unmatchedAfterMark (P.available h) p.2.2 ∧
            P.horizon h' = P.horizon h - p.1 at hy
          change hardUpperPotential (P.horizon h') (hardUnmatchedFraction (P.available h')) ≤ _
          change _ ≤ hardUpperPotential (max 0 (P.horizon h - p.1))
            (hardUnmatchedFraction (unmatchedAfterMark (P.available h) p.2.2))
          rw [← hy.2.2, max_eq_right (P.horizon_pos h').le, hy.2.1]

theorem hardPotential_step (x : ControllerState H ι) :
    (∫ x', P.hardPotential x' ∂P.step x) ≤ P.hardPotential x := by
  cases x with
  | inl A =>
      change (∫ x', P.hardPotential x' ∂Measure.dirac (.inl A)) ≤ P.hardPotential (.inl A)
      rw [integral_dirac' _ _ P.hardPotential_measurable.stronglyMeasurable]
  | inr h =>
      letI := P.probability h
      change (∫ x', P.hardPotential x' ∂Measure.map Prod.snd (P.next h)) ≤ _
      rw [integral_map_of_stronglyMeasurable measurable_snd P.hardPotential_measurable.stronglyMeasurable]
      have hi : Integrable (fun y => P.hardPotential y.2) (P.next h) :=
        integrable_of_abs_bounded _ (P.hardPotential_measurable.comp measurable_snd) 1 (fun y => by
          rw [abs_of_nonneg (P.hardPotential_bounds y.2).1]
          exact (P.hardPotential_bounds y.2).2)
      have hj : Integrable (fun y => hardMarkedUpperPayoff (P.horizon h) (P.available h) y.1) (P.next h) :=
        integrable_of_abs_bounded _
          ((hardMarkedUpperPayoff_measurable _ _).comp measurable_fst) 1 (fun y => by
            rw [abs_of_nonneg (hardMarkedUpperPayoff_bounds _ _ _).1]
            exact (hardMarkedUpperPayoff_bounds _ _ _).2)
      apply (integral_mono_ae hi hj ((P.valid h).mono (fun y hy => P.hardPotential_step_pointwise h y hy))).trans
      apply hardPoisson_joint_routing_step_upper_bound (P.horizon_pos h) (P.available h)
        (P.next h) Prod.fst measurable_fst (P.input_law h)
      filter_upwards [P.valid h] with y hy
      cases he : y.1 with
      | inl _ => trivial
      | inr p =>
          simp only [ControllerStepValid, he] at hy
          exact hy.1

end PoissonOnlineController
end StochasticMatching
