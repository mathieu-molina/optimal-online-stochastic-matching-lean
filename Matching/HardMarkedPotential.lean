import Matching.HardArrivalPotential

/-! The one-step upper bound holds for every random routing decision with
the correct Poisson time/type marginal and a fresh supported mark. It is
not restricted to greedy or to the constructed coverage algorithm. -/
open MeasureTheory Set
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

def unmatchedAfterMark (A : Finset ι) : Option ι → Finset ι
  | none => A
  | some i => A.erase i

noncomputable def hardMarkedUpperPayoff (T : ℝ) (A : Finset ι) :
    Unit ⊕ (ℝ × (Finset ι × Option ι)) → ℝ :=
  Sum.elim (fun _ => 1 - hardUnmatchedFraction A) (fun e =>
    hardUpperPotential (max 0 (T - e.1)) (hardUnmatchedFraction (unmatchedAfterMark A e.2.2)))

theorem hardMarkedUpperPayoff_measurable (T : ℝ) (A : Finset ι) :
    Measurable (hardMarkedUpperPayoff T A) := by
  apply measurable_const.sumElim
  apply measurable_from_prod_countable
  intro p
  exact ((continuous_hardUpperPotential_time
    (hardUnmatchedFraction_bounds (unmatchedAfterMark A p.2)).1).comp
      (continuous_const.max (continuous_const.sub continuous_id))).measurable

theorem hardMarkedUpperPayoff_bounds (T : ℝ) (A : Finset ι)
    (e : Unit ⊕ (ℝ × (Finset ι × Option ι))) :
    0 ≤ hardMarkedUpperPayoff T A e ∧ hardMarkedUpperPayoff T A e ≤ 1 := by
  cases e with
  | inl _ => exact ⟨sub_nonneg.mpr (hardUnmatchedFraction_bounds A).2,
      sub_le_self _ (hardUnmatchedFraction_bounds A).1⟩
  | inr e =>
      exact hardUpperPotential_bounds (le_max_left _ _)
        (hardUnmatchedFraction_bounds (unmatchedAfterMark A e.2.2))

theorem hardUnmatchedFraction_erase (A : Finset ι) {i : ι} (hi : i ∈ A) :
    hardUnmatchedFraction (A.erase i) = hardUnmatchedFraction A - 1 / Fintype.card ι := by
  unfold hardUnmatchedFraction
  rw [Finset.card_erase_of_mem hi, Nat.cast_sub (Nat.succ_le.mpr (Finset.card_pos.mpr ⟨i, hi⟩))]
  norm_num
  ring

theorem hardAfterFraction_le_mark (A S : Finset ι) (j : Option ι)
    (hj : ∀ i, j = some i → i ∈ S ∩ A) :
    hardAfterFraction A S ≤ hardUnmatchedFraction (unmatchedAfterMark A j) := by
  cases j with
  | none =>
      unfold hardAfterFraction unmatchedAfterMark
      split_ifs
      · exact sub_le_self _ (by positivity)
      · exact le_rfl
  | some i =>
      have hi := hj i rfl
      rw [unmatchedAfterMark, hardUnmatchedFraction_erase A (Finset.mem_inter.mp hi).2,
        hardAfterFraction, if_pos ⟨i, hi⟩]

theorem hardMarkedUpperPayoff_le (T : ℝ) (A : Finset ι)
    (e : Unit ⊕ (ℝ × (Finset ι × Option ι)))
    (he : match e with
      | .inl _ => True
      | .inr p => ∀ i, p.2.2 = some i → i ∈ p.2.1 ∩ A) :
    hardMarkedUpperPayoff T A e ≤ hardArrivalUpperPayoff T A (arrivalTypeProjection e) := by
  cases e with
  | inl _ => exact le_rfl
  | inr p =>
      exact hardUpperPotential_antitone _ (hardAfterFraction_bounds A p.2.1).1
        (hardAfterFraction_le_mark A p.2.1 p.2.2 he)

theorem hardPoisson_arbitrary_routing_step_upper_bound {T : ℝ} (hT : 0 < T) (A : Finset ι)
    (μ : Measure (Unit ⊕ (ℝ × (Finset ι × Option ι)))) [IsProbabilityMeasure μ]
    (hinput : Measure.map arrivalTypeProjection μ =
      poissonNextArrival (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) T)
    (hvalid : ∀ᵐ e ∂μ, match e with
      | .inl _ => True
      | .inr p => ∀ i, p.2.2 = some i → i ∈ p.2.1 ∩ A) :
    (∫ e, hardMarkedUpperPayoff T A e ∂μ) ≤ hardUpperPotential T (hardUnmatchedFraction A) := by
  have hi : Integrable (hardMarkedUpperPayoff T A) μ :=
    integrable_of_abs_bounded _ (hardMarkedUpperPayoff_measurable T A) 1 (fun e => by
      rw [abs_of_nonneg (hardMarkedUpperPayoff_bounds T A e).1]
      exact (hardMarkedUpperPayoff_bounds T A e).2)
  have hj : Integrable (fun e => hardArrivalUpperPayoff T A (arrivalTypeProjection e)) μ :=
    integrable_of_abs_bounded _
      ((hardArrivalUpperPayoff_measurable T A).comp measurable_arrivalTypeProjection) 1 (fun e => by
        rw [abs_of_nonneg (hardArrivalUpperPayoff_bounds T A _).1]
        exact (hardArrivalUpperPayoff_bounds T A _).2)
  calc
    _ ≤ ∫ e, hardArrivalUpperPayoff T A (arrivalTypeProjection e) ∂μ :=
      integral_mono_ae hi hj (hvalid.mono (fun e he => hardMarkedUpperPayoff_le T A e he))
    _ = ∫ e, hardArrivalUpperPayoff T A e
        ∂poissonNextArrival (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) T := by
      rw [← hinput, integral_map_of_stronglyMeasurable measurable_arrivalTypeProjection
        (hardArrivalUpperPayoff_measurable T A).stronglyMeasurable]
    _ ≤ _ := hardPoisson_first_arrival_upper_bound hT A

end StochasticMatching
