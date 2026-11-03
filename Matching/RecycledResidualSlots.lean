import Matching.RoutingRestarts

/-! Keep a fixed job-coordinate space after each arrival. When job j wins,
its now-inactive coordinate is filled by the residual rejection clock. All
still-active jobs retain their actual residual demands. The resulting whole
vector is again independent unit exponentials.
-/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def survivorSlot (j : Option ι) (i : ι) : {k : Option ι // k ≠ j} :=
  ⟨Equiv.swap none j (some i), by
    intro h
    have he : Equiv.swap none j (some i) = Equiv.swap none j none := by simpa using h
    have hi := (Equiv.swap none j).injective he
    cases hi⟩

theorem survivorSlot_injective (j : Option ι) : Function.Injective (survivorSlot (ι := ι) j) := by
  intro i k h
  exact Option.some.inj ((Equiv.swap none j).injective (congrArg Subtype.val h))

@[simp] theorem survivorSlot_none (i : ι) : (survivorSlot none i).val = some i := by
  simp [survivorSlot]

@[simp] theorem survivorSlot_self (j : ι) : (survivorSlot (some j) j).val = none := by
  simp [survivorSlot]

theorem survivorSlot_other (j i : ι) (hij : i ≠ j) : (survivorSlot (some j) i).val = some i := by
  simp [survivorSlot, Equiv.swap_apply_of_ne_of_ne, hij]

noncomputable def recycledObservation (p : ServiceCurveFamily (Option ι)) (j : Option ι)
    (z : Option ι → ℝ) : ℝ × (ι → ℝ) :=
  let t := cappedHit (p.service j) p.deadline (z j)
  (t, fun i => z (survivorSlot j i).val - p.service (survivorSlot j i).val t)

theorem measurable_recycledObservation (p : ServiceCurveFamily (Option ι)) (j : Option ι) :
    Measurable (recycledObservation p j) := by
  exact (p.measurable_clock j).prodMk (measurable_pi_lambda _ (fun i =>
    (measurable_pi_apply (survivorSlot j i).val).sub
      ((p.service_continuous (survivorSlot j i).val).measurable.comp (p.measurable_clock j))))

theorem recycledObservation_law (p : ServiceCurveFamily (Option ι)) (j : Option ι) :
    Measure.map (recycledObservation p j)
      (independentExponentials.restrict (variableWinner p.service p.deadline j)) =
      (variableMarkedTimeMeasure p.service p.rate p.deadline j).prod
        (independentExponentials (ι := ι)) := by
  letI : SigmaFinite (variableMarkedTimeMeasure p.service p.rate p.deadline j) := by
    unfold variableMarkedTimeMeasure
    infer_instance
  let F : ℝ × ({k : Option ι // k ≠ j} → ℝ) → ℝ × (ι → ℝ) :=
    fun x => (x.1, fun i => x.2 (survivorSlot j i))
  have hF : Measurable F := measurable_fst.prodMk
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply (survivorSlot j i)).comp measurable_snd))
  have h := congrArg (Measure.map F)
    (variable_first_completion_marked_law p.service_continuous p.rate_continuous p.deadline_pos
      p.service_monotone p.service_zero p.rate_nonneg p.service_deriv j)
  rw [Measure.map_map hF (p.measurable_observation j),
    product_exponential_coordinate_projection _ (survivorSlot j) (survivorSlot_injective j)] at h
  exact h

end StochasticMatching
