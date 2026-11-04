import Matching.LabelledHistoryService
import Matching.InitialState
import Matching.RecycledResidualSlots

/-! Restoring original job labels does not change the actual first job
completion. Inactive coordinates have zero service and cannot win.
-/
open MeasureTheory Set
namespace StochasticMatching.ServiceCurveFamily
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem labelled_clock_at_label (p : ServiceCurveFamily ι) (label : ι → J)
    (hinj : Function.Injective label) (i : ι) (z : ℝ) :
    cappedHit ((p.labelled label).service (label i)) (p.labelled label).deadline z =
      cappedHit (p.service i) p.deadline z := by
  have he : (p.labelled label).service (label i) = p.service i :=
    funext (p.labelled_service_at_label label hinj i)
  rw [he]
  rfl

theorem labelled_clock_off_labels (p : ServiceCurveFamily ι) (label : ι → J)
    (j : J) (hj : ∀ i, label i ≠ j) (z : ℝ) (hz : 0 < z) :
    cappedHit ((p.labelled label).service j) (p.labelled label).deadline z = p.deadline := by
  unfold cappedHit
  rw [p.labelled_service_off_labels label j hj, if_neg (not_le.mpr hz)]
  rfl

theorem labelled_winner_is_label (p : ServiceCurveFamily ι) (label : ι → J)
    (z : J → ℝ) (hz : ∀ j, 0 < z j) (j : J)
    (hw : z ∈ variableWinner (p.labelled label).service (p.labelled label).deadline j) :
    ∃ i, label i = j := by
  by_contra hn
  have he := (p.labelled label).winner_service_eq (hz j) hw
  rw [p.labelled_service_off_labels label j (not_exists.mp hn)] at he
  exact (hz j).ne he

theorem labelled_winner_iff (p : ServiceCurveFamily ι) (label : ι → J)
    (hinj : Function.Injective label) (z : J → ℝ) (hz : ∀ j, 0 < z j) (j : ι) :
    z ∈ variableWinner (p.labelled label).service (p.labelled label).deadline (label j) ↔
      (fun i => z (label i)) ∈ variableWinner p.service p.deadline j := by
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · simpa only [p.labelled_clock_at_label label hinj] using hw.1
    · intro i hij
      have hi : label i ≠ label j := fun he => hij (hinj he)
      simpa only [p.labelled_clock_at_label label hinj] using hw.2 (label i) hi
  · intro hw
    refine ⟨?_, ?_⟩
    · simpa only [p.labelled_clock_at_label label hinj] using hw.1
    · intro a haj
      by_cases ha : ∃ i, label i = a
      · obtain ⟨i, rfl⟩ := ha
        have hij : i ≠ j := fun he => haj (congrArg label he)
        simpa only [p.labelled_clock_at_label label hinj] using hw.2 i hij
      · rw [p.labelled_clock_at_label label hinj,
          p.labelled_clock_off_labels label a (not_exists.mp ha) (z a) (hz a)]
        exact hw.1

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace J] [MeasurableSingletonClass J]

theorem labelled_firstEvent (p : ServiceCurveFamily ι) (label : ι → J)
    (hinj : Function.Injective label) (z : J → ℝ) (hz : ∀ j, 0 < z j) :
    (p.labelled label).firstEvent z =
      Sum.map id (Prod.map id label) (p.firstEvent (fun i => z (label i))) := by
  classical
  by_cases hw : ∃ j, (fun i => z (label i)) ∈ variableWinner p.service p.deadline j
  · obtain ⟨j, hj⟩ := hw
    rw [(p.labelled label).firstEvent_of_winner (label j)
      ((p.labelled_winner_iff label hinj z hz j).mpr hj), p.firstEvent_of_winner j hj,
      p.labelled_clock_at_label label hinj]
    rfl
  · have hn : ∀ j, (fun i => z (label i)) ∉ variableWinner p.service p.deadline j := not_exists.mp hw
    have hn' : ∀ a, z ∉ variableWinner (p.labelled label).service (p.labelled label).deadline a := by
      intro a ha
      obtain ⟨j, rfl⟩ := p.labelled_winner_is_label label z hz a ha
      exact hn j ((p.labelled_winner_iff label hinj z hz j).mp ha)
    rw [firstEvent, firstEvent, branchSelect_of_not_mem _ _ hn', branchSelect_of_not_mem _ _ hn]
    rfl

theorem labelled_firstEvent_law (p : ServiceCurveFamily ι) (label : ι → J)
    (hinj : Function.Injective label) :
    Measure.map (p.labelled label).firstEvent (independentExponentials (ι := J)) =
      Measure.map (Sum.map id (Prod.map id label)) (Measure.map p.firstEvent independentExponentials) := by
  let restrict : (J → ℝ) → (ι → ℝ) := fun z i => z (label i)
  have hr : Measurable restrict := measurable_pi_lambda _ (fun i => measurable_pi_apply (label i))
  have hf : Measurable (Sum.map (id : Unit → Unit) (Prod.map (id : ℝ → ℝ) label)) :=
    measurable_id.sumMap (measurable_id.prodMap (measurable_of_countable label))
  have he : (p.labelled label).firstEvent =ᵐ[independentExponentials]
      ((Sum.map id (Prod.map id label)) ∘ p.firstEvent) ∘ restrict := by
    filter_upwards [independentExponentials_ae_pos (ι := J)] with z hz
    exact p.labelled_firstEvent label hinj z hz
  rw [Measure.map_congr he, ← Measure.map_map (hf.comp p.measurable_firstEvent) hr,
    independentExponentials_injective_coordinates label hinj,
    Measure.map_map hf p.measurable_firstEvent]

end StochasticMatching.ServiceCurveFamily
