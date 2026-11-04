import Matching.PosteriorCursorDeadline
import Matching.LabelledFirstEvent

/-! Recover the original residual demand at the beginning of the current
posterior stage. Advancing through rejected arrivals leaves it unchanged.
-/
open MeasureTheory Set
namespace StochasticMatching.PosteriorStage
variable {H ι J : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J]

noncomputable def stageDemand (s : PosteriorStage H ι) (label : ι → J)
    (x : H × ℝ) (r : J → ℝ) (i : ι) : ℝ :=
  r (label i) + (s.service.curves x.1).service i ((s.service.labelled label).shiftOffset x)

theorem stageDemand_initial (s : PosteriorStage H ι) (label : ι → J) (h : H) (r : J → ℝ) :
    s.stageDemand label (h, 0) r = fun i => r (label i) := by
  funext i
  simp only [stageDemand, (s.service.labelled label).shiftOffset_eq h 0 le_rfl (s.deadline_pos h),
    (s.service.curves h).service_zero, add_zero]

theorem routingService_at_label (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × ℝ) (i : ι) (t : ℝ) :
    ((s.routingService label).curves x).service (label i) t =
      (s.service.curves x.1).service i ((s.service.labelled label).shiftOffset x + t) -
        (s.service.curves x.1).service i ((s.service.labelled label).shiftOffset x) := by
  change labelLift label _ (label i) - labelLift label _ (label i) = _
  rw [labelLift_at_label label hinj, labelLift_at_label label hinj]

theorem stageDemand_after_service (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × ℝ) (r : J → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (htT : t < ((s.routingService label).curves x).deadline) :
    s.stageDemand label (s.advanceRoutingTime label (x, t))
        (fun j => r j - ((s.routingService label).curves x).service j t) = s.stageDemand label x r := by
  have hb := s.advanceRoutingTime_bounds label x t ht0 htT
  funext i
  change r (label i) - ((s.routingService label).curves x).service (label i) t +
      (s.service.curves x.1).service i ((s.service.labelled label).shiftOffset
        (x.1, (s.advanceRoutingTime label (x, t)).2)) = _
  rw [(s.service.labelled label).shiftOffset_eq _ _ hb.1 hb.2, s.routingService_at_label label hinj]
  simp only [advanceRoutingTime, stageDemand]
  ring

theorem stageDemand_terminal (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × ℝ) (r : J → ℝ)
    (hr : ∀ j, ((s.routingService label).curves x).service j
      ((s.routingService label).curves x).deadline < r j) :
    (x.1, s.stageDemand label x r) ∈ s.service.terminalEvent := by
  intro i
  have hi := hr (label i)
  rw [s.routingService_at_label label hinj] at hi
  change (s.service.curves x.1).service i
      ((s.service.labelled label).shiftOffset x + (s.deadline x.1 - (s.service.labelled label).shiftOffset x)) -
    (s.service.curves x.1).service i ((s.service.labelled label).shiftOffset x) < r (label i) at hi
  rw [add_sub_cancel] at hi
  change (s.service.curves x.1).service i (s.deadline x.1) <
    r (label i) + (s.service.curves x.1).service i ((s.service.labelled label).shiftOffset x)
  linarith

theorem measurable_stageDemand (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (fun x : (H × ℝ) × (J → ℝ) => s.stageDemand label x.1 x.2) := by
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply (label i)).comp measurable_snd).add
    ((s.service.measurable_service i).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((s.service.labelled label).measurable_shiftOffset.comp measurable_fst)))

theorem routingService_clock_at_label (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × ℝ) (r : J → ℝ) (i : ι) (hr : 0 < r (label i)) :
    cappedHit (((s.routingService label).curves x).service (label i))
      ((s.routingService label).curves x).deadline (r (label i)) =
      cappedHit ((s.service.curves x.1).service i) (s.deadline x.1) (s.stageDemand label x r i) -
        (s.service.labelled label).shiftOffset x := by
  let u := (s.service.labelled label).shiftOffset x
  have hu0 := (s.service.labelled label).shiftOffset_nonneg x
  have huT := (s.service.labelled label).shiftOffset_lt x
  have hz : (s.service.curves x.1).service i u < s.stageDemand label x r i := by
    change _ < r (label i) + _
    linarith
  have he : ((s.routingService label).curves x).service (label i) =
      fun t => (s.service.curves x.1).service i (u + t) - (s.service.curves x.1).service i u :=
    funext (s.routingService_at_label label hinj x i)
  rw [he]
  have h := (s.service.curves x.1).afterTime_clock u hu0 huT i hz
  simpa only [ServiceCurveFamily.afterTime, stageDemand, u, add_sub_cancel_right] using h

theorem routingService_winner_source (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × ℝ) (r : J → ℝ) (hr : ∀ i, 0 < r (label i)) (j : ι)
    (hw : r ∈ variableWinner ((s.routingService label).curves x).service
      ((s.routingService label).curves x).deadline (label j)) :
    (x.1, s.stageDemand label x r) ∈ s.service.winner j := by
  refine ⟨?_, ?_⟩
  · have ht := hw.1
    rw [s.routingService_clock_at_label label hinj x r j (hr j)] at ht
    change _ - (s.service.labelled label).shiftOffset x <
      s.deadline x.1 - (s.service.labelled label).shiftOffset x at ht
    exact (sub_lt_sub_iff_right _).mp ht
  · intro i hij
    have hli : label i ≠ label j := fun he => hij (hinj he)
    have ht := hw.2 (label i) hli
    rw [s.routingService_clock_at_label label hinj x r j (hr j),
      s.routingService_clock_at_label label hinj x r i (hr i)] at ht
    exact (sub_lt_sub_iff_right _).mp ht

theorem routingService_source_clock (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × ℝ) (r : J → ℝ) (j : ι) (hr : 0 < r (label j)) :
    s.service.clock j (x.1, s.stageDemand label x r) =
      (s.service.labelled label).shiftOffset x +
        cappedHit (((s.routingService label).curves x).service (label j))
          ((s.routingService label).curves x).deadline (r (label j)) := by
  have h := s.routingService_clock_at_label label hinj x r j hr
  change cappedHit ((s.service.curves x.1).service j) (s.deadline x.1)
    (s.stageDemand label x r j) = _
  linarith

theorem routingService_source_observation (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × ℝ) (r : J → ℝ) (j : ι) (hr : 0 < r (label j)) :
    let t := cappedHit (((s.routingService label).curves x).service (label j))
      ((s.routingService label).curves x).deadline (r (label j))
    s.service.observation j (x.1, s.stageDemand label x r) =
      (s.advanceRoutingTime label (x, t),
        fun i : {i : ι // i ≠ j} => r (label i.1) - ((s.routingService label).curves x).service (label i.1) t) := by
  intro t
  unfold HistoryServiceFamily.observation
  rw [s.routingService_source_clock label hinj x r j hr]
  apply Prod.ext
  · rfl
  · funext i
    change s.stageDemand label x r i.1 - (s.service.curves x.1).service i.1
        ((s.service.labelled label).shiftOffset x + t) =
      r (label i.1) - ((s.routingService label).curves x).service (label i.1) t
    rw [s.routingService_at_label label hinj]
    simp only [stageDemand]
    ring

end StochasticMatching.PosteriorStage
