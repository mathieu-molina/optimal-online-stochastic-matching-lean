import Matching.CursorContinuation
import Matching.FirstEventRestart

/-! An accepted routing job takes exactly the same posterior branch as the
original scheduling trace, including its elapsed time and survivor demands.
-/
open MeasureTheory Set
namespace StochasticMatching
namespace ServiceCurveFamily
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem rejectionClock_job_winner (p : ServiceCurveFamily J) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 p.deadline, ∑ i, p.rate i t ≤ Λ)
    (z : Option J → ℝ) (j : J)
    (hw : z ∈ variableWinner (p.withRejectionClock Λ hΛ).service p.deadline (some j)) :
    (fun i => z (some i)) ∈ variableWinner p.service p.deadline j := by
  refine ⟨hw.1, ?_⟩
  intro i hij
  exact hw.2 (some i) (fun he => hij (Option.some.inj he))
end ServiceCurveFamily

namespace PosteriorStage
variable {H ι J : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J]

theorem cursorContinuation_accepted (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (L : H → CompletionLog J) (hL : Measurable L)
    (elapsed : H → ℝ) (he : Measurable elapsed) (k : ℕ) (x : H × ℝ)
    (r r' : J → ℝ) (hr : ∀ i, 0 < r (label i)) (j : ι)
    (hw : r ∈ variableWinner ((s.routingService label).curves x).service
      ((s.routingService label).curves x).deadline (label j))
    (hr' : ∀ i : {i : ι // i ≠ j}, r' (label i.1) = r (label i.1) -
      ((s.routingService label).curves x).service (label i.1)
        (cappedHit (((s.routingService label).curves x).service (label j))
          ((s.routingService label).curves x).deadline (r (label j)))) :
    let t := cappedHit (((s.routingService label).curves x).service (label j))
      ((s.routingService label).curves x).deadline (r (label j))
    s.cursorContinuation (n + 1) label L hL elapsed he k
      (acceptedRoutingCursor n label (label j) (s.advanceRoutingTime label (x, t)), r') =
      s.cursorContinuation (n + 1) label L hL elapsed he k (.inl x, r) := by
  intro t
  rw [acceptedRoutingCursor_at_label n label hinj j]
  change (s.next j).cursorContinuation n (fun i => label i.1)
      (s.appendLog label L elapsed k j) (s.measurable_appendLog label hL he k j)
      (fun h => elapsed h.1 + h.2) ((he.comp measurable_fst).add measurable_snd) (k + 1)
      (initialRoutingCursor n (s.advanceRoutingTime label (x, t)), r') =
    AdaptivePlan.run (tracePlan (n + 1) s label L hL elapsed he k) (x.1, s.stageDemand label x r)
  rw [cursorContinuation_initial, AdaptivePlan.run_of_winner _
    (s.routingService_winner_source label hinj x r hr j hw)]
  change AdaptivePlan.run _ (s.advanceRoutingTime label (x, t), fun i : {i : ι // i ≠ j} => r' (label i.1)) =
    AdaptivePlan.run _ (s.service.observation j (x.1, s.stageDemand label x r))
  rw [s.routingService_source_observation label hinj x r j (hr j)]
  congr 1
  apply Prod.ext
  · rfl
  · funext i
    exact hr' i

theorem routingService_winner_has_label (s : PosteriorStage H ι) (label : ι → J)
    (x : H × ℝ) (r : J → ℝ) (hr : ∀ a, 0 < r a) (a : J)
    (hw : r ∈ variableWinner ((s.routingService label).curves x).service
      ((s.routingService label).curves x).deadline a) : ∃ i, label i = a := by
  by_contra hn
  have he := ((s.routingService label).curves x).winner_service_eq (hr a) hw
  rw [s.routingService_frozen label a (not_exists.mp hn) x] at he
  exact (hr a).ne he

theorem recycled_active_residual (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (x : H × ℝ) (Λ : ℝ)
    (hΛ : ∀ t ∈ Icc 0 ((s.routingService label).curves x).deadline,
      ∑ a, ((s.routingService label).curves x).rate a t ≤ Λ)
    (z : Option J → ℝ) (j : ι) (i : {i : ι // i ≠ j}) :
    (recycledObservation (((s.routingService label).curves x).withRejectionClock Λ hΛ) (some (label j)) z).2
      (label i.1) = z (some (label i.1)) -
        ((s.routingService label).curves x).service (label i.1)
          (cappedHit (((s.routingService label).curves x).service (label j))
            ((s.routingService label).curves x).deadline (z (some (label j)))) := by
  have hij : label i.1 ≠ label j := fun he => i.2 (hinj he)
  simp only [recycledObservation, survivorSlot_other _ _ hij]
  rfl

end PosteriorStage
end StochasticMatching
