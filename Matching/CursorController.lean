import Matching.ControllerValidity
import Matching.CursorCardinality
import Matching.PosteriorRoutingProcess
import Matching.TerminalPayload

/-! Embed the existing posterior routing kernel into the general class of
Poisson online controllers, retaining the unmatched set at termination. -/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [MeasurableSpace (Finset J)] [MeasurableSingletonClass (Finset J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def cursorControllerUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (x : RoutingCursor n H ι × ControllerEvent σ J) : ControllerState (RoutingCursor n H ι) J :=
  fillTerminal (cursorAvailable n label x.1, s.typedCursorUpdate n label x)

theorem measurable_cursorControllerUpdate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.cursorControllerUpdate (σ := σ) n label) :=
  measurable_fillTerminal.comp
    (((measurable_cursorAvailable n label).comp measurable_fst).prodMk (s.measurable_typedCursorUpdate n label))

theorem cursorControllerUpdate_valid (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (hn : Fintype.card ι ≤ n) (N : σ → Finset J)
    (x : RoutingCursor n H ι) (e : ControllerEvent σ J)
    (he : e ∈ admissibleArrival N (cursorAvailable n label x)ᶜ ((s.cursorService n label).curves x).deadline) :
    ControllerStepValid N (fun y => ((s.cursorService n label).curves y).deadline)
      (cursorAvailable n label) x (e, s.cursorControllerUpdate n label (x, e)) := by
  cases e with
  | inl _ => rfl
  | inr p =>
      rcases p with ⟨t, a, j⟩
      have he' : t ∈ Ioo 0 ((s.cursorService n label).curves x).deadline ∧
          ∀ b, j = some b → b ∈ N a ∧ b ∈ cursorAvailable n label x := by
        simpa [admissibleArrival] using he
      have hU : s.typedCursorUpdate n label (x, .inr (t, (a, j))) =
          s.cursorUpdate n label (x, .inr (t, j)) :=
        guardedEventUpdate_of_valid (fun y => ((s.cursorService n label).curves y).deadline)
          (s.cursorUpdate n label) x t j he'.1.1.le he'.1.2
      have hnext : ∃ y, s.cursorUpdate n label (x, .inr (t, j)) = .inr y ∧
          cursorAvailable n label y = unmatchedAfterMark (cursorAvailable n label x) j := by
        cases j with
        | none =>
            obtain ⟨y, hy, _, hA⟩ := s.cursorUpdate_rejected n label x t
            exact ⟨y, hy, hA⟩
        | some b => exact s.cursorUpdate_accepted_exact n label hinj hn x t b (he'.2 b rfl).2
      obtain ⟨y, hy, hA⟩ := hnext
      obtain ⟨v, hv, hD⟩ := s.cursorUpdate_deadline n label x t j he'.1.1.le he'.1.2
      rw [hy] at hv
      have hv' : y = v := Sum.inr.inj hv
      subst v
      change (∀ b, j = some b → b ∈ N a ∩ cursorAvailable n label x) ∧ _
      refine ⟨fun b hb => Finset.mem_inter.mpr (he'.2 b hb), ?_⟩
      unfold cursorControllerUpdate
      rw [hU, hy]
      exact ⟨hA, hD⟩

noncomputable def cursorControllerJoint (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (intensity : σ → ℝ≥0)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N (fun a => (intensity a : ℝ)))) :
    Kernel (RoutingCursor n H ι)
      (ControllerEvent σ J × ControllerState (RoutingCursor n H ι) J) := by
  letI := historyRoutingKernel_markov N (fun a => (intensity a : ℝ)) (fun a => (intensity a).coe_nonneg)
    (s.cursorService n label) (s.cursorService_supply_feasible n label N _ (fun a => (intensity a).coe_nonneg) hmem)
  exact eventUpdateKernel (historyRoutingKernel N (fun a => (intensity a : ℝ)) (s.cursorService n label))
    (fun x => (x.2, s.cursorControllerUpdate n label x))

theorem cursorControllerJoint_apply (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (N : σ → Finset J) (intensity : σ → ℝ≥0)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N (fun a => (intensity a : ℝ))))
    (x : RoutingCursor n H ι) :
    s.cursorControllerJoint n label N intensity hmem x =
      Measure.map (fun e => (e, s.cursorControllerUpdate n label (x, e)))
        (routingNextArrival N (fun a => (intensity a : ℝ)) ((s.cursorService n label).curves x)) := by
  letI := historyRoutingKernel_markov N (fun a => (intensity a : ℝ)) (fun a => (intensity a).coe_nonneg)
    (s.cursorService n label) (s.cursorService_supply_feasible n label N _ (fun a => (intensity a).coe_nonneg) hmem)
  exact eventUpdateKernel_apply _ _
    (measurable_snd.prodMk (s.measurable_cursorControllerUpdate n label)) x

noncomputable def toPoissonController (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (hn : Fintype.card ι ≤ n)
    (N : σ → Finset J) (intensity : σ → ℝ≥0)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N (fun a => (intensity a : ℝ)))) :
    PoissonOnlineController (H := RoutingCursor n H ι) N intensity where
  horizon := fun x => ((s.cursorService n label).curves x).deadline
  horizon_pos := fun x => ((s.cursorService n label).curves x).deadline_pos
  horizon_measurable := (s.cursorService n label).deadline_measurable
  available := cursorAvailable n label
  available_measurable := measurable_cursorAvailable n label
  next := s.cursorControllerJoint n label N intensity hmem
  probability := by
    intro x
    letI := routingNextArrival_probability N _ (fun a => (intensity a).coe_nonneg)
      ((s.cursorService n label).curves x) (s.cursorService_supply_feasible n label N _ (fun a => (intensity a).coe_nonneg) hmem x)
    rw [s.cursorControllerJoint_apply]
    exact isProbabilityMeasure_map
      (measurable_id.prodMk ((s.measurable_cursorControllerUpdate n label).comp measurable_prodMk_left)).aemeasurable
  input_law := by
    intro x
    have hm := measurable_id.prodMk ((s.measurable_cursorControllerUpdate (σ := σ) n label).comp
      (measurable_prodMk_left (x := x)))
    rw [s.cursorControllerJoint_apply]
    have hf : Measurable (fun y : ControllerEvent σ J × ControllerState (RoutingCursor n H ι) J =>
        arrivalTypeProjection y.1) := measurable_arrivalTypeProjection.comp measurable_fst
    have hg : Measurable (fun e : ControllerEvent σ J => (e, s.cursorControllerUpdate n label (x, e))) := hm
    rw [Measure.map_map hf hg]
    exact routingNextArrival_type_law N _ (fun a => (intensity a).coe_nonneg)
      ((s.cursorService n label).curves x) (s.cursorService_supply_feasible n label N _ (fun a => (intensity a).coe_nonneg) hmem x)
  valid := by
    intro x
    rw [s.cursorControllerJoint_apply]
    apply (ae_map_iff
      (measurable_id.prodMk ((s.measurable_cursorControllerUpdate n label).comp measurable_prodMk_left)).aemeasurable
      (measurableSet_ControllerStepValid N _ (s.cursorService n label).deadline_measurable
        _ (measurable_cursorAvailable n label) x)).mpr
    have hs := routingNextArrival_admissible N _ (fun a => (intensity a).coe_nonneg)
      ((s.cursorService n label).curves x) (s.cursorService_supply_feasible n label N _ (fun a => (intensity a).coe_nonneg) hmem x)
      (cursorAvailable n label x)ᶜ (fun a ha t _ => s.cursorService_frozen_outside n label x a
        (Finset.mem_compl.mp ha) t)
    exact hs.mono (fun e he => s.cursorControllerUpdate_valid n label hinj hn N x e he)

end StochasticMatching.PosteriorStage
