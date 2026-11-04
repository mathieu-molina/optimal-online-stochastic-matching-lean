import Matching.CursorController
import Matching.TerminalPayloadProjection

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace StochasticMatching.PosteriorStage
variable {H ι J σ : Type} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
  [MeasurableSpace (Finset J)] [MeasurableSingletonClass (Finset J)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

theorem toPoissonController_step_live (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (hn : Fintype.card ι ≤ n)
    (N : σ → Finset J) (a : σ → ℝ≥0)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N (fun s => (a s : ℝ))))
    (x : RoutingCursor n H ι) :
    (s.toPoissonController n label hinj hn N a hmem).step (.inr x) =
      Measure.map (fun u => fillTerminal (cursorAvailable n label x, u))
        (routingTransition N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
          (s.cursorService n label) (s.cursorService_supply_feasible n label N _ (fun s => (a s).coe_nonneg) hmem)
          (s.typedCursorUpdate n label) x) := by
  letI := historyRoutingKernel_markov N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    (s.cursorService n label) (s.cursorService_supply_feasible n label N _ (fun s => (a s).coe_nonneg) hmem)
  change Measure.map Prod.snd (s.cursorControllerJoint n label N a hmem x) = _
  have hg : Measurable (fun e : ControllerEvent σ J => (e, s.cursorControllerUpdate n label (x, e))) :=
    measurable_id.prodMk ((s.measurable_cursorControllerUpdate n label).comp measurable_prodMk_left)
  rw [s.cursorControllerJoint_apply, Measure.map_map measurable_snd hg]
  rw [routingTransition, eventUpdateKernel_apply _ _ (s.measurable_typedCursorUpdate n label)]
  have hf : Measurable (fun u : Unit ⊕ RoutingCursor n H ι => fillTerminal (cursorAvailable n label x, u)) :=
    measurable_fillTerminal.comp (measurable_const.prodMk measurable_id)
  have hu : Measurable (fun e : ControllerEvent σ J => s.typedCursorUpdate n label (x, e)) :=
    (s.measurable_typedCursorUpdate n label).comp measurable_prodMk_left
  rw [Measure.map_map hf hu]
  rfl

theorem toPoissonController_trajectory_projection (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (hn : Fintype.card ι ≤ n)
    (N : σ → Finset J) (a : σ → ℝ≥0)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N (fun s => (a s : ℝ))))
    (x : RoutingCursor n H ι) :
    Measure.map (fun z : ℕ → ControllerState (RoutingCursor n H ι) J => fun k => forgetTerminal (z k))
      (markovTrajectory (s.toPoissonController n label hinj hn N a hmem).step (.inr x)) =
        s.routingTrajectory n label N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg) hmem x := by
  let L := routingTransition N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    (s.cursorService n label) (s.cursorService_supply_feasible n label N _ (fun s => (a s).coe_nonneg) hmem)
    (s.typedCursorUpdate n label)
  letI : IsMarkovKernel L := routingTransition_markov N (fun s => (a s : ℝ)) (fun s => (a s).coe_nonneg)
    (s.cursorService n label) (s.cursorService_supply_feasible n label N _ (fun s => (a s).coe_nonneg) hmem)
    (s.typedCursorUpdate n label) (s.measurable_typedCursorUpdate n label)
  exact terminalPayload_trajectory_projection _ L (cursorAvailable n label) (fun _ => rfl)
    (s.toPoissonController_step_live n label hinj hn N a hmem) (.inr x)

theorem toPoissonController_finite_termination (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (hn : Fintype.card ι ≤ n)
    (N : σ → Finset J) (a : σ → ℝ≥0)
    (hmem : s.data.FeasibleAllocation label (supplyRegion N (fun s => (a s : ℝ))))
    (x : RoutingCursor n H ι) :
    ∀ᵐ z ∂markovTrajectory (s.toPoissonController n label hinj hn N a hmem).step (.inr x),
      ∃ k, z k ∈ Set.range Sum.inl := by
  have ht := s.routingTrajectory_finite_termination n label N (fun s => (a s : ℝ))
    (fun s => (a s).coe_nonneg) hmem x
  rw [← s.toPoissonController_trajectory_projection n label hinj hn N a hmem x] at ht
  have hm : Measurable (fun z : ℕ → ControllerState (RoutingCursor n H ι) J => fun k => forgetTerminal (z k)) :=
    measurable_pi_lambda _ (fun k => measurable_forgetTerminal.comp (measurable_pi_apply k))
  have hset : MeasurableSet {z : ℕ → Unit ⊕ RoutingCursor n H ι | ∃ k, z k = .inl ()} := by
    have he : {z : ℕ → Unit ⊕ RoutingCursor n H ι | ∃ k, z k = .inl ()} =
        ⋃ k, (fun z => z k) ⁻¹' Set.range (Sum.inl : Unit → Unit ⊕ RoutingCursor n H ι) := by
      ext z
      simp only [mem_setOf_eq, mem_iUnion, mem_preimage, mem_range]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, (), hk.symm⟩
      · rintro ⟨k, u, hu⟩
        cases u
        exact ⟨k, hu.symm⟩
    rw [he]
    exact MeasurableSet.iUnion (fun k => measurableSet_range_inl.preimage (measurable_pi_apply k))
  have hh := (ae_map_iff hm.aemeasurable hset).mp ht
  filter_upwards [hh] with z hz
  obtain ⟨k, hk⟩ := hz
  refine ⟨k, ?_⟩
  cases he : z k with
  | inl A => exact ⟨A, rfl⟩
  | inr h => simp [he, forgetTerminal] at hk

end StochasticMatching.PosteriorStage
