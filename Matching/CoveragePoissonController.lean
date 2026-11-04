import Matching.CursorControllerPayoff
import Matching.PoissonCompetitiveLowerBound

/-! Achievability in the same general online-controller model used by the
impossibility proof. The witness is the existing posterior coverage policy. -/
open MeasureTheory Set
open scoped NNReal
namespace StochasticMatching
variable {ι σ : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
  [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def coveragePoissonController (N : σ → Finset ι) (a : σ → ℝ≥0) :
    PoissonOnlineController (H := RoutingCursor (Fintype.card ι) Unit ι) N a :=
  (coveragePosteriorData N a).initialStage.toPoissonController (Fintype.card ι) id
    Function.injective_id le_rfl N a
    ((coveragePosteriorData N a).initial_feasibleAllocation (coveragePosteriorData_feasible N a))

theorem coveragePoissonController_horizon (N : σ → Finset ι) (a : σ → ℝ≥0) :
    (coveragePoissonController N a).horizon (initialRoutingCursor (Fintype.card ι) ()) = 1 :=
  PosteriorStage.cursorService_initial_deadline _ _ _ _

theorem coveragePoissonController_available (N : σ → Finset ι) (a : σ → ℝ≥0) :
    (coveragePoissonController N a).available (initialRoutingCursor (Fintype.card ι) ()) = Finset.univ := by
  change cursorAvailable (Fintype.card ι) id (initialRoutingCursor (Fintype.card ι) ()) = _
  rw [cursorAvailable_initial_full _ _ le_rfl]
  simp

theorem coveragePoissonController_lower_bound (N : σ → Finset ι) (a : σ → ℝ≥0) :
    Comparison.ratio * poissonOfflineOptimum N a ≤
      (coveragePoissonController N a).expectedReward (initialRoutingCursor (Fintype.card ι) ()) := by
  apply (coverageRoutingOutput_vs_poisson_benchmark N a).trans
  exact (coveragePosteriorData N a).initialStage.toPoissonController_output_le N a
    ((coveragePosteriorData N a).initial_feasibleAllocation (coveragePosteriorData_feasible N a)) ()

theorem coveragePoissonController_exact_constant (N : σ → Finset ι) (a : σ → ℝ≥0) :
    (1 - Real.exp 1 / (Real.exp 1) ^ (Real.exp 1)) * poissonOfflineOptimum N a ≤
      (coveragePoissonController N a).expectedReward (initialRoutingCursor (Fintype.card ι) ()) := by
  rw [← Comparison.ratio_eq_e_rpow]
  exact coveragePoissonController_lower_bound N a

end StochasticMatching
