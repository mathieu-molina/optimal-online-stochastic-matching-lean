import Matching.CoveragePoissonController
import Matching.HardControllerUpperBound
import Matching.HardRatioSeparation

/-! Optimal competitive ratio in the unweighted Poisson arrival model.

The benchmark is expected maximum matching under independent Poisson type
counts. Online algorithms are arbitrary history-state randomized controllers
whose conditional next-input law is the fresh Poisson law, and whose marks
are supported and irrevocable. Reward is the expected limiting accepted count.
The horizon is one, with arbitrary finite type intensities.

The competitive ratio is the supremum of uniform guarantees over all finite
instances. The lower and upper bounds use this same controller model. -/
open MeasureTheory Set
open scoped NNReal
namespace StochasticMatching

def PoissonCompetitiveGuarantee {ι σ : Type} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
    [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
    [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]
    (r : ℝ) (N : σ → Finset ι) (a : σ → ℝ≥0) : Prop :=
  ∃ (H : Type) (mH : MeasurableSpace H),
    letI := mH
    ∃ (P : PoissonOnlineController (H := H) N a) (h : H),
      P.horizon h = 1 ∧ P.available h = Finset.univ ∧ r * poissonOfflineOptimum N a ≤ P.expectedReward h

def PoissonAchievable (r : ℝ) : Prop :=
  ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
    [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
    [Fintype σ] [DecidableEq σ] [MeasurableSpace σ] [MeasurableSingletonClass σ]
    (N : σ → Finset ι) (a : σ → ℝ≥0), PoissonCompetitiveGuarantee r N a

noncomputable def optimalPoissonCompetitiveRatio : ℝ := sSup {r | PoissonAchievable r}

theorem poissonAchievable_of_le {r : ℝ} (hr : r ≤ Comparison.ratio) : PoissonAchievable r := by
  intro ι σ _ _ _ _ _ _ _ _ _ _ _ _ N a
  refine ⟨RoutingCursor (Fintype.card ι) Unit ι, inferInstance, coveragePoissonController N a,
    initialRoutingCursor (Fintype.card ι) (), coveragePoissonController_horizon N a,
    coveragePoissonController_available N a, ?_⟩
  have hopt : 0 ≤ poissonOfflineOptimum N a := integral_nonneg (arrivalOfflineValue_nonneg N)
  exact (mul_le_mul_of_nonneg_right hr hopt).trans (coveragePoissonController_lower_bound N a)

theorem poissonAchievable_le {r : ℝ} (hr : PoissonAchievable r) : r ≤ Comparison.ratio := by
  by_contra hn
  have hgt : Comparison.ratio < r := lt_of_not_ge hn
  obtain ⟨m, hm, hgap⟩ := exists_poisson_ratio_separating hgt
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : MeasurableSpace (Fin m) := ⊤
  letI : MeasurableSingletonClass (Fin m) := ⟨fun _ => trivial⟩
  letI : MeasurableSpace (Option (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Option (Fin m)) := ⟨fun _ => trivial⟩
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Finset (Fin m)) := ⟨fun _ => trivial⟩
  obtain ⟨H, mH, hex⟩ := hr (Fin m) (Finset (Fin m)) id hardPoissonIntensity
  letI := mH
  obtain ⟨P, h, hT, hA, hguarantee⟩ := hex
  have hoff : (m : ℝ) - 2 * Real.sqrt m ≤ poissonOfflineOptimum id (hardPoissonIntensity (ι := Fin m)) := by
    simpa only [Fintype.card_fin, poissonOfflineOptimum] using
      (hardPoisson_expected_offline_lower_bound (ι := Fin m))
  have hon : P.expectedReward h ≤ (m : ℝ) * Comparison.ratio := by
    simpa only [Fintype.card_fin] using P.hard_expected_reward_upper_bound h hT hA
  have hstrict := (hgap _ _ hoff hon).2
  exact not_lt_of_ge hguarantee hstrict

theorem poissonAchievable_iff_le (r : ℝ) : PoissonAchievable r ↔ r ≤ Comparison.ratio :=
  ⟨poissonAchievable_le, poissonAchievable_of_le⟩

theorem optimalPoissonCompetitiveRatio_eq_ratio : optimalPoissonCompetitiveRatio = Comparison.ratio := by
  have hc : PoissonAchievable Comparison.ratio := poissonAchievable_of_le le_rfl
  apply le_antisymm
  · exact csSup_le ⟨Comparison.ratio, hc⟩ (fun _ hr => poissonAchievable_le hr)
  · exact le_csSup ⟨Comparison.ratio, fun _ hr => poissonAchievable_le hr⟩ hc

/-- The requested exact competitive ratio in the Poisson model. -/
theorem optimalPoissonCompetitiveRatio_eq :
    optimalPoissonCompetitiveRatio = 1 - Real.exp 1 / (Real.exp 1) ^ (Real.exp 1) := by
  rw [optimalPoissonCompetitiveRatio_eq_ratio, Comparison.ratio_eq_e_rpow]

end StochasticMatching
