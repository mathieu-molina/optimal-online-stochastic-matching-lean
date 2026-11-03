import Matching.InfiniteRenewalCount
import Matching.ExpectedOfflineEquality

/-! Independent renewal streams, one per arrival type, realize the exact
independent Poisson instance used by the offline benchmark.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {σ : Type*} [Fintype σ]

noncomputable def independentRenewalStreams : Measure (σ → ℕ → ℝ) :=
  Measure.pi (fun _ : σ => infiniteExponentials)

instance independentRenewalStreams_probability : IsProbabilityMeasure (independentRenewalStreams (σ := σ)) := by
  unfold independentRenewalStreams
  infer_instance

noncomputable def renewalTypeCounts (a : σ → ℝ≥0) (z : σ → ℕ → ℝ) (s : σ) : ℕ :=
  infiniteRenewalCount (a s) (z s)

theorem measurable_renewalTypeCounts (a : σ → ℝ≥0) : Measurable (renewalTypeCounts a) :=
  measurable_pi_lambda _ (fun s => (measurable_infiniteRenewalCount (a s)).comp (measurable_pi_apply s))

theorem renewalTypeCounts_poisson_law (a : σ → ℝ≥0) :
    Measure.map (renewalTypeCounts a) independentRenewalStreams = independentPoissons a := by
  apply (Measure.pi_eq (μ := fun s => poissonMeasure (a s)) _).symm
  intro E hE
  rw [Measure.map_apply (measurable_renewalTypeCounts a) (MeasurableSet.univ_pi hE)]
  have he : (renewalTypeCounts a) ⁻¹' Set.pi Set.univ E =
      Set.pi Set.univ (fun s => (infiniteRenewalCount (a s)) ⁻¹' E s) := by
    ext z
    simp [renewalTypeCounts, Set.mem_pi]
  rw [he]
  change Measure.pi (fun _ : σ => infiniteExponentials) _ = _
  rw [Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro s _
  dsimp only
  rw [← infiniteRenewalCount_poisson_law (a s),
    Measure.map_apply (measurable_infiniteRenewalCount (a s)) (hE s)]


theorem renewal_input_expected_offline_equality {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq σ] (N : σ → Finset ι) (intensity : σ → ℝ≥0) :
    (∫ z, offlineValue (supplyRegion N (fun s => (intensity s : ℝ))) z ∂independentExponentials) =
      ∫ streams, arrivalOfflineValue N (renewalTypeCounts intensity streams) ∂independentRenewalStreams := by
  rw [expected_offline_equality, ← renewalTypeCounts_poisson_law intensity]
  exact integral_map (measurable_renewalTypeCounts intensity).aemeasurable
    (measurable_of_countable (arrivalOfflineValue N)).aestronglyMeasurable

end StochasticMatching
