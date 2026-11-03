import Matching.ArrivalInstance
import Matching.IndependentPoissons
import Matching.PoissonProductThreshold
import Matching.RandomThresholdChains
import Matching.ExpectedOfflineDeficiency

/-! Reduction of exact expected offline equality to the Poisson/exponential
chain law. `PoissonExponentialChainLaw` is an explicit remaining hypothesis,
not an axiom or a theorem asserted here. All steps after that law are proved.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

def PoissonExponentialChainLaw (N : σ → Finset ι) (intensity : σ → ℝ≥0) : Prop :=
  ∀ a : ℝ≥0, ∀ C ∈ (finiteChains (Finset.univ : Finset (Finset ι))).erase ∅,
    (independentExponentials (ι := ι)).real
      (chainExceedance (supplyDeficiency N (fun s => (intensity s : ℝ))) a C) =
    ((independentPoissons intensity).prod (poissonMeasure a)).real
      {p : (σ → ℕ) × ℕ | ∀ A ∈ C,
        (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) A}

theorem maximum_deficiency_mixture_of_chain_law (N : σ → Finset ι) (intensity : σ → ℝ≥0)
    (hchain : PoissonExponentialChainLaw N intensity) (a : ℝ≥0) :
    (independentExponentials (ι := ι)).real
      {z | (a : ℝ) < maxSupplyDeficiency N (fun s => (intensity s : ℝ)) z} =
      ∫ counts, poissonLowerTail a (hallDeficiency (arrivalNeighbors N counts)) ∂independentPoissons intensity := by
  let d := supplyDeficiency N (fun s => (intensity s : ℝ))
  let e : ((σ → ℕ) × ℕ) → Finset ι → ℝ :=
    fun p => supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1)
  have hd : ∀ A, Measurable (fun z => d z A) := by
    intro A
    exact ((continuous_finset_sum A (fun i _ => continuous_apply i)).sub continuous_const).measurable
  have he : ∀ A, Measurable (fun p => e p A) := by
    intro A
    exact (measurable_of_countable (fun n : σ → ℕ =>
      supplyDeficiency N (fun s => (n s : ℝ)) (fun _ => 1) A)).comp measurable_fst
  have hm := maximum_random_threshold_eq_of_chain_laws independentExponentials
    ((independentPoissons intensity).prod (poissonMeasure a)) hd he
    (Filter.Eventually.of_forall (fun z A B => supplyDeficiency_supermodular N _
      (fun s => (intensity s).coe_nonneg) z A B))
    (Filter.Eventually.of_forall (fun p A B => supplyDeficiency_supermodular N _
      (fun s => Nat.cast_nonneg (p.1 s)) (fun _ => 1) A B))
    (a : ℝ) (fun p : (σ → ℕ) × ℕ => (p.2 : ℝ))
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp measurable_snd) (hchain a)
  have hl : maximumExceedance d a =
      {z | (a : ℝ) < maxSupplyDeficiency N (fun s => (intensity s : ℝ)) z} := by
    ext z
    exact (maxSupplyDeficiency_gt_iff N _ z a).symm
  have hr : {p : (σ → ℕ) × ℕ | ∃ A, (p.2 : ℝ) < e p A} =
      {p : (σ → ℕ) × ℕ | p.2 < hallDeficiency (arrivalNeighbors N p.1)} := by
    ext p
    change (∃ A, (p.2 : ℝ) < supplyDeficiency N (fun s => (p.1 s : ℝ)) (fun _ => 1) A) ↔ _
    rw [← maxSupplyDeficiency_gt_iff, arrival_max_deficiency_eq_hall, Nat.cast_lt]
    rfl
  rw [hl, hr] at hm
  exact hm.trans (poisson_product_threshold_probability (independentPoissons intensity)
    (fun counts => hallDeficiency (arrivalNeighbors N counts)) (measurable_of_countable _) a)

theorem expected_offline_equality_of_chain_law (N : σ → Finset ι) (intensity : σ → ℝ≥0)
    (hchain : PoissonExponentialChainLaw N intensity) :
    (∫ z, offlineValue (supplyRegion N (fun s => (intensity s : ℝ))) z ∂independentExponentials) =
      ∫ counts, arrivalOfflineValue N counts ∂independentPoissons intensity := by
  let D : (σ → ℕ) → ℕ := fun counts => hallDeficiency (arrivalNeighbors N counts)
  have hDm : Measurable D := measurable_of_countable _
  have hD : ∀ counts, D counts ≤ Fintype.card ι := fun counts => hallDeficiency_le_card _
  have hm := expected_offlineValue_eq_card_sub_count_of_mixture_tails N _
    (fun s => (intensity s).coe_nonneg) (independentPoissons intensity) D hDm
    (Fintype.card ι) hD (fun a ha => maximum_deficiency_mixture_of_chain_law N intensity hchain ⟨a, ha.le⟩)
  rw [hm]
  have hDi : Integrable (fun counts => (D counts : ℝ)) (independentPoissons intensity) :=
    integrable_bounded_nat_function _ D hDm (Fintype.card ι) hD Nat.cast
  change _ = ∫ counts, (Fintype.card ι : ℝ) - (D counts : ℝ) ∂independentPoissons intensity
  rw [integral_sub (integrable_const _) hDi, integral_const]
  simp

end StochasticMatching
