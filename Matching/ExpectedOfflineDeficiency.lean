import Matching.OfflineDeficiency
import Matching.ExponentialMean
import Matching.InitialState
import Matching.PoissonMixture

/-! Integrability and expectation of the exponential offline deficiency. The
final theorem isolates the exact remaining probability-law obligation: the
Poisson-mixture tail identity for the maximum deficiency.
-/

open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

theorem maxSupplyDeficiency_ae_eq_unprocessed (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) :
    maxSupplyDeficiency N capacity =ᵐ[independentExponentials]
      fun z => (∑ i, z i) - offlineValue (supplyRegion N capacity) z := by
  filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
  have h := offlineValue_eq_total_sub_deficiency N capacity hcapacity z (fun i => (hz i).le)
  linarith

theorem integrable_maxSupplyDeficiency (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) :
    Integrable (maxSupplyDeficiency N capacity) independentExponentials := by
  have hi : Integrable (fun z : ι → ℝ => ∑ i, z i) independentExponentials :=
    integrable_finset_sum _ (fun i _ => integrable_exponential_coordinate i)
  have hv := integrable_offlineValue (supplyRegion_compact N capacity)
    (zero_mem_supplyRegion N capacity hcapacity) (fun _ hx => supplyRegion_nonneg N capacity hx)
    (supplyRegion_downward N capacity) (independentExponentials (ι := ι))
  exact (hi.sub hv).congr (maxSupplyDeficiency_ae_eq_unprocessed N capacity hcapacity).symm

theorem expected_offlineValue_eq_card_sub_deficiency (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) :
    (∫ z, offlineValue (supplyRegion N capacity) z ∂independentExponentials) =
      (Fintype.card ι : ℝ) - ∫ z, maxSupplyDeficiency N capacity z ∂independentExponentials := by
  have hi : Integrable (fun z : ι → ℝ => ∑ i, z i) independentExponentials :=
    integrable_finset_sum _ (fun i _ => integrable_exponential_coordinate i)
  have hv := integrable_offlineValue (supplyRegion_compact N capacity)
    (zero_mem_supplyRegion N capacity hcapacity) (fun _ hx => supplyRegion_nonneg N capacity hx)
    (supplyRegion_downward N capacity) (independentExponentials (ι := ι))
  have he := integral_congr_ae (maxSupplyDeficiency_ae_eq_unprocessed N capacity hcapacity)
  rw [integral_sub hi hv, integral_finset_sum _ (fun i _ => integrable_exponential_coordinate i)] at he
  simp only [integral_exponential_coordinate, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at he
  linarith

variable {Ω : Type*} [MeasurableSpace Ω]

theorem expected_offlineValue_eq_card_sub_count_of_mixture_tails
    (N : σ → Finset ι) (capacity : σ → ℝ) (hcapacity : ∀ s, 0 ≤ capacity s)
    (μ : Measure Ω) [IsFiniteMeasure μ] (D : Ω → ℕ) (hDm : Measurable D)
    (M : ℕ) (hD : ∀ ω, D ω ≤ M)
    (htail : ∀ a : ℝ, 0 < a →
      (independentExponentials (ι := ι)).real {z | a < maxSupplyDeficiency N capacity z} =
        ∫ ω, poissonLowerTail a (D ω) ∂μ) :
    (∫ z, offlineValue (supplyRegion N capacity) z ∂independentExponentials) =
      (Fintype.card ι : ℝ) - ∫ ω, (D ω : ℝ) ∂μ := by
  rw [expected_offlineValue_eq_card_sub_deficiency N capacity hcapacity,
    expected_value_eq_count_of_poisson_mixture_tails μ independentExponentials D hDm M hD
      (maxSupplyDeficiency N capacity) (integrable_maxSupplyDeficiency N capacity hcapacity)
      (Filter.Eventually.of_forall (maxSupplyDeficiency_nonneg N capacity)) htail]

end StochasticMatching
