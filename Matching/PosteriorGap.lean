import Matching.ExponentialMean
import Matching.PosteriorTrajectory
import Matching.InitialState

/-! The deficit between the conditional demand mean and posterior rate is
exactly the mean unallocated demand. The allocation cap is required only on
nonnegative demand vectors, matching the original allocation domain.
-/

open MeasureTheory Set
open scoped NNReal

namespace StochasticMatching.PosteriorData

variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] (p : PosteriorData H ι)

theorem integrable_shifted_allocation (h : H) (x : ι → ℝ) (i : ι) :
    Integrable (fun z => p.allocation (h, x + z) i) independentExponentials := by
  have hm : Measurable (fun z => p.allocation (h, x + z) i) :=
    (measurable_pi_apply i).comp (p.measurable_allocation.comp
      (measurable_const.prodMk (measurable_const.add measurable_id)))
  apply (integrable_const (p.bound : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (p.allocation_nonneg h (x + z) i)]
  exact p.allocation_le h (x + z) i

theorem posterior_gap_eq (h : H) (x : ι → ℝ) (i : ι) :
    x i + 1 - posteriorRate p.allocation h x i =
      ∫ z, (x + z) i - p.allocation (h, x + z) i ∂independentExponentials := by
  have hz : Integrable (fun z : ι → ℝ => (x + z) i) independentExponentials :=
    (integrable_const (x i)).add (integrable_exponential_coordinate i)
  rw [integral_sub hz (p.integrable_shifted_allocation h x i), integral_shifted_exponential_coordinate]
  rfl

theorem posterior_gap_nonneg
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (h : H) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (i : ι) :
    0 ≤ x i + 1 - posteriorRate p.allocation h x i := by
  rw [p.posterior_gap_eq]
  apply integral_nonneg_of_ae
  filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
  exact sub_nonneg.mpr (hcap h (x + z) (fun j => add_nonneg (hx j) (hz j).le) i)

theorem posterior_rate_le_demand_mean
    (hcap : ∀ h z, (∀ i, 0 ≤ z i) → ∀ i, p.allocation (h, z) i ≤ z i)
    (h : H) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (i : ι) :
    posteriorRate p.allocation h x i ≤ x i + 1 :=
  sub_nonneg.mp (p.posterior_gap_nonneg hcap h x hx i)

end StochasticMatching.PosteriorData
