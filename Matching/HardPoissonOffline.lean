import Matching.IntegratedTailBound
import Matching.ExpectedOfflineEquality
import Matching.ExpectedOfflineDeficiency

/-! A finite-size lower bound on the actual expected offline matching value
of the hard Poisson instance: `m - 2 * sqrt m`. No random-graph theorem or
asymptotic offline-optimum hypothesis is assumed. -/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

theorem hardPoisson_expected_deficiency_le :
    (∫ z, maxSupplyDeficiency id (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) z
      ∂independentExponentials) ≤ 2 * Real.sqrt (Fintype.card ι) := by
  apply le_trans _ expected_integrated_tail_error_le
  apply integral_mono_ae
    (integrable_maxSupplyDeficiency id _ (fun S => (hardPoissonIntensity S).coe_nonneg))
    empiricalTailError_integrable_integral
  filter_upwards [independentExponentials_ae_pos (ι := ι)] with z hz
  exact hardPoisson_max_deficiency_le_tail_error z (fun i => (hz i).le)

theorem hardPoisson_expected_offline_lower_bound :
    (Fintype.card ι : ℝ) - 2 * Real.sqrt (Fintype.card ι) ≤
      ∫ counts, arrivalOfflineValue (id : Finset ι → Finset ι) counts
        ∂independentPoissons hardPoissonIntensity := by
  rw [← expected_offline_equality id hardPoissonIntensity,
    expected_offlineValue_eq_card_sub_deficiency id _ (fun S => (hardPoissonIntensity S).coe_nonneg)]
  exact sub_le_sub_left hardPoisson_expected_deficiency_le _

end StochasticMatching
