import Matching.ArrivalSampling
import Mathlib.MeasureTheory.Constructions.Pi

/-! The expected offline optimum for exactly k iid typed arrivals, with
monotonicity and the sampling inequality proved from concrete matchings. -/
open MeasureTheory Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def iidArrivalLaw (ν : Measure σ) (k : ℕ) : Measure (Fin k → σ) :=
  Measure.pi (fun _ => ν)

instance iidArrivalLaw_probability (ν : Measure σ) [IsProbabilityMeasure ν] (k : ℕ) :
    IsProbabilityMeasure (iidArrivalLaw ν k) := by unfold iidArrivalLaw; infer_instance

noncomputable def fixedCountOffline (N : σ → Finset ι) (ν : Measure σ) (k : ℕ) : ℝ :=
  ∫ x, arrivalOfflineValue N (finiteTypeCounts x) ∂iidArrivalLaw ν k

theorem integrable_finiteArrivalOffline (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν]
    {α : Type*} [Fintype α] [MeasurableSpace α] (k : ℕ) (f : (Fin k → σ) → α → σ) :
    Integrable (fun x => arrivalOfflineValue N (finiteTypeCounts (f x))) (iidArrivalLaw ν k) := by
  apply (integrable_const (Fintype.card ι : ℝ)).mono'
    (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (arrivalOfflineValue_nonneg N _)]
    exact arrivalOfflineValue_le_card N _)

theorem iidArrivalLaw_delete (ν : Measure σ) [IsProbabilityMeasure ν] (k : ℕ) (i : Fin (k + 1)) :
    Measure.map (fun x : Fin (k + 1) → σ => x ∘ i.succAbove) (iidArrivalLaw ν (k + 1)) =
      iidArrivalLaw ν k := by
  have h := congrArg (Measure.map Prod.snd)
    (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) i).map_eq
  rw [Measure.map_map measurable_snd (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => σ) i).measurable,
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

theorem fixedCountOffline_delete (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν]
    (k : ℕ) (i : Fin (k + 1)) :
    (∫ x : Fin (k + 1) → σ, arrivalOfflineValue N (finiteTypeCounts (x ∘ i.succAbove))
      ∂iidArrivalLaw ν (k + 1)) = fixedCountOffline N ν k := by
  unfold fixedCountOffline
  rw [← iidArrivalLaw_delete ν k i,
    integral_map_of_stronglyMeasurable (measurable_of_countable _) (measurable_of_countable _).stronglyMeasurable]

theorem fixedCountOffline_nonneg (N : σ → Finset ι) (ν : Measure σ) (k : ℕ) :
    0 ≤ fixedCountOffline N ν k := integral_nonneg (fun _ => arrivalOfflineValue_nonneg N _)

theorem fixedCountOffline_le_card (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν] (k : ℕ) :
    fixedCountOffline N ν k ≤ Fintype.card ι := by
  have h := integral_mono (integrable_finiteArrivalOffline N ν k id) (integrable_const (Fintype.card ι : ℝ))
    (fun x => arrivalOfflineValue_le_card N (finiteTypeCounts x))
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

theorem fixedCountOffline_monotone (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν] :
    Monotone (fixedCountOffline N ν) := by
  apply monotone_nat_of_le_succ
  intro k
  let i : Fin (k + 1) := Fin.last k
  rw [← fixedCountOffline_delete N ν k i]
  exact integral_mono (integrable_finiteArrivalOffline N ν (k + 1) (fun x => x ∘ i.succAbove))
    (integrable_finiteArrivalOffline N ν (k + 1) id)
    (fun x => arrivalOfflineValue_embedding_mono N x i.succAbove Fin.succAbove_right_injective)

theorem fixedCountOffline_sampling_step (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν] (k : ℕ) :
    (k : ℝ) * fixedCountOffline N ν (k + 1) ≤ (k + 1 : ℝ) * fixedCountOffline N ν k := by
  have hi (i : Fin (k + 1)) := integrable_finiteArrivalOffline N ν (k + 1) (fun x => x ∘ i.succAbove)
  have h := integral_mono ((integrable_finiteArrivalOffline N ν (k + 1) id).const_mul (k : ℝ))
    (integrable_finset_sum _ (fun i _ => hi i)) (offline_delete_sampling N k)
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => hi i)] at h
  simp only [fixedCountOffline_delete, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  exact h

theorem fixedCountOffline_sampling (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν]
    (n k : ℕ) (hn : 0 < n) (hnk : n ≤ k) :
    (n : ℝ) * fixedCountOffline N ν k ≤ (k : ℝ) * fixedCountOffline N ν n := by
  induction k, hnk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hnk ih =>
    have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (hn.trans_le hnk)
    have h1 := mul_le_mul_of_nonneg_left (fixedCountOffline_sampling_step N ν k) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h2 := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ k + 1 by positivity)
    have h3 : (k : ℝ) * ((n : ℝ) * fixedCountOffline N ν (k + 1)) ≤
        (k : ℝ) * ((k + 1 : ℝ) * fixedCountOffline N ν n) := by nlinarith
    exact (mul_le_mul_left hk).mp (by simpa only [Nat.cast_add, Nat.cast_one] using h3)

end StochasticMatching
