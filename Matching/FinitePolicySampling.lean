import Matching.FiniteOnlinePolicy

/-! Dummy insertion gives an actual causal policy on one fewer iid arrival.
Averaging the dummy's position and type retains exactly k/(k+1) of reward. -/
open MeasureTheory Set
open scoped BigOperators Classical
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [MeasurableSpace σ] [MeasurableSingletonClass σ]

namespace FiniteOnlinePolicy
variable {N : σ → Finset ι} {k : ℕ}

theorem integral_deleteDummy (P : FiniteOnlinePolicy N (k + 1))
    (ν : Measure σ) [IsProbabilityMeasure ν] (i : Fin (k + 1)) :
    (∫ a, (P.deleteDummy i a).expectedReward ν ∂ν) =
      ∫ x, routingReward (P.decide x ∘ i.succAbove) ∂iidArrivalLaw ν (k + 1) := by
  let f : σ × (Fin k → σ) → ℝ := fun y =>
    routingReward (P.decide (i.insertNth y.1 y.2) ∘ i.succAbove)
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) i).integral_comp' f
  have he (x : Fin (k + 1) → σ) :
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => σ) i) x) =
        routingReward (P.decide x ∘ i.succAbove) := by
    simp [f, MeasurableEquiv.piFinSuccAbove, Fin.insertNth_removeNth]
  simp only [he] at h
  unfold iidArrivalLaw
  rw [h, integral_prod f Integrable.of_finite]
  rfl

theorem sum_integral_deleteDummy (P : FiniteOnlinePolicy N (k + 1))
    (ν : Measure σ) [IsProbabilityMeasure ν] :
    (∑ i : Fin (k + 1), ∫ a, (P.deleteDummy i a).expectedReward ν ∂ν) =
      (k : ℝ) * P.expectedReward ν := by
  simp_rw [P.integral_deleteDummy ν]
  rw [← integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  change (∫ x, ∑ i : Fin (k + 1), ∑ j : Fin k,
    (if (P.decide x (i.succAbove j)).isSome then (1 : ℝ) else 0) ∂iidArrivalLaw ν (k + 1)) = _
  have he (x : Fin (k + 1) → σ) :
      (∑ i : Fin (k + 1), ∑ j : Fin k,
        if (P.decide x (i.succAbove j)).isSome then (1 : ℝ) else 0) =
      (k : ℝ) * routingReward (P.decide x) :=
    sum_delete_coordinate k (fun i => if (P.decide x i).isSome then (1 : ℝ) else 0)
  simp only [he]
  rw [integral_const_mul]
  rfl

def appendReject (P : FiniteOnlinePolicy N k) : FiniteOnlinePolicy N (k + 1) where
  decide x := Fin.snoc (P.decide (x ∘ Fin.castSucc)) none
  causal := by
    intro x y i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · intro hxy
      simp only [Fin.snoc_castSucc]
      apply P.causal
      intro r hr
      exact hxy r.castSucc (Fin.castSucc_le_castSucc_iff.mpr hr)
  supported := by
    intro x i b
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using P.supported (x ∘ Fin.castSucc) j b
  unique := by
    intro x i r b
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun q => ?_) r
      · simp
      · simp only [Fin.snoc_castSucc]
        intro hj hq
        exact congrArg Fin.castSucc (P.unique _ j q b hj hq)

theorem appendReject_reward (P : FiniteOnlinePolicy N k) (x : Fin (k + 1) → σ) :
    routingReward (P.appendReject.decide x) = routingReward (P.decide (x ∘ Fin.castSucc)) := by
  unfold routingReward
  rw [Fin.sum_univ_castSucc]
  simp only [appendReject, Fin.snoc_castSucc, Fin.snoc_last, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte, add_zero]

theorem appendReject_expectedReward (P : FiniteOnlinePolicy N k)
    (ν : Measure σ) [IsProbabilityMeasure ν] : P.appendReject.expectedReward ν = P.expectedReward ν := by
  unfold expectedReward
  simp_rw [appendReject_reward]
  have h := iidArrivalLaw_delete ν k (Fin.last k)
  simp only [Fin.succAbove_last] at h
  rw [← h, integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable]

end FiniteOnlinePolicy

theorem exists_best_finite_policy (N : σ → Finset ι) (ν : Measure σ) (k : ℕ) :
    ∃ P : FiniteOnlinePolicy N k, ∀ Q : FiniteOnlinePolicy N k,
      Q.expectedReward ν ≤ P.expectedReward ν := by
  classical
  obtain ⟨P, _, hP⟩ := Finset.exists_max_image Finset.univ
    (fun P : FiniteOnlinePolicy N k => P.expectedReward ν) Finset.univ_nonempty
  exact ⟨P, fun Q => hP Q (Finset.mem_univ Q)⟩

noncomputable def bestFinitePolicy (N : σ → Finset ι) (ν : Measure σ) (k : ℕ) :
    FiniteOnlinePolicy N k := (exists_best_finite_policy N ν k).choose

noncomputable def fixedOnlineValue (N : σ → Finset ι) (ν : Measure σ) (k : ℕ) : ℝ :=
  (bestFinitePolicy N ν k).expectedReward ν

theorem finite_policy_le_value {N : σ → Finset ι} (ν : Measure σ) {k : ℕ}
    (P : FiniteOnlinePolicy N k) : P.expectedReward ν ≤ fixedOnlineValue N ν k :=
  (exists_best_finite_policy N ν k).choose_spec P

theorem fixedOnlineValue_nonneg (N : σ → Finset ι) (ν : Measure σ) (k : ℕ) :
    0 ≤ fixedOnlineValue N ν k := (bestFinitePolicy N ν k).expectedReward_nonneg ν

theorem fixedOnlineValue_le_offline (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (k : ℕ) : fixedOnlineValue N ν k ≤ fixedCountOffline N ν k :=
  (bestFinitePolicy N ν k).expectedReward_le_offline ν

theorem fixedOnlineValue_monotone (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] : Monotone (fixedOnlineValue N ν) := by
  apply monotone_nat_of_le_succ
  intro k
  have h := finite_policy_le_value ν (bestFinitePolicy N ν k).appendReject
  rwa [FiniteOnlinePolicy.appendReject_expectedReward] at h

theorem fixedOnlineValue_sampling_step (N : σ → Finset ι) (ν : Measure σ)
    [IsProbabilityMeasure ν] (k : ℕ) :
    (k : ℝ) * fixedOnlineValue N ν (k + 1) ≤ (k + 1 : ℝ) * fixedOnlineValue N ν k := by
  rw [fixedOnlineValue, ← FiniteOnlinePolicy.sum_integral_deleteDummy]
  have h (i : Fin (k + 1)) :
      (∫ a, ((bestFinitePolicy N ν (k + 1)).deleteDummy i a).expectedReward ν ∂ν) ≤
        fixedOnlineValue N ν k := by
    have h' := integral_mono (μ := ν) Integrable.of_finite
      (integrable_const (fixedOnlineValue N ν k))
      (fun a => finite_policy_le_value ν ((bestFinitePolicy N ν (k + 1)).deleteDummy i a))
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h'
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

theorem fixedOnlineValue_sampling (N : σ → Finset ι) (ν : Measure σ) [IsProbabilityMeasure ν]
    (n k : ℕ) (hn : 0 < n) (hnk : n ≤ k) :
    (n : ℝ) * fixedOnlineValue N ν k ≤ (k : ℝ) * fixedOnlineValue N ν n := by
  induction k, hnk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hnk ih =>
    have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (hn.trans_le hnk)
    have h1 := mul_le_mul_of_nonneg_left (fixedOnlineValue_sampling_step N ν k) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h2 := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ k + 1 by positivity)
    have h3 : (k : ℝ) * ((n : ℝ) * fixedOnlineValue N ν (k + 1)) ≤
        (k : ℝ) * ((k + 1 : ℝ) * fixedOnlineValue N ν n) := by nlinarith
    exact (mul_le_mul_left hk).mp (by simpa only [Nat.cast_add, Nat.cast_one] using h3)

end StochasticMatching
