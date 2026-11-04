import Matching.FixedCountOffline

/-! Finite online matching policies with explicit prefix causality.
Inserting a sampled dummy arrival and deleting its decision preserves online
implementability, support, and irrevocable use of offline vertices. -/
open MeasureTheory Set
open scoped BigOperators Classical
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

structure FiniteOnlinePolicy (N : σ → Finset ι) (k : ℕ) where
  decide : (Fin k → σ) → Fin k → Option ι
  causal : ∀ x y i, (∀ j, j ≤ i → x j = y j) → decide x i = decide y i
  supported : ∀ x i j, decide x i = some j → j ∈ N (x i)
  unique : ∀ x i r j, decide x i = some j → decide x r = some j → i = r

namespace FiniteOnlinePolicy
variable {N : σ → Finset ι} {k : ℕ}

@[ext] theorem ext (P Q : FiniteOnlinePolicy N k) (h : P.decide = Q.decide) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

noncomputable instance : Fintype (FiniteOnlinePolicy N k) :=
  Fintype.ofInjective (fun P : FiniteOnlinePolicy N k => P.decide) (fun _ _ h => ext _ _ h)

instance : MeasurableSpace (FiniteOnlinePolicy N k) := ⊤
instance : MeasurableSingletonClass (FiniteOnlinePolicy N k) := ⟨fun _ => trivial⟩

def reject : FiniteOnlinePolicy N k where
  decide := fun _ _ => none
  causal := fun _ _ _ _ => rfl
  supported := by simp
  unique := by simp

instance : Nonempty (FiniteOnlinePolicy N k) := ⟨reject⟩

noncomputable def matching (P : FiniteOnlinePolicy N k) (x : Fin k → σ) :
    FiniteMatching (arrivalNeighbors N (finiteTypeCounts x)) := routingMatching N x (P.decide x) (P.supported x)

theorem matching_size (P : FiniteOnlinePolicy N k) (x : Fin k → σ) :
    ((P.matching x).size : ℝ) = routingReward (P.decide x) := by
  rw [matching, routingMatching_size_eq_accepted N x (P.decide x) (P.supported x) (P.unique x),
    routingReward_eq_card]

theorem reward_nonneg (P : FiniteOnlinePolicy N k) (x : Fin k → σ) : 0 ≤ routingReward (P.decide x) := by
  rw [← P.matching_size]
  exact Nat.cast_nonneg _

theorem reward_le_offline (P : FiniteOnlinePolicy N k) (x : Fin k → σ) :
    routingReward (P.decide x) ≤ arrivalOfflineValue N (finiteTypeCounts x) := by
  rw [← P.matching_size]
  obtain ⟨q, hq, hm⟩ := arrivalOfflineValue_realized N (finiteTypeCounts x)
  rw [← hq]
  exact_mod_cast hm (P.matching x)

def deleteDummy (P : FiniteOnlinePolicy N (k + 1)) (i : Fin (k + 1)) (a : σ) : FiniteOnlinePolicy N k where
  decide x j := P.decide (i.insertNth a x) (i.succAbove j)
  causal := by
    intro x y j hxy
    apply P.causal
    intro q hq
    by_cases hqi : q = i
    · subst q
      simp
    · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hqi
      have hr : r ≤ j := (Fin.strictMono_succAbove i).le_iff_le.mp hq
      simpa only [Fin.insertNth_apply_succAbove] using hxy r hr
  supported := by
    intro x j b hb
    simpa only [Fin.insertNth_apply_succAbove] using P.supported _ _ b hb
  unique := by
    intro x j r b hj hr
    exact Fin.succAbove_right_injective (P.unique _ _ _ b hj hr)

variable [MeasurableSpace σ] [MeasurableSingletonClass σ]

noncomputable def expectedReward (P : FiniteOnlinePolicy N k) (ν : Measure σ) : ℝ :=
  ∫ x, routingReward (P.decide x) ∂iidArrivalLaw ν k

theorem integrable_reward (P : FiniteOnlinePolicy N k) (ν : Measure σ) [IsProbabilityMeasure ν] :
    Integrable (fun x => routingReward (P.decide x)) (iidArrivalLaw ν k) := by
  apply (integrable_const (Fintype.card ι : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (P.reward_nonneg x)]
    exact (P.reward_le_offline x).trans (arrivalOfflineValue_le_card N _))

theorem expectedReward_nonneg (P : FiniteOnlinePolicy N k) (ν : Measure σ) : 0 ≤ P.expectedReward ν :=
  integral_nonneg P.reward_nonneg

theorem expectedReward_le_offline (P : FiniteOnlinePolicy N k) (ν : Measure σ) [IsProbabilityMeasure ν] :
    P.expectedReward ν ≤ fixedCountOffline N ν k :=
  integral_mono (P.integrable_reward ν) (integrable_finiteArrivalOffline N ν k id) P.reward_le_offline

end FiniteOnlinePolicy
end StochasticMatching
