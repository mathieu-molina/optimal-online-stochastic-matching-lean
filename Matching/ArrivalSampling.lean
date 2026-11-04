import Matching.FiniteMatchingJobs

/-! Deterministic sampling inequalities for the offline matching benchmark.
They are proved by restricting an actual maximum matching. -/
open scoped BigOperators Classical
namespace StochasticMatching
variable {ι σ α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

noncomputable def routingReward (job : α → Option ι) : ℝ :=
  ∑ a, if (job a).isSome then 1 else 0

theorem routingReward_eq_card (job : α → Option ι) :
    routingReward job = ((routedArrivals job).card : ℝ) := by
  rw [routedArrivals, Finset.card_filter, Nat.cast_sum]
  simp only [routingReward, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem FiniteMatching.routingReward_jobs {t : ι → Finset α} (m : FiniteMatching t) :
    routingReward m.jobs = (m.size : ℝ) := by
  rw [routingReward_eq_card, m.routedArrivals_jobs_card]

theorem restricted_routingReward_le_offline (N : σ → Finset ι) (kind : α → σ)
    (job : α → Option ι) (hs : ∀ a j, job a = some j → j ∈ N (kind a))
    (hu : ∀ a b j, job a = some j → job b = some j → a = b)
    (f : β → α) (hf : Function.Injective f) :
    routingReward (job ∘ f) ≤ arrivalOfflineValue N (finiteTypeCounts (kind ∘ f)) := by
  have hs' : ∀ b j, (job ∘ f) b = some j → j ∈ N ((kind ∘ f) b) := fun b j h => hs (f b) j h
  have hu' : ∀ a b j, (job ∘ f) a = some j → (job ∘ f) b = some j → a = b :=
    fun a b j ha hb => hf (hu _ _ j ha hb)
  have h := indexedMatching_size_le_offline N (kind ∘ f) (indexedRoutingMatching N (kind ∘ f) (job ∘ f) hs')
  rw [indexedRoutingMatching_size_eq_accepted N (kind ∘ f) (job ∘ f) hs' hu', ← routingReward_eq_card] at h
  exact h

theorem arrivalOfflineValue_embedding_mono (N : σ → Finset ι) (kind : α → σ)
    (f : β → α) (hf : Function.Injective f) :
    arrivalOfflineValue N (finiteTypeCounts (kind ∘ f)) ≤ arrivalOfflineValue N (finiteTypeCounts kind) := by
  obtain ⟨m, hm⟩ := exists_indexed_maximum_matching N (kind ∘ f)
  let m' : FiniteMatching (indexedArrivalNeighbors N kind) := {
    unmatched := m.unmatched
    assign := fun j => f (m.assign j)
    injective := hf.comp m.injective
    supported := fun j => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (m.supported j)).2⟩ }
  rw [← hm]
  exact indexedMatching_size_le_offline N kind m'

theorem sum_delete_coordinate (n : ℕ) (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), ∑ j : Fin n, f (i.succAbove j)) = (n : ℝ) * ∑ i, f i := by
  have he (i : Fin (n + 1)) : (∑ j : Fin n, f (i.succAbove j)) = (∑ j, f j) - f i := by
    have h := Fin.sum_univ_succAbove f i
    linarith
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  ring

theorem offline_delete_sampling (N : σ → Finset ι) (n : ℕ) (kind : Fin (n + 1) → σ) :
    (n : ℝ) * arrivalOfflineValue N (finiteTypeCounts kind) ≤
      ∑ i : Fin (n + 1), arrivalOfflineValue N (finiteTypeCounts (kind ∘ i.succAbove)) := by
  obtain ⟨m, hm⟩ := exists_indexed_maximum_matching N kind
  have hs : ∀ a j, m.jobs a = some j → j ∈ N (kind a) := by
    intro a j hj
    exact (Finset.mem_filter.mp (m.jobs_supported a j hj)).2
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    restricted_routingReward_le_offline N kind m.jobs hs m.jobs_unique i.succAbove Fin.succAbove_right_injective)
  have he : (∑ i : Fin (n + 1), routingReward (m.jobs ∘ i.succAbove)) = (n : ℝ) * m.size := by
    simp only [routingReward, Function.comp_def]
    rw [sum_delete_coordinate n (fun j => if (m.jobs j).isSome then (1 : ℝ) else 0)]
    exact congrArg (fun r : ℝ => (n : ℝ) * r) m.routingReward_jobs
  rwa [he, hm] at h

end StochasticMatching
