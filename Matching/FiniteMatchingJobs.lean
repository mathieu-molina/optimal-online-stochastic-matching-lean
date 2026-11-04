import Matching.FiniteArrivalMatching

/-! Read a finite matching as an irrevocable job decision at each arrival.
Injective restrictions retain exactly the accepted arrivals selected. -/
open scoped BigOperators Classical
namespace StochasticMatching
variable {ι α σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

noncomputable def FiniteMatching.jobs {t : ι → Finset α} (m : FiniteMatching t) (a : α) : Option ι :=
  if h : ∃ j : {i // i ∉ m.unmatched}, m.assign j = a then some h.choose.1 else none

theorem FiniteMatching.jobs_some_iff {t : ι → Finset α} (m : FiniteMatching t) (a : α) (j : ι) :
    m.jobs a = some j ↔ ∃ hj : j ∉ m.unmatched, m.assign ⟨j, hj⟩ = a := by
  unfold FiniteMatching.jobs
  split_ifs with h
  · constructor
    · intro he
      have he' := Option.some.inj he
      exact ⟨he' ▸ h.choose.2, by simpa only [← he'] using h.choose_spec⟩
    · rintro ⟨hj, he⟩
      have hsame := m.injective (h.choose_spec.trans he.symm)
      exact congrArg (fun x : {i // i ∉ m.unmatched} => some x.1) hsame
  · constructor
    · simp
    · rintro ⟨hj, he⟩
      exact False.elim (h ⟨⟨j, hj⟩, he⟩)

theorem FiniteMatching.jobs_unique {t : ι → Finset α} (m : FiniteMatching t)
    (a b : α) (j : ι) (ha : m.jobs a = some j) (hb : m.jobs b = some j) : a = b := by
  obtain ⟨hj, ha⟩ := (m.jobs_some_iff a j).mp ha
  obtain ⟨hj', hb⟩ := (m.jobs_some_iff b j).mp hb
  exact ha.symm.trans hb

theorem FiniteMatching.jobs_supported {t : ι → Finset α} (m : FiniteMatching t)
    (a : α) (j : ι) (ha : m.jobs a = some j) : a ∈ t j := by
  obtain ⟨hj, he⟩ := (m.jobs_some_iff a j).mp ha
  exact he ▸ m.supported ⟨j, hj⟩

theorem FiniteMatching.routedJobs_jobs {t : ι → Finset α} (m : FiniteMatching t) :
    routedJobs m.jobs = m.unmatchedᶜ := by
  ext j
  simp only [routedJobs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  constructor
  · rintro ⟨a, ha⟩
    exact ((m.jobs_some_iff a j).mp ha).choose
  · intro hj
    exact ⟨m.assign ⟨j, hj⟩, (m.jobs_some_iff _ j).mpr ⟨hj, rfl⟩⟩

theorem FiniteMatching.routedArrivals_jobs_card {t : ι → Finset α} (m : FiniteMatching t) :
    (routedArrivals m.jobs).card = m.size := by
  rw [← routedJobs_card_eq_arrivals m.jobs m.jobs_unique, m.routedJobs_jobs, Finset.card_compl]
  rfl

variable [Fintype σ] [DecidableEq σ]

theorem finiteTypeCounts_relabel {β : Type*} [Fintype β] (e : α ≃ β) (kind : β → σ) :
    finiteTypeCounts (kind ∘ e) = finiteTypeCounts kind := by
  funext s
  apply Fintype.card_congr
  exact e.subtypeEquiv (fun _ => Iff.rfl)

theorem indexedMatching_size_le_offline (N : σ → Finset ι) (kind : α → σ)
    (m : FiniteMatching (indexedArrivalNeighbors N kind)) :
    (m.size : ℝ) ≤ arrivalOfflineValue N (finiteTypeCounts kind) := by
  have hs : ∀ a j, m.jobs a = some j → j ∈ N (kind a) := by
    intro a j hj
    exact (Finset.mem_filter.mp (m.jobs_supported a j hj)).2
  let r := routingMatching N kind m.jobs hs
  have hr : r.size = m.size := by
    rw [routingMatching_size_eq_accepted N kind m.jobs hs m.jobs_unique, m.routedArrivals_jobs_card]
  obtain ⟨q, hq, hmax⟩ := arrivalOfflineValue_realized N (finiteTypeCounts kind)
  rw [← hq, ← hr]
  exact_mod_cast hmax r

theorem exists_indexed_maximum_matching (N : σ → Finset ι) (kind : α → σ) :
    ∃ m : FiniteMatching (indexedArrivalNeighbors N kind),
      (m.size : ℝ) = arrivalOfflineValue N (finiteTypeCounts kind) := by
  obtain ⟨q, hq, _⟩ := arrivalOfflineValue_realized N (finiteTypeCounts kind)
  let m : FiniteMatching (indexedArrivalNeighbors N kind) := {
    unmatched := q.unmatched
    assign := fun j => (arrivalCopyEquiv kind).symm (q.assign j)
    injective := (arrivalCopyEquiv kind).symm.injective.comp q.injective
    supported := by
      intro j
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hs := (Finset.mem_filter.mp (q.supported j)).2
      have ht := arrivalCopyEquiv_type kind ((arrivalCopyEquiv kind).symm (q.assign j))
      rw [(arrivalCopyEquiv kind).apply_symm_apply] at ht
      rwa [← ht] }
  exact ⟨m, hq⟩

end StochasticMatching
