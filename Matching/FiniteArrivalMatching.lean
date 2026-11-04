import Matching.ArrivalInstance

/-! Convert chronological routing decisions into a matching. Every arrival
has its own right vertex; rejected arrivals remain part of the input. -/
open scoped BigOperators
namespace StochasticMatching
variable {ι σ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype α] [DecidableEq α]

def routedJobs (job : α → Option ι) : Finset ι :=
  Finset.univ.filter (fun j => ∃ r, job r = some j)

def routedArrivals (job : α → Option ι) : Finset α :=
  Finset.univ.filter (fun r => (job r).isSome)

def indexedArrivalNeighbors (N : σ → Finset ι) (kind : α → σ) (j : ι) : Finset α :=
  Finset.univ.filter (fun r => j ∈ N (kind r))

noncomputable def routedJobIndex (job : α → Option ι) (j : ↥(routedJobs job)) : α :=
  Classical.choose ((Finset.mem_filter.mp j.2).2)

theorem routedJobIndex_spec (job : α → Option ι) (j : ↥(routedJobs job)) :
    job (routedJobIndex job j) = some j.1 :=
  Classical.choose_spec ((Finset.mem_filter.mp j.2).2)

theorem routedJobIndex_injective (job : α → Option ι) : Function.Injective (routedJobIndex job) := by
  intro i j h
  apply Subtype.ext
  apply Option.some.inj
  rw [← routedJobIndex_spec job i, ← routedJobIndex_spec job j, h]

noncomputable def indexedRoutingMatching (N : σ → Finset ι) (kind : α → σ) (job : α → Option ι)
    (hsupport : ∀ r j, job r = some j → j ∈ N (kind r)) :
    FiniteMatching (indexedArrivalNeighbors N kind) where
  unmatched := (routedJobs job)ᶜ
  assign j := routedJobIndex job ⟨j.1, by simpa using j.2⟩
  injective := by
    intro i j h
    have he := routedJobIndex_injective job h
    exact Subtype.ext (congrArg (fun x : ↥(routedJobs job) => x.1) he)
  supported j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupport _ _ (routedJobIndex_spec job _)⟩

theorem indexedRoutingMatching_size (N : σ → Finset ι) (kind : α → σ) (job : α → Option ι)
    (hsupport : ∀ r j, job r = some j → j ∈ N (kind r)) :
    (indexedRoutingMatching N kind job hsupport).size = (routedJobs job).card := by
  change Fintype.card ι - ((routedJobs job)ᶜ).card = _
  rw [Finset.card_compl]
  exact Nat.sub_sub_self (Finset.card_le_univ _)

theorem routedJobs_card_eq_arrivals (job : α → Option ι)
    (hunique : ∀ r q j, job r = some j → job q = some j → r = q) :
    (routedJobs job).card = (routedArrivals job).card := by
  let f : ↥(routedJobs job) → ↥(routedArrivals job) := fun j =>
    ⟨routedJobIndex job j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [routedJobIndex_spec job j]; rfl⟩⟩
  have hinj : Function.Injective f := fun i j h => routedJobIndex_injective job (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro r
    have hr := (Finset.mem_filter.mp r.2).2
    cases he : job r.1 with
    | none => simp [he] at hr
    | some j =>
      let q : ↥(routedJobs job) := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨r.1, he⟩⟩⟩
      refine ⟨q, Subtype.ext ?_⟩
      exact hunique _ _ j (routedJobIndex_spec job q) he
  simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem indexedRoutingMatching_size_eq_accepted (N : σ → Finset ι) (kind : α → σ) (job : α → Option ι)
    (hsupport : ∀ r j, job r = some j → j ∈ N (kind r))
    (hunique : ∀ r q j, job r = some j → job q = some j → r = q) :
    (indexedRoutingMatching N kind job hsupport).size = (routedArrivals job).card := by
  rw [indexedRoutingMatching_size, routedJobs_card_eq_arrivals job hunique]

def finiteTypeCounts (kind : α → σ) (s : σ) : ℕ := Fintype.card {r : α // kind r = s}

noncomputable def arrivalCopyEquiv (kind : α → σ) : α ≃ ArrivalCopies (finiteTypeCounts kind) :=
  (Equiv.sigmaFiberEquiv kind).symm.trans (Equiv.sigmaCongrRight (fun s => Fintype.equivFin {r : α // kind r = s}))

theorem arrivalCopyEquiv_type (kind : α → σ) (r : α) : (arrivalCopyEquiv kind r).1 = kind r := rfl

noncomputable def routingMatching (N : σ → Finset ι) (kind : α → σ) (job : α → Option ι)
    (hsupport : ∀ r j, job r = some j → j ∈ N (kind r)) :
    FiniteMatching (arrivalNeighbors N (finiteTypeCounts kind)) where
  unmatched := (indexedRoutingMatching N kind job hsupport).unmatched
  assign j := arrivalCopyEquiv kind ((indexedRoutingMatching N kind job hsupport).assign j)
  injective := (arrivalCopyEquiv kind).injective.comp (indexedRoutingMatching N kind job hsupport).injective
  supported j := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [arrivalCopyEquiv_type]
    exact (Finset.mem_filter.mp ((indexedRoutingMatching N kind job hsupport).supported j)).2

theorem routingMatching_size_eq_accepted (N : σ → Finset ι) (kind : α → σ) (job : α → Option ι)
    (hsupport : ∀ r j, job r = some j → j ∈ N (kind r))
    (hunique : ∀ r q j, job r = some j → job q = some j → r = q) :
    (routingMatching N kind job hsupport).size = (routedArrivals job).card :=
  indexedRoutingMatching_size_eq_accepted N kind job hsupport hunique

end StochasticMatching
