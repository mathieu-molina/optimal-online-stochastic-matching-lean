import Matching.SupplyFlowGeometry

/-! Row variations of a supporting supply flow. Positive residual demand
forces every adjacent type to use its full supply and prevents it from sending
flow outside the set of positive residuals.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

def FlowSupports (N : σ → Finset ι) (capacity : σ → ℝ) (x : ι → ℝ) (f : σ → ι → ℝ) : Prop :=
  ∀ g, FeasibleSupplyFlow N capacity g →
    (∑ i, (x i - aggregateSupplyFlow f i) *
      (aggregateSupplyFlow g i - aggregateSupplyFlow f i)) ≤ 0

theorem weighted_sum_update (v r : ι → ℝ) (i : ι) (a : ℝ) :
    (∑ j, r j * Function.update v i a j) = (∑ j, r j * v j) + r i * (a - v i) := by
  have he : (fun j => r j * Function.update v i a j) =
      fun j => r j * v j + if j = i then r i * (a - v i) else 0 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, if_pos rfl, ite_true]
      ring
    · simp only [Function.update_of_ne hj, if_neg hj, add_zero]
  rw [he, Finset.sum_add_distrib]
  simp

theorem sum_update_value (v : ι → ℝ) (i : ι) (a : ℝ) :
    (∑ j, Function.update v i a j) = (∑ j, v j) + (a - v i) := by
  simpa only [one_mul] using weighted_sum_update v (fun _ => 1) i a

theorem supplyFlow_update_row {N : σ → Finset ι} {capacity : σ → ℝ} {f : σ → ι → ℝ}
    (hf : FeasibleSupplyFlow N capacity f) (s : σ) (v : ι → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hvs : ∀ i, i ∉ N s → v i = 0) (hvc : ∑ i, v i ≤ capacity s) :
    FeasibleSupplyFlow N capacity (Function.update f s v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t i
    by_cases ht : t = s
    · subst t
      simpa only [Function.update_self] using hv0 i
    · simpa only [Function.update_of_ne ht] using hf.1 t i
  · intro t i hi
    by_cases ht : t = s
    · subst t
      simpa only [Function.update_self] using hvs i hi
    · simpa only [Function.update_of_ne ht] using hf.2.1 t i hi
  · intro t
    by_cases ht : t = s
    · subst t
      simpa only [Function.update_self] using hvc
    · simpa only [Function.update_of_ne ht] using hf.2.2 t

theorem aggregate_update_row (f : σ → ι → ℝ) (s : σ) (v : ι → ℝ) (i : ι) :
    aggregateSupplyFlow (Function.update f s v) i = aggregateSupplyFlow f i + (v i - f s i) := by
  have he : (fun t => Function.update f s v t i) = Function.update (fun t => f t i) s (v i) := by
    funext t
    by_cases ht : t = s
    · subst t
      simp only [Function.update_self]
    · simp only [Function.update_of_ne ht]
  unfold aggregateSupplyFlow
  rw [he, sum_update_value]

theorem supporting_row_optimal {N : σ → Finset ι} {capacity : σ → ℝ}
    {x : ι → ℝ} {f : σ → ι → ℝ} (hf : FeasibleSupplyFlow N capacity f)
    (hs : FlowSupports N capacity x f) (s : σ) (v : ι → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hvs : ∀ i, i ∉ N s → v i = 0) (hvc : ∑ i, v i ≤ capacity s) :
    (∑ i, (x i - aggregateSupplyFlow f i) * v i) ≤
      ∑ i, (x i - aggregateSupplyFlow f i) * f s i := by
  have h := hs (Function.update f s v) (supplyFlow_update_row hf s v hv0 hvs hvc)
  simp_rw [aggregate_update_row, add_sub_cancel_left, mul_sub] at h
  rw [Finset.sum_sub_distrib] at h
  linarith

theorem supporting_row_full {N : σ → Finset ι} {capacity : σ → ℝ}
    {x : ι → ℝ} {f : σ → ι → ℝ} (hf : FeasibleSupplyFlow N capacity f)
    (hs : FlowSupports N capacity x f) (s : σ) (i : ι) (hi : i ∈ N s)
    (hpos : 0 < x i - aggregateSupplyFlow f i) : (∑ j, f s j) = capacity s := by
  let δ := capacity s - ∑ j, f s j
  have hδ : 0 ≤ δ := sub_nonneg.mpr (hf.2.2 s)
  let v := Function.update (f s) i (f s i + δ)
  have hv0 : ∀ j, 0 ≤ v j := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [v, Function.update_self] using add_nonneg (hf.1 s i) hδ
    · simpa only [v, Function.update_of_ne hj] using hf.1 s j
  have hvs : ∀ j, j ∉ N s → v j = 0 := by
    intro j hj
    have hji : j ≠ i := fun he => hj (he.symm ▸ hi)
    simpa only [v, Function.update_of_ne hji] using hf.2.1 s j hj
  have hvc : (∑ j, v j) ≤ capacity s := by
    rw [sum_update_value]
    dsimp only [δ]
    linarith
  have hm := supporting_row_optimal hf hs s v hv0 hvs hvc
  rw [weighted_sum_update] at hm
  have hd : δ = 0 := by nlinarith
  dsimp only [δ] at hd
  linarith

theorem supporting_row_zero_nonpositive {N : σ → Finset ι} {capacity : σ → ℝ}
    {x : ι → ℝ} {f : σ → ι → ℝ} (hf : FeasibleSupplyFlow N capacity f)
    (hs : FlowSupports N capacity x f) (s : σ) (i j : ι) (hi : i ∈ N s)
    (hpos : 0 < x i - aggregateSupplyFlow f i)
    (hneg : x j - aggregateSupplyFlow f j ≤ 0) : f s j = 0 := by
  have hij : i ≠ j := by intro he; subst j; linarith
  let v := Function.update (Function.update (f s) j 0) i (f s i + f s j)
  have hv0 : ∀ k, 0 ≤ v k := by
    intro k
    by_cases hki : k = i
    · subst k
      simpa only [v, Function.update_self] using add_nonneg (hf.1 s i) (hf.1 s j)
    · by_cases hkj : k = j
      · subst k
        simp only [v, Function.update_of_ne hki, Function.update_self, le_refl]
      · simpa only [v, Function.update_of_ne hki, Function.update_of_ne hkj] using hf.1 s k
  have hvs : ∀ k, k ∉ N s → v k = 0 := by
    intro k hk
    have hki : k ≠ i := fun he => hk (he.symm ▸ hi)
    by_cases hkj : k = j
    · subst k
      simp only [v, Function.update_of_ne hki, Function.update_self]
    · simpa only [v, Function.update_of_ne hki, Function.update_of_ne hkj] using hf.2.1 s k hk
  have hvc : (∑ k, v k) ≤ capacity s := by
    rw [sum_update_value, sum_update_value, Function.update_of_ne hij]
    have hc := hf.2.2 s
    linarith
  have hm := supporting_row_optimal hf hs s v hv0 hvs hvc
  rw [weighted_sum_update, weighted_sum_update, Function.update_of_ne hij] at hm
  have hfj := hf.1 s j
  nlinarith

end StochasticMatching
