import Matching.SupplyFlow
import Matching.OfflineTightSets
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Compact convex geometry of supply flows. A Euclidean projection supplies
an optimal linear supporting inequality for the residual demand. This is the
analytic ingredient in the converse of the coverage/flow characterization.
-/

open Set
open scoped BigOperators RealInnerProductSpace
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

def supplyFlowSet (N : σ → Finset ι) (capacity : σ → ℝ) : Set (σ → ι → ℝ) :=
  {f | FeasibleSupplyFlow N capacity f}

theorem zero_mem_supplyFlowSet (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) : (0 : σ → ι → ℝ) ∈ supplyFlowSet N capacity := by
  exact ⟨fun _ _ => le_refl _, fun _ _ _ => rfl, by simpa using hcapacity⟩

theorem supplyFlowSet_closed (N : σ → Finset ι) (capacity : σ → ℝ) :
    IsClosed (supplyFlowSet N capacity) := by
  have h0 : IsClosed {f : σ → ι → ℝ | ∀ s i, 0 ≤ f s i} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun s => isClosed_iInter (fun i =>
      isClosed_le continuous_const ((continuous_apply i).comp (continuous_apply s))))
  have hs : IsClosed {f : σ → ι → ℝ | ∀ s i, i ∉ N s → f s i = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun s => isClosed_iInter (fun i => isClosed_iInter (fun _ =>
      isClosed_eq ((continuous_apply i).comp (continuous_apply s)) continuous_const)))
  have hc : IsClosed {f : σ → ι → ℝ | ∀ s, ∑ i, f s i ≤ capacity s} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun s => isClosed_le (continuous_finset_sum _
      (fun i _ => (continuous_apply i).comp (continuous_apply s))) continuous_const)
  exact h0.inter (hs.inter hc)

theorem supplyFlowSet_compact (N : σ → Finset ι) (capacity : σ → ℝ) :
    IsCompact (supplyFlowSet N capacity) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : σ → ι → ℝ) (fun s _ => capacity s))).of_isClosed_subset
    (supplyFlowSet_closed N capacity)
  intro f hf
  exact ⟨hf.1, fun s i => feasibleSupplyFlow_coordinate_le hf s i⟩

theorem supplyFlowSet_convex (N : σ → Finset ι) (capacity : σ → ℝ) :
    Convex ℝ (supplyFlowSet N capacity) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun s i => add_nonneg (mul_nonneg ha (hf.1 s i)) (mul_nonneg hb (hg.1 s i)), ?_, ?_⟩
  · intro s i hi
    change a * f s i + b * g s i = 0
    rw [hf.2.1 s i hi, hg.2.1 s i hi]
    ring
  · intro s
    change (∑ i, (a * f s i + b * g s i)) ≤ capacity s
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ ≤ a * capacity s + b * capacity s := add_le_add
        (mul_le_mul_of_nonneg_left (hf.2.2 s) ha) (mul_le_mul_of_nonneg_left (hg.2.2 s) hb)
      _ = capacity s := by rw [← add_mul, hab, one_mul]

noncomputable def aggregateEuclidean : (σ → ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun f := (WithLp.equiv 2 (ι → ℝ)).symm (aggregateSupplyFlow f)
  map_add' f g := by
    ext i
    simp [aggregateSupplyFlow, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    simp [aggregateSupplyFlow, Finset.mul_sum]

theorem continuous_aggregateEuclidean : Continuous (aggregateEuclidean (ι := ι) (σ := σ)) := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : ι => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_finset_sum _ (fun s _ => (continuous_apply i).comp (continuous_apply s))

theorem exists_supporting_supply_flow (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (x : ι → ℝ) :
    ∃ f : σ → ι → ℝ, FeasibleSupplyFlow N capacity f ∧
      ∀ g, FeasibleSupplyFlow N capacity g →
        (∑ i, (x i - aggregateSupplyFlow f i) *
          (aggregateSupplyFlow g i - aggregateSupplyFlow f i)) ≤ 0 := by
  let T := aggregateEuclidean (ι := ι) (σ := σ)
  let K := T '' supplyFlowSet N capacity
  have hk : IsCompact K := (supplyFlowSet_compact N capacity).image continuous_aggregateEuclidean
  have hkc : Convex ℝ K := (supplyFlowSet_convex N capacity).linear_image T
  have hkn : K.Nonempty := ⟨T 0, ⟨0, zero_mem_supplyFlowSet N capacity hcapacity, rfl⟩⟩
  obtain ⟨v, hv, hm⟩ := exists_norm_eq_iInf_of_complete_convex hkn hk.isComplete hkc
    ((WithLp.equiv 2 (ι → ℝ)).symm x)
  have hs := (norm_eq_iInf_iff_real_inner_le_zero hkc hv).mp hm
  obtain ⟨f, hf, rfl⟩ := hv
  refine ⟨f, hf, ?_⟩
  intro g hg
  have h := hs (T g) ⟨g, hg, rfl⟩
  simpa only [PiLp.inner_apply, real_inner_comm,
    PiLp.sub_apply, aggregateEuclidean, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.equiv_symm_pi_apply, RCLike.inner_apply, conj_trivial, mul_comm] using h

end StochasticMatching
