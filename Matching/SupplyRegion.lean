import Matching.PosteriorFeasibility
import Mathlib.Topology.Order.Compact

/-! The coverage region arising from finite matching arrival types. This
verifies the geometric hypotheses of the scheduling theorem directly from
nonnegative supplies and arbitrary overlapping neighborhoods.
-/

open Set
open scoped BigOperators
namespace StochasticMatching
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]

noncomputable def supplyCoverage (N : σ → Finset ι) (capacity : σ → ℝ) (A : Finset ι) : ℝ :=
  ∑ s, if (N s ∩ A).Nonempty then capacity s else 0

def supplyRegion (N : σ → Finset ι) (capacity : σ → ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ A : Finset ι, ∑ i ∈ A, x i ≤ supplyCoverage N capacity A}

theorem supplyCoverage_empty (N : σ → Finset ι) (capacity : σ → ℝ) : supplyCoverage N capacity ∅ = 0 := by
  simp [supplyCoverage]

theorem supplyCoverage_nonneg (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (A : Finset ι) : 0 ≤ supplyCoverage N capacity A := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · exact hcapacity s
  · exact le_refl 0

theorem supplyCoverage_mono (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) {A B : Finset ι} (hAB : A ⊆ B) :
    supplyCoverage N capacity A ≤ supplyCoverage N capacity B := by
  apply Finset.sum_le_sum
  intro s _
  by_cases hA : (N s ∩ A).Nonempty
  · have hB : (N s ∩ B).Nonempty := by
      obtain ⟨i, hi⟩ := hA
      exact ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1, hAB (Finset.mem_inter.mp hi).2⟩⟩
    simp only [if_pos hA, if_pos hB, le_refl]
  · rw [if_neg hA]
    split_ifs
    · exact hcapacity s
    · exact le_refl 0

theorem supplyCoverage_submodular (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (A B : Finset ι) :
    supplyCoverage N capacity (A ∪ B) + supplyCoverage N capacity (A ∩ B) ≤
      supplyCoverage N capacity A + supplyCoverage N capacity B := by
  unfold supplyCoverage
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have hu : (N s ∩ (A ∪ B)).Nonempty ↔ (N s ∩ A).Nonempty ∨ (N s ∩ B).Nonempty := by
    constructor
    · rintro ⟨i, hi⟩
      rcases Finset.mem_inter.mp hi with ⟨hiN, hiAB⟩
      rcases Finset.mem_union.mp hiAB with hiA | hiB
      · exact Or.inl ⟨i, Finset.mem_inter.mpr ⟨hiN, hiA⟩⟩
      · exact Or.inr ⟨i, Finset.mem_inter.mpr ⟨hiN, hiB⟩⟩
    · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
      · exact ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,
          Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hi).2)⟩⟩
      · exact ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,
          Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mp hi).2)⟩⟩
  have hiA : (N s ∩ (A ∩ B)).Nonempty → (N s ∩ A).Nonempty := by
    rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).1⟩⟩
  have hiB : (N s ∩ (A ∩ B)).Nonempty → (N s ∩ B).Nonempty := by
    rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hi).1,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).2⟩⟩
  by_cases hA : (N s ∩ A).Nonempty <;>
    by_cases hB : (N s ∩ B).Nonempty <;>
    by_cases hI : (N s ∩ (A ∩ B)).Nonempty <;> simp_all [hu] <;> linarith [hcapacity s]

theorem zero_mem_supplyRegion (N : σ → Finset ι) (capacity : σ → ℝ) (hcapacity : ∀ s, 0 ≤ capacity s) :
    (0 : ι → ℝ) ∈ supplyRegion N capacity := by
  refine ⟨fun _ => le_refl 0, fun A => ?_⟩
  simpa only [Pi.zero_apply, Finset.sum_const_zero] using supplyCoverage_nonneg N capacity hcapacity A

theorem supplyRegion_nonneg (N : σ → Finset ι) (capacity : σ → ℝ)
    {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) (i : ι) : 0 ≤ x i := hx.1 i

theorem supplyRegion_coordinate_bound (N : σ → Finset ι) (capacity : σ → ℝ)
    {x : ι → ℝ} (hx : x ∈ supplyRegion N capacity) (i : ι) : x i ≤ supplyCoverage N capacity {i} := by
  simpa only [Finset.sum_singleton] using hx.2 {i}

theorem supplyRegion_downward (N : σ → Finset ι) (capacity : σ → ℝ) :
    NonnegDownwardClosed (supplyRegion N capacity) := by
  intro x y hx hy hyx
  refine ⟨hy, fun A => ?_⟩
  exact (Finset.sum_le_sum (fun i _ => hyx i)).trans (hx.2 A)

theorem supplyRegion_convex (N : σ → Finset ι) (capacity : σ → ℝ) :
    Convex ℝ (supplyRegion N capacity) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
  intro A
  change (∑ i ∈ A, (a * x i + b * y i)) ≤ supplyCoverage N capacity A
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := mul_le_mul_of_nonneg_left (hx.2 A) ha
  have h2 := mul_le_mul_of_nonneg_left (hy.2 A) hb
  calc
    _ ≤ a * supplyCoverage N capacity A + b * supplyCoverage N capacity A := add_le_add h1 h2
    _ = supplyCoverage N capacity A := by rw [← add_mul, hab, one_mul]

theorem supplyRegion_closed (N : σ → Finset ι) (capacity : σ → ℝ) :
    IsClosed (supplyRegion N capacity) := by
  have h1 : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have h2 : IsClosed {x : ι → ℝ | ∀ A : Finset ι, ∑ i ∈ A, x i ≤ supplyCoverage N capacity A} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro A
    exact isClosed_le (continuous_finset_sum _ (fun i _ => continuous_apply i)) continuous_const
  exact h1.inter h2

theorem supplyRegion_compact (N : σ → Finset ι) (capacity : σ → ℝ) :
    IsCompact (supplyRegion N capacity) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : ι → ℝ) (fun i => supplyCoverage N capacity {i}))).of_isClosed_subset
    (supplyRegion_closed N capacity)
  intro x hx
  exact ⟨hx.1, fun i => supplyRegion_coordinate_bound N capacity hx i⟩

noncomputable def supplyDeficiency (N : σ → Finset ι) (capacity : σ → ℝ) (z : ι → ℝ) (A : Finset ι) : ℝ :=
  (∑ i ∈ A, z i) - supplyCoverage N capacity A

theorem supplyDeficiency_empty (N : σ → Finset ι) (capacity : σ → ℝ) (z : ι → ℝ) :
    supplyDeficiency N capacity z ∅ = 0 := by simp [supplyDeficiency, supplyCoverage_empty]

theorem supplyDeficiency_supermodular (N : σ → Finset ι) (capacity : σ → ℝ)
    (hcapacity : ∀ s, 0 ≤ capacity s) (z : ι → ℝ) (A B : Finset ι) :
    supplyDeficiency N capacity z A + supplyDeficiency N capacity z B ≤
      supplyDeficiency N capacity z (A ∪ B) + supplyDeficiency N capacity z (A ∩ B) := by
  have hc := supplyCoverage_submodular N capacity hcapacity A B
  have hm : (∑ i ∈ A ∪ B, z i) + (∑ i ∈ A ∩ B, z i) =
      (∑ i ∈ A, z i) + (∑ i ∈ B, z i) := Finset.sum_union_inter
  unfold supplyDeficiency
  linarith

end StochasticMatching
