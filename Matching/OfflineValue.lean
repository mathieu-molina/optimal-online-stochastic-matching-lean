import Matching.SupplyRegion
import Mathlib.Topology.MetricSpace.Lipschitz

/-! The deterministic offline work optimum. Compactness gives an optimizer
for every demand vector; downward closure gives a Lipschitz value function.
Pointwise existence here does not assert a measurable optimizer selection.
-/

open MeasureTheory Set
open scoped BigOperators NNReal
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def offlineFeasible (P : Set (ι → ℝ)) (z : ι → ℝ) : Set (ι → ℝ) :=
  P ∩ Iic (fun i => max (z i) 0)

noncomputable def offlineValue (P : Set (ι → ℝ)) (z : ι → ℝ) : ℝ :=
  sSup ((fun x : ι → ℝ => ∑ i, x i) '' offlineFeasible P z)

theorem offlineFeasible_nonnegative_demand (P : Set (ι → ℝ)) (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) : offlineFeasible P z = P ∩ Iic z := by
  have he : (fun i => max (z i) 0) = z := funext (fun i => max_eq_left (hz i))
  rw [offlineFeasible, he]

theorem zero_mem_offlineFeasible {P : Set (ι → ℝ)} (hP0 : (0 : ι → ℝ) ∈ P) (z : ι → ℝ) :
    (0 : ι → ℝ) ∈ offlineFeasible P z := ⟨hP0, fun i => le_max_right (z i) 0⟩

theorem offlineFeasible_compact {P : Set (ι → ℝ)} (hP : IsCompact P) (z : ι → ℝ) :
    IsCompact (offlineFeasible P z) :=
  hP.of_isClosed_subset (hP.isClosed.inter isClosed_Iic) inter_subset_left

theorem exists_offline_optimizer {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (z : ι → ℝ) :
    ∃ x ∈ offlineFeasible P z, offlineValue P z = ∑ i, x i ∧
      ∀ y ∈ offlineFeasible P z, (∑ i, y i) ≤ ∑ i, x i := by
  have hc : Continuous (fun x : ι → ℝ => ∑ i, x i) :=
    continuous_finset_sum _ (fun i _ => continuous_apply i)
  obtain ⟨x, hx, hm⟩ := (offlineFeasible_compact hP z).exists_isMaxOn
    ⟨0, zero_mem_offlineFeasible hP0 z⟩ hc.continuousOn
  have hg : IsGreatest ((fun y : ι → ℝ => ∑ i, y i) '' offlineFeasible P z) (∑ i, x i) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact hm hy
  exact ⟨x, hx, hg.csSup_eq, fun y hy => hm hy⟩

theorem offline_allocation_le_value {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (z : ι → ℝ) {x : ι → ℝ}
    (hx : x ∈ offlineFeasible P z) : (∑ i, x i) ≤ offlineValue P z := by
  obtain ⟨y, _, hv, hm⟩ := exists_offline_optimizer hP hP0 z
  rw [hv]
  exact hm x hx

theorem offlineValue_nonneg {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (z : ι → ℝ) : 0 ≤ offlineValue P z := by
  simpa only [Pi.zero_apply, Finset.sum_const_zero] using
    offline_allocation_le_value hP hP0 z (zero_mem_offlineFeasible hP0 z)

theorem offlineValue_le_demand {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (z : ι → ℝ) :
    offlineValue P z ≤ ∑ i, max (z i) 0 := by
  obtain ⟨x, hx, hv, _⟩ := exists_offline_optimizer hP hP0 z
  rw [hv]
  exact Finset.sum_le_sum (fun i _ => hx.2 i)

theorem offlineValue_le_add_distance {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (hPnonneg : ∀ x ∈ P, ∀ i, 0 ≤ x i)
    (hPdown : NonnegDownwardClosed P) (z w : ι → ℝ) :
    offlineValue P z ≤ offlineValue P w + ∑ i, |z i - w i| := by
  obtain ⟨x, hx, hv, _⟩ := exists_offline_optimizer hP hP0 z
  let y : ι → ℝ := fun i => min (x i) (max (w i) 0)
  have hy : y ∈ offlineFeasible P w :=
    ⟨hPdown hx.1 (fun i => le_min (hPnonneg x hx.1 i) (le_max_right _ _))
      (fun i => min_le_left _ _), fun i => min_le_right _ _⟩
  have hxy : ∀ i, x i ≤ y i + |z i - w i| := by
    intro i
    have habs := le_abs_self (z i - w i)
    have hw := le_max_left (w i) 0
    have hcap : max (z i) 0 ≤ max (w i) 0 + |z i - w i| := by
      apply max_le
      · linarith
      · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
    dsimp only [y]
    by_cases hi : x i ≤ max (w i) 0
    · rw [min_eq_left hi]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [min_eq_right (le_of_not_ge hi)]
      exact (hx.2 i).trans hcap
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hxy i)
  rw [Finset.sum_add_distrib] at hsum
  have hval := offline_allocation_le_value hP hP0 w hy
  rw [hv]
  linarith

theorem offlineValue_abs_sub_le {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (hPnonneg : ∀ x ∈ P, ∀ i, 0 ≤ x i)
    (hPdown : NonnegDownwardClosed P) (z w : ι → ℝ) :
    |offlineValue P z - offlineValue P w| ≤ ∑ i, |z i - w i| := by
  have h1 := offlineValue_le_add_distance hP hP0 hPnonneg hPdown z w
  have h2 := offlineValue_le_add_distance hP hP0 hPnonneg hPdown w z
  simp_rw [abs_sub_comm (w _) (z _)] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem offlineValue_lipschitz {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (hPnonneg : ∀ x ∈ P, ∀ i, 0 ≤ x i)
    (hPdown : NonnegDownwardClosed P) :
    LipschitzWith (Fintype.card ι : ℝ≥0) (offlineValue P) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq, dist_eq_norm]
  apply (offlineValue_abs_sub_le hP hP0 hPnonneg hPdown z w).trans
  calc
    (∑ i, |z i - w i|) ≤ ∑ _i : ι, ‖z - w‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_le_pi_norm (z - w) i
    _ = _ := by simp

theorem continuous_offlineValue {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (hPnonneg : ∀ x ∈ P, ∀ i, 0 ≤ x i)
    (hPdown : NonnegDownwardClosed P) : Continuous (offlineValue P) :=
  (offlineValue_lipschitz hP hP0 hPnonneg hPdown).continuous

theorem measurable_offlineValue {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (hPnonneg : ∀ x ∈ P, ∀ i, 0 ≤ x i)
    (hPdown : NonnegDownwardClosed P) : Measurable (offlineValue P) :=
  (continuous_offlineValue hP hP0 hPnonneg hPdown).measurable

theorem integrable_offlineValue {P : Set (ι → ℝ)} (hP : IsCompact P)
    (hP0 : (0 : ι → ℝ) ∈ P) (hPnonneg : ∀ x ∈ P, ∀ i, 0 ≤ x i)
    (hPdown : NonnegDownwardClosed P) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] :
    Integrable (offlineValue P) μ := by
  obtain ⟨C, hC⟩ := hP.isBounded.exists_norm_le
  apply (integrable_const ((Fintype.card ι : ℝ) * C)).mono'
    (measurable_offlineValue hP hP0 hPnonneg hPdown).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (offlineValue_nonneg hP hP0 z)]
  obtain ⟨x, hx, hv, _⟩ := exists_offline_optimizer hP hP0 z
  rw [hv]
  calc
    (∑ i, x i) ≤ ∑ _i : ι, C := by
      apply Finset.sum_le_sum
      intro i _
      exact (le_abs_self (x i)).trans ((norm_le_pi_norm x i).trans (hC x hx.1))
    _ = _ := by simp

end StochasticMatching
