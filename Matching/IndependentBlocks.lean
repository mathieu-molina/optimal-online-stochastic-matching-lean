import Matching.IndependentPoissons

/-! Mutual independence of disjoint groups of coordinates. This proves a
joint product law for all block counts, not just their separate marginals.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators NNReal
namespace StochasticMatching

theorem independent_disjoint_sigma_blocks {Ω σ κ : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : σ → MeasurableSpace Ω)
    (hm : ∀ s, m s ≤ mΩ) (hind : iIndep m μ) (B : κ → Finset σ)
    (hB : Pairwise (fun j k => Disjoint (B j) (B k))) :
    iIndep (fun j => ⨆ s ∈ B j, m s) μ := by
  classical
  rw [iIndep_iff]
  intro S E hE
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
    have hd : Disjoint (B j : Set σ) (S.biUnion B : Set σ) := by
      rw [Set.disjoint_left]
      intro s hs hs'
      obtain ⟨k, hk, hsk⟩ := Finset.mem_biUnion.mp hs'
      have hjk : j ≠ k := fun h => hj (h.symm ▸ hk)
      exact Finset.disjoint_left.mp (hB hjk) hs hsk
    have hi := indep_iSup_of_disjoint hm hind hd
    have hinc : ∀ k ∈ S, (⨆ s ∈ B k, m s) ≤ ⨆ s ∈ S.biUnion B, m s := by
      intro k hk
      apply iSup_le
      intro s
      apply iSup_le
      intro hs
      exact le_iSup_of_le s (le_iSup_of_le (Finset.mem_biUnion.mpr ⟨k, hk, hs⟩) le_rfl)
    have hEm : MeasurableSet[⨆ s ∈ S.biUnion B, m s] (⋂ k ∈ S, E k) := by
      apply Finset.measurableSet_biInter
      intro k hk
      exact (hinc k hk) _ (hE k (Finset.mem_insert_of_mem hk))
    have he := (Indep_iff _ _ μ).mp hi (E j) (⋂ k ∈ S, E k)
      (hE j (Finset.mem_insert_self _ _)) hEm
    rw [Finset.prod_insert hj, ← ih (fun k hk => hE k (Finset.mem_insert_of_mem hk))]
    simpa only [Finset.set_biInter_insert] using he

variable {σ κ : Type*} [Fintype σ]

theorem independentPoissons_block_sums_independent (a : σ → ℝ≥0) (B : κ → Finset σ)
    (hB : Pairwise (fun j k => Disjoint (B j) (B k))) :
    iIndepFun (fun j (n : σ → ℕ) => ∑ s ∈ B j, n s) (independentPoissons a) := by
  classical
  let m : σ → MeasurableSpace (σ → ℕ) := fun s =>
    MeasurableSpace.comap (fun n : σ → ℕ => n s) inferInstance
  have hm : ∀ s, m s ≤ (inferInstance : MeasurableSpace (σ → ℕ)) :=
    fun s => (measurable_pi_apply s).comap_le
  have hi := independent_disjoint_sigma_blocks (independentPoissons a) m hm
    (independentPoissons_coordinates_independent a).iIndep B hB
  apply (iIndepFun_iff_measure_inter_preimage_eq_mul).mpr
  intro S E hE
  apply hi.meas_biInter
  intro j hj
  apply (hE j hj).preimage
  apply Finset.measurable_sum
  intro s hs
  exact (comap_measurable (fun n : σ → ℕ => n s)).mono
    (le_iSup_of_le s (le_iSup_of_le hs le_rfl)) le_rfl

theorem independentPoissons_block_sum_law [Fintype κ] (a : σ → ℝ≥0) (B : κ → Finset σ)
    (hB : Pairwise (fun j k => Disjoint (B j) (B k))) :
    Measure.map (fun n : σ → ℕ => fun j => ∑ s ∈ B j, n s) (independentPoissons a) =
      independentPoissons (fun j => ∑ s ∈ B j, a s) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun j =>
    (Finset.measurable_sum (B j) (fun s _ => measurable_pi_apply s)).aemeasurable)).mp
      (independentPoissons_block_sums_independent a B hB)
  rw [h]
  change (Measure.pi fun j => Measure.map (fun n : σ → ℕ => ∑ s ∈ B j, n s)
    (independentPoissons a)) = _
  simp_rw [independentPoissons_subset_sum_law]
  rfl

end StochasticMatching
