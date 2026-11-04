import Matching.HardNeighborhoodLaw
import Matching.SupplyRegion

/-! Concrete finite Poisson hard instances. There is one type per subset of
offline vertices. Rates are nonnegative, sum to the vertex count, and have
the exact symmetric coverage k(1-log(k/m)). -/
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

noncomputable def hardPoissonIntensity (S : Finset ι) : ℝ≥0 :=
  ⟨(Fintype.card ι : ℝ) * (hardNeighborhoodMeasure (ι := ι)).real {S},
    mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg⟩

theorem hardPoissonIntensity_total :
    (∑ S : Finset ι, (hardPoissonIntensity S : ℝ)) = Fintype.card ι := by
  change (∑ S : Finset ι, (Fintype.card ι : ℝ) * hardNeighborhoodMeasure.real {S}) = _
  rw [← Finset.mul_sum]
  rw [sum_measureReal_singleton]
  simp

theorem hardPoissonIntensity_coverage_probability (A : Finset ι) :
    supplyCoverage id (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) A =
      (Fintype.card ι : ℝ) * (hardNeighborhoodMeasure (ι := ι)).real
        {S : Finset ι | (S ∩ A).Nonempty} := by
  classical
  let B : Finset (Finset ι) := Finset.univ.filter (fun S => (S ∩ A).Nonempty)
  have he : (B : Set (Finset ι)) = {S | (S ∩ A).Nonempty} := by ext S; simp [B]
  calc
    _ = (Fintype.card ι : ℝ) * ∑ S ∈ B, (hardNeighborhoodMeasure (ι := ι)).real {S} := by
      rw [Finset.mul_sum]
      simp only [B, Finset.sum_filter, supplyCoverage, hardPoissonIntensity, id_eq]
      rfl
    _ = _ := by rw [sum_measureReal_singleton, he]

theorem hardNeighborhoodMeasure_hit (A : Finset ι) :
    (hardNeighborhoodMeasure (ι := ι)).real {S : Finset ι | (S ∩ A).Nonempty} =
      1 - hardGeneratingFunction ((Aᶜ.card : ℝ) / Fintype.card ι) := by
  have he : {S : Finset ι | (S ∩ A).Nonempty} = {S : Finset ι | S ⊆ Aᶜ}ᶜ := by
    ext S
    simp only [mem_setOf_eq, mem_compl_iff]
    constructor
    · rintro ⟨i, hi⟩ hsub
      exact (Finset.mem_compl.mp (hsub (Finset.mem_inter.mp hi).1)) (Finset.mem_inter.mp hi).2
    · intro h
      by_contra hempty
      apply h
      intro i hi
      apply Finset.mem_compl.mpr
      intro hia
      exact hempty ⟨i, Finset.mem_inter.mpr ⟨hi, hia⟩⟩
  rw [he, measureReal_compl (Set.to_countable _).measurableSet, measureReal_univ_eq_one,
    measureReal_def, hardNeighborhoodMeasure_subset, ENNReal.toReal_ofReal]
  apply hardGeneratingFunction_nonneg
  constructor
  · positivity
  · apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
    exact_mod_cast Finset.card_le_univ Aᶜ

theorem hardPoissonIntensity_coverage (A : Finset ι) :
    supplyCoverage id (fun S : Finset ι => (hardPoissonIntensity S : ℝ)) A =
      (A.card : ℝ) * (1 - Real.log ((A.card : ℝ) / Fintype.card ι)) := by
  have hm : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hk : A.card ≤ Fintype.card ι := Finset.card_le_univ A
  have he : (Aᶜ.card : ℝ) / Fintype.card ι = 1 - (A.card : ℝ) / Fintype.card ι := by
    rw [Finset.card_compl, Nat.cast_sub hk]
    field_simp
  rw [hardPoissonIntensity_coverage_probability, hardNeighborhoodMeasure_hit, he,
    one_sub_hardGeneratingFunction]
  simp only [sub_sub_cancel]
  field_simp

end StochasticMatching
