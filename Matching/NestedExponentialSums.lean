import Matching.ExponentialSumLaw
import Matching.NestedPoissonCounts

/-! Joint laws of exponential demand sums along nested job sets. Each new
block is independent, and its law depends only on its number of jobs.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators
namespace StochasticMatching
variable {ι κ : Type*} [Fintype ι]

theorem independentExponentials_block_sums_independent (B : κ → Finset ι)
    (hB : Pairwise (fun j k => Disjoint (B j) (B k))) :
    iIndepFun (fun j (z : ι → ℝ) => ∑ i ∈ B j, z i) independentExponentials := by
  classical
  let m : ι → MeasurableSpace (ι → ℝ) := fun i =>
    MeasurableSpace.comap (fun z : ι → ℝ => z i) inferInstance
  have hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace (ι → ℝ)) :=
    fun i => (measurable_pi_apply i).comap_le
  have hi := independent_disjoint_sigma_blocks independentExponentials m hm
    independentExponentials_coordinates_independent.iIndep B hB
  apply (iIndepFun_iff_measure_inter_preimage_eq_mul).mpr
  intro S E hE
  apply hi.meas_biInter
  intro j hj
  apply (hE j hj).preimage
  apply Finset.measurable_sum
  intro i hi
  exact (comap_measurable (fun z : ι → ℝ => z i)).mono
    (le_iSup_of_le i (le_iSup_of_le hi le_rfl)) le_rfl

theorem independentExponentials_block_sum_law [Fintype κ] (B : κ → Finset ι)
    (hB : Pairwise (fun j k => Disjoint (B j) (B k))) :
    Measure.map (fun z : ι → ℝ => fun j => ∑ i ∈ B j, z i) independentExponentials =
      Measure.pi (fun j => exponentialSumLaw (B j).card) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun j =>
    (Finset.measurable_sum (B j) (fun i _ => measurable_pi_apply i)).aemeasurable)).mp
      (independentExponentials_block_sums_independent B hB)
  rw [h]
  simp_rw [independentExponentials_subset_sum_law]

theorem nested_exponential_sums_law [DecidableEq ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] (A : κ → Finset ι) (hA : Monotone A) :
    Measure.map (fun z : ι → ℝ => fun j => ∑ i ∈ A j, z i) independentExponentials =
      Measure.map (fun increments : κ → ℝ => fun j => ∑ k ∈ Finset.Iic j, increments k)
        (Measure.pi (fun k => exponentialSumLaw (disjointed A k).card)) := by
  have hlaw := independentExponentials_block_sum_law (disjointed A) (disjoint_disjointed A)
  have hm : Measurable (fun increments : κ → ℝ => fun j => ∑ k ∈ Finset.Iic j, increments k) :=
    measurable_pi_lambda _ (fun j => Finset.measurable_sum _ (fun k _ => measurable_pi_apply k))
  have hb : Measurable (fun z : ι → ℝ => fun j => ∑ i ∈ disjointed A j, z i) :=
    measurable_pi_lambda _ (fun j => Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  rw [← hlaw, Measure.map_map hm hb]
  congr 1
  funext z j
  exact nested_sum_eq_block_sums A hA z j

end StochasticMatching
