import Matching.HardDegreeLaw
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi

/-! A finite neighborhood law obtained by sampling the hard degree and then
that many independent uniform vertices, with replacement. Although the degree
is unbounded, the neighborhood type space is the finite powerset of vertices. -/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

noncomputable def uniformVertexMeasure : Measure ι := (PMF.uniformOfFintype ι).toMeasure

instance uniformVertexMeasure_probability : IsProbabilityMeasure (uniformVertexMeasure (ι := ι)) := by
  unfold uniformVertexMeasure
  infer_instance

noncomputable def replacementNeighborhoodMeasure (d : ℕ) : Measure (Finset ι) :=
  Measure.map (fun x : Fin d → ι => Finset.univ.image x)
    (Measure.pi (fun _ : Fin d => uniformVertexMeasure (ι := ι)))

instance replacementNeighborhoodMeasure_probability (d : ℕ) :
    IsProbabilityMeasure (replacementNeighborhoodMeasure (ι := ι) d) := by
  unfold replacementNeighborhoodMeasure
  exact isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem uniformVertexMeasure_finset (A : Finset ι) :
    uniformVertexMeasure (A : Set ι) = (A.card : ℝ≥0∞) / Fintype.card ι := by
  unfold uniformVertexMeasure
  simpa using PMF.toMeasure_uniformOfFintype_apply (A : Set ι) A.measurableSet

theorem replacementNeighborhoodMeasure_subset (d : ℕ) (A : Finset ι) :
    replacementNeighborhoodMeasure d {S : Finset ι | S ⊆ A} =
      ((A.card : ℝ≥0∞) / Fintype.card ι) ^ d := by
  rw [replacementNeighborhoodMeasure, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable _).measurableSet]
  have he : (fun x : Fin d → ι => Finset.univ.image x) ⁻¹' {S | S ⊆ A} =
      Set.univ.pi (fun _ : Fin d => (A : Set ι)) := by
    ext x
    simp [Finset.image_subset_iff]
  rw [he, Measure.pi_pi]
  simp only [uniformVertexMeasure_finset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

noncomputable def hardNeighborhoodMeasure : Measure (Finset ι) :=
  Measure.sum (fun k => ENNReal.ofReal (hardDegreeWeight k) •
    replacementNeighborhoodMeasure (ι := ι) (k + 2))

instance hardNeighborhoodMeasure_probability : IsProbabilityMeasure (hardNeighborhoodMeasure (ι := ι)) := by
  constructor
  rw [hardNeighborhoodMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hardDegreeWeight_pos k).le)
    hardDegreeWeight_hasSum.summable, hardDegreeWeight_hasSum.tsum_eq, ENNReal.ofReal_one]

theorem hardNeighborhoodMeasure_subset_series (A : Finset ι) :
    hardNeighborhoodMeasure {S : Finset ι | S ⊆ A} =
      ∑' k, ENNReal.ofReal (hardDegreeWeight k) *
        ((A.card : ℝ≥0∞) / Fintype.card ι) ^ (k + 2) := by
  rw [hardNeighborhoodMeasure, Measure.sum_apply _ (Set.to_countable _).measurableSet]
  simp only [Measure.smul_apply, smul_eq_mul, replacementNeighborhoodMeasure_subset]

theorem hardNeighborhoodMeasure_subset (A : Finset ι) :
    hardNeighborhoodMeasure {S : Finset ι | S ⊆ A} =
      ENNReal.ofReal (hardGeneratingFunction ((A.card : ℝ) / Fintype.card ι)) := by
  have hm : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hx0 : 0 ≤ (A.card : ℝ) / Fintype.card ι := by positivity
  have hx1 : (A.card : ℝ) / Fintype.card ι ≤ 1 := by
    apply (div_le_one hm).mpr
    exact_mod_cast Finset.card_le_univ A
  have hs : HasSum (fun k => hardDegreeWeight k *
      ((A.card : ℝ) / Fintype.card ι) ^ (k + 2))
      (hardGeneratingFunction ((A.card : ℝ) / Fintype.card ι)) := by
    rcases lt_or_eq_of_le hx1 with hlt | heq
    · exact hardDegreeWeight_generating hx0 hlt
    · rw [heq]
      exact hardDegreeWeight_generating_one
  rw [hardNeighborhoodMeasure_subset_series, ← hs.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hardDegreeWeight_pos k).le (pow_nonneg hx0 _)) hs.summable]
  apply tsum_congr
  intro k
  rw [ENNReal.ofReal_mul (hardDegreeWeight_pos k).le, ENNReal.ofReal_pow hx0,
    ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

end StochasticMatching
