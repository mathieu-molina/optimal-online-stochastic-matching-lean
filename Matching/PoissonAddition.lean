import Matching.PoissonWeights
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Probability.Independence.Basic

/-! Addition of independent Poisson counts, including finite sums. The law is
derived from the finite binomial convolution of the actual Poisson masses.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching

theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  by_cases hn : n = 0
  · subst n
    simp [poissonWeight]
  · simp [poissonWeight, hn, Ne.symm hn]

theorem poisson_addition_law (a b : ℝ≥0) :
    Measure.map (fun p : ℕ × ℕ => p.1 + p.2) ((poissonMeasure a).prod (poissonMeasure b)) =
      poissonMeasure (a + b) := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (measurable_fst.add measurable_snd) (measurableSet_singleton n)]
  have he : (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' {n} = (Finset.antidiagonal n : Set (ℕ × ℕ)) := by
    ext p
    simp
  rw [he, ← sum_measure_singleton, poissonMeasure_singleton]
  have hp : ∀ p : ℕ × ℕ, ((poissonMeasure a).prod (poissonMeasure b)) {p} =
      ENNReal.ofReal (poissonWeight a p.1 * poissonWeight b p.2) := by
    intro p
    rw [← singleton_prod_singleton, Measure.prod_prod, poissonMeasure_singleton, poissonMeasure_singleton,
      ← ENNReal.ofReal_mul (poissonWeight_nonneg a.coe_nonneg p.1)]
  simp_rw [hp]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg
    (poissonWeight_nonneg a.coe_nonneg p.1) (poissonWeight_nonneg b.coe_nonneg p.2)),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, poissonWeight_convolution]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem poisson_sum_of_independent {X Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y μ) (a b : ℝ≥0)
    (hXa : Measure.map X μ = poissonMeasure a) (hYb : Measure.map Y μ = poissonMeasure b) :
    Measure.map (fun ω => X ω + Y ω) μ = poissonMeasure (a + b) := by
  have hp := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hind
  rw [hXa, hYb] at hp
  have he : (fun ω => X ω + Y ω) = (fun p : ℕ × ℕ => p.1 + p.2) ∘ (fun ω => (X ω, Y ω)) := rfl
  rw [he, ← Measure.map_map (measurable_fst.add measurable_snd) (hX.prodMk hY), hp, poisson_addition_law]

variable {ι : Type*}

theorem poisson_finset_sum_law (S : Finset ι) (X : ι → Ω → ℕ) (a : ι → ℝ≥0)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hlaw : ∀ i, Measure.map (X i) μ = poissonMeasure (a i)) :
    Measure.map (fun ω => ∑ i ∈ S, X i ω) μ = poissonMeasure (∑ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [poissonMeasure_zero]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hm := Finset.measurable_sum S (fun j _ => hX j)
    have hi' := (hind.indepFun_finset_sum_of_not_mem hX hi).symm
    have he : (∑ j ∈ S, X j) = fun ω => ∑ j ∈ S, X j ω := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hi'
    have hi'' := hi'
    have h := poisson_sum_of_independent μ (hX i) hm hi'' (a i) (∑ j ∈ S, a j) (hlaw i) ih
    exact h

end StochasticMatching
