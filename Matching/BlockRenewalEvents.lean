import Matching.BlockRenewalRestart

/-! Factor all future observations through the full renewal restart law. -/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace StochasticMatching
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

theorem block_restart_event_probability (A : Finset ι) (j : ↥(Aᶜ)) {t : ℝ}
    (ht : 0 ≤ t) (E : Set (↥(Aᶜ) → ℝ)) (hE : MeasurableSet E) :
    (independentExponentials (ι := ι)).real
      {z | z ∈ vectorRenewalCut A j t ∧ blockRestart A j t z ∈ E} =
      poissonWeight t A.card * (independentExponentials (ι := ↥(Aᶜ))).real E := by
  have h := congrArg (fun μ : Measure (↥(Aᶜ) → ℝ) => μ.real E) (block_restart_law A j ht)
  dsimp only at h
  rw [map_measureReal_apply (measurable_blockRestart A j t) hE,
    measureReal_restrict_apply ((measurable_blockRestart A j t) hE),
    measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (poissonWeight_nonneg ht A.card)] at h
  convert h using 1
  congr 1
  ext z
  exact and_comm

theorem block_restart_joint_probability [Fintype κ] (A : Finset ι) (j : ↥(Aᶜ))
    (B : κ → Finset ι) (hAB : ∀ k, A ⊆ B k) (hjB : ∀ k, (j : ι) ∈ B k)
    {t : ℝ} (ht : 0 ≤ t) (u : κ → ℝ) :
    (independentExponentials (ι := ι)).real
      {z | z ∈ vectorRenewalCut A j t ∧ ∀ k, t + u k < ∑ i ∈ B k, z i} =
      poissonWeight t A.card * (independentExponentials (ι := ↥(Aᶜ))).real
        {w | ∀ k, u k < ∑ i ∈ remainingSubset A (B k), w i} := by
  have hE : MeasurableSet {w : ↥(Aᶜ) → ℝ | ∀ k, u k < ∑ i ∈ remainingSubset A (B k), w i} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_lt measurable_const
      (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)))
  have he : {z : ι → ℝ | z ∈ vectorRenewalCut A j t ∧ ∀ k, t + u k < ∑ i ∈ B k, z i} =
      {z | z ∈ vectorRenewalCut A j t ∧
        blockRestart A j t z ∈ {w | ∀ k, u k < ∑ i ∈ remainingSubset A (B k), w i}} := by
    ext z
    simp only [mem_setOf_eq]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro k
    rw [block_restart_sum A (B k) (hAB k) j (hjB k)]
    constructor <;> intro h <;> linarith
  rw [he]
  exact block_restart_event_probability A j ht _ hE

end StochasticMatching
