import Matching.HistoryFirstEventRestart
import Matching.NoiseKernelFactorization

/-! A concrete transition carrying the job residual demands and sampling
only one new auxiliary clock. Its observed history law agrees, after every
finite number of steps, with the exponential first-event kernel.
-/
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ProbabilityTheory
namespace StochasticMatching
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]

def augmentResidual (x : (ι → ℝ) × ℝ) (j : Option ι) : ℝ := j.elim x.2 x.1

theorem measurable_augmentResidual : Measurable (augmentResidual (ι := ι)) := by
  apply measurable_pi_lambda
  intro j
  cases j with
  | none => exact measurable_snd
  | some i => exact (measurable_pi_apply i).comp measurable_fst

theorem augmentResidual_law :
    Measure.map (augmentResidual (ι := ι))
      ((independentExponentials (ι := ι)).prod unitExponential) =
      independentExponentials (ι := Option ι) := by
  have h := Measure.pi_map_piOptionEquivProd (fun _ : Option ι => unitExponential)
  have hf : augmentResidual (ι := ι) =
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm := by
    funext x j
    cases j <;> rfl
  rw [hf]
  exact h

noncomputable def latentRestartUpdate (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → H) (x : (H × (ι → ℝ)) × ℝ) : H × (ι → ℝ) :=
  let q := historyRestart p (x.1.1, augmentResidual (x.1.2, x.2))
  (U (x.1.1, q.1), q.2)

theorem measurable_latentRestartUpdate (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → H) (hU : Measurable U) :
    Measurable (latentRestartUpdate p U) := by
  have hh : Measurable (fun x : (H × (ι → ℝ)) × ℝ => x.1.1) := measurable_fst.comp measurable_fst
  have hz : Measurable (fun x : (H × (ι → ℝ)) × ℝ => augmentResidual (x.1.2, x.2)) :=
    measurable_augmentResidual.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hq := (measurable_historyRestart p).comp (hh.prodMk hz)
  exact (hU.comp (hh.prodMk hq.fst)).prodMk hq.snd

noncomputable def latentExponentialKernel (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → H) : Kernel (H × (ι → ℝ)) (H × (ι → ℝ)) :=
  noiseKernel unitExponential (latentRestartUpdate p U)

theorem latentExponentialKernel_markov (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → H) (hU : Measurable U) :
    IsMarkovKernel (latentExponentialKernel p U) :=
  noiseKernel_markov _ _ (measurable_latentRestartUpdate p U hU)

theorem latentRestartUpdate_product_law (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → H) (hU : Measurable U) (h : H) :
    Measure.map (fun x : (ι → ℝ) × ℝ => latentRestartUpdate p U ((h, x.1), x.2))
        ((independentExponentials (ι := ι)).prod unitExponential) =
      (eventUpdateKernel (historyEventKernel p) U h).prod (independentExponentials (ι := ι)) := by
  let F : (Option ι → ℝ) → H × (ι → ℝ) := fun z =>
    (U (h, (historyRestart p (h, z)).1), (historyRestart p (h, z)).2)
  have hq : Measurable (fun z : Option ι → ℝ => historyRestart p (h, z)) :=
    (measurable_historyRestart p).comp measurable_prodMk_left
  have hF : Measurable F := (hU.comp (measurable_const.prodMk hq.fst)).prodMk hq.snd
  have hl := historyRestart_update_law p U hU h
  change Measure.map F independentExponentials = _ at hl
  rw [← augmentResidual_law, Measure.map_map hF measurable_augmentResidual] at hl
  exact hl

theorem latentExponentialKernel_intertwining (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → H) (hU : Measurable U) :
    latentExponentialKernel p U ∘ₖ freshResidualKernel (independentExponentials (ι := ι)) =
      freshResidualKernel independentExponentials ∘ₖ eventUpdateKernel (historyEventKernel p) U :=
  noiseKernel_intertwining _ _ _ (measurable_latentRestartUpdate p U hU) _
    (latentRestartUpdate_product_law p U hU)

theorem latentExponential_history_law (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → H) (hU : Measurable U) (n : ℕ) :
    (iterateKernel (latentExponentialKernel p U) n ∘ₖ
      freshResidualKernel (independentExponentials (ι := ι))).map Prod.fst =
      iterateKernel (eventUpdateKernel (historyEventKernel p) U) n :=
  latent_iterate_history_law _ _ _ (latentExponentialKernel_intertwining p U hU) n

theorem latentExponential_residual_factorization (p : HistoryServiceFamily H (Option ι))
    (U : H × (Unit ⊕ (ℝ × Option ι)) → H) (hU : Measurable U) (n : ℕ) (h : H) :
    (iterateKernel (latentExponentialKernel p U) n ∘ₖ
      freshResidualKernel (independentExponentials (ι := ι))) h =
      (iterateKernel (eventUpdateKernel (historyEventKernel p) U) n h).prod
        (independentExponentials (ι := ι)) := by
  rw [iterateKernel_intertwining _ _ _ (latentExponentialKernel_intertwining p U hU),
    freshResidualKernel_comp_apply]

end StochasticMatching
