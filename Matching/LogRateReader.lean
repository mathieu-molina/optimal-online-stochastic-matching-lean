import Matching.RatePath
import Matching.ObservationFiltration

/-! A measurable rate evaluator from the observed completion log. It reads
only the initial history and the log censored at the query time. Its agreement
with the sample-space service path is proved in LogRateAgreement.
-/

open MeasureTheory Set
namespace StochasticMatching
universe u v w
variable {J : Type w} [MeasurableSpace J]

def completionEntryLabel : Unit ⊕ (J × ℝ × ℝ) → Unit ⊕ J :=
  Sum.elim Sum.inl (fun q => Sum.inr q.1)

theorem measurable_completionEntryLabel : Measurable (completionEntryLabel (J := J)) :=
  Measurable.sumElim measurable_inl (measurable_inr.comp measurable_fst)

abbrev RateQuery (H J : Type*) := ℝ × (H × (ℝ × CompletionLog J))

namespace PosteriorStage
variable {H : Type u} {ι : Type v} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [MeasurableSingletonClass J]

def readerWinner (label : ι → J) (k : ℕ) (j : ι) : Set (RateQuery H J) :=
  {q | completionEntryLabel (q.2.2.2 k) = Sum.inr (label j)}

theorem readerWinner_disjoint (label : ι → J) (hinj : Function.Injective label) (k : ℕ) :
    Pairwise (fun i j => Disjoint (readerWinner (H := H) label k i) (readerWinner label k j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro q hi hj
  exact hij (hinj (Sum.inr.inj (hi.symm.trans hj)))

theorem measurable_readerWinner (label : ι → J) (k : ℕ) (j : ι) :
    MeasurableSet (readerWinner (H := H) label k j) := by
  have he : Measurable (fun q : RateQuery H J => q.2.2.2 k) :=
    (measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hs : MeasurableSet ({Sum.inr (label j)} : Set (Unit ⊕ J)) := by
    simpa only [Set.image_singleton] using (measurableSet_singleton (label j)).inr_image (α := Unit)
  exact hs.preimage (measurable_completionEntryLabel.comp he)

noncomputable def readerCurrent (s : PosteriorStage H ι) (label : ι → J) (q : RateQuery H J) : J → ℝ :=
  labelLift label (fun i => (s.service.curves q.2.1).rate i (q.1 - q.2.2.1))

theorem measurable_readerCurrent (s : PosteriorStage H ι) (label : ι → J) :
    Measurable (s.readerCurrent label) := by
  apply (labelLift label).continuous.measurable.comp
  apply measurable_pi_lambda
  intro i
  exact (s.service.measurable_rate i).comp
    ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.sub (measurable_fst.comp (measurable_snd.comp measurable_snd))))

def readerNextQuery (k : ℕ) (q : RateQuery H J) : RateQuery (H × ℝ) J :=
  let t := completionEntryTime (q.2.2.2 k)
  (q.1, ((q.2.1, t - q.2.2.1), (t, q.2.2.2)))

theorem measurable_readerNextQuery (k : ℕ) : Measurable (readerNextQuery (H := H) (J := J) k) := by
  have he : Measurable (fun q : RateQuery H J => q.2.2.2 k) :=
    (measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have ht := measurable_completionEntryTime.comp he
  exact measurable_fst.prodMk
    (((measurable_fst.comp measurable_snd).prodMk
      (ht.sub (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
        (ht.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))

noncomputable def readRate : (n : ℕ) → {H : Type u} → {ι : Type v} →
    [MeasurableSpace H] → [Fintype ι] → [DecidableEq ι] →
    PosteriorStage H ι → (ι → J) → ℕ → RateQuery H J → (J → ℝ)
  | 0, _, _, _, _, _, _, _, _, _ => 0
  | n + 1, _, _, _, _, _, s, label, k, q =>
      if 0 ≤ q.1 - q.2.2.1 ∧ q.1 - q.2.2.1 < s.deadline q.2.1 then
        branchSelect (readerWinner label k)
          (fun j q => readRate n (s.next j) (fun i => label i.1) (k + 1) (readerNextQuery k q))
          (s.readerCurrent label) q
      else 0

theorem measurable_readRate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (k : ℕ) : Measurable (readRate n s label k) := by
  induction n generalizing H ι k with
  | zero => exact measurable_const
  | succ n ih =>
    have ht : Measurable (fun q : RateQuery H J => q.1 - q.2.2.1) :=
      measurable_fst.sub (measurable_fst.comp (measurable_snd.comp measurable_snd))
    apply Measurable.ite ((measurableSet_le measurable_const ht).inter
      (measurableSet_lt ht (s.measurable_deadline.comp (measurable_fst.comp measurable_snd))))
    · apply measurable_branchSelect (readerWinner_disjoint label hinj k) (measurable_readerWinner label k)
      · intro j
        exact (ih (s.next j) (fun i => label i.1) (hinj.comp Subtype.val_injective) (k + 1)).comp
          (measurable_readerNextQuery k)
      · exact s.measurable_readerCurrent label
    · exact measurable_const

noncomputable def observedRate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (k : ℕ) (q : RateQuery H J) : J → ℝ :=
  readRate n s label k (q.1, (q.2.1, (q.2.2.1, censorLog q.1 q.2.2.2)))

theorem measurable_observedRate (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (k : ℕ) : Measurable (observedRate n s label k) := by
  apply (measurable_readRate n s label hinj k).comp
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
      (measurable_censorLog.comp (measurable_fst.prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))))

theorem observedRate_censor (n : ℕ) (s : PosteriorStage H ι) (label : ι → J)
    (k : ℕ) (t : ℝ) (h : H) (elapsed : ℝ) (L : CompletionLog J) :
    observedRate n s label k (t, (h, (elapsed, censorLog t L))) =
      observedRate n s label k (t, (h, (elapsed, L))) := by
  simp only [observedRate, censorLog_censorLog (le_refl t)]

theorem observedRate_measurable_filtration (s : PosteriorStage H ι) (label : ι → J)
    (hinj : Function.Injective label) (t : ℝ) :
    @Measurable (H × (ι → ℝ)) (J → ℝ) (s.observationFiltration label t) inferInstance
      (fun x => observedRate (Fintype.card ι) s label 0 (t, (x.1, (0, s.completionLog label x)))) := by
  have hr : Measurable (fun q : H × CompletionLog J =>
      readRate (Fintype.card ι) s label 0 (t, (q.1, (0, q.2)))) :=
    (measurable_readRate (Fintype.card ι) s label hinj 0).comp
      (measurable_const.prodMk (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  exact hr.comp (comap_measurable (observedAt Prod.fst (s.completionLog label) t))

end PosteriorStage
end StochasticMatching
