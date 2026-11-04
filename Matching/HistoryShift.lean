import Matching.ShiftedFirstEvent
import Matching.HistoryService

/-! Measurable shifts of service histories, with a total definition on
unreachable inputs. On a valid elapsed time this is exactly the unfinished
suffix of the original service segment.
-/
open MeasureTheory Set
namespace StochasticMatching.HistoryServiceFamily
variable {H ι : Type*} [MeasurableSpace H] [Fintype ι] [DecidableEq ι]

noncomputable def shiftOffset (p : HistoryServiceFamily H ι) (x : H × ℝ) : ℝ :=
  if 0 ≤ x.2 ∧ x.2 < (p.curves x.1).deadline then x.2 else 0

theorem measurable_shiftOffset (p : HistoryServiceFamily H ι) : Measurable p.shiftOffset :=
  Measurable.ite ((measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd (p.deadline_measurable.comp measurable_fst)))
    measurable_snd measurable_const

theorem shiftOffset_nonneg (p : HistoryServiceFamily H ι) (x : H × ℝ) :
    0 ≤ p.shiftOffset x := by
  unfold shiftOffset
  split_ifs with hx
  · exact hx.1
  · exact le_rfl

theorem shiftOffset_lt (p : HistoryServiceFamily H ι) (x : H × ℝ) :
    p.shiftOffset x < (p.curves x.1).deadline := by
  unfold shiftOffset
  split_ifs with hx
  · exact hx.2
  · exact (p.curves x.1).deadline_pos

theorem shiftOffset_eq (p : HistoryServiceFamily H ι) (h : H) (t : ℝ)
    (ht0 : 0 ≤ t) (htT : t < (p.curves h).deadline) : p.shiftOffset (h, t) = t :=
  if_pos ⟨ht0, htT⟩

noncomputable def shifted (p : HistoryServiceFamily H ι) : HistoryServiceFamily (H × ℝ) ι where
  curves x := (p.curves x.1).afterTime (p.shiftOffset x) (p.shiftOffset_nonneg x) (p.shiftOffset_lt x)
  deadline_measurable := (p.deadline_measurable.comp measurable_fst).sub p.measurable_shiftOffset
  service_at_measurable i t :=
    ((p.measurable_service i).comp (measurable_fst.prodMk (p.measurable_shiftOffset.add_const t))).sub
      ((p.measurable_service i).comp (measurable_fst.prodMk p.measurable_shiftOffset))
  rate_at_measurable i t :=
    (p.measurable_rate i).comp (measurable_fst.prodMk (p.measurable_shiftOffset.add_const t))

theorem shifted_service (p : HistoryServiceFamily H ι) (h : H) (t : ℝ)
    (ht0 : 0 ≤ t) (htT : t < (p.curves h).deadline) (i : ι) (u : ℝ) :
    (p.shifted.curves (h, t)).service i u = (p.curves h).service i (t + u) - (p.curves h).service i t := by
  simp only [shifted, ServiceCurveFamily.afterTime, p.shiftOffset_eq h t ht0 htT]

theorem shifted_rate (p : HistoryServiceFamily H ι) (h : H) (t : ℝ)
    (ht0 : 0 ≤ t) (htT : t < (p.curves h).deadline) (i : ι) (u : ℝ) :
    (p.shifted.curves (h, t)).rate i u = (p.curves h).rate i (t + u) := by
  simp only [shifted, ServiceCurveFamily.afterTime, p.shiftOffset_eq h t ht0 htT]

theorem shifted_deadline (p : HistoryServiceFamily H ι) (h : H) (t : ℝ)
    (ht0 : 0 ≤ t) (htT : t < (p.curves h).deadline) :
    (p.shifted.curves (h, t)).deadline = (p.curves h).deadline - t := by
  simp only [shifted, ServiceCurveFamily.afterTime, p.shiftOffset_eq h t ht0 htT]

theorem shifted_rate_mem (p : HistoryServiceFamily H ι) (P : Set (ι → ℝ))
    (hp : ∀ h u, u ∈ Icc 0 (p.curves h).deadline → (fun i => (p.curves h).rate i u) ∈ P)
    (x : H × ℝ) (u : ℝ) (hu : u ∈ Icc 0 (p.shifted.curves x).deadline) :
    (fun i => (p.shifted.curves x).rate i u) ∈ P := by
  apply hp
  have h0 := p.shiftOffset_nonneg x
  change 0 ≤ u ∧ u ≤ (p.curves x.1).deadline - p.shiftOffset x at hu
  constructor <;> linarith

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
theorem shifted_firstEvent (p : HistoryServiceFamily H ι) (h : H) (t : ℝ)
    (ht0 : 0 ≤ t) (htT : t < (p.curves h).deadline) (z : ι → ℝ)
    (hz : ∀ i, (p.curves h).service i t < z i) :
    (p.shifted.curves (h, t)).firstEvent (fun i => z i - (p.curves h).service i t) =
      Sum.map id (Prod.map (fun u => u - t) id) ((p.curves h).firstEvent z) := by
  have he : p.shifted.curves (h, t) = (p.curves h).afterTime t ht0 htT := by
    unfold shifted
    simp only [p.shiftOffset_eq h t ht0 htT]
  rw [he]
  exact (p.curves h).afterTime_firstEvent t ht0 htT z hz

end StochasticMatching.HistoryServiceFamily
