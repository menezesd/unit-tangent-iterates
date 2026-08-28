import UnitTangentIterates.SelectedRearOneStepRegularity
import UnitTangentIterates.SelectedInverseShiftEquivariance

/-!
# Arbitrary regularity from local shifted-front rear stages

Global phase coherence is unnecessary for regularity.  At each row the front
of the limiting physical stage may be an independent cyclic re-marking of the
next limiting datum.
-/

noncomputable section

open MarkedSpace

namespace SelectedRearAllOrdersRegularity

/-- A cyclic change of marking preserves every finite differentiability
order of the physical arclength representative. -/
theorem contDiff_ev_shiftData
    {c kmin dlt : ℝ} {p : Data}
    (hc : 0 < c) (hp : IsTubeMember c kmin dlt p) {m : ℕ}
    (h : ContDiff ℝ (m : ℕ) (ev p)) (b : ℝ) :
    ContDiff ℝ (m : ℕ) (ev (MarkedShift.shiftData b p)) := by
  have hL : perim p ≠ 0 := ne_of_gt (perim_pos hc hp)
  have htranslate : ContDiff ℝ (m : ℕ)
      (fun s : ℝ => s + b * perim p) := contDiff_id.add contDiff_const
  have hc := h.comp htranslate
  convert hc using 1
  funext s
  simpa [Function.comp_def] using
    SelectedInverseShiftEquivariance.ev_shiftData hp hL b s

/-- Independent shifted-front stages bootstrap the ambient `C2` regularity to
every finite order. -/
theorem contDiff_add_two_of_local_shifted_stages
    {c dlt : ℝ} (hc : 0 < c) (X : ℕ → Data)
    (htube : ∀ n, IsTubeMember c 0 dlt (X n))
    (hC2 : ∀ n, ContDiff ℝ (2 : ℕ) (ev (X n)))
    (hstage : ∀ n, ∃ q : ℝ, Nonempty
      (PathMetric.PhysicalRearLimitStageComponents
        (X n) (MarkedShift.shiftData q (X (n + 1))))) :
    ∀ r n, ContDiff ℝ (r + 2 : ℕ) (ev (X n)) := by
  intro r
  induction r with
  | zero =>
      intro n
      simpa using hC2 n
  | succ r ih =>
      intro n
      obtain ⟨q, ⟨S⟩⟩ := hstage n
      have hfront : ContDiff ℝ (r + 2 : ℕ)
          (ev (MarkedShift.shiftData q (X (n + 1)))) :=
        contDiff_ev_shiftData hc (htube (n + 1)) (ih (n + 1)) q
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SelectedRearOneStepRegularity.contDiff_succ_ev_of_stage_of_front r S hfront

/-- Independent local phase choices therefore suffice for `C∞` regularity
of every original, unshifted limiting representative. -/
theorem contDiff_infty_of_local_shifted_stages
    {c dlt : ℝ} (hc : 0 < c) (X : ℕ → Data)
    (htube : ∀ n, IsTubeMember c 0 dlt (X n))
    (hC2 : ∀ n, ContDiff ℝ (2 : ℕ) (ev (X n)))
    (hstage : ∀ n, ∃ q : ℝ, Nonempty
      (PathMetric.PhysicalRearLimitStageComponents
        (X n) (MarkedShift.shiftData q (X (n + 1))))) :
    ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ev (X n)) := by
  have hall := contDiff_add_two_of_local_shifted_stages hc X htube hC2 hstage
  intro n
  exact contDiff_infty.2 fun m =>
    (hall m n).of_le (by exact_mod_cast Nat.le_add_right m 2)

end SelectedRearAllOrdersRegularity
