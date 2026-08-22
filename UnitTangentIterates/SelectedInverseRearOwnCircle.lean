import Mathlib
import UnitTangentIterates.SelectedInverseRearOwn
import UnitTangentIterates.SelectedInverseTubeCircle

/-!
# The marked selected inverse of a circle, in its own arclength

`SelectedInverseRearOwn.exists_marked_rearOwn` identifies the marked selected
inverse of a member of the tube with the rear track of that member written in
its own arclength.  This file checks that its hypotheses are not vacuous: they
hold for the marked circle of radius `r > 1`, whose curvature is `1/r < 1` and
whose rear tracks are embedded (`SelectedInverseTubeCircle.lean`).

`exists_marked_rearOwn_circle` is the resulting instance: the marked circle of
radius `r > 1` has a marked selected inverse which is literally the rear track
of the circle written in its own arclength and marked at `x = 0`.
-/

noncomputable section

open Set Function MarkedSpace RearTrack

namespace SelectedInverseRearOwnCircle

open SelectedInverseCircle SelectedInverseTubeCircle

/-- **The marked selected inverse of a circle is its rear track in its own
arclength.**  An instance of `SelectedInverseRearOwn.exists_marked_rearOwn`,
showing that its hypotheses are satisfiable. -/
theorem exists_marked_rearOwn_circle {r : ℝ} (hr : 1 < r) :
    ∃ (q : Data) (Θ K dl sf : ℝ → ℝ) (dR : ℝ),
      (∀ s, HasDerivAt (ev (circleData r)) (Complex.exp (Complex.I * (Θ s : ℂ))) s) ∧
      (∀ s, HasDerivAt Θ (K s) s) ∧ (∀ s, 1 / r ≤ K s) ∧ (∀ s, K s ≤ 1 / r) ∧
      Function.Periodic dl (perim (circleData r)) ∧
      (∀ s, dl s ∈ Icc 0 (Real.arcsin (1 / r))) ∧
      (∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) ∧
      (∀ x, rearArclength dl (sf x) = x) ∧
      0 < dR ∧
      IsTubeMember (perim q) ((1 / r) / Real.sqrt (1 - (1 / r) ^ 2)) dR q ∧
      perim q = rearArclength dl (perim (circleData r)) ∧
      MainTheoremConditional.IsOval (ev q) ∧
      (∀ u, ((starRingEnd ℂ) (q.2.1 u) * q.2.2 u).im
        ≤ (1 / r) / Real.sqrt (1 - (1 / r) ^ 2) * ‖q.2.1 u‖ ^ 3) ∧
      range (UnitTangent.unitTangentMap (ev q)) = range (ev (circleData r)) ∧
      (∀ x, ev q x = rearTrack (ev (circleData r)) Θ dl (sf x)) ∧
      (∀ t u, q.1 u
        = RearOwnArclength.rearOwn (fun _ => ev (circleData r)) (fun _ => Θ) (fun _ => dl)
            (fun _ => sf) t (perim q * u)) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hppos : 0 < 2 * Real.pi * r := by positivity
  have hkmin : 0 < 1 / r := by positivity
  have hkap1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  exact SelectedInverseRearOwn.exists_marked_rearOwn hppos hkmin hkap1
    (circleData_mem_tube hr0) (circleData_curvature_le hr0)
    (fun Θ K dl hX hΘ hdlper hdlmem hdlode =>
      injOn_rearTrack_evCircleData hr Θ K dl hX hΘ hdlper hdlmem hdlode)

end SelectedInverseRearOwnCircle
