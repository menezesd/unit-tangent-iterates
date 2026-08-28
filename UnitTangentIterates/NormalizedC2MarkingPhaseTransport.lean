import UnitTangentIterates.NormalizedTerminalMarkingComposition
import UnitTangentIterates.MarkedShift
import UnitTangentIterates.MarkedRigid

/-!
# Phase transport for normalized terminal markings

A cyclic change of marking at the rear endpoint must not be applied by the
same parameter shift to the terminal base: that would destroy the normalized
condition `psi 0 = 0`.  The correct base shift is the image of the rear phase
under `psi`.  This is the endpoint rephasing used by the gauge-first configured
recursion.
-/

noncomputable section

open Function MarkedSpace

namespace NormalizedTerminalMarkingComposition.NormalizedC2Marking

/-- A common orientation-preserving rigid motion preserves a normalized
terminal marking and all of its scalar jets. -/
def rigid {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda)
    (a w : ℂ) (hw : ‖w‖ = 1) :
    NormalizedC2Marking (MarkedRigid.rigidData a w base)
      (MarkedRigid.rigidData a w rear) lambda Lambda := by
  refine
    { lambda_pos := M.lambda_pos
      marking :=
        { psi := M.marking.psi
          dpsi := M.marking.dpsi
          position := ?_
          velocity := ?_
          translate := M.marking.translate
          lower := M.marking.lower
          upper := M.marking.upper }
      ddpsi := M.ddpsi
      psi_deriv := M.psi_deriv
      dpsi_deriv := M.dpsi_deriv
      ddpsi_cont := M.ddpsi_cont
      psi_zero := M.psi_zero }
  · intro u
    change a + w * rear.1 u = a + w * base.1 (M.marking.psi u)
    rw [M.marking.position u]
  · intro u
    change w * rear.2.1 u =
      (M.marking.dpsi u : ℂ) * (w * base.2.1 (M.marking.psi u))
    rw [M.marking.velocity u]
    ring

/-- Rebase a normalized marking after shifting its rear endpoint by `q`.
The base is shifted by `psi q`, so the transported marking is again normalized
at zero. -/
def rephase {base rear : Data} {lambda Lambda : ℝ}
    (M : NormalizedC2Marking base rear lambda Lambda) (q : ℝ) :
    NormalizedC2Marking
      (MarkedShift.shiftData (M.marking.psi q) base)
      (MarkedShift.shiftData q rear) lambda Lambda := by
  let c := M.marking.psi q
  let psi : ℝ → ℝ := fun u => M.marking.psi (u + q) - c
  let dpsi : ℝ → ℝ := fun u => M.marking.dpsi (u + q)
  let ddpsi : ℝ → ℝ := fun u => M.ddpsi (u + q)
  refine
    { lambda_pos := M.lambda_pos
      marking :=
        { psi := psi
          dpsi := dpsi
          position := ?_
          velocity := ?_
          translate := ?_
          lower := ?_
          upper := ?_ }
      ddpsi := ddpsi
      psi_deriv := ?_
      dpsi_deriv := ?_
      ddpsi_cont := ?_
      psi_zero := ?_ }
  · intro u
    dsimp [psi, c, MarkedShift.shiftData, MarkedShift.shiftMap]
    simpa only [sub_add_cancel] using M.marking.position (u + q)
  · intro u
    dsimp [psi, dpsi, c, MarkedShift.shiftData, MarkedShift.shiftMap]
    simpa only [sub_add_cancel] using M.marking.velocity (u + q)
  · intro u
    dsimp [psi, c]
    rw [show u + 1 + q = (u + q) + 1 by ring, M.marking.translate]
    ring
  · intro u
    exact M.marking.lower (u + q)
  · intro u
    exact M.marking.upper (u + q)
  · intro u
    dsimp [psi, dpsi]
    simpa [Function.comp_def] using ((M.psi_deriv (u + q)).comp u
      ((hasDerivAt_id u).add_const q)).sub_const c
  · intro u
    dsimp [dpsi, ddpsi]
    simpa [Function.comp_def] using (M.dpsi_deriv (u + q)).comp u
      ((hasDerivAt_id u).add_const q)
  · exact M.ddpsi_cont.comp (continuous_id.add continuous_const)
  · simp [psi, c]

end NormalizedTerminalMarkingComposition.NormalizedC2Marking
