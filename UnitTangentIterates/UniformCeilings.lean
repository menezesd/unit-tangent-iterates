import UnitTangentIterates.GaugeFlowDerivCost
import UnitTangentIterates.ConstantToVariableSpeed
import UnitTangentIterates.ArclengthInverse

/-!
# The variable-speed ceilings do not compound along the orbit
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function Real

namespace GaugeFlowDerivCost

theorem costP1_nonneg {ell kappa M : ℝ} (hell : 0 ≤ ell) : 0 ≤ costP1 ell kappa M := by
  rw [costP1]; positivity

/-- **The ceilings do not compound.**

`GaugeRearFamilyFromFront` outputs the variable-speed ceilings

    G1 = costP1 ell khat M = ell · exp (khat · M)
    Cg = costG1 ell khat kappa2 M = (costP1 ell khat M)² · (kappa2 · M)

where `ell` is the rear period *of that step* and `M` its total cost.  Neither
expression mentions the incoming ceilings.  So iterating the rear map does not
accumulate them: a uniform bound on the periods and on the costs bounds the
ceilings at *every* step at once, by monotonicity alone.

This is what §96 left open.  The concern there — that `(0,0) ↦ (costG1 …, …)`
makes the class un-preserved — is real for a *fixed* pair of ceilings, but the
growth is not iterative, so `IsVariableSpeedNormalPath.mono` re-enlarges to one
common pair valid along the whole orbit. -/
theorem ceilings_uniform {ell Q khat kappa2 M Mtot : ℝ}
    (hell : 0 ≤ ell) (hellQ : ell ≤ Q) (hk : 0 ≤ khat) (hk2 : 0 ≤ kappa2)
    (hM : 0 ≤ M) (hMM : M ≤ Mtot) :
    costP1 ell khat M ≤ costP1 Q khat Mtot ∧
      costG1 ell khat kappa2 M ≤ costG1 Q khat kappa2 Mtot := by
  have hP : costP1 ell khat M ≤ costP1 Q khat Mtot :=
    costP1_le hell hellQ hk hM hMM
  refine ⟨hP, ?_⟩
  have hP0 : 0 ≤ costP1 ell khat M := costP1_nonneg hell
  have hsq : costP1 ell khat M ^ 2 ≤ costP1 Q khat Mtot ^ 2 :=
    pow_le_pow_left₀ hP0 hP 2
  have hlin : kappa2 * M ≤ kappa2 * Mtot := mul_le_mul_of_nonneg_left hMM hk2
  have hlin0 : 0 ≤ kappa2 * M := mul_nonneg hk2 hM
  have hsq0 : (0:ℝ) ≤ costP1 ell khat M ^ 2 := by positivity
  rw [costG1, costG1]
  calc costP1 ell khat M ^ 2 * (kappa2 * M)
      ≤ costP1 Q khat Mtot ^ 2 * (kappa2 * M) :=
        mul_le_mul_of_nonneg_right hsq hlin0
    _ ≤ costP1 Q khat Mtot ^ 2 * (kappa2 * Mtot) :=
        mul_le_mul_of_nonneg_left hlin (by positivity)

/-! The uniform `Q` of `ceilings_uniform` may be taken to be the speed ceiling
`P1` of the class: `ArclengthInverse.rearArclength_le_of_period` already shows
the rear period never exceeds the front period, so the periods along the orbit
need no separate argument. -/

end GaugeFlowDerivCost
