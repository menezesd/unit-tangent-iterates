import UnitTangentIterates.NormalPathC2IncrementVariableSpeed
import UnitTangentIterates.ConstantSpeedPathDist

/-!
# Constant speed is variable speed with vanishing `u`-derivatives
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Function MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2Increment NormalPathC2IncrementVariableSpeed

namespace NormalPathC2IncrementVariableSpeed

variable {p q : Data} {P0 P1 khat : ℝ}

/-- **The constant-speed class embeds in the variable-speed class**, with both
`u`-derivative ceilings equal to zero.  This is the compatibility the closing
chain needs: `GaugeRearFamilyFromFront` produces an
`IsVariableSpeedNormalPath`, while `hmap` is stated with
`IsConstantSpeedNormalPath`, and the two must live in one class for the
pullback iteration to compose. -/
theorem IsConstantSpeedNormalPath.toVariableSpeed (Γ : NormalPath p q)
    (h : IsConstantSpeedNormalPath P0 P1 khat Γ) :
    IsVariableSpeedNormalPath P0 P1 khat 0 0 Γ := by
  obtain ⟨P, Pd, theta, kappa, etas, kt, hPnn, hPub, hkap, hXu, hthetau, hPd,
    hPdc, hPdbd, hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := h
  refine ⟨fun t _ => P t, fun _ _ => 0, fun t _ => Pd t, fun _ _ => 0,
    theta, kappa, etas, kt,
    fun t _ => hPnn t, fun t _ => hPub t, fun _ _ => by simp, hkap, hXu,
    fun t u => hasDerivAt_const u (P t), hthetau,
    fun t _ => hPd t, fun _ => hPdc, fun t _ => hPdbd t,
    fun t u => hasDerivAt_const t (0:ℝ), fun _ => continuous_const,
    fun t _ => by simpa using mul_nonneg (le_refl (0:ℝ)) (Γ.m_nonneg t),
    hthetat, hetasc, hetas, hkappat, hktc, hkt⟩

/-- Hence any bound proved for the variable-speed class applies to
constant-speed paths, with `G1 = Cg = 0`. -/
theorem isVariableSpeed_of_constantSpeed_mono (Γ : NormalPath p q)
    (h : IsConstantSpeedNormalPath P0 P1 khat Γ) (hk : 0 ≤ khat)
    {G1 Cg : ℝ} (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) :
    IsVariableSpeedNormalPath P0 P1 khat G1 Cg Γ :=
  (IsConstantSpeedNormalPath.toVariableSpeed Γ h).mono Γ hk (le_refl _) hG1 hCg

end NormalPathC2IncrementVariableSpeed
