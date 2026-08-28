import UnitTangentIterates.RichStageBoundMonotonicity

/-!
# Monotonicity in the analytic curvature ceiling

The configured interpolation is certified with its canonical `kstar`, while
recursive selected-rear paths use a larger analytic ceiling.  This adapter
enlarges all coupled variable-speed bounds without changing the path.
-/

noncomputable section

open MarkedSpace PathMetric

namespace NormalPathC2IncrementVariableSpeed

/-- Simultaneously enlarge the speed, curvature, speed-derivative, and mixed
ceilings in a variable-speed normal-path certificate. -/
theorem IsVariableSpeedNormalPath.monoAnalytic
    {p q : Data} {P0 P1 P1' khat khat' G1 G1' Cg Cg' : ℝ}
    (Gamma : NormalPath p q)
    (h : IsVariableSpeedNormalPath P0 P1 khat G1 Cg Gamma)
    (hP10 : 0 ≤ P1) (hkhat0 : 0 ≤ khat)
    (hP1 : P1 ≤ P1') (hkhat : khat ≤ khat')
    (hG1 : G1 ≤ G1') (hCg : Cg ≤ Cg') :
    IsVariableSpeedNormalPath P0 P1' khat' G1' Cg' Gamma := by
  obtain ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn, hgub, hguB, hkap,
    hXu, hgud, hthetau, hgt, hgtc, hgtbd, hgut, hgutc, hgutbd,
    hthetat, hetasc, hetas, hkappat, hktc, hkt⟩ := h
  have hP1'0 : 0 ≤ P1' := hP10.trans hP1
  have hkhat'0 : 0 ≤ khat' := hkhat0.trans hkhat
  refine ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn,
    (fun t u => (hgub t u).trans hP1),
    (fun t u => (hguB t u).trans hG1),
    (fun t u => (hkap t u).trans hkhat), hXu, hgud, hthetau,
    hgt, hgtc, ?_, hgut, hgutc, ?_, hthetat, hetasc, hetas,
    hkappat, hktc, ?_⟩
  · intro t u
    refine (hgtbd t u).trans (mul_le_mul_of_nonneg_right ?_ (Gamma.m_nonneg t))
    exact mul_le_mul hkhat hP1 hP10 hkhat'0
  · intro t u
    exact (hgutbd t u).trans
      (mul_le_mul_of_nonneg_right hCg (Gamma.m_nonneg t))
  · intro t u
    refine (hkt t u).trans (mul_le_mul_of_nonneg_right ?_ (Gamma.m_nonneg t))
    have hsquare : khat ^ 2 ≤ khat' ^ 2 := by nlinarith
    linarith

end NormalPathC2IncrementVariableSpeed

namespace TriangularMarkedRecursiveChoiceVariableTerminalConstructor

open GaugeRearFamilyVariableTerminal
open NormalPathC2IncrementVariableSpeed

/-- Enlarge every analytic upper bound stored by a rich stage, including the
curvature ceiling. -/
def RichStageData.monoAnalytic
    {p front rear : Data}
    {bound bound' P0 P1 P1' khat khat' G1 G1' Cg Cg' c C dlt : ℝ}
    (S : RichStageData p front rear bound P0 P1 khat G1 Cg c C dlt)
    (hP10 : 0 ≤ P1) (hkhat0 : 0 ≤ khat)
    (hbound : bound ≤ bound') (hP1 : P1 ≤ P1')
    (hkhat : khat ≤ khat') (hG1 : G1 ≤ G1') (hCg : Cg ≤ Cg') :
    RichStageData p front rear bound' P0 P1' khat' G1' Cg' c C dlt where
  stage :=
    { increment := S.stage.increment
      increment_geometry := S.stage.increment_geometry.monoAnalytic
        S.stage.increment hP10 hkhat0 hP1 hkhat hG1 hCg
      increment_cost := S.stage.increment_cost.trans hbound
      rear_curve_deriv := S.stage.rear_curve_deriv
      rear_vel_deriv := S.stage.rear_vel_deriv
      rear_periodic := S.stage.rear_periodic
      rear_curvature_nonnegative := S.stage.rear_curvature_nonnegative
      range_edge := S.stage.range_edge
      rear_harnack := S.stage.rear_harnack }
  terminalBase := S.terminalBase
  lambda := S.lambda
  Lambda := S.Lambda
  marking := S.marking

end TriangularMarkedRecursiveChoiceVariableTerminalConstructor

