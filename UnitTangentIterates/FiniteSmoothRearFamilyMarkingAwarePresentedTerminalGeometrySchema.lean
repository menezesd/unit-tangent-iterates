import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalFrontData
import UnitTangentIterates.FiniteSmoothRearFamilyPhysicalFront

/-! # Public schema of pre-output presented terminal geometry -/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength

namespace FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareRegularitySum

variable {a b : Data} {Gamma : NormalPath a b}
  {P0 kh khat Qmax : ℝ}

/-- The complete terminal geometry available before choosing a long-theorem
`Output`.  Its physical successor is the canonical marked unit-tangent data,
not an arbitrary endpoint presentation. -/
structure PresentedTerminalGeometry
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) where
  sidecars : ExactSidecars A
  presented : Data
  dlt : ℝ
  dlt_pos : 0 < dlt
  period_eq : perim presented = terminalPeriod A
  carrier : ∀ x, presented.1 (x / perim presented) = terminalCurve A x
  physical : ConfiguredGaugeEndpointDefect.TerminalPhysicalFacts presented
  physical_angle_eq : physical.Theta = terminalAngle A
  physical_curvature_eq : physical.curvature = terminalCurvature A
  physical_cq_eq : physical.cq = terminalPeriod A
  physical_L_eq : physical.L = terminalPeriod A
  physical_kb_eq : physical.kb = GaugeMarkedDataOfRearFamily.rearKappa1 kh
  physical_kL_eq : physical.kL = A.kx
  physical_dlt_eq : physical.dlt = dlt
  physical_dlt_pos : 0 < physical.dlt
  zero_floor_tube : IsTubeMember physical.cq 0 physical.dlt presented
  angle_periodic : ∀ x, terminalAngle A (x + terminalPeriod A) =
    terminalAngle A x + 2 * Real.pi
  curvature_positive : ∀ x, 0 < terminalCurvature A x
  tube : IsTubeMember (terminalPeriod A) 0 dlt presented
  oval : MainTheoremConditional.IsOval (ev presented)
  embedded : InjOn (ev presented) (Ico 0 (terminalPeriod A))
  tangent_range : range (UnitTangent.unitTangentMap (ev presented)) =
    range (A.F Gamma.T)
  strict : UnconditionalAssembly.LimitStrictnessDataH presented
  frontData : Data
  frontData_eq : frontData = unitTangentData A
  frontKinematics : PhysicalRearLimitKinematics kh presented frontData
  physicalFront : FiniteSmoothRearFamilyPhysicalFront.Certificate kh
    presented frontData
  front_range : range (ev frontData) = range (A.F Gamma.T)
  normal_sup : ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
    (iteratedDeriv j (fun u ↦ rearNormal A t (E.Phi t u))) ≤ A.m t
  Lmax : ℝ
  period_le : ∀ t, rearPeriod A t ≤ Lmax

end FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
