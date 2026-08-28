import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenCanonicalEndpointCap
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
import UnitTangentIterates.NormalizedSteeringPhysicalRescaling

/-!
# Canonical selected-inverse endpoint target of a geometric presented row

The retained physical rear kinematics contain the complete marked selected
inverse equations.  Packaging those equations and applying weak-strip
uniqueness identifies the row's ordinary presented terminal exactly with the
canonical selected inverse of its retained ordinary front datum.  Thus the
canonical endpoint-cap target has phase zero; no equality is inferred merely
from equality of ranges.
-/

noncomputable section

open Set Function MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareGeometricRowCanonicalEndpointCap

open FiniteSmoothRearFamilyMarkingAwareChosenCanonicalEndpointCap
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  NormalizedSteeringPhysicalRescaling

/-- Physical rear kinematics, together with ordinary tube witnesses at both
ends, are a marked selected-inverse witness. -/
theorem isMarkedSelectedInverse_of_physicalKinematics
    {kh cF kF dF cR kR dR : ℝ} {rear front : Data}
    (K : PhysicalRearLimitKinematics kh rear front)
    (hcF : 0 < cF) (hfront : IsTubeMember cF kF dF front)
    (hrear : IsTubeMember cR kR dR rear) :
    SelectedInverseMap.IsMarkedSelectedInverse kh front rear := by
  have hP : 0 < perim front := perim_pos hcF hfront
  refine ⟨⟨cR, kR, dR, hrear⟩,
    thetaPhys K.steering (perim front) K.theta0,
    curvaturePhys K.steering (perim front),
    deltaPhys K.steering (perim front), K.sf,
    K.front_frenet, ?_, deltaPhys_periodic K.steering,
    deltaPhys_mem K.steering, ?_, K.arclength_rightInverse,
    K.rear_perimeter, K.rear_track⟩
  · exact hasDerivAt_thetaPhys K.steering K.curvature_continuous
  · exact hasDerivAt_deltaPhys K.steering hP

/-- Weak-strip uniqueness fixes the complete normalized arclength marking,
not just the curve image. -/
theorem rear_eq_selInv_of_physicalKinematics
    {kh cF kF dF cR kR dR : ℝ} {rear front : Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (K : PhysicalRearLimitKinematics kh rear front)
    (hcF : 0 < cF) (hfront : IsTubeMember cF kF dF front)
    (hrear : IsTubeMember cR kR dR rear) :
    rear = SelectedInverseMap.selInv kh front := by
  exact SelectedInverseMap.eq_selInv_of_isMarkedSelectedInverse
    hcF hkh0 hkh1 hfront
      (isMarkedSelectedInverse_of_physicalKinematics K hcF hfront hrear)

variable
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
    {P0 P1 khat G1 Cg C kh Qmax : ℕ → ℝ} {c dlt : ℝ}
    {S : GeometricCorrelatedColumn Q current e k P0 P1 khat G1 Cg C
      c dlt kh Qmax}

/-- The actual theorem-produced geometric row has the canonical selected
inverse of its retained ordinary front as its phase-zero endpoint-cap target. -/
noncomputable def phaseCanonicalTarget
    (R : GeometricPresentedRowSelection (n := n) S)
    (hkh0 : 0 ≤ kh n) (hkh1 : kh n < 1)
    {cF kF dF : ℝ} (hcF : 0 < cF)
    (hfront : IsTubeMember cF kF dF R.terminalInput.frontData) :
    PhaseCanonicalTarget R.output
      (SelectedInverseMap.selInv (kh n) R.terminalInput.frontData) where
  phase := 0
  base_eq := by
    rw [MarkedShift.shiftData_zero]
    exact rear_eq_selInv_of_physicalKinematics hkh0 hkh1
      R.output.frontKinematics hcF hfront R.terminalInput.zero_floor_tube

/-- Direct row-cap form against the literal canonical selected inverse. -/
theorem endpoint_dist_le_selInv
    (R : GeometricPresentedRowSelection (n := n) S)
    (hkh0 : 0 ≤ kh n) (hkh1 : kh n < 1)
    {cF kF dF : ℝ} (hcF : 0 < cF)
    (hfront : IsTubeMember cF kF dF R.terminalInput.frontData) :
    dist R.output.jets.rear
        (SelectedInverseMap.selInv (kh n) R.terminalInput.frontData) ≤
      exactEndpointCap R.output := by
  simpa [phaseCanonicalTarget] using
    (phaseCanonicalTarget R hkh0 hkh1 hcF hfront).endpoint_dist_le

/-- Coefficient-times-diagonal form consumed by the finite pullback capstone. -/
theorem endpoint_dist_le_coefficient_mul_diagonal
    (R : GeometricPresentedRowSelection (n := n) S)
    (hkh0 : 0 ≤ kh n) (hkh1 : kh n < 1)
    {cF kF dF M coefficient diagonal : ℝ}
    (hcF : 0 < cF)
    (hfront : IsTubeMember cF kF dF R.terminalInput.frontData)
    (hM : 0 ≤ M) (hL : 0 ≤ R.terminalInput.physical.L)
    (hkb : 0 ≤ R.terminalInput.physical.kb)
    (hkL : 0 ≤ R.terminalInput.physical.kL)
    (hcostM : R.output.chosen.Delta.cost ≤ M)
    (hcoefficient :
      InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
        R.terminalInput.Lmax (rearPeriod (S.source n) 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 (kh n))
        (GaugeMarkedDataOfRearFamily.rearKappa2 (kh n)) M
        R.terminalInput.physical.L R.terminalInput.physical.kb
        R.terminalInput.physical.kL ≤ coefficient)
    (hcostDiagonal : R.output.chosen.Delta.cost ≤ diagonal) :
    dist R.output.jets.rear
        (SelectedInverseMap.selInv (kh n) R.terminalInput.frontData) ≤
      coefficient * diagonal := by
  simpa [phaseCanonicalTarget] using
    FiniteSmoothRearFamilyMarkingAwareChosenCanonicalEndpointCap.PhaseCanonicalTarget.endpoint_dist_le_coefficient_mul_diagonal
      (phaseCanonicalTarget R hkh0 hkh1 hcF hfront)
      hM hL hkb hkL hcostM hcoefficient hcostDiagonal

end FiniteSmoothRearFamilyMarkingAwareGeometricRowCanonicalEndpointCap
