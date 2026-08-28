import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometrySchema
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalMarkedFacts

/-! # Split assembly of pre-output terminal geometry -/

noncomputable section

open Function Set MarkedSpace PathMetric RearTrack RearOwnArclength ArclengthInverse

namespace FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareRegularitySum
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  GaugeMarkedDataOfRearFamily

variable {a b : Data} {Gamma : NormalPath a b}
  {P0 kh khat Qmax : ℝ}

theorem exists_presentedTerminalGeometry
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) (S : ExactSidecars A)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s)
    (hnormal : ∀ t, ∀ j ≤ 2, MarkedTopology.supNorm
      (iteratedDeriv j (fun u ↦ rearNormal A t (E.Phi t u))) ≤ A.m t)
    (Lmax : ℝ) (hperiod : ∀ t, rearPeriod A t ≤ Lmax) :
    Nonempty (PresentedTerminalGeometry A E) := by
  obtain ⟨M⟩ := exists_markedTerminal A hK0
  let P := M.physical
  let FK := terminalFrontKinematics A M.presented M.ev_eq M.period_eq hK0
  exact ⟨{
    sidecars := S
    presented := M.presented
    dlt := M.dlt
    dlt_pos := M.dlt_pos
    period_eq := M.period_eq
    carrier := M.carrier
    physical := P
    physical_angle_eq := rfl
    physical_curvature_eq := rfl
    physical_cq_eq := rfl
    physical_dlt_eq := rfl
    physical_dlt_pos := by
      change 0 < M.dlt
      exact M.dlt_pos
    zero_floor_tube := M.tube
    angle_periodic :=
      (MarkingAwareSource.successorFrontCore A).angle_periodic Gamma.T
    curvature_positive := terminalCurvature_positive A hK0
    tube := M.tube
    oval := M.oval
    embedded := M.embedded
    tangent_range := M.tangent_range
    strict := M.strict hK0
    frontData := unitTangentData A
    frontData_eq := rfl
    frontKinematics := FK
    physicalFront := FiniteSmoothRearFamilyPhysicalFront.Certificate.ofSame FK
    front_range := by rw [ev_unitTangentData]
    normal_sup := hnormal
    Lmax := Lmax
    period_le := hperiod
  }⟩

theorem exists_presentedTerminalGeometry_of_spatial
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (E : Applied Gamma A) (S : ExactSidecars A)
    (R : SpatialFrameRegularity Gamma A.Ydot A.Theta A.delta A.sf
      A.P A.m kh Qmax)
    (hK0 : ∀ s, 0 ≤ A.K Gamma.T s)
    (hd1 : ∀ t, 2 * (Gamma.m t / Real.sqrt (1 - kh ^ 2)) *
      GaugeFlowDerivCost.costP1 (rearPeriod A 0)
        (rearKappa1 kh) (∫ s in (0 : ℝ)..Gamma.T, A.m s) ≤ A.m t)
    (hd2 : ∀ t,
      (A.Dd t + 2 * (Gamma.m t / Real.sqrt (1 - kh ^ 2))) *
          GaugeFlowDerivCost.costP1 (rearPeriod A 0)
            (rearKappa1 kh) (∫ s in (0 : ℝ)..Gamma.T, A.m s) ^ 2 +
        2 * (Gamma.m t / Real.sqrt (1 - kh ^ 2)) *
          GaugeFlowDerivCost.costG1 (rearPeriod A 0)
            (rearKappa1 kh) (rearKappa2 kh)
            (∫ s in (0 : ℝ)..Gamma.T, A.m s) ≤ A.m t)
    (Lmax : ℝ) (hperiod : ∀ t, rearPeriod A t ≤ Lmax) :
    Nonempty (PresentedTerminalGeometry A E) :=
  exists_presentedTerminalGeometry A E S hK0
    (E.normal_sup_of_spatial R hd1 hd2) Lmax hperiod

end FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
