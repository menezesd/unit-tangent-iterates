import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
import UnitTangentIterates.VariableMarkedTube

/-! # Physical interfaces of a presented terminal geometry

This module is an independent, non-recursive adapter.  It exposes the exact
single-edge physical data retained by `PresentedTerminalGeometry`; an
all-depth `FinitePullbackPhysicalRearKinematics` requires a compatible grid of
such edges and therefore cannot be manufactured from one terminal alone.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwarePresentedTerminalPhysicalAdapter

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

variable {a b : Data} {Gamma : NormalPath a b}
  {P0 kh khat Qmax : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- The ordinary zero-floor tube retained by the presented rear. -/
def ordinaryTube (G : PresentedTerminalGeometry A E) :
    IsTubeMember G.physical.cq 0 G.physical.dlt G.presented :=
  G.zero_floor_tube

/-- The same rear as a variable-speed tube member.  The upper speed is its
marked perimeter, exactly as in `VariableMarkedTube.ofTubeMember`. -/
def variableTube (G : PresentedTerminalGeometry A E) :
    VariableMarkedTube.IsVariableTubeMember G.physical.cq
      (perim G.presented) 0 G.physical.dlt G.presented :=
  VariableMarkedTube.ofTubeMember G.zero_floor_tube

/-- Since the presented rear has perimeter `physical.cq`, both variable-speed
bounds can be written using the same retained constant. -/
def variableTubePhysicalSpeed (G : PresentedTerminalGeometry A E) :
    VariableMarkedTube.IsVariableTubeMember G.physical.cq G.physical.cq
      0 G.physical.dlt G.presented := by
  have hper : perim G.presented = G.physical.cq :=
    G.period_eq.trans G.physical_cq_eq.symm
  simpa [hper] using variableTube G

/-- Exact single-edge kinematics with the canonical front data. -/
def canonicalKinematics (G : PresentedTerminalGeometry A E) :
    PhysicalRearLimitKinematics kh G.presented G.frontData :=
  G.frontKinematics

/-- The independently retained physical-front certificate. -/
def retainedPhysicalFront (G : PresentedTerminalGeometry A E) :
    FiniteSmoothRearFamilyPhysicalFront.Certificate kh G.presented G.frontData :=
  G.physicalFront

/-- The retained certificate's ordinary physical representative has the same
range as the terminal source front. -/
theorem retainedPhysicalFront_range_source
    (G : PresentedTerminalGeometry A E) :
    range (ev G.physicalFront.physicalFront) = range (A.F Gamma.T) :=
  G.physicalFront.range_eq.symm.trans G.front_range

/-- The canonical marked front itself has the terminal source range. -/
theorem canonicalFront_range_source
    (G : PresentedTerminalGeometry A E) :
    range (ev G.frontData) = range (A.F Gamma.T) :=
  G.front_range

/-- Link the canonical front to the raw marked endpoint range whenever the
source package supplies its endpoint identification. -/
theorem canonicalFront_range_endpoint
    (G : PresentedTerminalGeometry A E)
    (hterminal : range (A.F Gamma.T) = range (b.1 : ℝ → ℂ)) :
    range (ev G.frontData) = range (b.1 : ℝ → ℂ) :=
  G.front_range.trans hterminal

/-- The retained ordinary physical front has the same raw endpoint range. -/
theorem retainedPhysicalFront_range_endpoint
    (G : PresentedTerminalGeometry A E)
    (hterminal : range (A.F Gamma.T) = range (b.1 : ℝ → ℂ)) :
    range (ev G.physicalFront.physicalFront) = range (b.1 : ℝ → ℂ) :=
  (retainedPhysicalFront_range_source G).trans hterminal

/-- Upgrade raw endpoint-range identification to the exact downstream
`Certificate`.  Nonzero endpoint perimeter is necessary because `ev b`
rescales the raw marked curve by `perim b`. -/
def endpointPhysicalFront
    (G : PresentedTerminalGeometry A E) (hbperim : perim b ≠ 0)
    (hterminal : range (A.F Gamma.T) = range (b.1 : ℝ → ℂ)) :
    FiniteSmoothRearFamilyPhysicalFront.Certificate kh G.presented b where
  physicalFront := G.physicalFront.physicalFront
  range_eq :=
    (range_ev_of_perim_ne_zero hbperim).trans
      (hterminal.symm.trans (retainedPhysicalFront_range_source G).symm)
  kinematics := G.physicalFront.kinematics

/-- A tube certificate on the marked endpoint supplies the nonzero-perimeter
hypothesis required by `endpointPhysicalFront`. -/
def endpointPhysicalFrontOfTube
    (G : PresentedTerminalGeometry A E) {c kmin dlt : ℝ} (hc : 0 < c)
    (hb : IsTubeMember c kmin dlt b)
    (hterminal : range (A.F Gamma.T) = range (b.1 : ℝ → ℂ)) :
    FiniteSmoothRearFamilyPhysicalFront.Certificate kh G.presented b :=
  endpointPhysicalFront G (ne_of_gt (perim_pos hc hb)) hterminal

/-- Full physical stage components for the canonical edge, once its front
has the ordinary tube membership required by the existing constructor. -/
def canonicalStageComponents
    (G : PresentedTerminalGeometry A E) {c dlt : ℝ} (hc : 0 < c)
    (hfront : IsTubeMember c 0 dlt G.frontData) :
    PhysicalRearLimitStageComponents G.presented G.frontData :=
  G.frontKinematics.toStageComponents A.kh_nonnegative A.kh_lt_one hc hfront

/-- Full physical stage components for the retained ordinary representative. -/
def retainedStageComponents
    (G : PresentedTerminalGeometry A E) {c dlt : ℝ} (hc : 0 < c)
    (hfront : IsTubeMember c 0 dlt G.physicalFront.physicalFront) :
    PhysicalRearLimitStageComponents G.presented G.physicalFront.physicalFront :=
  G.physicalFront.kinematics.toStageComponents
    A.kh_nonnegative A.kh_lt_one hc hfront

end FiniteSmoothRearFamilyMarkingAwarePresentedTerminalPhysicalAdapter
