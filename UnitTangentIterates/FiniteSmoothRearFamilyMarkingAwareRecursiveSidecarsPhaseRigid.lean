import UnitTangentIterates.MarkingAwareSourcePhaseRigidTransport
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars

/-! # Phase-rigid transport of fresh recursive sidecars -/

noncomputable section

open MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareRecursiveSidecarsPhaseRigid

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorSelectionBounds
  FiniteSmoothRearFamilyMarkingAwareRecursiveExactSidecars

/-- Fresh selection bounds are invariant under the marking-only phase/rigid
normalization because all fields defining the intrinsic successor front are
definitionally unchanged. -/
def SelectionBounds.phaseRigid
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (S : SelectionBounds A)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    SelectionBounds (A.phaseRigid phase a w hw) := by
  exact
    { periodLower := S.periodLower
      periodUpper := S.periodUpper
      Md := S.Md
      MP := S.MP
      periodLower_pos := S.periodLower_pos
      period_lower := S.period_lower
      period_upper := S.period_upper
      Md_nonnegative := S.Md_nonnegative
      MP_nonnegative := S.MP_nonnegative
      normalizedCurvatureTime_le := S.normalizedCurvatureTime_le
      periodTime_le := S.periodTime_le }

/-- Transport the strengthened exact package through the same normalization. -/
def RecursiveExactSidecars.phaseRigid
    {p q : Data} {Gamma : NormalPath p q} {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (S : RecursiveExactSidecars A)
    (phase : ℝ) (a w : ℂ) (hw : ‖w‖ = 1) :
    RecursiveExactSidecars (A.phaseRigid phase a w hw) :=
  RecursiveExactSidecars.ofSource _
    (SelectionBounds.phaseRigid A S.selection phase a w hw)

end FiniteSmoothRearFamilyMarkingAwareRecursiveSidecarsPhaseRigid
