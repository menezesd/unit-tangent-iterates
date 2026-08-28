import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry

/-! # Automatic terminal geometry for composition-stable recursive sources -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedTerminalGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry
  FiniteSmoothRearFamilyMarkingAwareCompositionRecursiveAnalyticSuccessor

variable {p q a b : Data} {Gamma : NormalPath p q}
  {Delta : NormalPath a b}
  {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}

/-- No rowwise `hd1`/`hd2` callback remains: both are retained by the scaled
recursive source itself. -/
theorem CompositionRecursiveAnalyticSuccessor.exists_presentedTerminalGeometry
    (X : CompositionRecursiveAnalyticSuccessor Delta A periodLower kap
      khatNext QmaxNext)
    (E : Applied Delta X.source)
    (Lmax : ℝ)
    (hperiod : ∀ t, rearPeriod X.source t ≤ Lmax) :
    Nonempty (PresentedTerminalGeometry X.source E) :=
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry.RecursiveAnalyticSuccessor.exists_presentedTerminalGeometry_of_spatial
      X.toRecursiveAnalyticSuccessor E X.composition_d1 X.composition_d2
      Lmax hperiod

end FiniteSmoothRearFamilyMarkingAwareCompositionRecursivePresentedTerminalGeometry
