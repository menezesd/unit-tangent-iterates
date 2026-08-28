import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

/-! # Presented terminal geometry from recursive exact sidecars -/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareRecursiveAnalyticSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry

variable {p q a b : Data} {Gamma : NormalPath p q}
  {Delta : NormalPath a b}
  {P0 kh khat Qmax periodLower kap khatNext QmaxNext : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}

/-- The recursive wrapper supplies both exact first-order sidecars and the
terminal convexity premise required by the pre-output terminal constructor. -/
theorem RecursiveAnalyticSuccessor.exists_presentedTerminalGeometry_of_spatial
    (X : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext)
    (E : Applied Delta X.source)
    (hd1 : ∀ t, 2 * (Delta.m t / Real.sqrt (1 - kap ^ 2)) *
      GaugeFlowDerivCost.costP1
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod X.source 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
        (∫ s in (0 : ℝ)..Delta.T, X.source.m s) ≤ X.source.m t)
    (hd2 : ∀ t,
      (X.source.Dd t + 2 * (Delta.m t / Real.sqrt (1 - kap ^ 2))) *
          GaugeFlowDerivCost.costP1
            (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod X.source 0)
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
            (∫ s in (0 : ℝ)..Delta.T, X.source.m s) ^ 2 +
        2 * (Delta.m t / Real.sqrt (1 - kap ^ 2)) *
          GaugeFlowDerivCost.costG1
            (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod X.source 0)
            (GaugeMarkedDataOfRearFamily.rearKappa1 kap)
            (GaugeMarkedDataOfRearFamily.rearKappa2 kap)
            (∫ s in (0 : ℝ)..Delta.T, X.source.m s) ≤ X.source.m t)
    (Lmax : ℝ)
    (hperiod : ∀ t,
      FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod X.source t ≤ Lmax) :
    Nonempty (PresentedTerminalGeometry X.source E) :=
  FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.exists_presentedTerminalGeometry_of_spatial
    X.source E
    X.sidecars.regularity X.spatial X.terminalCurvature_nonnegative
    hd1 hd2 Lmax hperiod

/-- The intrinsic tangent range of the constructed terminal is the retained
chosen endpoint range, not merely an unrelated physical presentation. -/
theorem RecursiveAnalyticSuccessor.presented_tangentRange_endpoint
    (X : RecursiveAnalyticSuccessor Delta A periodLower kap khatNext QmaxNext)
    {E : Applied Delta X.source}
    (G : PresentedTerminalGeometry X.source E) :
    range (UnitTangent.unitTangentMap (ev G.presented)) = range b.1 :=
  G.tangent_range.trans X.terminalRange

end FiniteSmoothRearFamilyMarkingAwareRecursivePresentedTerminalGeometry
