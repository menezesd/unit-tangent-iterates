import UnitTangentIterates.ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts

/-!
# Automatic row facts for configured exact edge sources

This file discharges the functional and terminal-perimeter facts that follow
intrinsically from the exact configured edge source.  It also records the
cost-based form of the component estimate, which avoids treating a previously
period-scaled recursive bound as an unscaled path cost.
-/

open MarkedSpace PathMetricCircle
open ConfiguredCombinedPhysicalDiagonalLargeSeparation
open ConfiguredBaseProfiledEdgeSourceFamily
open ConfiguredBaseProfiledEdgeExactAnalyticSuccessorFamily
open FiniteSmoothRearFamilyMarkingAwareSource
open FiniteSmoothRearFamilyMarkingAwareAppliedSource
open FiniteSmoothRearFamilyMarkingAwareChosenTerminal
open FiniteSmoothRearFamilyMarkingAwareConfiguredTransition
open FiniteSmoothRearFamilyMarkingAwareAutomaticRowFacts
open FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts
open PhysicalArclengthJacobiTransition EnrichedPhysicalChosenRichFamily

namespace ConfiguredRecursiveEdgeExactAutomaticRowFacts

noncomputable section

variable {MA NA : ℝ}

/-- The physical front period of every exact edge source is large enough for
the fixed selected-inverse strip constant. -/
theorem edge_front_period_scale_one
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    (t : ℝ) :
    1 ≤ Real.sqrt (1 - sourceKh ^ 2) * (edgeSourceFamily O n).P t := by
  rw [edgeSource_period_eq O n]
  simp only [ConfiguredBaseInterpolationShiftedFront.period]
  have hH : 1 ≤ (data O).Hs (n + 1) :=
    O.large.separation_one.trans ((data O).separation_lower (n + 1))
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt (1 - sourceKh ^ 2) := by
    rw [sourceKh_eq]
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  have hs0 : 0 ≤ Real.sqrt (1 - sourceKh ^ 2) := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hH)]

/-- Functional facts for any chosen terminal produced from the configured
exact edge source. -/
def edgeFunctionalFacts
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    {E : Applied (edgeOutput O (n + 1)).increment (edgeSourceFamily O n)}
    {a base : MarkedSpace.Data} {bound : ℝ}
    {B : TerminalInput (p := a) (base := base) (bound := bound) E}
    (R : Output E B) : FunctionalFacts R :=
  ChosenPath.functionalFacts_of_exactSource R
    (edgeOutput O (n + 1)).increment_functional

/-- Every terminal attached to an exact edge source has physical perimeter at
least one. -/
theorem edgeTerminal_perim_ge_one
    (O : ConfiguredRecursiveEdgeSourceP0ScalarStart.Output MA NA) (n : ℕ)
    {E : Applied (edgeOutput O (n + 1)).increment (edgeSourceFamily O n)}
    {a base : MarkedSpace.Data} {bound : ℝ}
    (B : TerminalInput (p := a) (base := base) (bound := bound) E) :
    1 ≤ perim base :=
  terminal_perim_ge_one_of_front_period B
    (edge_front_period_scale_one O n
      (edgeOutput O (n + 1)).increment.T)

/-- Component control in terms of the chosen path's actual cost.  This is the
correct interface when the recursive `bound` has already been multiplied by
the physical period. -/
def components_bound_of_chosen_cost
    {p q a base : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
    {P0 kh khat Qmax bound : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    {B : TerminalInput (p := a) (base := base) (bound := bound) E}
    (O : Output E B) (F : FunctionalFacts O)
    {P diagonal : ℝ} (hGammaT : Gamma.T = 1) (hP : 1 ≤ P)
    (hcost : P * O.chosen.Delta.cost ≤ diagonal) :
    ComponentBound (components P O.chosen.Delta.eta) diagonal := by
  apply componentBound_mono
    (ComponentBound.of_cost O.chosen.Delta
      (O.chosen.time_eq.trans hGammaT) F.rear hP le_rfl)
  exact hcost

end

end ConfiguredRecursiveEdgeExactAutomaticRowFacts
