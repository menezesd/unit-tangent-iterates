import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierNormalizedLayer
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierRowBudget
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedOuterTubeStep
import UnitTangentIterates.ConfiguredRecursiveEdgePhysicalBaseFinalTailState

/-!
# Outer distance induction for multiplier-aware diagonal layers

The recursive geometric invariant needs a common tube for the newly displayed
row.  That tube is not an analytic input: it follows from the finite prefix of
the already-public cell errors and the final configured row budget.
-/

noncomputable section

open Function Set MarkedSpace PathMetric
open scoped BigOperators

namespace ConfiguredRecursiveEdgeRecostMultiplierOuterLayer

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierNormalizedLayer
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeRecostedOuterTubeStep
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep

def accumulated
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O)
    (n k : ℕ) : ℝ :=
  Finset.sum (Finset.range k) (fun j ↦ R.error n j)

@[simp] theorem accumulated_zero
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n : ℕ) :
    accumulated R n 0 = 0 := by
  simp [accumulated]

theorem accumulated_succ
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O) (n k : ℕ) :
    accumulated R n (k + 1) = accumulated R n k + R.error n k := by
  simp [accumulated, Finset.sum_range_succ]

/-- A diagonal normalized layer together with its exact distance from the
fixed physical row model. -/
structure Layer
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} (R : RecostClosingOutput J O)
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1geom G1 Cg Cprof Qmax : ℕ → ℝ}
    {kappaHat c dlt : ℝ}
    (stateP1 defect : ℕ → ℝ)
    (X : ConfiguredRecursiveEdgeRecostedGeometricState.State
      Q e P0 P1geom G1 Cg Cprof Qmax kappaHat c dlt
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh) where
  normalized : ConfiguredRecursiveEdgeRecostMultiplierNormalizedLayer.Layer
    (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R)
      stateP1 defect X
  dist_le : ∀ n,
    dist (base R n) (X.stage n).displayed ≤ accumulated R n X.depth

namespace Layer

noncomputable def ofBase
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} {R : RecostClosingOutput J O}
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1geom G1 Cg Cprof Qmax : ℕ → ℝ}
    {kappaHat c dlt : ℝ} {stateP1 defect : ℕ → ℝ}
    {X : ConfiguredRecursiveEdgeRecostedGeometricState.State
      Q e P0 P1geom G1 Cg Cprof Qmax kappaHat c dlt
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh}
    (N : ConfiguredRecursiveEdgeRecostMultiplierNormalizedLayer.Layer
      (ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R)
        stateP1 defect X)
    (hdepth : X.depth = 0)
    (hdisplayed : ∀ n, (X.stage n).displayed = base R n) :
    Layer R stateP1 defect X where
  normalized := N
  dist_le n := by
    rw [hdisplayed n, hdepth]
    simp [accumulated]

noncomputable def next
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} {R : RecostClosingOutput J O}
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1geom G1 Cg Cprof Qmax : ℕ → ℝ}
    {kappaHat c dlt : ℝ} {stateP1 defect : ℕ → ℝ}
    {X : ConfiguredRecursiveEdgeRecostedGeometricState.State
      Q e P0 P1geom G1 Cg Cprof Qmax kappaHat c dlt
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh}
    (L : Layer R stateP1 defect X)
    (G : StepInput X)
    (hE : ConfiguredRecursiveEdgeFinitePresentedFinalAssembly.distortionTotal ≤
      1 / 8)
    (hcur : ∀ n,
      (G.scaled n).eps ≤
        ((ConfiguredRecursiveEdgePhysicalBaseFinalTailState.finalGaugeOutput R).shiftOutput
          (n + 1 + X.depth)).major (X.depth + 1))
    (hupper : ∀ n,
      (G.scaled n).slice.periodUpper ≤ stateP1 (n + 1 + X.depth))
    (hstep : ∀ n,
      dist (X.stage n).displayed (G.next.stage n).displayed ≤
        R.error n X.depth) :
    Layer R stateP1 defect G.next where
  normalized := L.normalized.next G hE hcur hupper
  dist_le n := by
    have H := dist_next_le_prefix_add (L.dist_le n) (hstep n)
    simpa [StepInput.next,
      ConfiguredRecursiveEdgeRecostedGeometricState.State.next,
      accumulated_succ] using H

/-- The exact common-tube certificate supplied to `CoherenceCore.toStepInput`.
The local differential facts belong to the theorem-produced mapped initial;
the radius estimate is completely configured. -/
theorem mappedInitialTube
    {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
      ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
      ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
    {O : GaugeOutput J} {R : RecostClosingOutput J O}
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1geom G1 Cg Cprof Qmax : ℕ → ℝ}
    {kappaHat c dlt : ℝ} {stateP1 defect : ℕ → ℝ}
    {X : ConfiguredRecursiveEdgeRecostedGeometricState.State
      Q e P0 P1geom G1 Cg Cprof Qmax kappaHat c dlt
        ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh}
    (B : BudgetType R) (L : Layer R stateP1 defect X)
    (G : StepInput X) (n : ℕ)
    (hmodel : IsTubeMember
      (2 * R.data.Hs 0) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model) (base R n))
    (hmodel_acc : ∀ u, ‖(base R n).2.2 u‖ ≤
      ConfiguredInductiveTubeBudget.accBound R.data.model n)
    (hcurve : ∀ u, HasDerivAt (⇑(G.next.stage n).displayed.1)
      ((G.next.stage n).displayed.2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑(G.next.stage n).displayed.2.1)
      ((G.next.stage n).displayed.2.2 u) u)
    (hperiodic : Function.Periodic (⇑(G.next.stage n).displayed.1) 1)
    (hcurvature : ∀ u, 0 ≤ ((starRingEnd ℂ)
      ((G.next.stage n).displayed.2.1 u) *
        (G.next.stage n).displayed.2.2 u).im)
    (hstep : dist (X.stage n).displayed (G.next.stage n).displayed ≤
      R.error n X.depth) :
    VariableMarkedTube.IsVariableTubeMember
      (R.data.Hs 0) (upper R n) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (G.next.stage n).displayed := by
  apply variableTube_next_of_rowBudget B n hmodel hmodel_acc hcurve hvel
    hperiodic hcurvature (L.dist_le n) hstep
  exact error_prefix_add_step_le_radius R n X.depth

end Layer

end ConfiguredRecursiveEdgeRecostMultiplierOuterLayer
