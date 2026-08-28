import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedScaledGeometricStep

/-!
# Tail bridge from the global geometric column to intrinsic diagonal nodes

The global column must not be reindexed as a dependent source family.  This
module instead selects each global row and rebuilds only the lightweight
unary stage at that row.  The source itself is reused without transport.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostMultiplierIntrinsicTailBridge

open ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicDiagonalRows
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicReachableLayer
  ConfiguredRecursiveEdgeRecostMultiplierIntrinsicStepAssembly
  ConfiguredRecursiveEdgeRecostedGeometricState
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry
  ConfiguredRecursiveEdgeRecostedScaledGeometricStep
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow

variable {J : ConfiguredRecursiveEdgeSourceP0RowJetTail.RowJetScalarOutput
    ConfiguredRecursiveSourceP0FixedDistortion.choice.MA0
    ConfiguredRecursiveSourceP0FixedDistortion.choice.NA0}
  {O : GaugeOutput J} (R : RecostClosingOutput J O)

abbrev P0Profile : ℕ → ℝ := fun q ↦
  ConfiguredRecursiveEdgeSourceP0.edgeSourceP0
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) q

abbrev QmaxProfile : ℕ → ℝ := fun q ↦
  ConfiguredRecursiveEdgeSourceP0.edgeSpeedCap
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar) q

def tailRow (n : ℕ) : ℕ := R.totalShift + n

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P1 G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  (X : State Q e (P0Profile (J := J)) P1 G1 Cg C
    (QmaxProfile (J := J))
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
      (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
    c dlt ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh)

/-- Exact global row `totalShift+n`, presented as an intrinsic unary node. -/
noncomputable def node (n : ℕ) : Node where
  P0 := P0Profile (J := J) (tailRow R n + X.depth)
  khat := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
    (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
  Qmax := QmaxProfile (J := J) (tailRow R n + X.depth)
  stage :=
    { start := X.column.pathStart (tailRow R n)
      rear := X.column.pathEnd (tailRow R n)
      Gamma := X.column.path (tailRow R n)
      source := X.column.source (tailRow R n)
      applied := applied X.invariant (tailRow R n)
      displayed := X.column.initial (tailRow R n) }

@[simp] theorem node_displayed (n : ℕ) :
    (node R X n).stage.displayed = X.column.initial (tailRow R n) := rfl

/-- Canonical theorem-produced geometry, with no source cast. -/
noncomputable def geometric (n : ℕ) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.GeometricInput
      (node R X n).stage where
  base := (geometry X.invariant (tailRow R n)).presented
  bound := e (tailRow R n) (X.depth + 1)
  terminal := terminalInput X.invariant (tailRow R n)
  output := output X.invariant (tailRow R n)

noncomputable def pre
    (G : StepInput X) (n : ℕ) :
    ConfiguredRecursiveEdgeRecostedPreCarrier.Core (node R X n).stage where
  geometric := geometric R X n
  eta_continuous := (G.regularity (tailRow R n)).eta_continuous
  eta1_continuous := (G.regularity (tailRow R n)).eta1_continuous
  eta2_continuous := (G.regularity (tailRow R n)).eta2_continuous
  time_one := (G.regularity (tailRow R n)).time_one

/-- The configured canonical row supplies its raw metric package. -/
noncomputable def rawMetric (G : StepInput X) (n : ℕ) :
    RawMetricGeometry.Bounded (pre R X G n).geometric := by
  let q := tailRow R n
  let A := G.rowBounds.row q
  let c0 := Classical.choose (X.invariant.initialOrdinaryTube q)
  let hc0 := Classical.choose_spec (X.invariant.initialOrdinaryTube q)
  let d0 := Classical.choose hc0
  let hTube := (Classical.choose_spec hc0).2
  exact
    { pathP0 := P0Profile (J := J) (q + X.depth)
      pathP1 := P1 q
      pathKhat := ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
        (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar)
      pathG1 := G1 q
      pathCg := Cg q
      start_curve_deriv := hTube.hasDerivAt_curve
      start_vel_deriv := hTube.hasDerivAt_vel
      geometry := by
        change NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
          (P0Profile (J := J) (q + X.depth)) (P1 q)
          (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat
            (ConfiguredRecursiveEdgeSourceP0CappedRowProduction.D J.scalar))
          (G1 q) (Cg q) (output X.invariant q).stage.increment
        rw [(output X.invariant q).stage_eq]
        exact A.increment_geometry
      rawBound := e q (X.depth + 1)
      rawBound_nonnegative := by
        have hcost : (output X.invariant q).stage.increment.cost ≤
            e q (X.depth + 1) := by
          rw [(output X.invariant q).stage_eq]
          exact chosen_cost_le X.invariant q
        exact (output X.invariant q).stage.increment.cost_nonneg.trans hcost
      cost_le := by
        change (output X.invariant q).stage.increment.cost ≤ e q (X.depth + 1)
        rw [(output X.invariant q).stage_eq]
        exact chosen_cost_le X.invariant q }

end ConfiguredRecursiveEdgeRecostMultiplierIntrinsicTailBridge
