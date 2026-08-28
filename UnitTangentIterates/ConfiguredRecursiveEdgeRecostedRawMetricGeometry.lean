import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal

/-!
# Raw metric geometry for recosted recursive rows

Canonical recosting changes the density of a chosen path.  Consequently the
raw variable-speed certificate, whose derivative bounds are stated against
the chosen density, must not be coerced to the recosted path.  This module
keeps the two roles separate: raw geometry proves the marked endpoint
distance, while the fully physical split history controls the auxiliary
recosted path and the next source.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedRawMetricGeometry

open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricPresentedRecursion
  FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow
  NormalPathC2IncrementVariableSpeed

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S0 : Stage P0 kh khat Qmax j}

/-- The geometric facts used only for the marked distance of the raw chosen
path.  In contrast to the legacy `MetricGeometry`, no claim is made that the
same certificate is valid after replacing the path density by its canonical
recost. -/
structure RawMetricGeometry (G : GeometricInput S0) where
  pathP0 : ℝ
  pathP1 : ℝ
  pathKhat : ℝ
  pathG1 : ℝ
  pathCg : ℝ
  start_curve_deriv : ∀ u,
    HasDerivAt (⇑S0.displayed.1) (S0.displayed.2.1 u) u
  start_vel_deriv : ∀ u,
    HasDerivAt (⇑S0.displayed.2.1) (S0.displayed.2.2 u) u
  geometry : IsVariableSpeedNormalPath
    pathP0 pathP1 pathKhat pathG1 pathCg G.rawPath

namespace RawMetricGeometry

variable {G : GeometricInput S0}

def pathFactor (M : RawMetricGeometry G) : ℝ :=
  c2ConstVar M.pathP0 M.pathP1 M.pathKhat M.pathG1 M.pathCg

theorem pathFactor_nonnegative (M : RawMetricGeometry G) :
    0 ≤ M.pathFactor :=
  c2ConstVar_nonneg _ _ _ _ _

/-- The raw chosen path, not its recost, controls the marked distance to the
intermediate selected rear. -/
theorem dist_start_rear_le (M : RawMetricGeometry G) :
    dist S0.displayed G.output.jets.rear ≤
      M.pathFactor * G.rawPath.cost := by
  exact dist_le_cost_variableSpeed G.rawPath
    M.start_curve_deriv G.output.stage.rear_curve_deriv
    M.start_vel_deriv G.output.stage.rear_vel_deriv M.geometry

/-- Raw path geometry together with a truthful raw cost ceiling. -/
structure Bounded (G : GeometricInput S0) extends RawMetricGeometry G where
  rawBound : ℝ
  rawBound_nonnegative : 0 ≤ rawBound
  cost_le : G.rawPath.cost ≤ rawBound

namespace Bounded

variable {G : GeometricInput S0}

def edgeBudget (M : Bounded G) : ℝ :=
  M.toRawMetricGeometry.pathFactor * M.rawBound + G.endpointCap

theorem edgeBudget_nonnegative (M : Bounded G) : 0 ≤ M.edgeBudget := by
  exact add_nonneg
    (mul_nonneg M.toRawMetricGeometry.pathFactor_nonnegative
      M.rawBound_nonnegative)
    G.endpointCap_nonnegative

/-- Add the nonaffine endpoint cap exactly once, after the raw path metric
estimate. -/
theorem dist_displayed_base_le (M : Bounded G) :
    dist S0.displayed G.base ≤ M.edgeBudget := by
  let K := M.toRawMetricGeometry.pathFactor
  calc
    dist S0.displayed G.base ≤
        dist S0.displayed G.output.jets.rear +
          dist G.output.jets.rear G.base := dist_triangle _ _ _
    _ ≤ K * G.rawPath.cost + G.endpointCap :=
      add_le_add M.toRawMetricGeometry.dist_start_rear_le
        G.rear_dist_base_le_endpointCap
    _ ≤ K * M.rawBound + G.endpointCap :=
      add_le_add
        (mul_le_mul_of_nonneg_left M.cost_le
          M.toRawMetricGeometry.pathFactor_nonnegative) le_rfl
    _ = M.edgeBudget := rfl

/-- The configured scalar bridge for the split raw metric leg.  The raw path
has the inverse-square-root factor `2`, the physical history has the common
period-square factor, and the endpoint discrepancy is charged exactly once. -/
theorem edgeBudget_le_recostDirectDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E C0 C1 C2 Mend : ℝ) (q : ℕ)
    (M : Bounded G)
    (hfactor : M.toRawMetricGeometry.pathFactor ≤
      ConfiguredRecursiveEdgeSourceP0Growth.edgeConversion D
        (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
        MA NA q)
    (hraw : M.rawBound ≤
      2 * ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostPeriodScale D q *
        (4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
          E C0 C1 C2 *
            ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (q + 1)))
    (hendpoint : G.endpointCap ≤
      ConfiguredRecursiveEdgeSourceP0Growth.edgeEndpointConversion D
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh Mend q *
        ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (q + 1)) :
    M.edgeBudget ≤
      ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostDirectDiagonal
        D MA NA E C0 C1 C2 Mend q := by
  let K := ConfiguredRecursiveEdgeSourceP0Growth.edgeConversion D
    (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D) MA NA q
  let L2 := ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostPeriodScale D q
  let B := ConfiguredRecursiveEdgeSourceP0Growth.edgeEndpointConversion D
    ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh Mend q
  let T := ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget E C0 C1 C2
  let d := ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (q + 1)
  have hK0 : 0 ≤ K :=
    ConfiguredRecursiveEdgeSourceP0Growth.edgeConversion_nonnegative D _ _ _ q
  have hL0 : 0 ≤ L2 :=
    ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostPeriodScale_nonnegative D q
  have hB0 : 0 ≤ B :=
    ConfiguredRecursiveEdgeSourceP0Growth.edgeEndpointConversion_nonnegative D
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_nonnegative
      ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh_lt_one q
  have hT0 : 0 ≤ T :=
    ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget_nonnegative
      E C0 C1 C2
  have hd0 : 0 ≤ d :=
    ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect_nonnegative D (q + 1)
  have hraw0 : 0 ≤ M.rawBound := M.rawBound_nonnegative
  have hpath : M.toRawMetricGeometry.pathFactor * M.rawBound ≤
      K * (2 * L2 * (4 * T * d)) := by
    exact mul_le_mul hfactor (by simpa [L2, T, d] using hraw) hraw0 hK0
  have hfirst : M.edgeBudget ≤ (4 * T * (2 * L2 * K) + B) * d := by
    calc
      M.edgeBudget ≤ K * (2 * L2 * (4 * T * d)) + B * d :=
        add_le_add hpath (by simpa [B, d] using hendpoint)
      _ = (4 * T * (2 * L2 * K) + B) * d := by ring
  have hscale : 4 * T * (2 * L2 * K) + B ≤
      (4 * T + 1) * (2 * L2 * K + B) := by
    have hfourT : 0 ≤ 4 * T := mul_nonneg (by norm_num) hT0
    have htwoL2K : 0 ≤ 2 * L2 * K :=
      mul_nonneg (mul_nonneg (by norm_num) hL0) hK0
    nlinarith [mul_nonneg hfourT hB0]
  calc
    M.edgeBudget ≤ (4 * T * (2 * L2 * K) + B) * d := hfirst
    _ ≤ (4 * T + 1) * (2 * L2 * K + B) * d :=
      mul_le_mul_of_nonneg_right hscale hd0
    _ = ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostDirectDiagonal
        D MA NA E C0 C1 C2 Mend q := by
      simp [ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostDirectDiagonal,
        ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostDirectConversion,
        ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostCombinedConversion,
        ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal.recostEdgeConversion,
        ConfiguredRecursiveEdgeFiniteColumnScalarClosing.directScale,
        ConfiguredRecursiveEdgeWeightedEffectiveError.weightedSequence,
        K, L2, B, T, d]

end Bounded

end RawMetricGeometry

/-! ## Callback-free reachable-row constructor -/

variable {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k n : ℕ}
  {P0r P1r G1r Cgr Cr Qmaxr : ℕ → ℝ}
  {kappa kappaHat c dlt : ℝ}
  {S : GeometricCorrelatedColumn Q current e k P0r P1r
    (fun _ ↦ kappaHat) G1r Cgr Cr c dlt (fun _ ↦ kappa) Qmaxr}

/-- Every reachable canonical geometric row produces its raw metric package.
The ordinary initial tube supplies the two displayed derivatives; the row's
widened chosen geometry supplies the path certificate; and the row theorem
supplies the exact raw cost bound. -/
noncomputable def ofCanonicalRow
    (H : GeometricCompositionInvariant S) (n : ℕ)
    (hP1 : GaugeFlowDerivCost.costP1
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        (S.source n) 0) kappaHat
      (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤ P1r n)
    (hG1 : GaugeFlowDerivCost.costG1
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        (S.source n) 0) kappaHat
      (GaugeMarkedDataOfRearFamily.rearKappa2 kappa)
      (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤ G1r n)
    (hCg : kappaHat * GaugeFlowDerivCost.costG1
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
          (S.source n) 0) kappaHat
        (GaugeMarkedDataOfRearFamily.rearKappa2 kappa)
        (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) +
      GaugeMarkedDataOfRearFamily.rearKappa2 kappa *
        GaugeFlowDerivCost.costP1
          (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
            (S.source n) 0) kappaHat
          (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ^ 2 ≤ Cgr n) :
    RawMetricGeometry.Bounded
      (ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.geometricInput H n) := by
  let G := ConfiguredRecursiveEdgeRecostedCanonicalGeometricInput.geometricInput H n
  let R := FiniteSmoothRearFamilyMarkingAwareCompositionGeometricCanonicalRow.row
    H n hP1 hG1 hCg
  let c0 := Classical.choose (H.initialOrdinaryTube n)
  let hc0 := Classical.choose_spec (H.initialOrdinaryTube n)
  let d0 := Classical.choose hc0
  let hTube := (Classical.choose_spec hc0).2
  exact
    { pathP0 := P0r (n + k)
      pathP1 := P1r n
      pathKhat := kappaHat
      pathG1 := G1r n
      pathCg := Cgr n
      start_curve_deriv := hTube.hasDerivAt_curve
      start_vel_deriv := hTube.hasDerivAt_vel
      geometry := by
        change IsVariableSpeedNormalPath (P0r (n + k)) (P1r n)
          kappaHat (G1r n) (Cgr n) (output H n).stage.increment
        rw [(output H n).stage_eq]
        exact R.increment_geometry
      rawBound := e n (k + 1)
      rawBound_nonnegative := by
        have hcost : (output H n).stage.increment.cost ≤ e n (k + 1) := by
          rw [(output H n).stage_eq]
          exact chosen_cost_le H n
        exact (output H n).stage.increment.cost_nonneg.trans hcost
      cost_le := by
        change (output H n).stage.increment.cost ≤ e n (k + 1)
        rw [(output H n).stage_eq]
        exact chosen_cost_le H n }

@[simp] theorem ofCanonicalRow_pathFactor
    (H : GeometricCompositionInvariant S) (n : ℕ)
    (hP1 : GaugeFlowDerivCost.costP1
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        (S.source n) 0) kappaHat
      (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤ P1r n)
    (hG1 : GaugeFlowDerivCost.costG1
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
        (S.source n) 0) kappaHat
      (GaugeMarkedDataOfRearFamily.rearKappa2 kappa)
      (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ≤ G1r n)
    (hCg : kappaHat * GaugeFlowDerivCost.costG1
        (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
          (S.source n) 0) kappaHat
        (GaugeMarkedDataOfRearFamily.rearKappa2 kappa)
        (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) +
      GaugeMarkedDataOfRearFamily.rearKappa2 kappa *
        GaugeFlowDerivCost.costP1
          (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod
            (S.source n) 0) kappaHat
          (∫ t in (0 : ℝ)..(S.path n).T, (S.source n).m t) ^ 2 ≤ Cgr n) :
    (ofCanonicalRow H n hP1 hG1 hCg).toRawMetricGeometry.pathFactor =
      c2ConstVar (P0r (n + k)) (P1r n) kappaHat (G1r n) (Cgr n) := by
  simp [ofCanonicalRow, RawMetricGeometry.pathFactor]

end ConfiguredRecursiveEdgeRecostedRawMetricGeometry
