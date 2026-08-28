import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenTerminal
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFiniteSource
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
import UnitTangentIterates.ConfiguredRecursiveEdgeActualStageBudget

/-!
# Actual selected-rear pullback stages with endpoint caps

This is the one-dimensional source recursion used by the paper.  The source
at depth `j + 1` is built on the raw path produced by `applyLong` at depth
`j`.  Canonical recosting never changes that recursive source: it is retained
only as a metric path.  The nonaffine terminal marking is charged once, after
the metric length of the path, as an outgoing endpoint cap.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareActualPullbackStages

open FiniteColumnStablePhysicalComponentCompactness
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenTerminal
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
  NormalPathC2IncrementVariableSpeed

/-- One actual recursive source.  `displayed` is allowed to differ from the
terminal endpoint of `Gamma`: that difference is precisely the preceding
nonaffine endpoint cap. -/
structure Stage
    (P0 kh khat Qmax : ℕ → ℝ) (j : ℕ) where
  start : Data
  rear : Data
  Gamma : NormalPath start rear
  source : MarkingAwareSource Gamma (P0 j) (kh j) (khat j) (Qmax j)
  applied : Applied Gamma source
  displayed : Data

/-- Geometric data selecting the next actual rear.  Its raw path starts at
the current displayed datum, while `base` is the canonical presentation that
will be displayed at the next depth. -/
structure GeometricInput
    {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
    (S : Stage P0 kh khat Qmax j) where
  base : Data
  bound : ℝ
  terminal : PresentedTerminalInputCore
    (p := S.displayed) (base := base) (bound := bound) S.applied
  output : PresentedOutputCore S.applied terminal

namespace GeometricInput

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S : Stage P0 kh khat Qmax j}

/-- The raw path is the path used to construct the next source. -/
def rawPath (G : GeometricInput S) :
    NormalPath S.displayed G.output.jets.rear :=
  G.output.stage.increment

/-- The exact outgoing marking cap. -/
def endpointCap (G : GeometricInput S) : ℝ :=
  intrinsicEndpointCap G.output

theorem endpointCap_nonnegative (G : GeometricInput S) :
    0 ≤ G.endpointCap := by
  exact dist_nonneg.trans (by
    simpa [endpointCap, intrinsicEndpointCap] using G.output.endpoint_dist)

theorem rear_dist_base_le_endpointCap (G : GeometricInput S) :
    dist G.output.jets.rear G.base ≤ G.endpointCap := by
  simpa [endpointCap, intrinsicEndpointCap] using G.output.endpoint_dist

end GeometricInput

/-- The smooth selected-inverse data which build the next source on the raw
path.  In particular, the successor theorem installs the density
`rawPath.m / sqrt (1-kh^2)`; no recosted density enters this record. -/
structure AnalyticInput
    {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
    {S : Stage P0 kh khat Qmax j} (G : GeometricInput S) where
  successor : AnalyticSuccessor G.rawPath S.source
    (P0 (j + 1)) (kh (j + 1)) (khat (j + 1)) (Qmax (j + 1))

namespace AnalyticInput

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S : Stage P0 kh khat Qmax j} {G : GeometricInput S}

/-- The normalized successor source on the raw selected-rear path. -/
def nextSource (A : AnalyticInput G) :
    MarkingAwareSource G.rawPath (P0 (j + 1)) (kh (j + 1))
      (khat (j + 1)) (Qmax (j + 1)) := by
  cases A.successor with
  | legacy smooth steering regularity majorants =>
      exact Classical.choice
        (exists_markingAwareSuccessorSource_of_majorants majorants)
  | exact source slice => exact source

end AnalyticInput

/-- The auxiliary canonical physical path.  It has the same geometry and
endpoints as the raw path but the paper's canonical component density. -/
def GeometricInput.recost
    {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
    {S : Stage P0 kh khat Qmax j} (G : GeometricInput S)
    (hC2 : C2NormalPathData G.rawPath)
    (heta : Continuous (Function.uncurry G.rawPath.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) :
    NormalPath S.displayed G.output.jets.rear :=
  CanonicalNormalPathRecost.recost G.rawPath hC2 heta heta1 heta2

/-- Physical metric data for one selected path.  Stability controls only the
canonical recost.  The raw path remains the input of `AnalyticInput`. -/
structure PhysicalMetricInput
    {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
    {S : Stage P0 kh khat Qmax j} (G : GeometricInput S)
    (E C0 C1 C2 d : ℝ) where
  pathP0 : ℝ
  pathP1 : ℝ
  pathKhat : ℝ
  pathG1 : ℝ
  pathCg : ℝ
  c2 : C2NormalPathData G.rawPath
  eta_continuous : Continuous (Function.uncurry G.rawPath.eta)
  eta1_continuous : Continuous (Function.uncurry c2.eta1)
  eta2_continuous : Continuous (Function.uncurry c2.eta2)
  start_curve_deriv : ∀ u,
    HasDerivAt (⇑S.displayed.1) (S.displayed.2.1 u) u
  start_vel_deriv : ∀ u,
    HasDerivAt (⇑S.displayed.2.1) (S.displayed.2.2 u) u
  geometry : IsVariableSpeedNormalPath pathP0 pathP1 pathKhat pathG1 pathCg
    (G.recost c2 eta_continuous eta1_continuous eta2_continuous)
  time_one : G.rawPath.T = 1
  d_nonnegative : 0 ≤ d
  stable : StablePhysicalComponents
    (G.recost c2 eta_continuous eta1_continuous eta2_continuous) 1
    (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
      E C0 C1 C2) d

namespace PhysicalMetricInput

variable {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
  {S : Stage P0 kh khat Qmax j} {G : GeometricInput S}
  {E C0 C1 C2 d : ℝ}

/-- The cap-aware scalar budget: physical recost length first, then the
single outgoing nonaffine endpoint cap. -/
def edgeBudget (M : PhysicalMetricInput G E C0 C1 C2 d) : ℝ :=
  c2ConstVar M.pathP0 M.pathP1 M.pathKhat M.pathG1 M.pathCg *
    (4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
      E C0 C1 C2 * d) + G.endpointCap

theorem edgeBudget_nonnegative (M : PhysicalMetricInput G E C0 C1 C2 d) :
    0 ≤ M.edgeBudget := by
  exact add_nonneg
    (mul_nonneg (c2ConstVar_nonneg _ _ _ _ _)
      (mul_nonneg
      (mul_nonneg (by norm_num)
        (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget_nonnegative
          E C0 C1 C2))
      M.d_nonnegative))
    G.endpointCap_nonnegative

theorem dist_start_rear_le_recost
    (M : PhysicalMetricInput G E C0 C1 C2 d) :
    dist S.displayed G.output.jets.rear ≤
      c2ConstVar M.pathP0 M.pathP1 M.pathKhat M.pathG1 M.pathCg *
        (G.recost M.c2 M.eta_continuous M.eta1_continuous
          M.eta2_continuous).cost := by
  exact dist_le_cost_variableSpeed
    (G.recost M.c2 M.eta_continuous M.eta1_continuous M.eta2_continuous)
    M.start_curve_deriv G.output.stage.rear_curve_deriv
    M.start_vel_deriv G.output.stage.rear_vel_deriv M.geometry

theorem dist_displayed_base_le_edgeBudget
    (M : PhysicalMetricInput G E C0 C1 C2 d) :
    dist S.displayed G.base ≤ M.edgeBudget := by
  let K := c2ConstVar M.pathP0 M.pathP1 M.pathKhat M.pathG1 M.pathCg
  have hK0 : 0 ≤ K := c2ConstVar_nonneg _ _ _ _ _
  have hcost :=
    FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability.recost_cost_le_four_configuredTarget_mul
      M.c2 M.eta_continuous M.eta1_continuous M.eta2_continuous M.stable
  have hcap := G.rear_dist_base_le_endpointCap
  calc
    dist S.displayed G.base ≤
        dist S.displayed G.output.jets.rear +
          dist G.output.jets.rear G.base := dist_triangle _ _ _
    _ ≤ K * (G.recost M.c2 M.eta_continuous M.eta1_continuous
          M.eta2_continuous).cost + G.endpointCap :=
      add_le_add M.dist_start_rear_le_recost hcap
    _ ≤ K * (4 *
          ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
            E C0 C1 C2 * d) + G.endpointCap :=
      add_le_add (mul_le_mul_of_nonneg_left hcost hK0) le_rfl
    _ = M.edgeBudget := by rfl

/-- The two configured row ceilings needed to charge an actual physical
edge to the scalar diagonal: one for the canonical recost conversion and one
for the single outgoing endpoint cap.  No raw source-mass estimate enters
this comparison. -/
theorem edgeBudget_le_directDiagonal
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA Mend : ℝ)
    (M : PhysicalMetricInput G E C0 C1 C2
      (ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (j + 1)))
    (hconversion :
      c2ConstVar M.pathP0 M.pathP1 M.pathKhat M.pathG1 M.pathCg ≤
        ConfiguredRecursiveEdgeSourceP0Growth.edgeConversion D
          (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D)
          MA NA j)
    (hendpoint : G.endpointCap ≤
      ConfiguredRecursiveEdgeSourceP0Growth.edgeEndpointConversion D
          ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh Mend j *
        ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (j + 1)) :
    M.edgeBudget ≤
      ConfiguredRecursiveEdgeFiniteColumnScalarClosing.directDiagonal D
        MA NA E C0 C1 C2 Mend j := by
  exact ConfiguredRecursiveEdgeFiniteColumnScalarClosing.capAwareBudget_le_directDiagonal
    D (c2ConstVar_nonneg _ _ _ _ _) hconversion hendpoint

end PhysicalMetricInput

/-- All data for one sound recursive step. -/
structure StepInput
    {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
    (S : Stage P0 kh khat Qmax j)
    (E C0 C1 C2 d : ℝ) where
  geometric : GeometricInput S
  analytic : AnalyticInput geometric
  metric : PhysicalMetricInput geometric E C0 C1 C2 d
  nextApplied : Applied geometric.rawPath analytic.nextSource

/-- Advance the actual source on the raw path, but advance the displayed
trajectory to the canonical terminal base. -/
def StepInput.next
    {P0 kh khat Qmax : ℕ → ℝ} {j : ℕ}
    {S : Stage P0 kh khat Qmax j} {E C0 C1 C2 d : ℝ}
    (I : StepInput S E C0 C1 C2 d) : Stage P0 kh khat Qmax (j + 1) where
  start := S.displayed
  rear := I.geometric.output.jets.rear
  Gamma := I.geometric.rawPath
  source := I.analytic.nextSource
  applied := I.nextApplied
  displayed := I.geometric.base

/-- A dependent provider of actual selected-rear stages. -/
structure Provider
    {P0 kh khat Qmax : ℕ → ℝ}
    (B : Stage P0 kh khat Qmax 0) (E C0 C1 C2 : ℝ) (d : ℕ → ℝ) where
  step : ∀ j (S : Stage P0 kh khat Qmax j), StepInput S E C0 C1 C2 (d j)

namespace Provider

variable {P0 kh khat Qmax : ℕ → ℝ}
  {B : Stage P0 kh khat Qmax 0} {E C0 C1 C2 : ℝ} {d : ℕ → ℝ}

/-- The finite-depth actual source recursion. -/
def stages (P : Provider B E C0 C1 C2 d) :
    ∀ j, Stage P0 kh khat Qmax j
  | 0 => B
  | j + 1 => (P.step j (P.stages j)).next

/-- The displayed terminal presentation at every depth. -/
def displayed (P : Provider B E C0 C1 C2 d) (j : ℕ) : Data :=
  (P.stages j).displayed

/-- The cap-aware physical budget consumed at depth `j`. -/
def error (P : Provider B E C0 C1 C2 d) (j : ℕ) : ℝ :=
  (P.step j (P.stages j)).metric.edgeBudget

theorem error_nonnegative (P : Provider B E C0 C1 C2 d) (j : ℕ) :
    0 ≤ P.error j :=
  (P.step j (P.stages j)).metric.edgeBudget_nonnegative

theorem step_dist (P : Provider B E C0 C1 C2 d) (j : ℕ) :
    dist (P.displayed j) (P.displayed (j + 1)) ≤ P.error j := by
  exact (P.step j (P.stages j)).metric.dist_displayed_base_le_edgeBudget

/-- A summable cap-aware physical budget makes the actual displayed
pullback stages Cauchy. -/
theorem cauchy_displayed (P : Provider B E C0 C1 C2 d)
    (hsum : Summable P.error) : CauchySeq P.displayed := by
  apply cauchySeq_of_summable_dist
  exact Summable.of_nonneg_of_le (fun _ => dist_nonneg) P.step_dist hsum

end Provider

end FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
