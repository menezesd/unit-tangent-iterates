import UnitTangentIterates.CoherentPhaseReachableMetricRange
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostMultiplierConcreteGridShadow

/-!
# Coherent reachable grids as concrete shadow inputs

This module separates the geometric/metric completion of a reachable
phase-normalized grid from the propagated Jacobi comparison used only for
uniqueness.  It is independent of the concrete intrinsic tail builder.
-/

noncomputable section

open Filter Topology MarkedTopology
open MarkedSpace PathMetric PathMetric.NormalPath

namespace ConfiguredRecursiveEdgeRecostMultiplierCoherentGridShadowAdapter

open AnchoredJacobiStableTransition
  CoherentPhaseReachableMetricRange
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeRecostMultiplierClosing
  ConfiguredRecursiveEdgeRecostMultiplierConcreteGridShadow
  ConfiguredRecursiveEdgeRecostMultiplierRowBudget
  ConfiguredRecursiveEdgeRecostedOuterTubeStep
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveSourceP0FixedDistortion
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  VariableMarkedTube

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {O : GaugeOutput J}

/-- The non-comparison part of a concrete shadow input.  The coherent system
already proves the displayed metric increments, diagonal range edges, prefix
bounds, and configured tube propagation.  The only additional data here are
actual normal paths realizing the error budget and their row limits. -/
structure GridCompletion (R : RecostClosingOutput J O) where
  system : System (base R) R.error
  X : ℕ → MarkedSpace.Data
  step : ∀ n k, NormalPath (system.P n k) (system.P n (k + 1))
  step_cost : ∀ n k, cost (step n k) ≤ R.error n k
  row_tendsto : ∀ n, Tendsto (system.P n) atTop (nhds (X n))

namespace GridCompletion

variable {R : RecostClosingOutput J O}

/-- The metric increment furnished by coherent phase cancellation. -/
theorem stepDistance (G : GridCompletion R) (n k : ℕ) :
    dist (G.system.P n k) (G.system.P n (k + 1)) ≤ R.error n k :=
  G.system.stepDistance n k

/-- The exact diagonal range edge is independent of the cumulative marking
phase. -/
theorem rangeEdge (G : GridCompletion R) (n k : ℕ) :
    GeometricUnitTangentRangeEdge
      (G.system.P (n + 1) k) (G.system.P n (k + 1)) :=
  G.system.rangeEdge n k

/-- Triangle accumulation from the configured fixed-row base. -/
theorem prefixDistance (G : GridCompletion R) (n k : ℕ) :
    dist (base R n) (G.system.P n k) ≤
      Finset.sum (Finset.range k) (fun j ↦ R.error n j) :=
  G.system.prefixDistance n k

/-- The configured row budget converts the coherent prefix and next-edge
bounds into the common variable tube. -/
theorem variableTube_next
    (G : GridCompletion R) (B : BudgetType R) (n k : ℕ)
    (hmodel : IsTubeMember
      (2 * R.data.Hs 0) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model) (base R n))
    (hmodel_acc : ∀ u, ‖(base R n).2.2 u‖ ≤
      ConfiguredInductiveTubeBudget.accBound R.data.model n)
    (hcurve : ∀ u, HasDerivAt (⇑(G.system.P n (k + 1)).1)
      ((G.system.P n (k + 1)).2.1 u) u)
    (hvel : ∀ u, HasDerivAt (⇑(G.system.P n (k + 1)).2.1)
      ((G.system.P n (k + 1)).2.2 u) u)
    (hperiodic : Function.Periodic (⇑(G.system.P n (k + 1)).1) 1)
    (hcurvature : ∀ u, 0 ≤ ((starRingEnd ℂ)
      ((G.system.P n (k + 1)).2.1 u) *
        (G.system.P n (k + 1)).2.2 u).im) :
    IsVariableTubeMember
      (R.data.Hs 0) (upper R n) 0
      (ConfiguredInductiveTubeBudget.chordBase R.data.model / 2)
      (G.system.P n (k + 1)) :=
  G.system.variableTube_next R B n k hmodel hmodel_acc hcurve hvel
    hperiodic hcurvature

end GridCompletion

/-- Exactly the propagated comparison fields still needed after a coherent
grid and its row completion have been constructed. -/
structure PropagatedComparison (R : RecostClosingOutput J O)
    (G : GridCompletion R) where
  Y : ℕ → MarkedSpace.Data
  metricConst : ℝ
  metricConst_nonneg : 0 ≤ metricConst
  comparison : ℕ → ℕ → ℕ → Components
  comparison_nonnegative : ∀ n N k, (comparison n N k).Nonnegative
  comparison_initial : ∀ n N,
    (comparison n N 0).w ≤ R.radius N ∧
    (comparison n N 0).s0 ≤ R.radius N ∧
    (comparison n N 0).s1 ≤ R.radius N ∧
    (comparison n N 0).s2 ≤ R.radius N
  comparison_transition : ∀ n N k,
    Transition (comparison n N k) (comparison n N (k + 1))
      (NearIdentityDistortionBudget.invLower (pairedMajor O.major) k)
      (NearIdentityDistortionBudget.upper (pairedMajor O.major) k)
      (pairedMajor O.major k)
      physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
      physicalTransitionCeilings.C2
  comparison_distance : ∀ n k, dist (G.X n) (Y n) ≤ metricConst *
    ((comparison n (n + k) k).w + (comparison n (n + k) k).s0 +
      (comparison n (n + k) k).s1 + (comparison n (n + k) k).s2)

/-- Mechanical assembly of the concrete shadow input after the propagated
comparison has been supplied. -/
def GridCompletion.toConcreteGridInput
    {R : RecostClosingOutput J O} (G : GridCompletion R)
    (C : PropagatedComparison R G) : ConcreteGridInput R where
  P := G.system.P
  X := G.X
  step := G.step
  step_cost := G.step_cost
  row_tendsto := G.row_tendsto
  Y := C.Y
  metricConst := C.metricConst
  metricConst_nonneg := C.metricConst_nonneg
  comparison := C.comparison
  comparison_nonnegative := C.comparison_nonnegative
  comparison_initial := C.comparison_initial
  comparison_transition := C.comparison_transition
  comparison_distance := C.comparison_distance

/-- Paper shadowing for a coherent reachable grid.  All remaining obligations
are visibly confined to `PropagatedComparison`. -/
theorem paperShadow
    {R : RecostClosingOutput J O} (G : GridCompletion R)
    (C : PropagatedComparison R G) :
    (∀ n, ∃ A q : ℝ, Nonempty
      (GeometricScheduledACTail.Certificate (G.step n) (G.X n) A q)) ∧
    G.X = C.Y :=
  ConfiguredRecursiveEdgeRecostMultiplierConcreteGridShadow.paperShadow R
    (G.toConcreteGridInput C)

end ConfiguredRecursiveEdgeRecostMultiplierCoherentGridShadowAdapter
