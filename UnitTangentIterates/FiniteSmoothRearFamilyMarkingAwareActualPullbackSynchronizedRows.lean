import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackPresentedArray
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings

/-!
# Diagonally synchronized actual pullback rows

The recursive source stored at row `n` is carried by the edge one row ahead.
Consequently a successor column uses the geometric output at `n` for its new
displayed point, but uses the analytic successor of the output at `n + 1` for
its new carrier and source.  This is the paper indexing
`P (n,k) = B^k Q_(n+k)` and avoids the arbitrary-stage callback in `Rows`.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows

open FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwareSmoothSource
  FiniteSmoothRearFamilyMarkingAwareSource
  NormalPathC2IncrementVariableSpeed
  VariableMarkedTube

/-- One reachable source state at a triangular cell.  Its raw carrier is the
edge one row ahead, while `displayed` is the current point of this row. -/
structure Stage
    (P0 kh khat Qmax : ℕ → ℕ → ℝ) (n k : ℕ) where
  start : Data
  rear : Data
  Gamma : NormalPath start rear
  source : MarkingAwareSource Gamma (P0 n k) (kh n k) (khat n k) (Qmax n k)
  applied : FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied Gamma source
  displayed : Data

/-- Every reachable stage receives the paper's fixed fully physical Jacobi
ceilings from its intrinsic source facts.  No row transition or affine
marking hypothesis is used. -/
def Stage.fullyPhysicalAnalyticInput
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {n k : ℕ}
    (S : Stage P0 kh khat Qmax n k)
    (hkh : 0 < kh n k)
    (H : FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource.SeparatedFacts
      S.source P1)
    (F : ControlledJunctionPathFunctionalBounds.FunctionalIntegrable S.Gamma.eta) :
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.AnalyticInput
      S.source.P
      (FiniteSmoothRearFamilyMarkingAwareAppliedSource.rearPeriod S.source)
      S.Gamma.eta
      (FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW.normalizedRearDensity
        S.source)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0
        (kh n k))
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1
        (kh n k))
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2
        (kh n k)) :=
  FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.fullyPhysicalAnalyticInput
    (E := S.applied) hkh H F

/-- Forget the triangular indices when invoking the already-proved local
geometric and physical-metric APIs. -/
def Stage.asUnary
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {n k : ℕ}
    (S : Stage P0 kh khat Qmax n k) :
    FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.Stage
      (fun _ ↦ P0 n k) (fun _ ↦ kh n k) (fun _ ↦ khat n k)
      (fun _ ↦ Qmax n k) 0 where
  start := S.start
  rear := S.rear
  Gamma := S.Gamma
  source := S.source
  applied := S.applied
  displayed := S.displayed

abbrev GeometricInput
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {n k : ℕ}
    (S : Stage P0 kh khat Qmax n k) :=
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages.GeometricInput S.asUnary

/-- Analytic successor for row `n` is built from the reachable geometric
output at row `n + 1`, with the exact scalar type of cell `(n,k+1)`. -/
structure AnalyticInput
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {k : ℕ}
    (S : ∀ n, Stage P0 kh khat Qmax n k)
    (G : ∀ n, GeometricInput (S n)) (n : ℕ) where
  successor : AnalyticSuccessor (G (n + 1)).rawPath (S (n + 1)).source
    (P0 n (k + 1)) (kh n (k + 1)) (khat n (k + 1)) (Qmax n (k + 1))

def AnalyticInput.nextSource
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {k : ℕ}
    {S : ∀ n, Stage P0 kh khat Qmax n k}
    {G : ∀ n, GeometricInput (S n)} {n : ℕ}
    (A : AnalyticInput S G n) :
    MarkingAwareSource (G (n + 1)).rawPath
      (P0 n (k + 1)) (kh n (k + 1)) (khat n (k + 1)) (Qmax n (k + 1)) := by
  cases A.successor with
  | legacy smooth steering regularity majorants =>
      exact Classical.choice
        (exists_markingAwareSuccessorSource_of_majorants majorants)
  | exact source slice => exact source

/-- One reachable synchronized successor column. -/
structure Step
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {k : ℕ}
    (S : ∀ n, Stage P0 kh khat Qmax n k)
    (E C0 C1 C2 : ℕ → ℝ) (d : ℕ → ℕ → ℝ) where
  geometric : ∀ n, GeometricInput (S n)
  analytic : ∀ n, AnalyticInput S geometric n
  metric : ∀ n,
    PhysicalMetricInput (geometric n) (E n) (C0 n) (C1 n) (C2 n) (d n k)
  nextApplied : ∀ n,
    FiniteSmoothRearFamilyMarkingAwareAppliedSource.Applied
      (geometric (n + 1)).rawPath (analytic n).nextSource

/-- Advance a full family.  Displayed row `n` comes from output `n`; its new
raw carrier/source come from the output and analytic successor at `n + 1`. -/
def Step.next
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {k : ℕ}
    {S : ∀ n, Stage P0 kh khat Qmax n k}
    {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}
    (I : Step S E C0 C1 C2 d) (n : ℕ) :
    Stage P0 kh khat Qmax n (k + 1) where
  start := (S (n + 1)).displayed
  rear := (I.geometric (n + 1)).output.jets.rear
  Gamma := (I.geometric (n + 1)).rawPath
  source := (I.analytic n).nextSource
  applied := I.nextApplied n
  displayed := (I.geometric n).base

/-- A terminal oriented reparametrization preserves the underlying curve
range. -/
theorem GeometricInput.base_rear_curve_range
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {n k : ℕ}
    {S : Stage P0 kh khat Qmax n k} (G : GeometricInput S) :
    range G.base.1 = range G.output.jets.rear.1 := by
  have hcont : Continuous G.output.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (G.output.psi_deriv u).continuousAt
  have hmono : StrictMono G.output.marking.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(G.output.psi_deriv u).deriv]
    exact lt_of_lt_of_le G.terminal.lambda_pos (G.output.marking.lower u)
  have hsurj : Surjective G.output.marking.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono G.output.marking.translate G.output.psi_zero
  apply Subset.antisymm
  · rintro z ⟨x, rfl⟩
    obtain ⟨u, hu⟩ := hsurj x
    exact ⟨u, by rw [G.output.marking.position u, hu]⟩
  · rintro z ⟨u, rfl⟩
    exact ⟨G.output.marking.psi u, (G.output.marking.position u).symm⟩

/-- The same oriented marking preserves geometric unit-tangent range. -/
theorem GeometricInput.base_rear_geometric_range
    {P0 kh khat Qmax : ℕ → ℕ → ℝ} {n k : ℕ}
    {S : Stage P0 kh khat Qmax n k} (G : GeometricInput S) :
    range (geometricUnitTangent G.base) =
      range (geometricUnitTangent G.output.jets.rear) := by
  have hcont : Continuous G.output.marking.psi :=
    continuous_iff_continuousAt.2 fun u => (G.output.psi_deriv u).continuousAt
  have hmono : StrictMono G.output.marking.psi := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(G.output.psi_deriv u).deriv]
    exact lt_of_lt_of_le G.terminal.lambda_pos (G.output.marking.lower u)
  have hsurj : Surjective G.output.marking.psi :=
    GaugeMarkedSelectedInverseEndpoint.surjective_of_continuous_strictMono_quasiPeriodic
      one_pos hcont hmono G.output.marking.translate G.output.psi_zero
  have hbase : geometricUnitTangent G.base = normalizedUnitTangent G.base := by
    funext u
    rw [geometricUnitTangent, normalizedUnitTangent,
      norm_vel_eq_perim G.terminal.zero_floor_tube u]
  rw [hbase]
  apply Subset.antisymm
  · rintro z ⟨x, rfl⟩
    obtain ⟨u, hu⟩ := hsurj x
    refine ⟨u, ?_⟩
    rw [GaugeRearFamilyVariableTerminal.geometricUnitTangent_eq_normalized_of_orientedReparametrization
      G.terminal.physical.cq_pos G.terminal.lambda_pos
      G.terminal.zero_floor_tube G.output.marking u, hu]
  · rintro z ⟨u, rfl⟩
    exact ⟨G.output.marking.psi u,
      (GaugeRearFamilyVariableTerminal.geometricUnitTangent_eq_normalized_of_orientedReparametrization
        G.terminal.physical.cq_pos G.terminal.lambda_pos
        G.terminal.zero_floor_tube G.output.marking u).symm⟩

/-- Reachable synchronized recursion.  `base_range` is the depth-zero
carrier/displayed alignment already present in the correlated base column. -/
structure Rows
    (P0 kh khat Qmax : ℕ → ℕ → ℝ)
    (E C0 C1 C2 : ℕ → ℝ) (d : ℕ → ℕ → ℝ) where
  base : ∀ n, Stage P0 kh khat Qmax n 0
  base_range : ∀ n, range (base n).rear.1 = range (base (n + 1)).displayed.1
  step : ∀ k (S : ∀ n, Stage P0 kh khat Qmax n k), Step S E C0 C1 C2 d

namespace Rows

variable {P0 kh khat Qmax : ℕ → ℕ → ℝ}
  {E C0 C1 C2 : ℕ → ℝ} {d : ℕ → ℕ → ℝ}

def stages (R : Rows P0 kh khat Qmax E C0 C1 C2 d) :
    ∀ k n, Stage P0 kh khat Qmax n k
  | 0, n => R.base n
  | k + 1, n => (R.step k (R.stages k)).next n

def input (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :=
  (R.step k (R.stages k)).geometric n

def P (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) : Data :=
  (R.stages k n).displayed

@[simp] theorem P_zero (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n : ℕ) :
    R.P n 0 = (R.base n).displayed := rfl

@[simp] theorem P_succ (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (n k : ℕ) :
    R.P n (k + 1) = (R.input n k).base := rfl

def intermediateRear (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (n k : ℕ) : Data :=
  (R.input n k).output.jets.rear

/-- Short cap-aware notation for the intermediate selected rear. -/
abbrev R (A : Rows P0 kh khat Qmax E C0 C1 C2 d) := A.intermediateRear

def rawPath (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    NormalPath (R.P n k) (R.intermediateRear n k) :=
  (R.input n k).rawPath

def recostPath (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    NormalPath (R.P n k) (R.intermediateRear n k) :=
  let I := R.step k (R.stages k)
  let G := I.geometric n
  let M := I.metric n
  G.recost M.c2 M.eta_continuous M.eta1_continuous M.eta2_continuous

def endpointCap (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) : ℝ :=
  (R.input n k).endpointCap

/-- The outgoing nonaffine cap error. -/
abbrev capError (R : Rows P0 kh khat Qmax E C0 C1 C2 d) := R.endpointCap

def pathConversion (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (n k : ℕ) : ℝ :=
  let M := (R.step k (R.stages k)).metric n
  c2ConstVar M.pathP0 M.pathP1 M.pathKhat M.pathG1 M.pathCg

def pathError (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) : ℝ :=
  R.pathConversion n k *
    (4 * ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
      (E n) (C0 n) (C1 n) (C2 n) * d n k)

def error (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) : ℝ :=
  ((R.step k (R.stages k)).metric n).edgeBudget

theorem stages_range
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) :
    ∀ k n, range (R.stages k n).rear.1 = range (R.stages k (n + 1)).displayed.1 := by
  intro k
  induction k with
  | zero => exact R.base_range
  | succ k ih =>
      intro n
      exact ((R.input (n + 1) k).base_rear_curve_range).symm

theorem path_dist_le_pathError
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    dist (R.P n k) (R.intermediateRear n k) ≤ R.pathError n k := by
  let I := R.step k (R.stages k)
  let M := I.metric n
  have hK0 : 0 ≤ R.pathConversion n k := c2ConstVar_nonneg _ _ _ _ _
  have hcost :=
    FiniteSmoothRearFamilyMarkingAwareNonaffineFiniteStability.recost_cost_le_four_configuredTarget_mul
      M.c2 M.eta_continuous M.eta1_continuous M.eta2_continuous M.stable
  exact M.dist_start_rear_le_recost.trans
    (mul_le_mul_of_nonneg_left hcost hK0)

theorem cap_dist_le
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    dist (R.intermediateRear n k) (R.P n (k + 1)) ≤ R.endpointCap n k :=
  (R.input n k).rear_dist_base_le_endpointCap

theorem combined_dist_le
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    dist (R.P n k) (R.P n (k + 1)) ≤ R.error n k :=
  ((R.step k (R.stages k)).metric n).dist_displayed_base_le_edgeBudget

/-- Exact displayed diagonal range edge, derived from the reachable carrier
alignment, raw output range edge, and terminal marking. -/
theorem range_edge
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d) (n k : ℕ) :
    GeometricUnitTangentRangeEdge (R.P (n + 1) k) (R.P n (k + 1)) := by
  unfold GeometricUnitTangentRangeEdge
  calc
    range (R.P (n + 1) k).1 = range (R.stages k n).rear.1 :=
      (R.stages_range k n).symm
    _ = range (geometricUnitTangent (R.intermediateRear n k)) :=
      (R.input n k).output.stage.range_edge
    _ = range (geometricUnitTangent (R.P n (k + 1))) :=
      (R.input n k).base_rear_geometric_range.symm

structure Ceilings
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (pathCeiling endpointCeiling q : ℕ → ℕ → ℝ) : Prop where
  path : ∀ n k, R.pathConversion n k ≤ pathCeiling n k
  endpoint : ∀ n k, R.endpointCap n k ≤ endpointCeiling n k * q n k

theorem configured_combined_le
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (MA NA E0 C00 C10 C20 M : ℝ) (idx : ℕ → ℕ → ℕ)
    (H : Ceilings R
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgeConversion D
        (ConfiguredCombinedPhysicalDiagonalLargeSeparation.analyticKhat D) MA NA (idx n k))
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgeEndpointConversion
        D ConfiguredCombinedPhysicalDiagonalLargeSeparation.sourceKh M (idx n k))
      (fun n k => ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect
        D (idx n k + 1)))
    (hE : ∀ n, E n = E0) (hC0 : ∀ n, C0 n = C00)
    (hC1 : ∀ n, C1 n = C10) (hC2 : ∀ n, C2 n = C20)
    (hd : ∀ n k, d n k =
      ConfiguredRecursiveEdgeSourceP0Growth.edgePhysicalDefect D (idx n k + 1)) :
    ∀ n k, R.pathError n k + R.endpointCap n k ≤
      ConfiguredRecursiveEdgeFiniteColumnScalarClosing.directDiagonal
        D MA NA E0 C00 C10 C20 M (idx n k) := by
  intro n k
  rw [pathError, hE n, hC0 n, hC1 n, hC2 n, hd n k]
  exact ConfiguredRecursiveEdgeFiniteColumnScalarClosing.capAwareBudget_le_directDiagonal
    D (c2ConstVar_nonneg _ _ _ _ _) (H.path n k) (H.endpoint n k)

def toCapAwareActualPullbackStages
    (R : Rows P0 kh khat Qmax E C0 C1 C2 d)
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (hbase : ∀ n, R.P n 0 = Q n)
    (hcombined : ∀ n k, R.pathError n k + R.endpointCap n k ≤ e n k) :
    WeightedRecursiveDefect.CapAwareActualPullbackStages
      Q R.P R.intermediateRear R.pathError R.endpointCap e where
  base := hbase
  path := R.recostPath
  path_dist_le := R.path_dist_le_pathError
  cap_dist_le := R.cap_dist_le
  combined_le := hcombined
  range_edge := R.range_edge

end Rows

end FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows
