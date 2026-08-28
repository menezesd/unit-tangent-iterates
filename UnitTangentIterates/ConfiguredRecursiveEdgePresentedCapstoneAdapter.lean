import UnitTangentIterates.ConfiguredRecursiveEdgePresentedJetBounds
import UnitTangentIterates.ConfiguredMarkingAwareCorrelatedDiagonalDirectAssembly
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareDirectCappedProvider
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGridDischarge
import UnitTangentIterates.GenericVariableTerminalDirectCapstoneExplicitFront

/-!
# Configured capstone adapter for the presented recursion

This leaf module isolates the parts of the presented capstone which are
already consequences of the configured scalar construction.  In particular,
the diagonal row errors are automatically nonnegative and summable, finite
Harnack certificates are retained by the presented stages, and the complete
row-zero width/perimeter gap follows from the large-separation output.

The genuinely geometric construction of a `CapFamily` remains separate.  It
depends on the physical presentation chosen by the recursive row provider and
must not be replaced by an unrelated configured terminal.
-/

noncomputable section

open Filter Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgePresentedCapstoneAdapter

open ConfiguredAlignedQGeometry
  ConfiguredApproximateDefectPathRowwise
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredDiagonalStableRowDefectProvider
  ConfiguredGaugeEndpointLinearRadius
  ConfiguredInductiveTubeBudget
  ConfiguredPhysicalDiagonalRowBudget
  ConfiguredPolynomialDiagonalStableRowDefectProvider
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly
  FiniteSmoothRearFamilyMarkingAwareCorrelatedRecursion
  FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGridDischarge
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeRearFamilyVariableTerminal
  GenericVariableTerminalDirectCapstoneExplicitFront
  NormalizedTerminalMarkingComposition
  RichFamilyPhysicalMarkingIntegration
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- The configured physical diagonal supplies the scalar error sign required
by the presented cap family. -/
theorem configuredError_nonnegative
    (D : ConstructedConfiguredSequenceWeighted.Data) (n k : ℕ) :
    0 ≤ ConfiguredDiagonalStableRowDefectProvider.error D
      (physicalCoeff D) n k :=
  (ConfiguredDiagonalStableRowDefectProvider.provider D
    (physicalCertificate D)).nonnegative n k

/-- The configured physical diagonal is summable in every triangular row. -/
theorem configuredError_summable
    (D : ConstructedConfiguredSequenceWeighted.Data) (n : ℕ) :
    Summable (ConfiguredDiagonalStableRowDefectProvider.error D
      (physicalCoeff D) n) :=
  (ConfiguredDiagonalStableRowDefectProvider.provider D
    (physicalCertificate D)).summable n

/-- The only finite Harnack datum not already stored by the recursive stages
is the depth-zero configured base certificate. -/
def finiteHarnack_of_base
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (baseHarnack : ∀ n, VariableMarkedTube.ArclengthHarnackCertificate
      (Q n)) :
    ∀ n k, VariableMarkedTube.ArclengthHarnackCertificate (F.columns n k) := by
  intro n k
  cases k with
  | zero => simpa using baseHarnack n
  | succ k => exact (F.stage n k).stage.rear_harnack

namespace RecursiveConstruction

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- The rich stage on the actually reachable recursive state.  This is the
sound substitute for coercing a recursive provider to a total sliced
provider on states for which no recursive invariant is available. -/
noncomputable def stage
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) :
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData
      (markedGrid F n k) (markedGrid F (n + 1) k)
      (markedGrid F n (k + 1)) (e n (k + 1))
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt := by
  change TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData
    ((F.state k).column.column.step.next n)
    ((F.state k).column.column.step.next (n + 1))
    ((F.state (k + 1)).column.column.step.next n) (e n (k + 1))
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt
  change TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RichStageData
    ((F.state k).column.column.step.next n)
    ((F.state k).column.column.step.next (n + 1))
    ((RecursivePresentedSlicedState.next F.provider
      (F.state k)).column.column.step.next n) (e n (k + 1))
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt
  simpa [RecursivePresentedSlicedState.next, successorAt, rowFamilyAt,
    RecursivePresentedConstructionCore.state_depth] using
      ((successorAt F k).column.step.richStage n)

/-- Reachable recursive stages form the direct geometric scheme required by
the source-free explicit-front capstone. -/
def geometricScheme
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (error_nonnegative : ∀ n k, 0 ≤ e n k)
    (error_summable : ∀ n, Summable (e n))
    (tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k)) :
    GeometricScheme Q (markedGrid F)
      (FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly.ConstructionCore.depthError e)
      P0 P1 khat G1 Cg C c dlt where
  base := F.base_eq
  error_nonnegative := fun n k => error_nonnegative n (k + 1)
  error_summable := fun n => by
    simpa [FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly.ConstructionCore.depthError,
      Nat.add_comm] using ShadowingTails.summable_shift (error_summable n) 1
  tube := tube
  stepPath := fun n k => (stage F n k).stage.increment
  stepGeometry := fun n k => (stage F n k).stage.increment_geometry
  stepCost := fun n k => (stage F n k).stage.increment_cost
  finiteEdge := fun n k => (stage F n k).stage.range_edge

/-- The physical grid has no incoming edge at depth zero.  Filling that
boundary with the displayed base datum gives an exact identity marking while
leaving every selected-rear edge unchanged. -/
def rearRows
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n : ℕ) : ℕ → Data
  | 0 => markedGrid F n 0
  | k + 1 => rearGrid F n (k + 1)

/-- Actual selected rows retain the normalized marking from each ordinary
rear representative to the displayed recursive node. -/
def directPhysicalMarkings
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) :
    DirectPhysicalTerminalMarkingFamily (rearRows F) (markedGrid F) where
  lambda n k := match k with
    | 0 => 1
    | k + 1 => ((rowFamilyAt F k).row n).terminalInput.lambda
  Lambda n k := match k with
    | 0 => 1
    | k + 1 => ((rowFamilyAt F k).row n).terminalInput.Lambda
  marking n k := by
    cases k with
    | zero =>
        exact NormalizedC2Marking.refl (markedGrid F n 0)
    | succ k =>
        let W := (rowFamilyAt F k).row n
        change NormalizedC2Marking W.presented W.output.jets.rear
          W.terminalInput.lambda W.terminalInput.Lambda
        exact
          { lambda_pos := W.terminalInput.lambda_pos
            marking := W.output.marking
            ddpsi := W.output.ddpsi
            psi_deriv := W.output.psi_deriv
            dpsi_deriv := W.output.dpsi_deriv
            ddpsi_cont := W.output.ddpsi_cont
            psi_zero := W.output.psi_zero }

/-- Positive variable speed at the marked basepoint supplies the perimeter
nondegeneracy needed only for converting raw ranges to arclength ranges. -/
theorem markedPerim_ne
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (hc : 0 < c)
    (tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k)) (n k : ℕ) :
    perim (markedGrid F n k) ≠ 0 := by
  apply ne_of_gt
  exact hc.trans_le (by simpa [perim] using (tube n k).speed_lb 0)

/-- The migrated range grid, with all marking and curvature-ceiling bridges
discharged from the recursive provider and the configured constant `sourceKh`. -/
noncomputable def configuredRangeKinematics
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (hkh : ∀ n, kh n = sourceKh) (hc : 0 < c)
    (tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k)) :
    FinitePullbackPhysicalRearRangeKinematics sourceKh
      (rearRows F) (markedGrid F) := by
  let R := rangeKinematics F sourceKh hkh (markedPerim_ne F hc tube)
  exact
    { front := R.front
      stage := by
        intro n k
        simpa [rearRows] using R.stage n k
      front_range := R.front_range }

/-- A vanishing endpoint modulus gives the exact physical/marked defect
convergence consumed by the explicit-front capstone. -/
theorem physicalDefect_tendsto_of_rho
    {B P : ℕ → ℕ → Data} {rho : ℕ → ℕ → ℝ}
    (hdist : ∀ n k, dist (B n k) (P n k) ≤ rho n k)
    (hrho : ∀ n, Tendsto (rho n) atTop (nhds 0)) (n : ℕ) :
    Tendsto (fun k => dist (B n k) (P n k)) atTop (nhds 0) :=
  squeeze_zero (fun _ => dist_nonneg) (hdist n) (hrho n)

/-- Presented analogue of the legacy row cap.  It is tied to the actual
`PresentedOutputCore`, so no coercion to an independently chosen terminal is
involved. -/
structure PresentedRowCap
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {S : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (M endpoint defect : ℝ) : Prop where
  cost_le_M : R.output.chosen.Delta.cost ≤ M
  coefficient_le :
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
      R.terminalInput.Lmax (rearPeriod (S.source n) 0)
      (GaugeMarkedDataOfRearFamily.rearKappa1 (kh n))
      (GaugeMarkedDataOfRearFamily.rearKappa2 (kh n)) M
      R.terminalInput.physical.L R.terminalInput.physical.kb
      R.terminalInput.physical.kL ≤ endpoint
  cost_le_defect : R.output.chosen.Delta.cost ≤ defect

/-- The retained exact marking modulus linearizes to the presented row cap. -/
theorem PresentedRowCap.endpoint_dist_le
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 M endpoint defect : ℝ}
    {S : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    {R : PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S}
    (hM : 0 ≤ M) (H : PresentedRowCap R M endpoint defect) :
    dist R.output.jets.rear R.presented ≤ endpoint * defect := by
  have hL : 0 ≤ R.terminalInput.physical.L := by
    rw [← R.terminalInput.physical.perim_eq]
    exact zero_le_one.trans R.terminal_perim_ge_one
  have hkb : 0 ≤ R.terminalInput.physical.kb :=
    (abs_nonneg (R.terminalInput.physical.curvature 0)).trans
      (R.terminalInput.physical.curvature_bound 0)
  have hkL : 0 ≤ R.terminalInput.physical.kL := by
    have Hlip := R.terminalInput.physical.curvature_lipschitz 0 1
    have H0 := (abs_nonneg
      (R.terminalInput.physical.curvature 0 -
        R.terminalInput.physical.curvature 1)).trans Hlip
    norm_num at H0
    exact H0
  have hlinear : dist R.output.jets.rear R.presented ≤
      InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
        R.terminalInput.Lmax (rearPeriod (S.source n) 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 (kh n))
        (GaugeMarkedDataOfRearFamily.rearKappa2 (kh n)) M
        R.terminalInput.physical.L R.terminalInput.physical.kb
        R.terminalInput.physical.kL * R.output.chosen.Delta.cost := by
    apply R.output.endpoint_dist.trans
    apply InterpolationVariableSpeedSelInvAdapter.markingC2Bound_flow_le_linear
    · exact ((S.source n).rear_period_pos 0).le.trans
        (R.terminalInput.rearPeriod_le 0)
    · exact ((S.source n).rear_period_pos 0).le
    · exact GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
        (S.source n).kh_nonnegative (S.source n).kh_lt_one
    · exact GaugeMarkedDataOfRearFamily.rearKappa2_nonneg
        (S.source n).kh_nonnegative (S.source n).kh_lt_one
    · exact hM
    · exact hL
    · exact hkb
    · exact hkL
    · exact R.output.chosen.Delta.cost_nonneg
    · exact H.cost_le_M
  have hcanonical : 0 ≤
      InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst
        R.terminalInput.Lmax (rearPeriod (S.source n) 0)
        (GaugeMarkedDataOfRearFamily.rearKappa1 (kh n))
        (GaugeMarkedDataOfRearFamily.rearKappa2 (kh n)) M
        R.terminalInput.physical.L R.terminalInput.physical.kb
        R.terminalInput.physical.kL :=
    InterpolationVariableSpeedSelInvAdapter.canonicalMarkingLinearConst_nonneg
      (((S.source n).rear_period_pos 0).le.trans
        (R.terminalInput.rearPeriod_le 0))
      (GaugeMarkedDataOfRearFamily.rearKappa1_nonneg
        (S.source n).kh_nonnegative (S.source n).kh_lt_one)
  exact hlinear.trans
    (mul_le_mul H.coefficient_le H.cost_le_defect
      R.output.chosen.Delta.cost_nonneg
      (hcanonical.trans H.coefficient_le))

/-- The full `C²` endpoint estimate retained by each chosen `RowCap` closes
the physical/marked row defect as soon as its scalar diagonal vanishes. -/
theorem physicalDefect_tendsto_of_rowCaps
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    {M : ℝ} (hM : 0 ≤ M) (endpoint : ℕ → ℝ)
    (defect : ℕ → ℕ → ℝ)
    (caps : ∀ n k,
      PresentedRowCap
        ((rowFamilyAt F k).row n) M (endpoint n) (defect n k))
    (hdefect : ∀ n, Tendsto (defect n) atTop (nhds 0)) (n : ℕ) :
    Tendsto (fun k => dist (rearRows F n k) (markedGrid F n k))
      atTop (nhds 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro k
    have H := PresentedRowCap.endpoint_dist_le hM (caps n k)
    simpa [rearRows, rearGrid, markedGrid, rowFamilyAt, successorAt,
      RecursivePresentedConstructionCore.state,
      RecursivePresentedSlicedState.next, dist_comm] using H
  · simpa using (tendsto_const_nhds.mul (hdefect n))

/-- The ordinary terminal acceleration is controlled by its retained period
and curvature ceilings. -/
theorem presented_acc_le
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {depth n : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 L K : ℝ}
    {S : CorrelatedColumn Q current e depth P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax K0 K1 K2}
    (R : PresentedRowSelection (n := n) (a := a) (MA := MA) (NA := NA)
      (K0 := K0) (K1 := K1) (K2 := K2) S)
    (hL0 : 0 ≤ L) (hper : perim R.presented ≤ L)
    (hK : R.terminalInput.physical.kb ≤ K) (u : ℝ) :
    ‖R.presented.2.2 u‖ ≤ L ^ 2 * K := by
  have hp0 : 0 ≤ perim R.presented :=
    zero_le_one.trans R.terminal_perim_ge_one
  have hkb0 : 0 ≤ R.terminalInput.physical.kb :=
    (abs_nonneg (R.terminalInput.physical.curvature 0)).trans
      (R.terminalInput.physical.curvature_bound 0)
  rw [MarkedSpace.acc_eq
    R.terminalInput.physical.cq_pos R.terminalInput.zero_floor_tube
    R.terminalInput.physical.curve_frenet
    R.terminalInput.physical.angle_deriv]
  have hexp : ‖Complex.exp (Complex.I *
      (R.terminalInput.physical.Theta (perim R.presented * u) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sq,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, hexp, one_mul, mul_one]
  exact mul_le_mul ((sq_le_sq₀ hp0 hL0).2 hper)
    ((R.terminalInput.physical.curvature_bound _).trans hK)
    (abs_nonneg _) (sq_nonneg L)

/-- Assemble uniform physical row bounds from the depth-zero configured
datum and the scalar equalities/ceilings retained by every actual presented
terminal.  Successor perimeter bounds and accelerations are derived here. -/
def physicalRowBounds_of_presented
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    {cb db : ℝ}
    (baseTube : ∀ n, IsTubeMember cb 0 db (markedGrid F n 0))
    (basePerimLower : ∀ n, 1 ≤ perim (markedGrid F n 0))
    (basePerimUpper : ∀ n, perim (markedGrid F n 0) ≤ Qmax n)
    (baseAcc : ∀ n u, ‖(markedGrid F n 0).2.2 u‖ ≤ Qmax n ^ 2 * khat n)
    (hkhat : ∀ n, 0 ≤ khat n)
    (succCq : ∀ n k, cb ≤
      ((rowFamilyAt F k).row n).terminalInput.physical.cq)
    (succDlt : ∀ n k, db ≤
      ((rowFamilyAt F k).row n).terminalInput.physical.dlt)
    (succKb : ∀ n k,
      ((rowFamilyAt F k).row n).terminalInput.physical.kb ≤ khat n)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (endpoint : ∀ n k,
      dist (rearRows F n k) (markedGrid F n k) ≤ r n) :
    PhysicalRowBounds (rearRows F) (markedGrid F) cb db where
  Lmin := fun _ => 1
  Lmax := Qmax
  Ab := fun n => Qmax n ^ 2 * khat n
  r := r
  Lmin_pos := fun _ => one_pos
  Ab_nonneg := fun n => mul_nonneg (sq_nonneg _) (hkhat n)
  r_nonneg := hr
  physical_tube := by
    intro n k
    cases k with
    | zero => exact baseTube n
    | succ k =>
        have H := ((rowFamilyAt F k).row n).terminalInput.zero_floor_tube
        simpa [rearRows] using H.mono (succCq n k) (succDlt n k)
  physical_perim_lower := by
    intro n k
    cases k with
    | zero => exact basePerimLower n
    | succ k =>
        simpa [rearRows, rearGrid, successorAt,
          FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor.PresentedRowFamily.successor,
          FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor.successorOfPresentedRows]
          using ((rowFamilyAt F k).row n).terminal_perim_ge_one
  physical_perim_upper := by
    intro n k
    cases k with
    | zero => exact basePerimUpper n
    | succ k =>
        let W := (rowFamilyAt F k).row n
        have H := ((F.state k).column.source n).rear_period_le
          ((F.state k).column.column.step.richStage (n + 1)).stage.increment.T
        have HT := W.terminalInput.rearPeriod_terminal
        have hEq : ((successorAt F k).column.step.richStage n).terminalBase =
            W.presented := rfl
        change perim ((successorAt F k).column.step.richStage n).terminalBase ≤ Qmax n
        rw [hEq, ← HT]
        exact H
  physical_acc := by
    intro n k u
    cases k with
    | zero => exact baseAcc n u
    | succ k =>
        let W := (rowFamilyAt F k).row n
        have hp : perim W.presented ≤ Qmax n := by
          have H := ((F.state k).column.source n).rear_period_le
            ((F.state k).column.column.step.richStage (n + 1)).stage.increment.T
          exact W.terminalInput.rearPeriod_terminal ▸ H
        have hQ0 : 0 ≤ Qmax n :=
          (((F.state k).column.source n).rear_period_pos 0).le.trans
            (((F.state k).column.source n).rear_period_le 0)
        simpa [rearRows, rearGrid, successorAt,
          FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor.PresentedRowFamily.successor,
          FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor.successorOfPresentedRows,
          W] using presented_acc_le W hQ0 hp (succKb n k) u
  endpoint_dist := endpoint

/-- Direct paper-facing closure of a reachable recursive construction.  The
ordinary rear bounds, front tubes, and vanishing endpoint modulus are the
three genuinely geometric quantitative inputs; row markings, range alignment,
and the subunit curvature constant are automatic. -/
theorem exists_paperFacingOutput
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (error_nonnegative : ∀ n k, 0 ≤ e n k)
    (error_summable : ∀ n, Summable (e n))
    (tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k))
    (hkh : ∀ n, kh n = sourceKh)
    {cb db cp dp : ℝ}
    (physical : PhysicalRowBounds (rearRows F) (markedGrid F) cb db)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (frontTube : ∀ n k, IsTubeMember cp 0 dp (physicalFrontGrid F n k))
    (physicalDefect : ∀ n, Tendsto
      (fun k => dist (rearRows F n k) (markedGrid F n k))
      atTop (nhds 0))
    (hc : 0 < c) {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤ MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (markedGrid F)
      (FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly.ConstructionCore.depthError e)
      P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q (markedGrid F)
        (FiniteSmoothRearFamilyMarkingAwarePresentedSlicedAssembly.ConstructionCore.depthError e)
        P0 P1 khat G1 Cg C c dlt,
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) :=
  GenericVariableTerminalDirectCapstoneExplicitFront.exists_paperFacingOutput
    (geometricScheme F error_nonnegative error_summable tube)
    (directPhysicalMarkings F) physical sourceKh_nonnegative sourceKh_lt_one
    hcb hdb hcp frontTube (configuredRangeKinematics F hkh hc tube).toMixed
    physicalDefect hc hdirection hQbounded hQwidth hQlength hgap

/-- The direct recursive output has exactly the ordinary-curve content of the
paper theorem; no legacy `CoherentPackage` coercion is required. -/
theorem paperMain_of_paperFacingOutput
    {P : ℕ → ℕ → Data} {err : ℕ → ℕ → ℝ}
    {P0' P1' khat' G1' Cg' C' : ℕ → ℝ} {c' dlt' : ℝ}
    {direction : ℂ} {modelWidth H : ℝ}
    (Z : Nonempty
      (Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q P err P0' P1' khat' G1' Cg' C' c' dlt',
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H)) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨O, Hpaper⟩ := Z
  exact PaperMainTheoremDirectProjection.of_output Hpaper

end RecursiveConstruction

namespace Construction

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
  {jetError : ℕ → ℕ → ℝ}

/-- The independent canonical physical front used by the selected-rear edge
at row `n-1`, depth `k`.  Row zero is irrelevant to the mixed edge relation
and is filled by the configured base datum. -/
def frontRows
    (A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError) : ℕ → ℕ → Data
  | 0, _ => Q 0
  | n + 1, k =>
      ((A.provider.rows (A.core.state k).column
        (A.core.state k).sliced).row n).terminalInput.physicalFront.physicalFront

/-- Every actual presented row retains the exact normalized marking from its
ordinary rear presentation to the displayed marked column. -/
def directPhysicalMarkings
    (A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError) :
    DirectPhysicalTerminalMarkingFamily
      (FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows A)
      A.core.columns where
  lambda n k := match k with
    | 0 => 1
    | k + 1 => ((A.provider.rows (A.core.state k).column
        (A.core.state k).sliced).row n).terminalInput.lambda
  Lambda n k := match k with
    | 0 => 1
    | k + 1 => ((A.provider.rows (A.core.state k).column
        (A.core.state k).sliced).row n).terminalInput.Lambda
  marking n k := by
    cases k with
    | zero =>
        simpa [FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows]
          using NormalizedC2Marking.refl (Q n)
    | succ k =>
        let W := (A.provider.rows (A.core.state k).column
          (A.core.state k).sliced).row n
        change NormalizedC2Marking W.presented W.output.jets.rear
          W.terminalInput.lambda W.terminalInput.Lambda
        exact
          { lambda_pos := W.terminalInput.lambda_pos
            marking := W.output.marking
            ddpsi := W.output.ddpsi
            psi_deriv := W.output.psi_deriv
            dpsi_deriv := W.output.dpsi_deriv
            ddpsi_cont := W.output.ddpsi_cont
            psi_zero := W.output.psi_zero }

/-- The migrated presented provider gives mixed rear/front kinematics without
identifying the canonical physical front with the variable marked column. -/
def mixedPhysicalKinematics
    (A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError)
    {kh0 : ℝ} (hkh : ∀ n, kh n = kh0) :
    MixedFinitePhysicalRearKinematics kh0
      (FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows A)
      (frontRows A) where
  stage n k := by
    let W := (A.provider.rows (A.core.state k).column
      (A.core.state k).sliced).row n
    have H : Nonempty (PhysicalRearLimitKinematics (kh n)
        W.presented W.terminalInput.physicalFront.physicalFront) :=
      ⟨W.terminalInput.physicalFront.kinematics⟩
    simpa [FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows,
      frontRows, hkh n] using H

/-- The presented construction, its explicit canonical fronts, and rowwise
physical bounds give the exact `CapFamily`.  No equality between physical
fronts and marked columns is used. -/
def capFamily_of_explicitFront
    (A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError)
    (error_nonnegative : ∀ n k, 0 ≤ e n k)
    (error_summable : ∀ n, Summable (e n))
    (variableTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (A.core.columns n k))
    {kh0 cb db cp dp : ℝ}
    (physical : PhysicalRowBounds
      (FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows A)
      A.core.columns cb db)
    (hkh : ∀ n, kh n = kh0)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (frontTube : ∀ n k, IsTubeMember cp 0 dp (frontRows A n k))
    (physicalDefect : ∀ n, Tendsto
      (fun k ↦ dist
        (FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows A n k)
        (A.core.columns n k))
      atTop (nhds 0)) : CapFamily A.core := by
  let G : GeometricScheme Q A.core.columns
      (ConstructionCore.depthError e) P0 P1 khat G1 Cg C c dlt :=
    { base := A.core.columns_zero
      error_nonnegative := fun n k => error_nonnegative n (k + 1)
      error_summable := fun n => by
        simpa [ConstructionCore.depthError, Nat.add_comm] using
          ShadowingTails.summable_shift (error_summable n) 1
      tube := variableTube
      stepPath := fun n k => (A.core.stage n k).stage.increment
      stepGeometry := fun n k => (A.core.stage n k).stage.increment_geometry
      stepCost := fun n k => (A.core.stage n k).stage.increment_cost
      finiteEdge := fun n k => (A.core.stage n k).stage.range_edge }
  let S := G.toScheme physical hkh0 hkh1 hcb hdb hcp frontTube
    (mixedPhysicalKinematics A hkh) physicalDefect
  exact
    { error_nonnegative := error_nonnegative
      error_summable := error_summable
      tube := variableTube
      limitHarnack := S.limitHarnack }

/-- The same explicit-front data produce the oriented representatives needed
by the paper-facing closing step. -/
def orientedRepresentatives_of_explicitFront
    (A : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2 jetError)
    (variableTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (A.core.columns n k))
    {kh0 cb db cp dp : ℝ}
    (physical : PhysicalRowBounds
      (FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows A)
      A.core.columns cb db)
    (hkh : ∀ n, kh n = kh0)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1)
    (hc : 0 < c) (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (frontTube : ∀ n k, IsTubeMember cp 0 dp (frontRows A n k))
    (physicalDefect : ∀ n, Tendsto
      (fun k ↦ dist
        (FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows A n k)
        (A.core.columns n k))
      atTop (nhds 0))
    (O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput Q
      A.core.columns (ConstructionCore.depthError e)
      P0 P1 khat G1 Cg C c dlt) :
    ∀ n, VariableMarkedTube.OrientedArclengthRepresentative (O.X n) := by
  have hphysical : ∀ n, Tendsto
      (FiniteSmoothRearFamilyMarkingAwarePresentedNearIdentityClosure.Construction.physicalRows A n)
      atTop (nhds (O.X n)) := by
    intro n
    exact EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
      (O.row_limit n) (physicalDefect n)
  let rowGeometry := geometricRowMarkingDataDirect (directPhysicalMarkings A)
    physical hc variableTube
  let markingBounds := rowGeometry.toRowwiseBounds
  intro n
  let W := limitOrientedReparametrization_of_rowwise_bounds
    (markingBounds.lambda_pos n) (markingBounds.secondBound_nonneg n)
    (markingBounds.reparametrization n) (hphysical n) (O.row_limit n)
    (markingBounds.basepoint n) (markingBounds.psi_hasDerivAt n)
    (markingBounds.ddpsi n) (markingBounds.dpsi_hasDerivAt n)
    (markingBounds.ddpsi_bound n)
  have hbase : IsTubeMember cb 0 db (O.X n) :=
    (isClosed_tube cb 0 db).mem_of_tendsto (hphysical n)
      (Eventually.of_forall (physical.physical_tube n))
  exact orientedArclengthRepresentative_of_orientedReparametrization
    hcb hdb W.lambda_pos hbase W.reparametrization W.psi_hasDerivAt
    W.dpsi_continuous W.surjective
    (limitStrictnessDataH_of_explicitFrontRowLimit
      hkh0 hkh1 hcb hcp physical.physical_tube frontTube
      (mixedPhysicalKinematics A hkh) (hphysical n))

end Construction

/-- A configured large-separation output discharges every row-zero closing
obligation for the presented capstone.  Because the presented construction
drops the depth-zero path error, its shadow tail starts at index one; the
configured full row radius is therefore still a valid upper bound. -/
theorem exists_coherentPackage_of_configuredClosing
    {D : ConstructedConfiguredSequenceWeighted.Data}
    {conversion diagonal : ℕ → ℝ} {Cw : ℝ}
    (L : Output D conversion diagonal Cw)
    {Qmodel : ℕ → Data} {kh0 C0 K : ℝ} {d : ℕ → ℝ}
    (A : ConfiguredCanonicalPairSource.Output
      (shift D L.N) Qmodel kh0 C0 K d)
    (hQ : ∀ n, perim (Qmodel n) = 2 * (shift D L.N).Hs n ∧
      ev (Qmodel n) = TwoCapPairsAssembly.front
        ((shift D L.N).kappas n) (shift D L.N).model.thetaBase
        ((shift D L.N).Hs n))
    {P0 P1 khat G1 Cg : ℕ → ℝ} {period : ℕ → ℕ → ℝ}
    {sourceKh Qmax : ℕ → ℝ}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore
      (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
      (rowError (shiftSequence diagonal L.N)) P0 P1 khat G1 Cg
      (outputUpper D L) ((shift D L.N).Hs 0)
      (chordBase (shift D L.N).model / 2) period
      (shiftSequence diagonal L.N) sourceKh Qmax a MA NA K0 K1 K2)
    (R : CapFamily F)
    (hpathConversion : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) ≤
          shiftSequence conversion L.N n)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    (hmodelWidth : Width.width
      (range (TwoCapPairsAssembly.front ((shift D L.N).kappas 0)
        (shift D L.N).model.thetaBase ((shift D L.N).Hs 0))) direction ≤ Cw)
    (representatives : ∀ O :
      TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        (ConfiguredGaugeFirstPhysicalSequence.alignedQ A.input hQ)
        F.columns (ConstructionCore.depthError
          (rowError (shiftSequence diagonal L.N)))
        P0 P1 khat G1 Cg (outputUpper D L) ((shift D L.N).Hs 0)
        (chordBase (shift D L.N).model / 2),
      ∀ n, VariableMarkedTube.OrientedArclengthRepresentative (O.X n)) :
    Nonempty (CoherentPackage F R direction Cw ((shift D L.N).Hs 0)) := by
  let D' := shift D L.N
  apply CoherentPackage.exists_of_orientedRepresentatives
    D'.separation_zero_pos representatives hdirection
  · exact ConfiguredAlignedQGeometry.bounded_range A hQ 0
  · rw [ConfiguredAlignedQGeometry.width_zero_eq_model A hQ]
    exact hmodelWidth
  · rw [ConfiguredAlignedQGeometry.totalLength_eq A hQ 0]
  · intro O
    have htail : ShadowingTails.tail
        (ConstructionCore.depthError
          (rowError (shiftSequence diagonal L.N)) 0) 0 ≤
        ShadowingTails.tail (rowError (shiftSequence diagonal L.N) 0) 0 := by
      have hanti := ShadowingTails.tail_antitone (R.error_summable 0)
        (R.error_nonnegative 0) (Nat.zero_le 1)
      simpa [ConstructionCore.depthError, ShadowingTails.tail,
        Nat.add_assoc, Nat.add_comm] using hanti
    have hshadow : PaperFacingVariableTerminalOutput.shadowSize O ≤
        rowRadius (shiftSequence conversion L.N)
          (shiftSequence diagonal L.N) 0 := by
      calc
        PaperFacingVariableTerminalOutput.shadowSize O =
            NormalPathC2IncrementVariableSpeed.c2ConstVar
              (P0 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
              ShadowingTails.tail
                (ConstructionCore.depthError
                  (rowError (shiftSequence diagonal L.N)) 0) 0 := rfl
        _ ≤ NormalPathC2IncrementVariableSpeed.c2ConstVar
              (P0 0) (P1 0) (khat 0) (G1 0) (Cg 0) *
              ShadowingTails.tail
                (rowError (shiftSequence diagonal L.N) 0) 0 :=
          mul_le_mul_of_nonneg_left htail
            (NormalPathC2IncrementVariableSpeed.c2ConstVar_nonneg _ _ _ _ _)
        _ ≤ shiftSequence conversion L.N 0 *
              ShadowingTails.tail
                (rowError (shiftSequence diagonal L.N) 0) 0 :=
          mul_le_mul_of_nonneg_right (hpathConversion 0)
            (ShadowingTails.tail_nonneg (R.error_nonnegative 0) 0)
        _ = rowRadius (shiftSequence conversion L.N)
              (shiftSequence diagonal L.N) 0 := rfl
    have hleft : Cw + 2 * PaperFacingVariableTerminalOutput.shadowSize O ≤
        Cw + 2 * rowRadius (shiftSequence conversion L.N)
          (shiftSequence diagonal L.N) 0 := by linarith
    have hright :
        (2 * D'.Hs 0 - rowRadius (shiftSequence conversion L.N)
            (shiftSequence diagonal L.N) 0) / Real.pi ≤
        (2 * D'.Hs 0 - PaperFacingVariableTerminalOutput.shadowSize O) /
          Real.pi :=
      div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    exact hleft.trans_lt (L.width_gap.trans_le hright)

end ConfiguredRecursiveEdgePresentedCapstoneAdapter
