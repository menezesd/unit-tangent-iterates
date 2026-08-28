import UnitTangentIterates.ConfiguredRecursiveEdgeRecostScaledPaperCapstone
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRowState
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricGeometry
import UnitTangentIterates.ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareActualPullbackSynchronizedRows
import UnitTangentIterates.ConfiguredRecursiveEdgePresentedPhysicalSidecars

/-!
# Synchronized direct-recost grid for the paper capstone

`Direct.Provider.stages` is a single chain, not the triangular paper array.
Here each cell is evaluated at its exact public diagonal index.  Raw chosen
geometry controls displayed distance; the recost split history is retained
only by the recursive source provider.
-/

noncomputable section

open Function Set MarkedSpace PathMetric

namespace ConfiguredRecursiveEdgeRecostedDirectCapstoneAdapter

open ConfiguredCanonicalPairSource
  ConfiguredCombinedPhysicalDiagonalLargeSeparation
  ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant
  ConfiguredRecursiveEdgeFiniteColumnScalarClosing
  ConfiguredRecursiveEdgeFinitePresentedFinalAssembly
  ConfiguredRecursiveEdgeRecostPeriodScaledDiagonal
  ConfiguredRecursiveEdgeRecostScaledPaperCapstone
  ConfiguredRecursiveEdgeRecostedAnalyticCarrier
  ConfiguredRecursiveEdgeRecostedRawMetricGeometry
  ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows
  ConfiguredRecursiveEdgeRecostedRowState
  ConfiguredRecursiveEdgeSourceP0
  ConfiguredRecursiveEdgeSourceP0Growth
  ConfiguredRecursiveEdgeSourceP0RowJetTail
  ConfiguredRecursiveEdgeWeightedEffectiveError
  ConfiguredRecursiveSourceP0FixedDistortion
  ConstructedConfiguredInductiveTubeBudget.WeightedData
  ExponentialDiagonalLargeSeparation
  FiniteSmoothRearFamilyMarkingAwareActualPullbackStages
  FiniteSmoothRearFamilyMarkingAwareGeometricExactFiniteTower
  FiniteSmoothRearFamilyMarkingAwareGeometricPresentedArray
  FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  NormalPathC2IncrementVariableSpeed
  VariableMarkedTube

open FiniteSmoothRearFamilyMarkingAwarePresentedExplicitPhysicalArrays.GeometricArray

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}

abbrev rowData (J : RowJetScalarOutput choice.MA0 choice.NA0) :
    ConstructedConfiguredSequenceWeighted.Data :=
  ConfiguredRecursiveEdgeRecostScaledPaperCapstone.data J

/-- A triangular family of reachable stages.  Horizontal successor equality
and diagonal rear-range coherence are deliberately separate fields. -/
structure Grid (J : RowJetScalarOutput choice.MA0 choice.NA0) where
  D : ConstructedConfiguredSequenceWeighted.Data
  E0 : ℕ → ℝ
  C00 : ℕ → ℝ
  C10 : ℕ → ℝ
  C20 : ℕ → ℝ
  d0 : ℕ → ℕ → ℝ
  rows : ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Rows
    D E0 C00 C10 C20 d0
  rawBound_eq : ∀ n k,
    ((rows.step k (rows.stages k)).rawMetric n).rawBound =
      recostSourceAllowance (rowData J) distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 (publicIndex J n k)
  conversion : ∀ n k,
    ((rows.step k (rows.stages k)).rawMetric n).toRawMetricGeometry.pathFactor ≤
      edgeConversion (rowData J) (analyticKhat (rowData J))
        choice.MA0 choice.NA0 (publicIndex J n k)
  endpoint : ∀ n k,
    ((rows.step k (rows.stages k)).carrier n).geometric.endpointCap ≤
      edgeEndpointConversion (rowData J) sourceKh J.scalar.Mend
          (publicIndex J n k) *
        edgePhysicalDefect (rowData J) (publicIndex J n k + 1)

namespace Grid

def ofRows
    (D : ConstructedConfiguredSequenceWeighted.Data)
    (E0 C00 C10 C20 : ℕ → ℝ) (d0 : ℕ → ℕ → ℝ)
    (R : ConfiguredRecursiveEdgeRecostedRawMetricDiagonalRows.Rows
      D E0 C00 C10 C20 d0)
    (hraw : ∀ n k,
      ((R.step k (R.stages k)).rawMetric n).rawBound =
        recostSourceAllowance (rowData J) distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 (publicIndex J n k))
    (hconversion : ∀ n k,
      ((R.step k (R.stages k)).rawMetric n).toRawMetricGeometry.pathFactor ≤
        edgeConversion (rowData J) (analyticKhat (rowData J))
          choice.MA0 choice.NA0 (publicIndex J n k))
    (hendpoint : ∀ n k,
      ((R.step k (R.stages k)).carrier n).geometric.endpointCap ≤
        edgeEndpointConversion (rowData J) sourceKh J.scalar.Mend
            (publicIndex J n k) *
          edgePhysicalDefect (rowData J) (publicIndex J n k + 1)) : Grid J where
  D := D
  E0 := E0
  C00 := C00
  C10 := C10
  C20 := C20
  d0 := d0
  rows := R
  rawBound_eq := hraw
  conversion := hconversion
  endpoint := hendpoint

def stage (H : Grid J) (n k : ℕ) := H.rows.stages k n

def row (H : Grid J) (n k : ℕ) :=
  (H.rows.step k (H.rows.stages k)).carrier n

def rawMetric (H : Grid J) (n k : ℕ) :
    RawMetricGeometry.Bounded (H.row n k).geometric :=
  (H.rows.step k (H.rows.stages k)).rawMetric n

def P (H : Grid J) (n k : ℕ) : Data :=
  H.rows.P n k

@[simp] theorem P_succ (H : Grid J) (n k : ℕ) :
    H.P n (k + 1) = (H.row n k).geometric.base := by
  change (H.stage n (k + 1)).displayed = _
  rfl

private theorem base_rear_curve_range
    {P0 kh khat Qmax : ℕ → ℝ} {q : ℕ}
    {S : Stage P0 kh khat Qmax q} (G : GeometricInput S) :
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

theorem stages_range (H : Grid J) : ∀ k n,
    range (H.stage n k).rear.1 = range (H.stage (n + 1) k).displayed.1 := by
  intro k
  induction k with
  | zero => exact H.rows.base_range
  | succ k ih =>
      intro n
      exact (base_rear_curve_range (H.row (n + 1) k).geometric).symm

private theorem two_le_recostPeriodScale
    (D : ConstructedConfiguredSequenceWeighted.Data) (q : ℕ) :
    2 ≤ recostPeriodScale D q := by
  have hH : 0 ≤ D.Hs (q + 1) := (D.model.separation_pos (q + 1)).le
  unfold recostPeriodScale edgeSpeedCap speedCap
  nlinarith [sq_nonneg (3 * (1 + D.Hs (q + 1)) - 1)]

/-- The raw chosen-path budget is absorbed by the period-scaled direct
diagonal.  In particular, no recost geometry theorem occurs in this proof. -/
theorem rawMetric_le_directDiagonal (H : Grid J) (n k : ℕ) :
    (H.rawMetric n k).edgeBudget ≤
      recostDirectDiagonal (rowData J) choice.MA0 choice.NA0
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        J.scalar.Mend (publicIndex J n k) := by
  let q := publicIndex J n k
  let G := (H.row n k).geometric
  let M := H.rawMetric n k
  let K := M.toRawMetricGeometry.pathFactor
  let T := ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget
    distortionTotal physicalTransitionCeilings.C0
      physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
  let s := recostPeriodScale (rowData J) q
  let e := edgePhysicalDefect (rowData J) (q + 1)
  let c := edgeConversion (rowData J) (analyticKhat (rowData J))
    choice.MA0 choice.NA0 q
  let z := edgeEndpointConversion (rowData J) sourceKh J.scalar.Mend q
  let a := directScale distortionTotal physicalTransitionCeilings.C0
    physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
  have hK0 : 0 ≤ K := M.toRawMetricGeometry.pathFactor_nonnegative
  have hT0 : 0 ≤ 4 * T := mul_nonneg (by norm_num)
    (ConfiguredRecursiveEdgeFiniteColumnGaugeMajorant.configuredTarget_nonnegative
      _ _ _ _)
  have ha0 : 0 ≤ a := directScale_nonnegative _ _ _ _
  have hs0 : 0 ≤ s := recostPeriodScale_nonnegative (rowData J) q
  have he0 : 0 ≤ e := edgePhysicalDefect_nonnegative (rowData J) (q + 1)
  have hc0 : 0 ≤ c := edgeConversion_nonnegative
    (rowData J) (analyticKhat (rowData J)) choice.MA0 choice.NA0 q
  have hz0 : 0 ≤ z := edgeEndpointConversion_nonnegative
    (rowData J) sourceKh_nonnegative sourceKh_lt_one q
  have hs2 : 2 ≤ s := two_le_recostPeriodScale (rowData J) q
  have hfour : 4 * T ≤ a := by
    simp [a, directScale, T]
  have hprod : (4 * T) * 2 ≤ a * s :=
    mul_le_mul hfour hs2 (by norm_num) ha0
  have hKe : K * e ≤ c * e :=
    mul_le_mul_of_nonneg_right (by
      simpa [q, M, K, c] using H.conversion n k) he0
  have hpath : K *
      recostSourceAllowance (rowData J) distortionTotal
        physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
        physicalTransitionCeilings.C2 q ≤ a * (s * c) * e := by
    calc
      K * recostSourceAllowance (rowData J) distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 q =
          ((4 * T) * 2) * (K * e) := by
        simp [recostSourceAllowance, recostAllowance, T, e]
        ring
      _ ≤ (a * s) * (c * e) :=
        mul_le_mul hprod hKe (mul_nonneg hK0 he0)
          (mul_nonneg ha0 hs0)
      _ = a * (s * c) * e := by ring
  have hone : 1 ≤ a := one_le_directScale _ _ _ _
  have hend : G.endpointCap ≤ a * z * e := by
    calc
      G.endpointCap ≤ z * e := by
        simpa [q, G, z, e, row] using H.endpoint n k
      _ = 1 * (z * e) := by ring
      _ ≤ a * (z * e) :=
        mul_le_mul_of_nonneg_right hone (mul_nonneg hz0 he0)
      _ = a * z * e := by ring
  calc
    M.edgeBudget = K *
        recostSourceAllowance (rowData J) distortionTotal
          physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
          physicalTransitionCeilings.C2 q + G.endpointCap := by
      rw [RawMetricGeometry.Bounded.edgeBudget]
      have hb : M.rawBound =
          recostSourceAllowance (rowData J) distortionTotal
            physicalTransitionCeilings.C0 physicalTransitionCeilings.C1
            physicalTransitionCeilings.C2 q := by
        simpa [M, q, rawMetric] using H.rawBound_eq n k
      rw [hb]
    _ ≤ a * (s * c) * e + a * z * e := add_le_add hpath hend
    _ ≤ recostDirectDiagonal (rowData J) choice.MA0 choice.NA0
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        J.scalar.Mend q := by
      have hextra : 0 ≤ a * s * c * e :=
        mul_nonneg (mul_nonneg (mul_nonneg ha0 hs0) hc0) he0
      calc
        a * (s * c) * e + a * z * e ≤
            (a * (s * c) * e + a * z * e) + a * s * c * e :=
          le_add_of_nonneg_right hextra
        _ = recostDirectDiagonal (rowData J) choice.MA0 choice.NA0
            distortionTotal physicalTransitionCeilings.C0
            physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
            J.scalar.Mend q := by
          simp [recostDirectDiagonal, recostDirectConversion,
            recostCombinedConversion, recostEdgeConversion, weightedSequence,
            a, s, c, z, e]
          ring

theorem step_dist_le_error (H : Grid J) (n k : ℕ) :
    dist (H.P n k) (H.P n (k + 1)) ≤
      ConfiguredRecursiveEdgeRecostScaledPaperCapstone.error J n k := by
  calc
    dist (H.P n k) (H.P n (k + 1)) =
        dist (H.stage n k).displayed (H.row n k).geometric.base := by
      rw [H.P_succ]
      rfl
    _ ≤ (H.rawMetric n k).edgeBudget :=
      (H.rawMetric n k).dist_displayed_base_le
    _ ≤ recostDirectDiagonal (rowData J) choice.MA0 choice.NA0
        distortionTotal physicalTransitionCeilings.C0
        physicalTransitionCeilings.C1 physicalTransitionCeilings.C2
        J.scalar.Mend (publicIndex J n k) := H.rawMetric_le_directDiagonal n k
    _ = ConfiguredRecursiveEdgeRecostScaledPaperCapstone.error J n k :=
      (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.error_eq_directDiagonal
        J n k).symm

private theorem base_rear_geometric_range
    {P0 kh khat Qmax : ℕ → ℝ} {q : ℕ}
    {S : Stage P0 kh khat Qmax q} (G : GeometricInput S) :
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

theorem range_edge (H : Grid J) (n k : ℕ) :
    GeometricUnitTangentRangeEdge (H.P (n + 1) k) (H.P n (k + 1)) := by
  unfold GeometricUnitTangentRangeEdge
  calc
    range (H.P (n + 1) k).1 = range (H.stage n k).rear.1 :=
      (H.stages_range k n).symm
    _ = range (geometricUnitTangent (H.row n k).geometric.output.jets.rear) :=
      (H.row n k).geometric.output.stage.range_edge
    _ = range (geometricUnitTangent (H.P n (k + 1))) := by
      rw [H.P_succ]
      exact (base_rear_geometric_range (H.row n k).geometric).symm

end Grid

structure LocalInput (H : Grid J) (n k : ℕ) where
  P1 : ℝ
  markingLower : ℝ
  markingUpper : ℝ
  facts : Nonaffine.Facts (H.stage n k).source P1 markingLower markingUpper
  frontData_eq : (H.row n k).geometric.terminal.frontData =
    FiniteSmoothRearFamilyMarkingAwarePresentedTerminalGeometry.unitTangentData
      (H.stage n k).source
  frontTube : IsTubeMember (commonC (rowData J)) 0 (commonDlt (rowData J))
    (H.row n k).geometric.terminal.frontData

namespace LocalInput

variable {J : RowJetScalarOutput choice.MA0 choice.NA0}
  {H : Grid J} {n k : ℕ}

def state (L : LocalInput (J := J) H n k) : State where
  start := (H.stage n k).start
  finish := (H.stage n k).rear
  path := (H.stage n k).Gamma
  P0 := Profiles.P0 H.D n k
  kh := Profiles.kh H.D n k
  khat := Profiles.khat H.D n k
  Qmax := Profiles.Qmax H.D n k
  source := (H.stage n k).source
  P1 := L.P1
  markingLower := L.markingLower
  markingUpper := L.markingUpper
  facts := L.facts

def row (L : LocalInput (J := J) H n k) : PresentedRow L.state.source where
  applied := (H.stage n k).applied
  p := H.P n k
  base := (H.row n k).geometric.base
  frontEndpoint := (H.stage n k).rear
  bound := (H.row n k).geometric.bound
  terminalInput := (H.row n k).geometric.terminal
  output := (H.row n k).geometric.output
  cFront := commonC (rowData J)
  kFront := 0
  dFront := commonDlt (rowData J)
  cFront_pos := by
    simpa [commonC] using (rowData J).model.separation_pos 0
  front_tube := L.frontTube
  frontData_eq := L.frontData_eq

def cell (L : LocalInput (J := J) H n k) : Cell H.P n k where
  state := L.state
  row := L.row
  kh_nonnegative := sourceKh_nonnegative
  kh_lt_one := sourceKh_lt_one
  selectedStart := H.P n k
  selectedEnd := (H.row n k).geometric.output.jets.rear
  path := (H.row n k).geometric.rawPath
  physicalFrontData := (H.row n k).geometric.terminal.frontData
  physicalKinematics := ⟨by
    rw [H.P_succ]
    exact (H.row n k).geometric.output.frontKinematics⟩
  physicalRearSpeedConst := by
    intro u v
    rw [H.P_succ]
    exact (H.row n k).geometric.terminal.zero_floor_tube.speed_const u v
  range_edge := H.range_edge n k

end LocalInput

structure CellFamily (H : Grid J) where
  input : ∀ n k, LocalInput H n k
  baseTube : ∀ n,
    IsTubeMember (commonC (rowData J)) 0 (commonDlt (rowData J)) (H.P n 0)

namespace CellFamily

variable {J : RowJetScalarOutput choice.MA0 choice.NA0} {H : Grid J}

def cell (F : CellFamily (J := J) H) (n k : ℕ) : Cell H.P n k :=
  (F.input n k).cell

end CellFamily

structure Assembly (J : RowJetScalarOutput choice.MA0 choice.NA0) where
  grid : Grid J
  cells : CellFamily grid
  C : ℕ → ℝ
  tube : ∀ n k, IsVariableTubeMember
    (commonC (rowData J)) (C n) 0 (commonDlt (rowData J)) (grid.P n k)

namespace Assembly

def core (A : Assembly J) :
    ConfiguredRecursiveEdgeRecostScaledPaperCapstone.GeometricCore J where
  Q := fun n => A.grid.P n 0
  P := A.grid.P
  B0 := fun n => A.grid.P n 0
  C := A.C
  c := commonC (rowData J)
  dlt := commonDlt (rowData J)
  cell := A.cells.cell
  base := fun _ => rfl
  tube := A.tube
  stepDistance := A.grid.step_dist_le_error

def cellFacts (A : Assembly J) :
    ConfiguredRecursiveEdgePresentedPhysicalSidecars.CellFacts
      (rowData J) A.core.array where
  baseTube := A.cells.baseTube
  cellKh := by
    intro n k
    change ((A.cells.input n k).cell).state.kh = sourceKh
    rfl
  cellFrontTube := by
    intro n k
    change IsTubeMember (commonC (rowData J)) 0 (commonDlt (rowData J))
      ((A.cells.input n k).cell).physicalFront
    exact (A.cells.input n k).frontTube

end Assembly

structure CapstoneInput (J : RowJetScalarOutput choice.MA0 choice.NA0) where
  assembly : Assembly J
  kh0 : ℝ
  cb : ℝ
  db : ℝ
  cp : ℝ
  dp : ℝ
  physical : GeometricArray.Package assembly.core.array assembly.core.B0
    kh0 cb db cp dp
  kh0_nonnegative : 0 ≤ kh0
  kh0_lt_one : kh0 < 1
  cb_pos : 0 < cb
  db_pos : 0 < db
  cp_pos : 0 < cp
  Q_zero : assembly.core.Q 0 = J.scalar.Q
    (ConfiguredRecursiveEdgeRecostScaledPaperCapstone.large J).N

namespace CapstoneInput

def directInput (I : CapstoneInput J) :
    ConfiguredRecursiveEdgeRecostScaledPaperCapstone.DirectInput J where
  core := I.assembly.core
  kh0 := I.kh0
  cb := I.cb
  db := I.db
  cp := I.cp
  dp := I.dp
  physical := I.physical
  kh0_nonnegative := I.kh0_nonnegative
  kh0_lt_one := I.kh0_lt_one
  cb_pos := I.cb_pos
  db_pos := I.db_pos
  cp_pos := I.cp_pos
  c_pos := by
    simpa [Assembly.core, commonC] using (rowData J).model.separation_pos 0
  Q_zero := I.Q_zero

theorem paper (I : CapstoneInput J) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L :=
  I.directInput.paper

end CapstoneInput

end ConfiguredRecursiveEdgeRecostedDirectCapstoneAdapter
