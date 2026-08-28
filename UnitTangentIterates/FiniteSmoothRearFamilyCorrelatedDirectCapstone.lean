import UnitTangentIterates.FiniteSmoothRearFamilyCorrelatedPhysicalCore
import UnitTangentIterates.GenericVariableTerminalCapstoneFromEndpointDefect
import UnitTangentIterates.EnrichedPhysicalHarnackClosure
import UnitTangentIterates.GenericVariableTerminalDirectCapstone

/-!
# Direct capstone for the source-preserving correlated recursion

This module connects the actual dependent sequence of correlated columns to
the variable-terminal limit theorem.  It deliberately does not manufacture a
legacy map provider on arbitrary erased columns: all finite physical and
endpoint-defect data are taken from the selected correlated recursion itself.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed

namespace FiniteSmoothRearFamilyCorrelatedDirectCapstone

open FiniteSmoothRearFamilyCorrelatedPhysicalCore
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  RichFamilyPhysicalMarkingIntegration VariableMarkedTube
  GaugeRearFamilyVariableTerminal VariableTerminalRowTubeAdapter
  VariableTerminalRowTubeStepAdapter NormalizedTerminalMarkingComposition

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax Mtotal : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- The selected correlated columns form a rich family.  Harnack closure is
proved from the retained physical rows, rather than assumed on the marked
columns or inherited from a universally quantified map provider. -/
def toRichFamily
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {kh0 cb db : ℝ} (physical : PhysicalProducer F kh0 cb db)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (hbaseHarnack : ∀ n, ArclengthHarnackCertificate (Q n)) :
    RichFamily Q e P0 P1 khat G1 Cg C c dlt where
  P n k := F.columns k n
  base := fun _ => rfl
  defect := F.defect
  base_harnack := hbaseHarnack
  richStage := fun n k => (F.chosenColumn k).column.step.richStage n
  harnackClosed := by
    intro n x hcolumn _
    have hphysical : Tendsto (F.retainedRows n) atTop (nhds x) :=
      EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
        hcolumn (physical.endpointTendsto n)
    have htubeX : IsTubeMember cb 0 db x :=
      (isClosed_tube cb 0 db).mem_of_tendsto hphysical
        (Eventually.of_forall (physical.physicalBounds.physical_tube n))
    exact
      { q := x
        c := cb
        dlt := db
        c_pos := hcb
        dlt_pos := hdb
        tube := htubeX
        same_range := rfl
        strictness :=
          EnrichedPhysicalHarnackClosure.limitStrictnessDataH_of_finitePullbackRowLimit
            hkh0 hkh1 hcb physical.physicalBounds.physical_tube
              physical.finite hphysical }

/-- The retained rows of the rich-family projection are the physical rows of
the correlated construction. -/
@[simp] theorem retainedRows_toRichFamily
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {kh0 cb db : ℝ} (physical : PhysicalProducer F kh0 cb db)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (hbaseHarnack : ∀ n, ArclengthHarnackCertificate (Q n)) (n k : ℕ) :
    RichFamilyRetainedPhysicalRows.rows
      (toRichFamily F physical hkh0 hkh1 hcb hdb hbaseHarnack) n k =
        F.retainedRows n k := by
  cases k <;> rfl

/-- The correlated physical producer is the corrected retained-row
certificate expected by the generic paper-facing capstone. -/
def correctedCertificate
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {kh0 cb db : ℝ} (physical : PhysicalProducer F kh0 cb db)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (hbaseHarnack : ∀ n, ArclengthHarnackCertificate (Q n)) :
    RichFamilyRetainedPhysicalCertificate.CorrectedCertificate
      (toRichFamily F physical hkh0 hkh1 hcb hdb hbaseHarnack) kh0 cb db where
  bounds := by
    let RF := toRichFamily F physical hkh0 hkh1 hcb hdb hbaseHarnack
    have hrows : RichFamilyRetainedPhysicalRows.rows RF = F.retainedRows := by
      funext n k
      exact retainedRows_toRichFamily F physical hkh0 hkh1 hcb hdb
        hbaseHarnack n k
    change PhysicalRowBounds (RichFamilyRetainedPhysicalRows.rows RF)
      (fun n k => F.columns k n) cb db
    rw [hrows]
    exact physical.physicalBounds
  finite := by
    let RF := toRichFamily F physical hkh0 hkh1 hcb hdb hbaseHarnack
    have hrows : RichFamilyRetainedPhysicalRows.rows RF = F.retainedRows := by
      funext n k
      exact retainedRows_toRichFamily F physical hkh0 hkh1 hcb hdb
        hbaseHarnack n k
    change FinitePullbackPhysicalRearKinematics kh0
      (RichFamilyRetainedPhysicalRows.rows RF)
    rw [hrows]
    exact physical.finite

/-- The endpoint defect required by the generic capstone is the one-step
shift of the correlated producer's retained-row defect. -/
theorem terminalDefect_tendsto
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {kh0 cb db : ℝ} (physical : PhysicalProducer F kh0 cb db)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (hbaseHarnack : ∀ n, ArclengthHarnackCertificate (Q n)) (n : ℕ) :
    Tendsto (fun k => dist
      ((toRichFamily F physical hkh0 hkh1 hcb hdb hbaseHarnack).richStage n k).terminalBase
      ((toRichFamily F physical hkh0 hkh1 hcb hdb hbaseHarnack).P n (k + 1)))
      atTop (nhds 0) := by
  simpa only [retainedRows_toRichFamily] using
    (physical.endpointTendsto n).comp (tendsto_add_atTop_nat 1)

/-- Direct normalized markings between the retained physical rows and the
actual correlated marked columns. -/
def directMarkings
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2) :
    DirectPhysicalTerminalMarkingFamily F.retainedRows
      (fun n k => F.columns k n) where
  lambda n
    | 0 => 1
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.lambda
  Lambda n
    | 0 => 1
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.Lambda
  marking n
    | 0 => NormalizedC2Marking.refl (Q n)
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.marking

/-- Direct limit-facing scheme for the correlated recursion.  Harnack enters
only at the row limit and is proved there from the convergent physical rows;
no configured depth-zero front Harnack datum is used. -/
def toDirectScheme
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {kh0 cb db : ℝ} (physical : PhysicalProducer F kh0 cb db)
    (hcolumnsTube : ∀ n k,
      IsVariableTubeMember c (C n) 0 dlt (F.columns k n))
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1) (hcb : 0 < cb) (hdb : 0 < db) :
    TriangularMarkedPathSchemeVariableTerminalDirect.Scheme
      Q (fun n k => F.columns k n) e P0 P1 khat G1 Cg C c dlt where
  base := fun _ => rfl
  error_nonnegative := F.defect.nonnegative
  error_summable := F.defect.summable
  tube := hcolumnsTube
  stepPath := fun n k => (F.chosenColumn k).column.step.richStage n |>.stage.increment
  stepGeometry := fun n k =>
    (F.chosenColumn k).column.step.richStage n |>.stage.increment_geometry
  stepCost := fun n k =>
    (F.chosenColumn k).column.step.richStage n |>.stage.increment_cost
  finiteEdge := fun n k =>
    (F.chosenColumn k).column.step.richStage n |>.stage.range_edge
  limitHarnack := by
    intro n x hcolumn
    have hphysical : Tendsto (F.retainedRows n) atTop (nhds x) :=
      EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
        hcolumn (physical.endpointTendsto n)
    have htubeX : IsTubeMember cb 0 db x :=
      (isClosed_tube cb 0 db).mem_of_tendsto hphysical
        (Eventually.of_forall (physical.physicalBounds.physical_tube n))
    exact
      { q := x
        c := cb
        dlt := db
        c_pos := hcb
        dlt_pos := hdb
        tube := htubeX
        same_range := rfl
        strictness :=
          EnrichedPhysicalHarnackClosure.limitStrictnessDataH_of_finitePullbackRowLimit
            hkh0 hkh1 hcb physical.physicalBounds.physical_tube
              physical.finite hphysical }

/-- Direct paper-facing limit theorem for the actual source-preserving
correlated recursion.  Its assumptions are exactly the scalar tube budget,
base geometry, physical producer, and final shadow-gap data used downstream;
there is no erased-column map-provider premise. -/
theorem exists_paperFacingOutput
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax Mtotal a MA NA K0 K1 K2)
    {c0 d0 A0 r rho tail : ℕ → ℝ}
    (RB : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbaseTube : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n)
    {cb db kh0 : ℝ} (hcb : 0 < cb) (hdb : 0 < db)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1)
    (physical : PhysicalProducer F kh0 cb db)
    (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (fun n k => F.columns k n) e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (
      Σ (O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q (fun n k => F.columns k n) e P0 P1 khat G1 Cg C c dlt),
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let stepPath : ∀ n k, NormalPath (F.columns k n) (F.columns (k + 1) n) :=
    fun n k => (F.chosenColumn k).column.step.richStage n |>.stage.increment
  have hPcurve : ∀ n k u,
      HasDerivAt (⇑(F.columns k n).1) ((F.columns k n).2.1 u) u := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseTube n).hasDerivAt_curve u
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_curve_deriv u
  have hPvel : ∀ n k u,
      HasDerivAt (⇑(F.columns k n).2.1) ((F.columns k n).2.2 u) u := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseTube n).hasDerivAt_vel u
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_vel_deriv u
  have hPperiodic : ∀ n k, Periodic (⇑(F.columns k n).1) 1 := by
    intro n k
    cases k with
    | zero => simpa using (hbaseTube n).periodic
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_periodic
  have hPoriented : ∀ n k u,
      0 ≤ ((starRingEnd ℂ) ((F.columns k n).2.1 u) *
        (F.columns k n).2.2 u).im := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseTube n).curv_lb u
    | succ k =>
        exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_curvature_nonnegative u
  have htube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt
      (F.columns k n) :=
    schemeTube_of_steps RB (fun _ => rfl) hbaseTube hbaseAcc stepPath
      hPcurve hPvel hPperiodic hPoriented
      (fun n k => (F.chosenColumn k).column.step.richStage n |>.stage.increment_geometry)
      (fun n k => (F.chosenColumn k).column.step.richStage n |>.stage.increment_cost)
      hpartial hradius
  exact GenericVariableTerminalDirectCapstone.exists_paperFacingOutput
    (toDirectScheme F physical htube hkh0 hkh1 hcb hdb)
    (directMarkings F) physical.physicalBounds hkh0 hkh1 hcb hdb
    physical.finite physical.endpointTendsto hc hdirection hQbounded hQwidth
    hQlength hgap

end FiniteSmoothRearFamilyCorrelatedDirectCapstone
