import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwarePhysicalCore
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareCappedProvider
import UnitTangentIterates.GenericVariableTerminalDirectCapstoneExplicitFront

/-!
# Direct capstone for marking-aware correlated columns

No analytic source occurs in the theorem interface.  Sources are used only by
the upstream provider to select the columns; the limit theorem consumes their
marked paths, terminal markings, and ordinary physical certificates.
-/

noncomputable section

open Set Filter MarkedSpace PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareDirectCapstone

open FiniteSmoothRearFamilyMarkingAwarePhysicalCore
  GenericVariableTerminalDirectCapstoneExplicitFront
  RichFamilyPhysicalMarkingIntegration

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- Direct normalized markings from retained terminal bases to the actual
nonaffinely marked columns. -/
def directMarkings
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) :
    DirectPhysicalTerminalMarkingFamily F.retainedRows
      (fun n k ↦ F.columns k n) where
  lambda n
    | 0 => 1
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.lambda
  Lambda n
    | 0 => 1
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.Lambda
  marking n
    | 0 => NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl (Q n)
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.marking

/-- Source-free marked-column geometry selected by the recursion. -/
def geometricScheme
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (hcolumnsTube : ∀ n k,
      VariableMarkedTube.IsVariableTubeMember c (C n) 0 dlt
        (F.columns k n)) :
    GeometricScheme Q (fun n k ↦ F.columns k n) e
      P0 P1 khat G1 Cg C c dlt where
  base := fun _ ↦ rfl
  error_nonnegative := F.defect.nonnegative
  error_summable := F.defect.summable
  tube := hcolumnsTube
  stepPath := fun n k ↦
    (F.chosenColumn k).column.step.richStage n |>.stage.increment
  stepGeometry := fun n k ↦
    (F.chosenColumn k).column.step.richStage n |>.stage.increment_geometry
  stepCost := fun n k ↦
    (F.chosenColumn k).column.step.richStage n |>.stage.increment_cost
  finiteEdge := fun n k ↦
    (F.chosenColumn k).column.step.richStage n |>.stage.range_edge

/-- The finite retained-row package is also a mixed package whose explicit
front array is that same ordinary retained array.  This conversion is valid
because `ConstructionCore.finitePhysical` used the successor's explicit
physical front and its proved `physicalFront_eq`. -/
def mixedOfFinite
    {B : ℕ → ℕ → Data} {kh0 : ℝ}
    (K : FinitePullbackPhysicalRearKinematics kh0 B) :
    MixedFinitePhysicalRearKinematics kh0 B B :=
  ⟨K.stage⟩

/-- Minimal paper-facing downstream theorem for the marking-aware recursion. -/
theorem exists_paperFacingOutput_of_columnsTube
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    {kh0 cb db : ℝ} (physical : PhysicalProducer F kh0 cb db)
    (hcolumnsTube : ∀ n k,
      VariableMarkedTube.IsVariableTubeMember c (C n) 0 dlt
        (F.columns k n))
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (fun n k ↦ F.columns k n) e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q (fun n k ↦ F.columns k n) e P0 P1 khat G1 Cg C c dlt,
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  exact GenericVariableTerminalDirectCapstoneExplicitFront.exists_paperFacingOutput
    (geometricScheme F hcolumnsTube) (directMarkings F)
    physical.physicalBounds hkh0 hkh1 hcb hdb hcb
    physical.physicalBounds.physical_tube (mixedOfFinite physical.finite)
    physical.endpointTendsto hc hdirection hQbounded hQwidth hQlength hgap

/-- Row-budget form used by configured large-separation assembly. -/
theorem exists_paperFacingOutput
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    {c0 d0 A0 r rho tail : ℕ → ℝ}
    (RB : VariableTerminalRowTubeAdapter.RowBudget
      Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbaseTube : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n)
    {kh0 cb db : ℝ} (physical : PhysicalProducer F kh0 cb db)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (fun n k ↦ F.columns k n) e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q (fun n k ↦ F.columns k n) e P0 P1 khat G1 Cg C c dlt,
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let stepPath : ∀ n k, NormalPath (F.columns k n) (F.columns (k + 1) n) :=
    fun n k ↦ (F.chosenColumn k).column.step.richStage n |>.stage.increment
  have hPcurve : ∀ n k u,
      HasDerivAt (⇑(F.columns k n).1) ((F.columns k n).2.1 u) u := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseTube n).hasDerivAt_curve u
    | succ k =>
        exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_curve_deriv u
  have hPvel : ∀ n k u,
      HasDerivAt (⇑(F.columns k n).2.1) ((F.columns k n).2.2 u) u := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseTube n).hasDerivAt_vel u
    | succ k =>
        exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_vel_deriv u
  have hPperiodic : ∀ n k, Function.Periodic (⇑(F.columns k n).1) 1 := by
    intro n k
    cases k with
    | zero => simpa using (hbaseTube n).periodic
    | succ k =>
        exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_periodic
  have hPoriented : ∀ n k u, 0 ≤
      ((starRingEnd ℂ) ((F.columns k n).2.1 u) *
        (F.columns k n).2.2 u).im := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseTube n).curv_lb u
    | succ k =>
        exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_curvature_nonnegative u
  have htube : ∀ n k,
      VariableMarkedTube.IsVariableTubeMember c (C n) 0 dlt
        (F.columns k n) :=
    VariableTerminalRowTubeStepAdapter.schemeTube_of_steps RB
      (fun _ ↦ rfl) hbaseTube hbaseAcc stepPath hPcurve hPvel hPperiodic
      hPoriented
      (fun n k ↦
        (F.chosenColumn k).column.step.richStage n |>.stage.increment_geometry)
      (fun n k ↦
        (F.chosenColumn k).column.step.richStage n |>.stage.increment_cost)
      hpartial hradius
  exact exists_paperFacingOutput_of_columnsTube F physical htube
    hkh0 hkh1 hcb hdb hc hdirection hQbounded hQwidth hQlength hgap

end FiniteSmoothRearFamilyMarkingAwareDirectCapstone

namespace FiniteSmoothRearFamilyMarkingAwareDirectCapstone

open FiniteSmoothRearFamilyMarkingAwareCappedProvider
  GenericVariableTerminalDirectCapstoneExplicitFront
  RichFamilyPhysicalMarkingIntegration

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

def slicedDirectMarkings
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2) :
    DirectPhysicalTerminalMarkingFamily F.retainedRows
      (fun n k ↦ F.columns k n) where
  lambda n
    | 0 => 1
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.lambda
  Lambda n
    | 0 => 1
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.Lambda
  marking n
    | 0 => NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl (Q n)
    | k + 1 => (F.chosenColumn k).column.step.richStage n |>.marking

def slicedGeometricScheme
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    (hcolumnsTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.columns k n)) :
    GeometricScheme Q (fun n k ↦ F.columns k n) e
      P0 P1 khat G1 Cg C c dlt where
  base := fun _ ↦ rfl
  error_nonnegative := F.defect.nonnegative
  error_summable := F.defect.summable
  tube := hcolumnsTube
  stepPath := fun n k ↦
    (F.chosenColumn k).column.step.richStage n |>.stage.increment
  stepGeometry := fun n k ↦
    (F.chosenColumn k).column.step.richStage n |>.stage.increment_geometry
  stepCost := fun n k ↦
    (F.chosenColumn k).column.step.richStage n |>.stage.increment_cost
  finiteEdge := fun n k ↦
    (F.chosenColumn k).column.step.richStage n |>.stage.range_edge

theorem sliced_exists_paperFacingOutput_of_columnsTube
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    {kh0 cb db : ℝ} (physical : SlicedPhysicalProducer F kh0 cb db)
    (hcolumnsTube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.columns k n))
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤ MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (fun n k ↦ F.columns k n) e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (fun n k ↦ F.columns k n) e P0 P1 khat G1 Cg C c dlt,
      PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  exact GenericVariableTerminalDirectCapstoneExplicitFront.exists_paperFacingOutput
    (slicedGeometricScheme F hcolumnsTube) (slicedDirectMarkings F)
    physical.physicalBounds hkh0 hkh1 hcb hdb hcb
    physical.physicalBounds.physical_tube (mixedOfFinite physical.finite)
    physical.endpointTendsto hc hdirection hQbounded hQwidth hQlength hgap

theorem sliced_exists_paperFacingOutput
    (F : SlicedConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      kh Qmax a MA NA K0 K1 K2)
    {c0 d0 A0 r rho tail : ℕ → ℝ}
    (RB : VariableTerminalRowTubeAdapter.RowBudget
      Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbaseTube : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n, NormalPathC2IncrementVariableSpeed.c2ConstVar
      (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n)
    {kh0 cb db : ℝ} (physical : SlicedPhysicalProducer F kh0 cb db)
    (hkh0 : 0 ≤ kh0) (hkh1 : kh0 < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤ MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (fun n k ↦ F.columns k n) e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (fun n k ↦ F.columns k n) e P0 P1 khat G1 Cg C c dlt,
      PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let stepPath : ∀ n k, NormalPath (F.columns k n) (F.columns (k + 1) n) :=
    fun n k ↦ (F.chosenColumn k).column.step.richStage n |>.stage.increment
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
  have hPperiodic : ∀ n k, Function.Periodic (⇑(F.columns k n).1) 1 := by
    intro n k
    cases k with
    | zero => simpa using (hbaseTube n).periodic
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_periodic
  have hPoriented : ∀ n k u, 0 ≤
      ((starRingEnd ℂ) ((F.columns k n).2.1 u) * (F.columns k n).2.2 u).im := by
    intro n k u
    cases k with
    | zero => simpa using (hbaseTube n).curv_lb u
    | succ k => exact (F.chosenColumn k).column.step.richStage n |>.stage.rear_curvature_nonnegative u
  have htube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (F.columns k n) :=
    VariableTerminalRowTubeStepAdapter.schemeTube_of_steps RB
      (fun _ ↦ rfl) hbaseTube hbaseAcc stepPath hPcurve hPvel hPperiodic
      hPoriented
      (fun n k ↦ (F.chosenColumn k).column.step.richStage n |>.stage.increment_geometry)
      (fun n k ↦ (F.chosenColumn k).column.step.richStage n |>.stage.increment_cost)
      hpartial hradius
  exact sliced_exists_paperFacingOutput_of_columnsTube F physical htube
    hkh0 hkh1 hcb hdb hc hdirection hQbounded hQwidth hQlength hgap

end FiniteSmoothRearFamilyMarkingAwareDirectCapstone
