import UnitTangentIterates.GenericVariableTerminalCapstone
import UnitTangentIterates.RichFamilyRetainedPhysicalCertificate

/-!
# Variable-terminal capstone from an already chosen rich family

The provider-based capstone reconstructs the recursive family, which erases
certificates retained only along the choices actually made.  This companion
starts from that chosen `RichFamily`.  Its physical carrier is definitionally
the terminal-base array stored by the rich stages, so no canonical-marking
identification or separate alignment hypothesis is needed.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace GenericVariableTerminalCapstoneFromRichFamily

open VariableMarkedTube GaugeRearFamilyVariableTerminal
open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
open VariableTerminalRowTubeAdapter VariableTerminalRowTubeStepAdapter
open RichFamilyPhysicalMarkingIntegration

theorem exists_paperFacingOutput_from_richFamily
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    {c0 d0 A0 r rho tail : ℕ → ℝ}
    (RB : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbaseTube : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n)
    {cb db kh : ℝ} (hcb : 0 < cb) (hdb : 0 < db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (physical : RichFamilyRetainedPhysicalCertificate.CorrectedCertificate
      F kh cb db)
    {Xphys : ℕ → Data}
    (hphysicalLimit : ∀ n, Tendsto
      (RichFamilyRetainedPhysicalRows.rows F n) atTop (nhds (Xphys n)))
    (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q F.P e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (
      Σ (O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q F.P e P0 P1 khat G1 Cg C c dlt),
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let stepPath : ∀ n k, NormalPath (F.P n k) (F.P n (k + 1)) :=
    fun n k => (F.richStage n k).stage.increment
  have hPcurve : ∀ n k u,
      HasDerivAt (⇑(F.P n k).1) ((F.P n k).2.1 u) u := by
    intro n k u
    cases k with
    | zero => simpa only [F.base n] using (hbaseTube n).hasDerivAt_curve u
    | succ k => exact (F.richStage n k).stage.rear_curve_deriv u
  have hPvel : ∀ n k u,
      HasDerivAt (⇑(F.P n k).2.1) ((F.P n k).2.2 u) u := by
    intro n k u
    cases k with
    | zero => simpa only [F.base n] using (hbaseTube n).hasDerivAt_vel u
    | succ k => exact (F.richStage n k).stage.rear_vel_deriv u
  have hPperiodic : ∀ n k, Periodic (⇑(F.P n k).1) 1 := by
    intro n k
    cases k with
    | zero => simpa only [F.base n] using (hbaseTube n).periodic
    | succ k => exact (F.richStage n k).stage.rear_periodic
  have hPoriented : ∀ n k u,
      0 ≤ ((starRingEnd ℂ) ((F.P n k).2.1 u) * (F.P n k).2.2 u).im := by
    intro n k u
    cases k with
    | zero =>
        simpa only [F.base n, zero_mul] using (hbaseTube n).curv_lb u
    | succ k => exact (F.richStage n k).stage.rear_curvature_nonnegative u
  have htube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (F.P n k) :=
    schemeTube_of_steps RB F.base hbaseTube hbaseAcc stepPath
      hPcurve hPvel hPperiodic hPoriented
      (fun n k => (F.richStage n k).stage.increment_geometry)
      (fun n k => (F.richStage n k).stage.increment_cost) hpartial hradius
  let direct := RichFamilyRetainedPhysicalRows.directMarkings F
  let G := geometricRowMarkingDataDirect direct physical.bounds hc htube
  let markingBounds := G.toRowwiseBounds
  let family := F.toFamily htube
  let O := Nonempty.some
    (TriangularMarkedRecursiveChoiceVariableTerminal.exists_limitOutput family hc)
  have hreps : ∀ n, OrientedArclengthRepresentative (O.X n) :=
    orientedRepresentatives_of_rowwise_marking_bounds hkh0 hkh1 hcb hdb
      physical.bounds.physical_tube physical.finite hphysicalLimit O.row_limit
      markingBounds
  exact ⟨⟨O,
    PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
      O hreps hdirection hQbounded hQwidth hQlength (hgap O)⟩⟩

end GenericVariableTerminalCapstoneFromRichFamily
