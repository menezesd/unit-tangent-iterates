import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminalConstructor
import UnitTangentIterates.VariableTerminalRowTubeStepAdapter
import UnitTangentIterates.RichFamilyPhysicalMarkingIntegration
import UnitTangentIterates.PaperFacingVariableTerminalOutput

/-!
# Generic variable-terminal capstone

This module composes the stable, model-independent recursive interfaces.  It
constructs the rich triangular columns first, proves their common row tube by
telescoping step costs, obtains Harnack closure from physical marking
compactness, and finally chooses the paper-facing ordinary oval orbit.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace GenericVariableTerminalCapstone

open VariableMarkedTube GaugeRearFamilyVariableTerminal
open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
open VariableTerminalRowTubeAdapter VariableTerminalRowTubeStepAdapter
open RichFamilyPhysicalMarkingIntegration

/-- The complete generic variable-terminal construction.  No configured
model formula occurs here: those data only have to discharge the scalar row
budget, physical row bounds, alignment, and closing inequalities. -/
theorem exists_paperFacingOutput
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (D : RowDefectProvider e)
    (BS : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (MS : MapStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    {c0 d0 A0 r rho tail : ℕ → ℝ}
    (RB : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbaseTube : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      c2ConstVar (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n)
    (hbaseHarnack : ∀ n, ArclengthHarnackCertificate (Q n))
    {Bphys : ℕ → ℕ → Data} {cb db kh : ℝ}
    (hcb : 0 < cb) (hdb : 0 < db) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (physicalRows : PhysicalRowBounds Bphys
      (fun n k => columns BS MS k n) cb db)
    (finite : FinitePullbackPhysicalRearKinematics kh Bphys)
    {Xphys : ℕ → Data}
    (hphysicalLimit : ∀ n, Tendsto (Bphys n) atTop (nhds (Xphys n)))
    (hphysicalZero : ∀ n, Bphys n 0 = Q n)
    (hterminalBase : ∀ n k,
      ((chosenStep BS MS k).richStage n).terminalBase = Bphys n (k + 1))
    (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (fun n k => columns BS MS k n) e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (
      Σ (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt),
        Σ (O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
          Q F.P e P0 P1 khat G1 Cg C c dlt),
          PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let P : ℕ → ℕ → Data := fun n k => columns BS MS k n
  let S : ∀ n k, RichStageData (P n k) (P (n + 1) k) (P n (k + 1))
      (e n k) (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt := by
    intro n k
    simpa only [P, columns_succ] using (chosenStep BS MS k).richStage n
  let stepPath : ∀ n k, NormalPath (P n k) (P n (k + 1)) :=
    fun n k => (S n k).stage.increment
  have hPcurve : ∀ n k u, HasDerivAt (⇑(P n k).1) ((P n k).2.1 u) u := by
    intro n k
    cases k with
    | zero =>
        simpa only [P, columns_zero] using (hbaseTube n).hasDerivAt_curve
    | succ k => exact (S n k).stage.rear_curve_deriv
  have hPvel : ∀ n k u, HasDerivAt (⇑(P n k).2.1) ((P n k).2.2 u) u := by
    intro n k
    cases k with
    | zero =>
        simpa only [P, columns_zero] using (hbaseTube n).hasDerivAt_vel
    | succ k => exact (S n k).stage.rear_vel_deriv
  have hPperiodic : ∀ n k, Periodic (⇑(P n k).1) 1 := by
    intro n k
    cases k with
    | zero => simpa only [P, columns_zero] using (hbaseTube n).periodic
    | succ k => exact (S n k).stage.rear_periodic
  have hPoriented : ∀ n k u, 0 ≤
      ((starRingEnd ℂ) ((P n k).2.1 u) * (P n k).2.2 u).im := by
    intro n k u
    cases k with
    | zero =>
        simpa only [P, columns_zero, zero_mul] using (hbaseTube n).curv_lb u
    | succ k => exact (S n k).stage.rear_curvature_nonnegative u
  have htube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k) :=
    schemeTube_of_steps RB (by intro n; simp only [P, columns_zero])
      hbaseTube hbaseAcc stepPath hPcurve hPvel hPperiodic hPoriented
      (fun n k => (S n k).stage.increment_geometry)
      (fun n k => (S n k).stage.increment_cost) hpartial hradius
  let direct : DirectPhysicalTerminalMarkingFamily Bphys P :=
    { lambda := fun n k => match k with
        | 0 => 1
        | k + 1 => (S n k).lambda
      Lambda := fun n k => match k with
        | 0 => 1
        | k + 1 => (S n k).Lambda
      marking := by
        intro n k
        cases k with
        | zero =>
            simpa only [P, columns_zero, hphysicalZero n] using
              NormalizedTerminalMarkingComposition.NormalizedC2Marking.refl
                (Bphys n 0)
        | succ k =>
            have htb : (S n k).terminalBase = Bphys n (k + 1) := by
              simpa only [S] using hterminalBase n k
            rw [← htb]
            exact (S n k).marking }
  let G := geometricRowMarkingDataDirect direct physicalRows hc htube
  let markingBounds := G.toRowwiseBounds
  let limitReparam : ∀ n x, Tendsto (P n) atTop (nhds x) →
      LimitOrientedReparametrization (Xphys n) x := by
    intro n x hx
    exact GaugeRearFamilyVariableTerminal.limitOrientedReparametrization_of_rowwise_bounds
      (markingBounds.lambda_pos n) (markingBounds.secondBound_nonneg n)
      (markingBounds.reparametrization n) (hphysicalLimit n) hx
      (markingBounds.basepoint n) (markingBounds.psi_hasDerivAt n)
      (markingBounds.ddpsi n) (markingBounds.dpsi_hasDerivAt n)
      (markingBounds.ddpsi_bound n)
  let hclosed : ∀ n x, Tendsto (P n) atTop (nhds x) →
      (∀ k, ArclengthHarnackCertificate (P n k)) →
        ArclengthHarnackCertificate x :=
    harnackClosed_of_finitePullbackLimit hkh0 hkh1 hcb hdb
      physicalRows.physical_tube finite hphysicalLimit limitReparam
  let F : RichFamily Q e P0 P1 khat G1 Cg C c dlt :=
    construct D BS MS hbaseHarnack (by simpa only [P] using hclosed)
  have hFtube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (F.P n k) := by
    simpa only [F, construct, P] using htube
  let family := F.toFamily hFtube
  let O := Nonempty.some
    (TriangularMarkedRecursiveChoiceVariableTerminal.exists_limitOutput family hc)
  have hOasP : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt := by
    simpa only [F, construct, P] using O
  have hreps : ∀ n, OrientedArclengthRepresentative (O.X n) :=
    GaugeRearFamilyVariableTerminal.orientedRepresentatives_of_rowwise_marking_bounds
      hkh0 hkh1 hcb hdb physicalRows.physical_tube finite hphysicalLimit
      O.row_limit (by simpa only [F, construct, P] using markingBounds)
  exact ⟨⟨F, O,
    PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
      O hreps hdirection hQbounded hQwidth hQlength (by
        simpa only [F, construct, P] using hgap hOasP)⟩⟩

end GenericVariableTerminalCapstone
