import UnitTangentIterates.DiagonalEnrichedConstructionCoreDirectCapstone
import UnitTangentIterates.VariableTerminalRowTubeStepAdapter

/-!
# Filling the marked-column tube in the enriched-stage interface

The recursive analytic producer need only retain physical terminal-row facts.
The variable marked-column tube follows uniformly from the scalar row budget
and the actual chosen increment paths.
-/

noncomputable section

open Filter MarkedSpace PathMetric
open EnrichedPhysicalChosenRichFamily
open EnrichedPhysicalHarnackClosure
open RichFamilyPhysicalMarkingIntegration
open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
open VariableTerminalRowTubeAdapter
open DiagonalEnrichedConstructionCoreDirectCapstone

namespace EnrichedPhysicalStageProducerFromRowBudget

structure PhysicalProducer
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (kh cb db : ℝ) : Type where
  physicalBounds : PhysicalRowBounds
    (retainedRows F.baseProvider F.mapProvider)
    (fun n k => columns F.baseProvider F.mapProvider k n) cb db
  finite : FinitePullbackPhysicalRearKinematics kh
    (retainedRows F.baseProvider F.mapProvider)
  endpointDefect : F.EndpointDefectCertificate

def toEnrichedStageProducer
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg c0 d0 A0 r rho C tail : ℕ → ℝ}
    {c dlt : ℝ} {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh cb db : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (G : PhysicalProducer F kh cb db)
    (RB : RowBudget Q P0 P1 khat G1 Cg c0 d0 A0 r rho C c dlt)
    (hbase : ∀ n, IsTubeMember (c0 n) 0 (d0 n) (Q n))
    (hbaseAcc : ∀ n u, ‖(Q n).2.2 u‖ ≤ A0 n)
    (hpartial : ∀ n k, (∑ j ∈ Finset.range k, e n j) ≤ tail n)
    (hradius : ∀ n,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n) (P1 n) (khat n) (G1 n) (Cg n) * tail n ≤ r n) :
    EnrichedStageProducer F kh cb db where
  columnsTube := by
    let P : ℕ → ℕ → Data := fun n k => columns F.baseProvider F.mapProvider k n
    have hbaseEq : ∀ n, P n 0 = Q n := fun n =>
      congrFun (columns_zero F.baseProvider F.mapProvider) n
    let stepPath : ∀ n k, NormalPath (P n k) (P n (k + 1)) := fun n k => by
      simpa only [P, EnrichedPhysicalChosenRichFamily.columns_succ] using
        (F.chosenColumn k).step.richStage n |>.stage.increment
    have hPcurve : ∀ n k u, HasDerivAt (⇑(P n k).1) ((P n k).2.1 u) u := by
      intro n k u
      cases k with
      | zero => simpa [P, hbaseEq n] using (hbase n).hasDerivAt_curve u
      | succ k =>
          simpa only [P, EnrichedPhysicalChosenRichFamily.columns_succ] using
            ((F.chosenColumn k).step.richStage n |>.stage.rear_curve_deriv u)
    have hPvel : ∀ n k u, HasDerivAt (⇑(P n k).2.1) ((P n k).2.2 u) u := by
      intro n k u
      cases k with
      | zero => simpa [P, hbaseEq n] using (hbase n).hasDerivAt_vel u
      | succ k =>
          simpa only [P, EnrichedPhysicalChosenRichFamily.columns_succ] using
            ((F.chosenColumn k).step.richStage n |>.stage.rear_vel_deriv u)
    have hPperiodic : ∀ n k, Function.Periodic (⇑(P n k).1) 1 := by
      intro n k
      cases k with
      | zero => simpa [P, hbaseEq n] using (hbase n).periodic
      | succ k =>
          simpa only [P, EnrichedPhysicalChosenRichFamily.columns_succ] using
            ((F.chosenColumn k).step.richStage n |>.stage.rear_periodic)
    have horiented : ∀ n k u,
        0 ≤ (starRingEnd ℂ ((P n k).2.1 u) * (P n k).2.2 u).im := by
      intro n k u
      cases k with
      | zero => simpa [P, hbaseEq n] using (hbase n).curv_lb u
      | succ k =>
          simpa only [P, EnrichedPhysicalChosenRichFamily.columns_succ] using
            ((F.chosenColumn k).step.richStage n |>.stage.rear_curvature_nonnegative u)
    exact VariableTerminalRowTubeStepAdapter.schemeTube_of_steps
      RB hbaseEq hbase hbaseAcc stepPath hPcurve hPvel hPperiodic horiented
      (fun n k => by
        simpa only [stepPath, P, EnrichedPhysicalChosenRichFamily.columns_succ] using
          (F.chosenColumn k).step.richStage n |>.stage.increment_geometry)
      (fun n k => by
        simpa only [stepPath, P, EnrichedPhysicalChosenRichFamily.columns_succ] using
          (F.chosenColumn k).step.richStage n |>.stage.increment_cost)
      hpartial hradius
  physicalBounds := G.physicalBounds
  finite := G.finite
  endpointDefect := G.endpointDefect

end EnrichedPhysicalStageProducerFromRowBudget
