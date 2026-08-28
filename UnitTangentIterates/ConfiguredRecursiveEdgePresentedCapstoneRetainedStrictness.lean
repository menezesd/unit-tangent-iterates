import UnitTangentIterates.ConfiguredRecursiveEdgePresentedCapstoneAdapter

/-!
# Capstone closure from retained rear strictness

Every presented terminal already carries the integrated strictness certificate
for its ordinary rear.  Passing those certificates to the row limit avoids an
unjustified uniform tube hypothesis on independently marked physical fronts.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube
open RichFamilyPhysicalMarkingIntegration GaugeRearFamilyVariableTerminal

namespace GenericVariableTerminalDirectCapstoneRetainedStrictness

open GenericVariableTerminalDirectCapstoneExplicitFront

/-- Integrated strictness passes directly from the actual ordinary rears to
their marked limit. -/
def limitStrictnessDataH_of_rearStrictRowLimit
    {cb db : ℝ} {B : ℕ → ℕ → Data}
    (hcb : 0 < cb) (hBtube : ∀ n k, IsTubeMember cb 0 db (B n k))
    (finiteStrict : ∀ n k,
      UnconditionalAssembly.LimitStrictnessDataH (B n (k + 1)))
    {n : ℕ} {x : Data} (hX : Tendsto (B n) atTop (nhds x)) :
    UnconditionalAssembly.LimitStrictnessDataH x := by
  have hXmem : IsTubeMember cb 0 db x :=
    (isClosed_tube cb 0 db).mem_of_tendsto hX
      (Eventually.of_forall (hBtube n))
  have hXshift : Tendsto (fun k => B n (k + 1)) atTop (nhds x) :=
    hX.comp (tendsto_add_atTop_nat 1)
  apply UnconditionalAssembly.limitStrictnessDataH_of_limit'
    (P := fun k => B n (k + 1)) hcb hXmem hXshift
  intro k a b hab
  let D := finiteStrict n k
  have hcurv : ∀ s, D.k s =
      UnconditionalAssembly.arcCurv (B n (k + 1)) s :=
    RearTrackEmbedded.curvature_eq_arcCurv hcb (hBtube n (k + 1))
      D.curve_deriv D.angle_deriv
  have H := D.curvature_harnack a b hab
  change Real.exp (a - b) *
      (D.k a / Real.sqrt (1 + D.k a ^ 2)) ≤
    D.k b / Real.sqrt (1 + D.k b ^ 2) at H
  simpa only [hcurv a, hcurv b] using H

/-- Close a geometric scheme using strictness retained by its actual ordinary
rear rows. -/
def GeometricScheme.toSchemeOfRearStrictness
    {Q : ℕ → Data} {P B : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db : ℝ}
    (G : GeometricScheme Q P e P0 P1 khat G1 Cg C c dlt)
    (R : PhysicalRowBounds B P cb db)
    (hcb : 0 < cb) (hdb : 0 < db)
    (finiteStrict : ∀ n k,
      UnconditionalAssembly.LimitStrictnessDataH (B n (k + 1)))
    (hphysicalDefect : ∀ n,
      Tendsto (fun k => dist (B n k) (P n k)) atTop (nhds 0)) :
    TriangularMarkedPathSchemeVariableTerminalDirect.Scheme
      Q P e P0 P1 khat G1 Cg C c dlt where
  base := G.base
  error_nonnegative := G.error_nonnegative
  error_summable := G.error_summable
  tube := G.tube
  stepPath := G.stepPath
  stepGeometry := G.stepGeometry
  stepCost := G.stepCost
  finiteEdge := G.finiteEdge
  limitHarnack := by
    intro n x hcolumn
    have hphysical : Tendsto (B n) atTop (nhds x) :=
      EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
        hcolumn (hphysicalDefect n)
    have htubeX : IsTubeMember cb 0 db x :=
      (isClosed_tube cb 0 db).mem_of_tendsto hphysical
        (Eventually.of_forall (R.physical_tube n))
    exact
      { q := x
        c := cb
        dlt := db
        c_pos := hcb
        dlt_pos := hdb
        tube := htubeX
        same_range := rfl
        strictness := limitStrictnessDataH_of_rearStrictRowLimit
          hcb R.physical_tube finiteStrict hphysical }

/-- Paper-facing output with no physical-front tube input. -/
theorem exists_paperFacingOutput
    {Q : ℕ → Data} {P B : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db : ℝ}
    (G : GeometricScheme Q P e P0 P1 khat G1 Cg C c dlt)
    (M : DirectPhysicalTerminalMarkingFamily B P)
    (R : PhysicalRowBounds B P cb db)
    (hcb : 0 < cb) (hdb : 0 < db)
    (finiteStrict : ∀ n k,
      UnconditionalAssembly.LimitStrictnessDataH (B n (k + 1)))
    (hphysicalDefect : ∀ n,
      Tendsto (fun k => dist (B n k) (P n k)) atTop (nhds 0))
    (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q P e P0 P1 khat G1 Cg C c dlt,
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let S := GenericVariableTerminalDirectCapstoneRetainedStrictness.GeometricScheme.toSchemeOfRearStrictness G R hcb hdb finiteStrict hphysicalDefect
  obtain ⟨O⟩ :=
    TriangularMarkedPathSchemeVariableTerminalDirect.exists_limitOutput S hc
  have hphysical : ∀ n, Tendsto (B n) atTop (nhds (O.X n)) := by
    intro n
    exact EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
      (O.row_limit n) (hphysicalDefect n)
  let rowGeometry := geometricRowMarkingDataDirect M R hc G.tube
  let markingBounds := rowGeometry.toRowwiseBounds
  let reps : ∀ n, OrientedArclengthRepresentative (O.X n) := by
    intro n
    let W := limitOrientedReparametrization_of_rowwise_bounds
      (markingBounds.lambda_pos n) (markingBounds.secondBound_nonneg n)
      (markingBounds.reparametrization n) (hphysical n) (O.row_limit n)
      (markingBounds.basepoint n) (markingBounds.psi_hasDerivAt n)
      (markingBounds.ddpsi n) (markingBounds.dpsi_hasDerivAt n)
      (markingBounds.ddpsi_bound n)
    have hbase : IsTubeMember cb 0 db (O.X n) :=
      (isClosed_tube cb 0 db).mem_of_tendsto (hphysical n)
        (Eventually.of_forall (R.physical_tube n))
    exact orientedArclengthRepresentative_of_orientedReparametrization
      hcb hdb W.lambda_pos hbase W.reparametrization W.psi_hasDerivAt
      W.dpsi_continuous W.surjective
      (limitStrictnessDataH_of_rearStrictRowLimit
        hcb R.physical_tube finiteStrict (hphysical n))
  exact ⟨O, PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
    O reps hdirection hQbounded hQwidth hQlength (hgap O)⟩

end GenericVariableTerminalDirectCapstoneRetainedStrictness

namespace ConfiguredRecursiveEdgePresentedCapstoneAdapter.RecursiveConstruction

open FiniteSmoothRearFamilyMarkingAwarePresentedDirectSuccessor
  FiniteSmoothRearFamilyMarkingAwarePresentedRecursivePhysicalGrid
  FiniteSmoothRearFamilyMarkingAwareRecursivePresentedSlicedInvariant
  GenericVariableTerminalDirectCapstoneExplicitFront
  GenericVariableTerminalDirectCapstoneRetainedStrictness

variable {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
  {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
  {period : ℕ → ℕ → ℝ} {diagonal kh Qmax : ℕ → ℝ}
  {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}

/-- Every positive-depth ordinary rear is exactly the presented terminal which
already carries integrated strictness. -/
def finiteRearStrictness
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2) (n k : ℕ) :
    UnconditionalAssembly.LimitStrictnessDataH (rearRows F n (k + 1)) := by
  let W := (rowFamilyAt F k).row n
  simpa [W, rearRows, rearGrid, successorAt, rowFamilyAt,
    PresentedRowFamily.successor, successorOfPresentedRows] using
      W.terminalInput.strict

/-- Reachable recursive capstone closed from the actual terminal strictness;
no ordinary tube is requested for the canonical front marking. -/
theorem exists_paperFacingOutput_of_terminalStrictness
    (F : RecursivePresentedConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal kh Qmax a MA NA K0 K1 K2)
    (error_nonnegative : ∀ n k, 0 ≤ e n k)
    (error_summable : ∀ n, Summable (e n))
    (tube : ∀ n k, VariableMarkedTube.IsVariableTubeMember
      c (C n) 0 dlt (markedGrid F n k))
    {cb db : ℝ}
    (physical : PhysicalRowBounds (rearRows F) (markedGrid F) cb db)
    (hcb : 0 < cb) (hdb : 0 < db)
    (physicalDefect : ∀ n, Tendsto
      (fun k => dist (rearRows F n k) (markedGrid F n k))
      atTop (nhds 0))
    (hc : 0 < c) {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤ MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
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
  GenericVariableTerminalDirectCapstoneRetainedStrictness.exists_paperFacingOutput
    (geometricScheme F error_nonnegative error_summable tube)
    (directPhysicalMarkings F) physical hcb hdb (finiteRearStrictness F)
    physicalDefect hc hdirection hQbounded hQwidth hQlength hgap

end ConfiguredRecursiveEdgePresentedCapstoneAdapter.RecursiveConstruction
