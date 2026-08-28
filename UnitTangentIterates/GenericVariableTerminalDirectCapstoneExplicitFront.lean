import UnitTangentIterates.GenericVariableTerminalDirectCapstone
import UnitTangentIterates.MixedFinitePhysicalRearKinematics

/-!
# Direct capstone with explicit ordinary physical fronts

The marking-aware rear-family construction has three genuinely different
arrays: marked columns `P`, retained ordinary rears `B`, and ordinary physical
fronts `V`.  This module is the source-free downstream interface for that
construction.  It never identifies `V` with `P`; the only kinematic input is
the existing mixed package on `B` and `V`.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric PathMetric.NormalPath
open NormalPathC2IncrementVariableSpeed VariableMarkedTube
open RichFamilyPhysicalMarkingIntegration GaugeRearFamilyVariableTerminal

namespace GenericVariableTerminalDirectCapstoneExplicitFront

/-- The geometric marked-column scheme before limit Harnack is closed from
the independent physical arrays. -/
structure GeometricScheme
    (Q : ℕ → Data) (P : ℕ → ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  base : ∀ n, P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)
  stepPath : ∀ n k, NormalPath (P n k) (P n (k + 1))
  stepGeometry : ∀ n k,
    IsVariableSpeedNormalPath (P0 n) (P1 n) (khat n) (G1 n) (Cg n)
      (stepPath n k)
  stepCost : ∀ n k, cost (stepPath n k) ≤ e n k
  finiteEdge : ∀ n k,
    GeometricUnitTangentRangeEdge (P (n + 1) k) (P n (k + 1))

/-- Presented-row scheme using a genuine consecutive marked-distance bound. -/
structure GeometricDistanceScheme
    (Q : ℕ → Data) (P : ℕ → ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  base : ∀ n, P n 0 = Q n
  error_nonnegative : ∀ n k, 0 ≤ e n k
  error_summable : ∀ n, Summable (e n)
  tube : ∀ n k, IsVariableTubeMember c (C n) 0 dlt (P n k)
  stepDistance : ∀ n k,
    dist (P n k) (P n (k + 1)) ≤
      TriangularMarkedPathSchemeVariableTerminal.rowC P0 P1 khat G1 Cg n * e n k
  finiteEdge : ∀ n k,
    GeometricUnitTangentRangeEdge (P (n + 1) k) (P n (k + 1))

/-- Row-local strictness closure.  The physical fronts need tube bounds but
do not need to converge or agree as marked data with the columns. -/
def limitStrictnessDataH_of_explicitFrontRowLimit
    {kh cb db cp dp : ℝ} {B V : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hcp : 0 < cp)
    (hBtube : ∀ n k, IsTubeMember cb 0 db (B n k))
    (hVtube : ∀ n k, IsTubeMember cp 0 dp (V n k))
    (mixed : MixedFinitePhysicalRearKinematics kh B V)
    {n : ℕ} {x : Data} (hX : Tendsto (B n) atTop (nhds x)) :
    UnconditionalAssembly.LimitStrictnessDataH x := by
  have hXmem : IsTubeMember cb 0 db x :=
    (isClosed_tube cb 0 db).mem_of_tendsto hX
      (Eventually.of_forall (hBtube n))
  have hXshift : Tendsto (fun k ↦ B n (k + 1)) atTop (nhds x) :=
    hX.comp (tendsto_add_atTop_nat 1)
  apply UnconditionalAssembly.limitStrictnessDataH_of_limit'
    (P := fun k ↦ B n (k + 1)) hcb hXmem hXshift
  intro k a b hab
  let K := Nonempty.some (mixed.stage n k)
  let S := K.toStageComponents hkh0 hkh1 hcp (hVtube (n + 1) k)
  let D := S.limitStrictness hcp (hVtube (n + 1) k)
  let DH := D.toH (fun s ↦ (D.curvature_deriv s).differentiableAt)
  have hcurv : ∀ s, D.k s = UnconditionalAssembly.arcCurv (B n (k + 1)) s :=
    RearTrackEmbedded.curvature_eq_arcCurv hcb (hBtube n (k + 1))
      D.curve_deriv D.angle_deriv
  have hH := DH.curvature_harnack a b hab
  change Real.exp (a - b) *
      (D.k a / Real.sqrt (1 + D.k a ^ 2)) ≤
    D.k b / Real.sqrt (1 + D.k b ^ 2) at hH
  simpa only [hcurv a, hcurv b] using hH

/-- Close the direct marked-column scheme using only geometric physical data. -/
def GeometricScheme.toScheme
    {Q : ℕ → Data} {P B V : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db cp dp kh : ℝ}
    (G : GeometricScheme Q P e P0 P1 khat G1 Cg C c dlt)
    (R : PhysicalRowBounds B P cb db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (hVtube : ∀ n k, IsTubeMember cp 0 dp (V n k))
    (mixed : MixedFinitePhysicalRearKinematics kh B V)
    (hphysicalDefect : ∀ n,
      Tendsto (fun k ↦ dist (B n k) (P n k)) atTop (nhds 0)) :
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
        strictness := limitStrictnessDataH_of_explicitFrontRowLimit
          hkh0 hkh1 hcb hcp R.physical_tube hVtube mixed hphysical }

def GeometricDistanceScheme.toScheme
    {Q : ℕ → Data} {P B V : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db cp dp kh : ℝ}
    (G : GeometricDistanceScheme Q P e P0 P1 khat G1 Cg C c dlt)
    (R : PhysicalRowBounds B P cb db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (hVtube : ∀ n k, IsTubeMember cp 0 dp (V n k))
    (mixed : MixedFinitePhysicalRearKinematics kh B V)
    (hphysicalDefect : ∀ n,
      Tendsto (fun k ↦ dist (B n k) (P n k)) atTop (nhds 0)) :
    TriangularMarkedPathSchemeVariableTerminalDirect.DistanceScheme
      Q P e P0 P1 khat G1 Cg C c dlt where
  base := G.base
  error_nonnegative := G.error_nonnegative
  error_summable := G.error_summable
  tube := G.tube
  stepDistance := G.stepDistance
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
        strictness := limitStrictnessDataH_of_explicitFrontRowLimit
          hkh0 hkh1 hcb hcp R.physical_tube hVtube mixed hphysical }

/-- Paper-facing output from a source-free geometric scheme with explicit
ordinary fronts.  This is the minimal downstream target for the forthcoming
marking-aware recursive provider. -/
theorem exists_paperFacingOutput
    {Q : ℕ → Data} {P B V : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db cp dp kh : ℝ}
    (G : GeometricScheme Q P e P0 P1 khat G1 Cg C c dlt)
    (M : DirectPhysicalTerminalMarkingFamily B P)
    (R : PhysicalRowBounds B P cb db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (hVtube : ∀ n k, IsTubeMember cp 0 dp (V n k))
    (mixed : MixedFinitePhysicalRearKinematics kh B V)
    (hphysicalDefect : ∀ n,
      Tendsto (fun k ↦ dist (B n k) (P n k)) atTop (nhds 0))
    (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (
      Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
        Q P e P0 P1 khat G1 Cg C c dlt,
        PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let S := G.toScheme R hkh0 hkh1 hcb hdb hcp hVtube mixed hphysicalDefect
  obtain ⟨O⟩ :=
    TriangularMarkedPathSchemeVariableTerminalDirect.exists_limitOutput S hc
  have hphysical : ∀ n, Tendsto (B n) atTop (nhds (O.X n)) := by
    intro n
    exact EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
      (O.row_limit n) (hphysicalDefect n)
  let rowGeometry := geometricRowMarkingDataDirect M R hc G.tube
  let markingBounds := rowGeometry.toRowwiseBounds
  let limitReparam : ∀ n x, Tendsto (P n) atTop (nhds x) →
      LimitOrientedReparametrization (O.X n) x := by
    intro n x hx
    exact limitOrientedReparametrization_of_rowwise_bounds
      (markingBounds.lambda_pos n) (markingBounds.secondBound_nonneg n)
      (markingBounds.reparametrization n) (hphysical n) hx
      (markingBounds.basepoint n) (markingBounds.psi_hasDerivAt n)
      (markingBounds.ddpsi n) (markingBounds.dpsi_hasDerivAt n)
      (markingBounds.ddpsi_bound n)
  let reps : ∀ n, OrientedArclengthRepresentative (O.X n) := by
    intro n
    let W := limitReparam n (O.X n) (O.row_limit n)
    have hbase : IsTubeMember cb 0 db (O.X n) :=
      (isClosed_tube cb 0 db).mem_of_tendsto (hphysical n)
        (Eventually.of_forall (R.physical_tube n))
    exact orientedArclengthRepresentative_of_orientedReparametrization
      hcb hdb W.lambda_pos hbase W.reparametrization W.psi_hasDerivAt
      W.dpsi_continuous W.surjective
      (limitStrictnessDataH_of_explicitFrontRowLimit
        hkh0 hkh1 hcb hcp R.physical_tube hVtube mixed (hphysical n))
  exact ⟨O, PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
    O reps hdirection hQbounded hQwidth hQlength (hgap O)⟩

theorem exists_paperFacingOutputDistance
    {Q : ℕ → Data} {P B V : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db cp dp kh : ℝ}
    (G : GeometricDistanceScheme Q P e P0 P1 khat G1 Cg C c dlt)
    (M : DirectPhysicalTerminalMarkingFamily B P)
    (R : PhysicalRowBounds B P cb db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db) (hcp : 0 < cp)
    (hVtube : ∀ n k, IsTubeMember cp 0 dp (V n k))
    (mixed : MixedFinitePhysicalRearKinematics kh B V)
    (hphysicalDefect : ∀ n,
      Tendsto (fun k ↦ dist (B n k) (P n k)) atTop (nhds 0))
    (hc : 0 < c)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    Nonempty (Σ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt,
      PaperFacingVariableTerminalOutput.Output O direction modelWidth H) := by
  let S := G.toScheme R hkh0 hkh1 hcb hdb hcp hVtube mixed hphysicalDefect
  obtain ⟨O⟩ :=
    TriangularMarkedPathSchemeVariableTerminalDirect.exists_limitOutput_of_distance S hc
  have hphysical : ∀ n, Tendsto (B n) atTop (nhds (O.X n)) := fun n =>
    EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
      (O.row_limit n) (hphysicalDefect n)
  let rowGeometry := geometricRowMarkingDataDirect M R hc G.tube
  let markingBounds := rowGeometry.toRowwiseBounds
  let limitReparam : ∀ n x, Tendsto (P n) atTop (nhds x) →
      LimitOrientedReparametrization (O.X n) x := by
    intro n x hx
    exact limitOrientedReparametrization_of_rowwise_bounds
      (markingBounds.lambda_pos n) (markingBounds.secondBound_nonneg n)
      (markingBounds.reparametrization n) (hphysical n) hx
      (markingBounds.basepoint n) (markingBounds.psi_hasDerivAt n)
      (markingBounds.ddpsi n) (markingBounds.dpsi_hasDerivAt n)
      (markingBounds.ddpsi_bound n)
  let reps : ∀ n, OrientedArclengthRepresentative (O.X n) := by
    intro n
    let W := limitReparam n (O.X n) (O.row_limit n)
    have hbase : IsTubeMember cb 0 db (O.X n) :=
      (isClosed_tube cb 0 db).mem_of_tendsto (hphysical n)
        (Eventually.of_forall (R.physical_tube n))
    exact orientedArclengthRepresentative_of_orientedReparametrization
      hcb hdb W.lambda_pos hbase W.reparametrization W.psi_hasDerivAt
      W.dpsi_continuous W.surjective
      (limitStrictnessDataH_of_explicitFrontRowLimit
        hkh0 hkh1 hcb hcp R.physical_tube hVtube mixed (hphysical n))
  exact ⟨O, PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
    O reps hdirection hQbounded hQwidth hQlength (hgap O)⟩

end GenericVariableTerminalDirectCapstoneExplicitFront
