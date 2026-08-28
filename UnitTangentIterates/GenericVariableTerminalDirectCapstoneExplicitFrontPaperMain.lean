import UnitTangentIterates.GenericVariableTerminalDirectCapstoneExplicitFront
import UnitTangentIterates.PaperMainTheoremDirectProjection

/-! # Paper theorem from an explicit-front presented triangular array -/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed VariableMarkedTube

namespace GenericVariableTerminalDirectCapstoneExplicitFrontPaperMain

open GenericVariableTerminalDirectCapstoneExplicitFront
  RichFamilyPhysicalMarkingIntegration GaugeRearFamilyVariableTerminal

theorem paperMain
    {Q : ℕ → Data} {P B V : ℕ → ℕ → Data}
    {e : ℕ → ℕ → ℝ}
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
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨O, A⟩ :=
    GenericVariableTerminalDirectCapstoneExplicitFront.exists_paperFacingOutput
      G M R hkh0 hkh1 hcb hdb hcp hVtube mixed hphysicalDefect hc
      hdirection hQbounded hQwidth hQlength hgap
  exact PaperMainTheoremDirectProjection.of_output A

theorem paperMainDistance
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
    (hQlength : 2 * H ≤ MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : ∀ O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt,
      modelWidth + 2 * PaperFacingVariableTerminalOutput.shadowSize O <
        (2 * H - PaperFacingVariableTerminalOutput.shadowSize O) / Real.pi) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨O, A⟩ :=
    GenericVariableTerminalDirectCapstoneExplicitFront.exists_paperFacingOutputDistance
      G M R hkh0 hkh1 hcb hdb hcp hVtube mixed hphysicalDefect hc
      hdirection hQbounded hQwidth hQlength hgap
  exact PaperMainTheoremDirectProjection.of_output A

end GenericVariableTerminalDirectCapstoneExplicitFrontPaperMain
