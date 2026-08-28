import UnitTangentIterates.EnrichedPhysicalConstructionCoreDirect
import UnitTangentIterates.RichFamilyPhysicalMarkingIntegration
import UnitTangentIterates.PaperFacingVariableTerminalOutput

/-!
# Paper-facing capstone for the direct limit-Harnack scheme

Physical retained rows approach the recursive marked columns.  Their finite
pullback kinematics both close the Harnack estimate at the row limit and,
together with the retained normalized markings, produce the oriented
arclength representatives used by the paper-facing output.
-/

noncomputable section

open Set Filter MarkedSpace PathMetric
open VariableMarkedTube
open RichFamilyPhysicalMarkingIntegration

namespace GenericVariableTerminalDirectCapstone

theorem exists_paperFacingOutput
    {Q : ℕ → Data} {P B : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db kh : ℝ}
    (S : TriangularMarkedPathSchemeVariableTerminalDirect.Scheme
      Q P e P0 P1 khat G1 Cg C c dlt)
    (M : DirectPhysicalTerminalMarkingFamily B P)
    (R : PhysicalRowBounds B P cb db)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hcb : 0 < cb) (hdb : 0 < db)
    (finite : FinitePullbackPhysicalRearKinematics kh B)
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
  obtain ⟨O⟩ :=
    TriangularMarkedPathSchemeVariableTerminalDirect.exists_limitOutput S hc
  have hphysical : ∀ n, Tendsto (B n) atTop (nhds (O.X n)) := by
    intro n
    exact EnrichedPhysicalHarnackClosure.tendsto_retained_of_column_and_defect
      (O.row_limit n) (hphysicalDefect n)
  let A : ∀ n, OrientedArclengthRepresentative (O.X n) := fun n =>
    orientedRepresentativesDirect M R hc hkh0 hkh1 hcb hdb S.tube finite
      hphysical O.row_limit n
  exact ⟨O, PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
    O A hdirection hQbounded hQwidth hQlength (hgap O)⟩

end GenericVariableTerminalDirectCapstone
