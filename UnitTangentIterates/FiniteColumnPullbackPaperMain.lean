import UnitTangentIterates.FiniteColumnPullbackPaperCapstone
import UnitTangentIterates.PaperMainTheoremDirectProjection

/-!
# Paper theorem projected from a finite pullback-column provider

This leaf removes the terminal output packaging from the statement consumed by
the configured construction.  It states exactly the theorem asserted in the
paper, conditional only on the concrete finite-column provider and its closing
gap.
-/

noncomputable section

open Set MarkedSpace PathMetric

namespace FiniteColumnPullbackPaperMain

open FiniteColumnPullbackPaperCapstone

theorem Provider.paperMain
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (F : Provider kh Q w c dlt) (hc : 0 < c) (hdlt : 0 < dlt)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u ↦ (Q 0).2.1 u))
    (hgap : modelWidth + 2 *
        PaperFacingVariableTerminalOutput.shadowSize (F.toLimitOutput hc hdlt) <
      (2 * H - PaperFacingVariableTerminalOutput.shadowSize
        (F.toLimitOutput hc hdlt)) / Real.pi) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧ Function.Periodic (Gamma 0) L ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, range (Gamma (n + 1)) =
        range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ClosingArgument.IsCircleOfPerimeter (range (Gamma 0)) L := by
  obtain ⟨A⟩ := F.exists_paperFacingOutput hc hdlt hdirection
    hQbounded hQwidth hQlength hgap
  exact PaperMainTheoremDirectProjection.of_output A

end FiniteColumnPullbackPaperMain
