import UnitTangentIterates.PaperMainTheoremSmoothInput
import UnitTangentIterates.PhysicalRearLocalShiftedStageAutomaticClosure

/-!
# Paper-facing smooth input from automatic fixed-row compactness

This is the direct-construction target for a concrete finite tower.  It asks
for no limiting stage and no synchronized convergence callback: those are
constructed from the terminal phase sidecar and normalized-steering
Lipschitz bounds.
-/

noncomputable section

open MarkedSpace

namespace PaperMainTheoremAutomaticSmoothInput

/-- Honest paper-facing input whose only additional analytic data are the
concrete fixed-row arrays and their common steering moduli. -/
structure Input
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt)
    (direction : ℂ) (modelWidth H : ℝ) where
  representatives : ∀ n,
    VariableMarkedTube.OrientedArclengthRepresentative (O.X n)
  paperOutput : PaperFacingVariableTerminalOutput.Output
    O direction modelWidth H
  gamma_eq : paperOutput.Gamma = fun n => ev (representatives n).q
  kh : ℝ
  tubeC : ℝ
  tubeDlt : ℝ
  kh_nonneg : 0 ≤ kh
  kh_lt_one : kh < 1
  tubeC_pos : 0 < tubeC
  representative_tube : ∀ n,
    IsTubeMember tubeC 0 tubeDlt (representatives n).q
  fixedRows : ∀ n,
    PhysicalRearLocalShiftedStageAutomaticClosure.FixedRowInput kh tubeC tubeDlt
      (representatives n).q (representatives (n + 1)).q

/-- Automatic rowwise compactness supplies the exact smooth-input wrapper. -/
def Input.toSmoothInput
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt}
    {direction : ℂ} {modelWidth H : ℝ}
    (I : Input O direction modelWidth H) :
    PaperMainTheoremSmoothInput.Input O direction modelWidth H where
  representatives := I.representatives
  paperOutput := I.paperOutput
  gamma_eq := I.gamma_eq
  localShiftedStages :=
    PhysicalRearLocalShiftedStageAutomaticClosure.localShiftedStages_of_fixedRowInputs
      I.kh_nonneg I.kh_lt_one I.tubeC_pos I.representative_tube I.fixedRows

/-- Strongest paper-facing conclusion from concrete automatic fixed-row
compactness.  Here `(⊤ : ℕ∞)` is the explicit `C∞` regularity index. -/
theorem paperSmooth
    {Q : ℕ → Data} {P : ℕ → ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {O : TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q P e P0 P1 khat G1 Cg C c dlt}
    {direction : ℂ} {modelWidth H : ℝ}
    (I : Input O direction modelWidth H) :
    ∃ Gamma : ℕ → ℝ → ℂ, ∃ L : ℝ,
      0 < L ∧
      Function.Periodic (Gamma 0) L ∧
      Set.InjOn (Gamma 0) (Set.Ico 0 L) ∧
      (∀ n, MainTheoremConditional.IsOval (Gamma n)) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (Gamma n)) ∧
      (∀ n, Set.range (Gamma (n + 1)) =
        Set.range (UnitTangent.unitTangentMap (Gamma n))) ∧
      ¬ ClosingArgument.IsCircleOfPerimeter (Set.range (Gamma 0)) L :=
  PaperMainTheoremSmoothInput.paperSmooth I.toSmoothInput

end PaperMainTheoremAutomaticSmoothInput
