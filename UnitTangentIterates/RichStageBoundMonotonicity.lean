import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-! # Monotonicity of rich-stage cost bounds -/

noncomputable section

open MarkedSpace PathMetric

namespace TriangularMarkedRecursiveChoiceVariableTerminalConstructor

open GaugeRearFamilyVariableTerminal

/-- Enlarging only the scalar path-cost cap preserves a rich stage. -/
def RichStageData.monoBound
    {p front rear : Data} {bound bound' P0 P1 khat G1 Cg c C dlt : ℝ}
    (S : RichStageData p front rear bound P0 P1 khat G1 Cg c C dlt)
    (hbound : bound ≤ bound') :
    RichStageData p front rear bound' P0 P1 khat G1 Cg c C dlt where
  stage :=
    { increment := S.stage.increment
      increment_geometry := S.stage.increment_geometry
      increment_cost := S.stage.increment_cost.trans hbound
      rear_curve_deriv := S.stage.rear_curve_deriv
      rear_vel_deriv := S.stage.rear_vel_deriv
      rear_periodic := S.stage.rear_periodic
      rear_curvature_nonnegative := S.stage.rear_curvature_nonnegative
      range_edge := S.stage.range_edge
      rear_harnack := S.stage.rear_harnack }
  terminalBase := S.terminalBase
  lambda := S.lambda
  Lambda := S.Lambda
  marking := S.marking

/-- Simultaneous enlargement of the path-cost and variable-speed ceilings. -/
def RichStageData.monoBounds
    {p front rear : Data}
    {bound bound' P0 P1 P1' khat G1 G1' Cg Cg' c C dlt : ℝ}
    (S : RichStageData p front rear bound P0 P1 khat G1 Cg c C dlt)
    (hkhat : 0 ≤ khat) (hbound : bound ≤ bound')
    (hP1 : P1 ≤ P1') (hG1 : G1 ≤ G1') (hCg : Cg ≤ Cg') :
    RichStageData p front rear bound' P0 P1' khat G1' Cg' c C dlt where
  stage :=
    { increment := S.stage.increment
      increment_geometry := S.stage.increment_geometry.mono
        S.stage.increment hkhat hP1 hG1 hCg
      increment_cost := S.stage.increment_cost.trans hbound
      rear_curve_deriv := S.stage.rear_curve_deriv
      rear_vel_deriv := S.stage.rear_vel_deriv
      rear_periodic := S.stage.rear_periodic
      rear_curvature_nonnegative := S.stage.rear_curvature_nonnegative
      range_edge := S.stage.range_edge
      rear_harnack := S.stage.rear_harnack }
  terminalBase := S.terminalBase
  lambda := S.lambda
  Lambda := S.Lambda
  marking := S.marking

/-- Pointwise enlargement of the error array transports a whole selected
column without changing its endpoint or any retained marking. -/
def ColumnStep.monoError
    {Q current : ℕ → Data} {e e' : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (S : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt)
    (he : ∀ n, e n k ≤ e' n k) :
    ColumnStep Q current e' k P0 P1 khat G1 Cg C c dlt where
  next := S.next
  richStage n := (S.richStage n).monoBound (he n)

/-- In particular, a base provider may be reused after a pointwise increase
of its depth-zero bounds. -/
def BaseStageProvider.monoErrorZero
    {Q : ℕ → Data} {e e' : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (he : ∀ n, e n 0 ≤ e' n 0) :
    BaseStageProvider Q e' P0 P1 khat G1 Cg C c dlt :=
  ⟨B.base.map (fun S => S.monoError he)⟩

/-- Widen the depth-zero error and the three upper derivative ceilings in one
step.  This is the adapter needed by a gauge-first base provider when mapped
columns use common widened ceilings. -/
def BaseStageProvider.monoBounds
    {Q : ℕ → Data} {e e' : ℕ → ℕ → ℝ}
    {P0 P1 P1' khat G1 G1' Cg Cg' C : ℕ → ℝ} {c dlt : ℝ}
    (B : BaseStageProvider Q e P0 P1 khat G1 Cg C c dlt)
    (hkhat : ∀ n, 0 ≤ khat n)
    (he : ∀ n, e n 0 ≤ e' n 0)
    (hP1 : ∀ n, P1 n ≤ P1' n)
    (hG1 : ∀ n, G1 n ≤ G1' n)
    (hCg : ∀ n, Cg n ≤ Cg' n) :
    BaseStageProvider Q e' P0 P1' khat G1' Cg' C c dlt :=
  ⟨B.base.map (fun S =>
    { next := S.next
      richStage := fun n => (S.richStage n).monoBounds
        (hkhat n) (he n) (hP1 n) (hG1 n) (hCg n) })⟩

end TriangularMarkedRecursiveChoiceVariableTerminalConstructor
