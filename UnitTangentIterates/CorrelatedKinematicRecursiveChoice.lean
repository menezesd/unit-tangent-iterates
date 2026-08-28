import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminalConstructor
import UnitTangentIterates.PhysicalRearLimitKinematicClosure

/-!
# Correlated variable/physical recursive choices

The physical rear furnished by a gauge stage is not the variable-marked
terminal datum.  This module retains both, together with their normalized
marking, through dependent choice.  The resulting certificate is deliberately
mixed-edge: converting it to `FinitePullbackPhysicalRearKinematics` requires a
separate front-reparametrization equivariance theorem.
-/

noncomputable section

open MarkedSpace PathMetric

namespace CorrelatedKinematicRecursiveChoice

open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  NormalizedTerminalMarkingComposition

/-- A chosen variable transition column together with the physical selected
rear of each adjacent variable front. -/
structure KinematicColumnStep
    (kh : ℝ) (Q current : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  column : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt
  physical : ∀ n, PhysicalRearLimitKinematics kh
    (column.richStage n).terminalBase (current (n + 1))

structure KinematicBaseStageProvider
    (kh : ℝ) (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  base : Nonempty (KinematicColumnStep kh Q Q e 0 P0 P1 khat G1 Cg C c dlt)

structure KinematicMapStageProvider
    (kh : ℝ) (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) where
  map : ∀ k {current}
    (S : KinematicColumnStep kh Q current e k P0 P1 khat G1 Cg C c dlt),
    Nonempty (KinematicColumnStep kh Q S.column.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt)

def stages
    {kh c dlt : ℝ} {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ}
    (B : KinematicBaseStageProvider kh Q e P0 P1 khat G1 Cg C c dlt)
    (M : KinematicMapStageProvider kh Q e P0 P1 khat G1 Cg C c dlt) :
    ∀ k, (current : ℕ → Data) ×
      KinematicColumnStep kh Q current e k P0 P1 khat G1 Cg C c dlt
  | 0 => ⟨Q, Classical.choice B.base⟩
  | k + 1 =>
      let S := stages B M k
      ⟨S.2.column.next, Classical.choice (M.map k S.2)⟩

def variableRows
    {kh c dlt : ℝ} {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ}
    (B : KinematicBaseStageProvider kh Q e P0 P1 khat G1 Cg C c dlt)
    (M : KinematicMapStageProvider kh Q e P0 P1 khat G1 Cg C c dlt)
    (n k : ℕ) : Data :=
  (stages B M k).1 n

def physicalRearRows
    {kh c dlt : ℝ} {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ}
    (B : KinematicBaseStageProvider kh Q e P0 P1 khat G1 Cg C c dlt)
    (M : KinematicMapStageProvider kh Q e P0 P1 khat G1 Cg C c dlt)
    (n k : ℕ) : Data :=
  ((stages B M k).2.column.richStage n).terminalBase

/-- Exact finite physical information retained by the variable-terminal
recursion.  The marking field records why the physical rear and next variable
row have the same oriented curve, without identifying their markings. -/
structure MixedFinitePhysicalRearKinematics
    (kh : ℝ) (P A : ℕ → ℕ → Data) : Type where
  stage : ∀ n k, Nonempty (PhysicalRearLimitKinematics kh (A n k) (P (n + 1) k))
  lambda : ℕ → ℕ → ℝ
  Lambda : ℕ → ℕ → ℝ
  marking : ∀ n k, NormalizedC2Marking (A n k) (P n (k + 1))
    (lambda n k) (Lambda n k)

def mixedFinite
    {kh c dlt : ℝ} {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ}
    (B : KinematicBaseStageProvider kh Q e P0 P1 khat G1 Cg C c dlt)
    (M : KinematicMapStageProvider kh Q e P0 P1 khat G1 Cg C c dlt) :
    MixedFinitePhysicalRearKinematics kh (variableRows B M)
      (physicalRearRows B M) where
  stage := fun n k => ⟨(stages B M k).2.physical n⟩
  lambda := fun n k => ((stages B M k).2.column.richStage n).lambda
  Lambda := fun n k => ((stages B M k).2.column.richStage n).Lambda
  marking := by
    intro n k
    change NormalizedC2Marking
      (((stages B M k).2.column.richStage n).terminalBase)
      ((stages B M (k + 1)).1 n) _ _
    simpa [stages] using ((stages B M k).2.column.richStage n).marking

end CorrelatedKinematicRecursiveChoice
