import UnitTangentIterates.ConfiguredCompatiblePhysicalRearSequence
import UnitTangentIterates.MixedFinitePhysicalRearKinematics
import UnitTangentIterates.RichFamilyRetainedPhysicalRows

/-!
# Physical certificates on the retained rows of a rich family

The physical rows used by the limiting argument are the terminal bases stored
by the rich stages, not a separately reconstructed canonical pullback.  This
module packages bounds and finite rear kinematics directly on those retained
rows.  The base edge is supplied by the compatible physical-pair recursion;
later edges retain the physical kinematics produced by the mapped rich stages.
-/

noncomputable section

open MarkedSpace

namespace RichFamilyRetainedPhysicalCertificate

open ConfiguredCompatiblePhysicalRearSequence
  RichFamilyPhysicalMarkingIntegration
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- The geometric data consumed by the physical limit argument, stated on the
actual terminal bases retained by a rich recursive family. -/
structure Certificate
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    (kh cb db : ℝ) where
  bounds : PhysicalRowBounds
    (RichFamilyRetainedPhysicalRows.rows F) F.P cb db
  mixed : PathMetric.MixedFinitePhysicalRearKinematics kh
    (RichFamilyRetainedPhysicalRows.rows F) F.P

/-- Strong retained-row package used when mapped-stage construction keeps its
physical kinematics against the preceding retained terminal base itself. -/
structure CorrectedCertificate
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    (kh cb db : ℝ) where
  bounds : PhysicalRowBounds
    (RichFamilyRetainedPhysicalRows.rows F) F.P cb db
  finite : PathMetric.FinitePullbackPhysicalRearKinematics kh
    (RichFamilyRetainedPhysicalRows.rows F)

/-- The direct normalized markings are definitionally aligned with the same
retained rows appearing in `Certificate`. -/
def Certificate.directMarkings
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt kh cb db : ℝ}
    {F : RichFamily Q e P0 P1 khat G1 Cg C c dlt}
    (_ : Certificate F kh cb db) :
    DirectPhysicalTerminalMarkingFamily
      (RichFamilyRetainedPhysicalRows.rows F) F.P :=
  RichFamilyRetainedPhysicalRows.directMarkings F

/-- The corrected package uses the same definitionally aligned terminal
markings as the mixed package. -/
def CorrectedCertificate.directMarkings
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt kh cb db : ℝ}
    {F : RichFamily Q e P0 P1 khat G1 Cg C c dlt}
    (_ : CorrectedCertificate F kh cb db) :
    DirectPhysicalTerminalMarkingFamily
      (RichFamilyRetainedPhysicalRows.rows F) F.P :=
  RichFamilyRetainedPhysicalRows.directMarkings F

/-- Corrected stage-local physical witnesses assemble into ordinary finite
pullback kinematics on the retained rows.  The successor premise is the exact
type a mapped affine provider must retain; it is not derived from range or
normalized-marking equivalence. -/
def corrected_of_pairSourceOutput
    {D : ConstructedConfiguredSequenceWeighted.Data} {kh c0 d0 : ℝ}
    (S : PairSource D kh c0 d0) {q0 : Data} (O : S.Output q0)
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db : ℝ}
    (F : RichFamily O.Q e P0 P1 khat G1 Cg C c dlt)
    (hbaseCarrier : ∀ n, (F.richStage n 0).terminalBase = O.A n)
    (hsucc : ∀ n k, Nonempty
      (PathMetric.PhysicalRearLimitKinematics kh
        (F.richStage n (k + 1)).terminalBase
        (F.richStage (n + 1) k).terminalBase))
    (bounds : PhysicalRowBounds
      (RichFamilyRetainedPhysicalRows.rows F) F.P cb db) :
    CorrectedCertificate F kh cb db where
  bounds := bounds
  finite := by
    refine ⟨?_⟩
    intro n k
    cases k with
    | zero =>
        simpa only [RichFamilyRetainedPhysicalRows.rows_succ,
          RichFamilyRetainedPhysicalRows.rows_zero, hbaseCarrier n,
          F.base (n + 1)] using O.physical n
    | succ k =>
        simpa only [RichFamilyRetainedPhysicalRows.rows_succ] using hsucc n k

/-- Assemble retained-row kinematics.  Only the depth-zero edge is imported
from the compatible configured pair.  The successor premise is deliberately
stated between the terminal bases stored by adjacent rich stages, so mapped
providers can retain their physical output without identifying it with a
canonical selected-inverse marking. -/
def of_pairSourceOutput
    {D : ConstructedConfiguredSequenceWeighted.Data} {kh c0 d0 : ℝ}
    (S : PairSource D kh c0 d0) {q0 : Data} (O : S.Output q0)
    {e : ℕ → ℕ → ℝ} {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db : ℝ}
    (F : RichFamily O.Q e P0 P1 khat G1 Cg C c dlt)
    (hbaseCarrier : ∀ n, (F.richStage n 0).terminalBase = O.A n)
    (hsucc : ∀ n k, Nonempty
      (PathMetric.PhysicalRearLimitKinematics kh
        (F.richStage n (k + 1)).terminalBase
        (F.P (n + 1) (k + 1))))
    (bounds : PhysicalRowBounds
      (RichFamilyRetainedPhysicalRows.rows F) F.P cb db) :
    Certificate F kh cb db where
  bounds := bounds
  mixed := by
    refine ⟨?_⟩
    intro n k
    cases k with
    | zero =>
        simpa only [RichFamilyRetainedPhysicalRows.rows_succ,
          RichFamilyRetainedPhysicalRows.rows_zero, hbaseCarrier n,
          F.base (n + 1)] using O.physical n
    | succ k =>
        simpa only [RichFamilyRetainedPhysicalRows.rows_succ] using hsucc n k

end RichFamilyRetainedPhysicalCertificate
