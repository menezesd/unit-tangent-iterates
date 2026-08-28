import UnitTangentIterates.EnrichedPhysicalChosenRichFamily
import UnitTangentIterates.RichFamilyRetainedPhysicalRows
import UnitTangentIterates.PhysicalRearLimitHarnackAdapter
import UnitTangentIterates.RichFamilyRetainedPhysicalCertificate
import UnitTangentIterates.RichFamilyRetainedPhysicalConvergence

/-! # Finite physical kinematics for enriched retained rows -/

noncomputable section

open MarkedSpace PathMetric

namespace EnrichedGaugeFirstFinitePhysicalCertificate

open EnrichedPhysicalChosenRichFamily
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor

/-- The complete physical input consumed by the rich-family capstone: the
finite physical certificate and the limits of its retained physical rows. -/
structure LimitCertificate
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt kh cb db : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt) where
  Xphysical : ℕ → Data
  corrected : RichFamilyRetainedPhysicalCertificate.CorrectedCertificate
    F kh cb db
  converges : ∀ n, Filter.Tendsto
    (RichFamilyRetainedPhysicalRows.rows F n) Filter.atTop
    (nhds (Xphysical n))

/-- The exact physical datum which a corrected mapped gauge transition must
retain.  It relates the target column's physical terminal base to the
diagonally adjacent physical terminal base in the source column. -/
structure PhysicalTransitionCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (T : CertifiedColumn Q S.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal GaugeCertificate)
    (kh : ℝ) : Prop where
  physical : ∀ n, Nonempty
    (PhysicalRearLimitKinematics kh
      (T.step.richStage n).terminalBase
      (S.step.richStage (n + 1)).terminalBase)

/-- Base physical kinematics plus the exact certificate retained by every
chosen enriched transition assemble into ordinary finite pullback kinematics
on the terminal-base rows. -/
def finite_of_enriched
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh : ℝ}
    (E : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2)
    (hbase : ∀ n, Nonempty
      (PhysicalRearLimitKinematics kh
        ((E.chosenColumn 0).step.richStage n).terminalBase (Q (n + 1))))
    (htransition : ∀ k,
      PhysicalTransitionCertificate (E.chosenColumn k)
        (E.mapProvider.map k (E.chosenColumn k)).val kh) :
    FinitePullbackPhysicalRearKinematics kh
      (RichFamilyRetainedPhysicalRows.rows E.toRichFamily) := by
  refine ⟨?_⟩
  intro n k
  cases k with
  | zero =>
      simpa only [RichFamilyRetainedPhysicalRows.rows_succ,
        RichFamilyRetainedPhysicalRows.rows_zero,
        Construction.toRichFamily,
        EnrichedPhysicalChosenRichFamily.columns_zero] using hbase n
  | succ k =>
      simpa only [RichFamilyRetainedPhysicalRows.rows_succ,
        Construction.toRichFamily] using (htransition k).physical n

/-- Package the generic enriched finite adapter with independently established
uniform physical-row bounds, in the exact form consumed by the rich-family
paper-facing capstone. -/
def correctedCertificate_of_enriched
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh cb db : ℝ}
    (E : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2)
    (hbase : ∀ n, Nonempty
      (PhysicalRearLimitKinematics kh
        ((E.chosenColumn 0).step.richStage n).terminalBase (Q (n + 1))))
    (htransition : ∀ k,
      PhysicalTransitionCertificate (E.chosenColumn k)
        (E.mapProvider.map k (E.chosenColumn k)).val kh)
    (bounds : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
      (RichFamilyRetainedPhysicalRows.rows E.toRichFamily)
      E.toRichFamily.P cb db) :
    RichFamilyRetainedPhysicalCertificate.CorrectedCertificate
      E.toRichFamily kh cb db where
  bounds := bounds
  finite := finite_of_enriched E hbase htransition

/-- Enriched finite kinematics, uniform physical bounds, terminal-row
convergence and a vanishing marking defect give the complete physical limit
input without assuming retained-row convergence separately. -/
def limitCertificate_of_enriched
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh cb db : ℝ}
    (E : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2)
    (hbase : ∀ n, Nonempty
      (PhysicalRearLimitKinematics kh
        ((E.chosenColumn 0).step.richStage n).terminalBase (Q (n + 1))))
    (htransition : ∀ k,
      PhysicalTransitionCertificate (E.chosenColumn k)
        (E.mapProvider.map k (E.chosenColumn k)).val kh)
    (bounds : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
      (RichFamilyRetainedPhysicalRows.rows E.toRichFamily)
      E.toRichFamily.P cb db)
    (X : ℕ → Data)
    (hterminal : ∀ n, Filter.Tendsto
      (fun k => E.toRichFamily.P n (k + 1)) Filter.atTop (nhds (X n)))
    (hdefect : ∀ n, Filter.Tendsto
      (fun k => dist (E.toRichFamily.richStage n k).terminalBase
        (E.toRichFamily.P n (k + 1))) Filter.atTop (nhds 0)) :
    LimitCertificate (kh := kh) (cb := cb) (db := db) E.toRichFamily where
  Xphysical := X
  corrected := correctedCertificate_of_enriched E hbase htransition bounds
  converges :=
    RichFamilyRetainedPhysicalConvergence.tendsto_rows_of_terminalBase_dist
      E.toRichFamily hterminal hdefect

end EnrichedGaugeFirstFinitePhysicalCertificate
