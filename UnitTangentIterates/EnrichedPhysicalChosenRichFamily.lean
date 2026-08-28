import UnitTangentIterates.TriangularMarkedRecursiveChoiceVariableTerminalConstructor
import UnitTangentIterates.EnrichedPhysicalGaugeStage

/-!
# Chosen rich families retaining physical component transitions

The ordinary recursive constructor deliberately forgets the separated
physical Jacobi data when a `ColumnStep` is selected.  This companion performs
dependent choice on an enriched column.  It retains both the four physical
components of every selected path and the exact transition to the next
selected column, and only then projects to the existing `RichFamily` API.
-/

noncomputable section

open Function Filter Topology MarkedSpace PathMetric

namespace EnrichedPhysicalChosenRichFamily

open AnchoredJacobiStableTransition
  PhysicalArclengthJacobiTransition
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  VariableMarkedTube

/-- Four simultaneous scalar bounds on a physical component vector. -/
structure ComponentBound (x : Components) (d : ℝ) : Prop where
  w : x.w ≤ d
  s0 : x.s0 ≤ d
  s1 : x.s1 ≤ d
  s2 : x.s2 ≤ d

/-- A certificate family allowed to inspect the complete selected step.  This
is the correct dependency for `EnrichedPhysicalGaugeStage.Output`, whose
front/raw/anchored fields are the actual normal velocities stored in that
step. -/
abbrev GaugeFamily
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ) :=
  ∀ {current : ℕ → Data} {k : ℕ},
    ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt → ℕ → Type

/-- A selected column before erasure.  Its path at `(n,k)` is measured using
the supplied physical perimeter `period n k`, and is bounded by the diagonal
source `diagonal (n+k)`.

The `gauge` field is intentionally a type family: its configured instance is
`EnrichedPhysicalGaugeStage.Output`, retaining the separated flowed,
integrated, and physical raw estimates in addition to the final transition.
-/
structure CertifiedColumn
    (Q current : ℕ → Data) (e : ℕ → ℕ → ℝ) (k : ℕ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt) where
  step : ColumnStep Q current e k P0 P1 khat G1 Cg C c dlt
  period_ge_one : ∀ n, 1 ≤ period n k
  components_nonnegative : ∀ n,
    (components (period n k) (step.richStage n).stage.increment.eta).Nonnegative
  components_bound : ∀ n,
    ComponentBound
      (components (period n k) (step.richStage n).stage.increment.eta)
      (diagonal (n + k))
  gauge : ∀ n, GaugeCertificate step n

/-- The exact physical transition retained between two actually selected
columns.  No statement is required for arbitrary raw gauge outputs. -/
structure TransitionCertificate
    {Q current : ℕ → Data} {e : ℕ → ℕ → ℝ} {k : ℕ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (T : CertifiedColumn Q S.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal GaugeCertificate)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) : Prop where
  transition : ∀ n,
    Transition
      (components (period (n + 1) k)
        (S.step.richStage (n + 1)).stage.increment.eta)
      (components (period n (k + 1))
        (T.step.richStage n).stage.increment.eta)
      (a n k) (MA n k) (NA n k) K0 K1 K2

structure BaseProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt) where
  base : CertifiedColumn Q Q e 0 P0 P1 khat G1 Cg C c dlt
    period diagonal GaugeCertificate

structure MapProvider
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  map : ∀ k {current}
    (S : CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate),
    {T : CertifiedColumn Q S.step.next e (k + 1)
      P0 P1 khat G1 Cg C c dlt period diagonal GaugeCertificate //
      TransitionCertificate S T a MA NA K0 K1 K2}

def stageColumns
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2) :
    ∀ k, (current : ℕ → Data) ×
      CertifiedColumn Q current e k P0 P1 khat G1 Cg C c dlt
        period diagonal GaugeCertificate
  | 0 => ⟨Q, B.base⟩
  | k + 1 =>
      let S := stageColumns B M k
      let next := M.map k S.2
      ⟨S.2.step.next, next.val⟩

def columns
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (k : ℕ) : ℕ → Data := (stageColumns B M k).1

def chosenColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (k : ℕ) :
    CertifiedColumn Q (columns B M k) e k P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate := by
  change CertifiedColumn Q (stageColumns B M k).1 e k
    P0 P1 khat G1 Cg C c dlt period diagonal GaugeCertificate
  exact (stageColumns B M k).2

theorem columns_zero
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2) :
    columns B M 0 = Q := rfl

theorem columns_succ
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2) (k : ℕ) :
    columns B M (k + 1) = (chosenColumn B M k).step.next := rfl

/-- Provider-backed chosen construction.  Keeping the providers in the output
makes every certificate selected by `Classical.choice` recoverable, without a
dependent equality between an erased endpoint column and its successor. -/
structure Construction
    (Q : ℕ → Data) (e : ℕ → ℕ → ℝ)
    (P0 P1 khat G1 Cg C : ℕ → ℝ) (c dlt : ℝ)
    (period : ℕ → ℕ → ℝ) (diagonal : ℕ → ℝ)
    (GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt)
    (a MA NA : ℕ → ℕ → ℝ) (K0 K1 K2 : ℝ) where
  defect : RowDefectProvider e
  baseProvider : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal GaugeCertificate
  mapProvider : MapProvider Q e P0 P1 khat G1 Cg C c dlt
    period diagonal GaugeCertificate a MA NA K0 K1 K2
  base_harnack : ∀ n, ArclengthHarnackCertificate (Q n)
  harnackClosed : ∀ n x,
    Tendsto (fun k => columns baseProvider mapProvider k n) atTop (nhds x) →
    (∀ k, ArclengthHarnackCertificate
      (columns baseProvider mapProvider k n)) →
      ArclengthHarnackCertificate x

def Construction.toRichFamily
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2) :
    RichFamily Q e P0 P1 khat G1 Cg C c dlt where
  P n k := columns F.baseProvider F.mapProvider k n
  base := fun _ => rfl
  defect := F.defect
  base_harnack := F.base_harnack
  richStage := by
    intro n k
    change RichStageData
      (columns F.baseProvider F.mapProvider k n)
      (columns F.baseProvider F.mapProvider k (n + 1))
      (columns F.baseProvider F.mapProvider (k + 1) n)
      (e n k) (P0 n) (P1 n) (khat n) (G1 n) (Cg n) c (C n) dlt
    rw [columns_succ]
    exact (chosenColumn F.baseProvider F.mapProvider k).step.richStage n
  harnackClosed := F.harnackClosed

/-- The concrete component state at a chosen depth. -/
def Construction.chosenColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2) (k : ℕ) :=
  EnrichedPhysicalChosenRichFamily.chosenColumn
    F.baseProvider F.mapProvider k

/-- The exact transition certificate chosen after depth `k`. -/
def Construction.chosenTransition
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2) (k : ℕ) :
    TransitionCertificate (F.chosenColumn k)
      (F.mapProvider.map k (F.chosenColumn k)).val
      a MA NA K0 K1 K2 :=
  (F.mapProvider.map k (F.chosenColumn k)).property

end EnrichedPhysicalChosenRichFamily
