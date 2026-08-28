import UnitTangentIterates.EnrichedPhysicalChosenRichFamily
import UnitTangentIterates.EnrichedPhysicalHarnackClosure

/-!
# Construction core and physical Harnack completion

The recursive choice is made before Harnack closure is available.  This file
separates that choice data from the final `Construction` record and derives
the latter only after the retained physical rows and their vanishing endpoint
defect have been certified.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric

namespace EnrichedPhysicalChosenRichFamily

open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  GaugeRearFamilyVariableTerminal VariableMarkedTube

/-- The chosen recursive columns, with no limit-closure callback. -/
structure ConstructionCore
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

/-- The actual enriched column chosen at depth `k`. -/
def ConstructionCore.chosenColumn
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2) (k : ℕ) :=
  EnrichedPhysicalChosenRichFamily.chosenColumn
    F.baseProvider F.mapProvider k

/-- The exact transition selected at depth `k`, before any closure field is
assembled. -/
def ConstructionCore.chosenTransition
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2) (k : ℕ) :
    TransitionCertificate (F.chosenColumn k)
      (F.mapProvider.map k (F.chosenColumn k)).val
      a MA NA K0 K1 K2 :=
  (F.mapProvider.map k (F.chosenColumn k)).property

/-- The provider-level endpoint defect needed before a final rich family can
be constructed. -/
structure ConstructionCore.EndpointDefectCertificate
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2) : Prop where
  tendsToZero : ∀ n, Tendsto
    (fun k => dist
      (EnrichedPhysicalHarnackClosure.retainedRows
        F.baseProvider F.mapProvider n k)
      (columns F.baseProvider F.mapProvider k n))
    atTop (nhds 0)

/-- Complete the chosen core only after physical finite-stage kinematics and
the vanishing terminal marking defect prove Harnack closure. -/
def ConstructionCore.complete
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh cb db : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2)
    (hbaseHarnack : ∀ n, ArclengthHarnackCertificate (Q n))
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ n k, IsTubeMember cb 0 db
      (EnrichedPhysicalHarnackClosure.retainedRows
        F.baseProvider F.mapProvider n k))
    (finite : FinitePullbackPhysicalRearKinematics kh
      (EnrichedPhysicalHarnackClosure.retainedRows
        F.baseProvider F.mapProvider))
    (endpointDefect : F.EndpointDefectCertificate) :
    Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2 where
  defect := F.defect
  baseProvider := F.baseProvider
  mapProvider := F.mapProvider
  base_harnack := hbaseHarnack
  harnackClosed := EnrichedPhysicalHarnackClosure.harnackClosed_of_providers
    F.baseProvider F.mapProvider hkh0 hkh1 hcb hdb htube finite
      endpointDefect.tendsToZero

/-- Forget only the closure fields of an already assembled construction. -/
def Construction.toCore
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (F : Construction Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2) :
    ConstructionCore Q e P0 P1 khat G1 Cg C c dlt period diagonal
      GaugeCertificate a MA NA K0 K1 K2 where
  defect := F.defect
  baseProvider := F.baseProvider
  mapProvider := F.mapProvider

end EnrichedPhysicalChosenRichFamily
