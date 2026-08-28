import UnitTangentIterates.EnrichedPhysicalConstructionCore
import UnitTangentIterates.TriangularMarkedPathSchemeVariableTerminalDirect

/-!
# Direct-limit projection of an enriched construction core

The physical retained rows certify the Harnack estimate only at the marked
row limit.  No Harnack certificate for the initial configured marking, and no
finite-column Harnack induction, is used here.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed
open EnrichedPhysicalChosenRichFamily
open EnrichedPhysicalHarnackClosure
open VariableMarkedTube

namespace EnrichedPhysicalConstructionCoreDirect

def limitHarnack_of_providers
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh cb db : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (htube : ∀ n k, IsTubeMember cb 0 db (retainedRows B M n k))
    (finite : FinitePullbackPhysicalRearKinematics kh (retainedRows B M))
    (hdefect : ∀ n, Tendsto
      (fun k => dist (retainedRows B M n k) (columns B M k n))
      atTop (nhds 0)) :
    ∀ n x, Tendsto (fun k => columns B M k n) atTop (nhds x) →
      ArclengthHarnackCertificate x := by
  intro n x hcolumn
  have hphysical : Tendsto (retainedRows B M n) atTop (nhds x) :=
    tendsto_retained_of_column_and_defect hcolumn (hdefect n)
  have htubeX : IsTubeMember cb 0 db x :=
    (isClosed_tube cb 0 db).mem_of_tendsto hphysical
      (Eventually.of_forall (htube n))
  exact
    { q := x
      c := cb
      dlt := db
      c_pos := hcb
      dlt_pos := hdb
      tube := htubeX
      same_range := rfl
      strictness := limitStrictnessDataH_of_finitePullbackRowLimit
        hkh0 hkh1 hcb htube finite hphysical }

def toDirectScheme
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh cb db : ℝ}
    (F : ConstructionCore Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (hcolumnsTube : ∀ n k,
      IsVariableTubeMember c (C n) 0 dlt
        (columns F.baseProvider F.mapProvider k n))
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb) (hdb : 0 < db)
    (hphysicalTube : ∀ n k,
      IsTubeMember cb 0 db (retainedRows F.baseProvider F.mapProvider n k))
    (finite : FinitePullbackPhysicalRearKinematics kh
      (retainedRows F.baseProvider F.mapProvider))
    (endpointDefect : F.EndpointDefectCertificate) :
    TriangularMarkedPathSchemeVariableTerminalDirect.Scheme
      Q (fun n k => columns F.baseProvider F.mapProvider k n) e
      P0 P1 khat G1 Cg C c dlt where
  base := fun n => congrFun (columns_zero F.baseProvider F.mapProvider) n
  error_nonnegative := F.defect.nonnegative
  error_summable := F.defect.summable
  tube := hcolumnsTube
  stepPath := fun n k => by
    simpa only [columns_succ] using
      (F.chosenColumn k).step.richStage n |>.stage.increment
  stepGeometry := fun n k => by
    simpa only [columns_succ] using
      (F.chosenColumn k).step.richStage n |>.stage.increment_geometry
  stepCost := fun n k => by
    simpa only [columns_succ] using
      (F.chosenColumn k).step.richStage n |>.stage.increment_cost
  finiteEdge := fun n k => by
    simpa only [columns_succ] using
      (F.chosenColumn k).step.richStage n |>.stage.range_edge
  limitHarnack := limitHarnack_of_providers F.baseProvider F.mapProvider
    hkh0 hkh1 hcb hdb hphysicalTube finite endpointDefect.tendsToZero

end EnrichedPhysicalConstructionCoreDirect
