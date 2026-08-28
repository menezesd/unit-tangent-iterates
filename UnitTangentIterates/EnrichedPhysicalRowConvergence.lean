import UnitTangentIterates.EnrichedPhysicalRowBounds
import UnitTangentIterates.RichFamilyRetainedPhysicalConvergence

/-!
# Retained physical-row convergence for enriched chosen families

The fixed row radius used by `PhysicalRowBounds` is not a convergence rate.
This module keeps the genuinely depth-dependent terminal marking defect as a
separate certificate and transfers the variable-terminal row limit to the
retained physical row by the metric squeeze theorem.
-/

noncomputable section

open Filter Topology MarkedSpace

namespace EnrichedPhysicalRowConvergence

open TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  RichFamilyRetainedPhysicalRows

/-- The actual terminal-base/variable-terminal error retained at every chosen
depth.  Unlike the row tube radius, `rho n k` is required to vanish with `k`. -/
structure EndpointDefectCertificate
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    (rho : ℕ → ℕ → ℝ) where
  rho_nonneg : ∀ n k, 0 ≤ rho n k
  terminalBase_dist : ∀ n k,
    dist (F.richStage n k).terminalBase (F.P n (k + 1)) ≤ rho n k
  rho_tendsto_zero : ∀ n, Tendsto (rho n) atTop (nhds 0)

/-- The actual retained terminal-base distance vanishes rowwise. -/
theorem EndpointDefectCertificate.terminalBase_dist_tendsto_zero
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {F : RichFamily Q e P0 P1 khat G1 Cg C c dlt}
    {rho : ℕ → ℕ → ℝ}
    (D : EndpointDefectCertificate F rho) (n : ℕ) :
    Tendsto
      (fun k => dist (F.richStage n k).terminalBase (F.P n (k + 1)))
      atTop (nhds 0) := by
  exact squeeze_zero (fun _ => dist_nonneg) (D.terminalBase_dist n)
    (D.rho_tendsto_zero n)

/-- A variable-terminal row limit and the vanishing retained endpoint defect
give the corresponding retained physical-row limit. -/
theorem EndpointDefectCertificate.rows_tendsto
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {F : RichFamily Q e P0 P1 khat G1 Cg C c dlt}
    {rho : ℕ → ℕ → ℝ} {X : ℕ → Data}
    (D : EndpointDefectCertificate F rho)
    (hterminal : ∀ n, Tendsto (fun k => F.P n (k + 1)) atTop (nhds (X n))) :
    ∀ n, Tendsto (rows F n) atTop (nhds (X n)) :=
  RichFamilyRetainedPhysicalConvergence.tendsto_rows_of_terminalBase_dist F
    hterminal D.terminalBase_dist_tendsto_zero

/-- The two physical-row inputs used downstream: fixed rowwise geometric
bounds and convergence to the already constructed variable-terminal limit. -/
structure LimitPackage
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db : ℝ}
    (F : RichFamily Q e P0 P1 khat G1 Cg C c dlt)
    (X : ℕ → Data) where
  bounds : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
    (rows F) F.P cb db
  physical_limit : ∀ n, Tendsto (rows F n) atTop (nhds (X n))

/-- Assemble the downstream package from independently proved row bounds and
the exact vanishing endpoint defect. -/
def LimitPackage.of_bounds_and_defect
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db : ℝ}
    {F : RichFamily Q e P0 P1 khat G1 Cg C c dlt}
    {rho : ℕ → ℕ → ℝ} {X : ℕ → Data}
    (bounds : RichFamilyPhysicalMarkingIntegration.PhysicalRowBounds
      (rows F) F.P cb db)
    (D : EndpointDefectCertificate F rho)
    (hterminal : ∀ n, Tendsto (fun k => F.P n (k + 1)) atTop (nhds (X n))) :
    LimitPackage (cb := cb) (db := db) F X :=
  { bounds := bounds
    physical_limit := D.rows_tendsto hterminal }

/-- The direct integration point for an enriched bounded construction. -/
def LimitPackage.of_boundedConstruction
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt cb db : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : EnrichedPhysicalChosenRichFamily.GaugeFamily
      Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    {E : EnrichedPhysicalChosenRichFamily.Construction
      Q e P0 P1 khat G1 Cg C c dlt period diagonal GaugeCertificate
      a MA NA K0 K1 K2}
    (B : EnrichedPhysicalRowBounds.BoundedConstruction E cb db)
    {rho : ℕ → ℕ → ℝ} {X : ℕ → Data}
    (D : EndpointDefectCertificate E.toRichFamily rho)
    (hterminal : ∀ n,
      Tendsto (fun k => E.toRichFamily.P n (k + 1)) atTop (nhds (X n))) :
    LimitPackage (cb := cb) (db := db) E.toRichFamily X :=
  of_bounds_and_defect B.physicalRowBounds D hterminal

end EnrichedPhysicalRowConvergence
