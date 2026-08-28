import UnitTangentIterates.EnrichedPhysicalHarnackClosure

/-!
# Provider certificates for enriched physical Harnack closure

These adapters convert the base and selected-successor certificates retained
before `Construction` exists into the three inputs of
`EnrichedPhysicalHarnackClosure.harnackClosed_of_providers`.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric

namespace EnrichedPhysicalHarnackClosureAdapters

open EnrichedPhysicalChosenRichFamily
  EnrichedPhysicalHarnackClosure
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  VariableMarkedTube

/-- Base and selected terminal-base tube bounds give a fixed tube on every
provider-retained physical row. -/
theorem retainedRows_tube
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 cb db : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (hbase : ∀ n, IsTubeMember cb 0 db (Q n))
    (hterminal : ∀ k n,
      IsTubeMember cb 0 db ((chosenColumn B M k).step.richStage n).terminalBase) :
    ∀ n k, IsTubeMember cb 0 db (retainedRows B M n k) := by
  intro n k
  cases k with
  | zero => exact hbase n
  | succ k => exact hterminal k n

/-- The physical base edge and every selected successor edge assemble into
finite pullback kinematics on the provider-retained rows. -/
def finite_of_provider_edges
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 kh : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    (hbase : ∀ n, Nonempty (PhysicalRearLimitKinematics kh
      ((chosenColumn B M 0).step.richStage n).terminalBase (Q (n + 1))))
    (hsuccessor : ∀ k n, Nonempty (PhysicalRearLimitKinematics kh
      ((chosenColumn B M (k + 1)).step.richStage n).terminalBase
      ((chosenColumn B M k).step.richStage (n + 1)).terminalBase)) :
    FinitePullbackPhysicalRearKinematics kh (retainedRows B M) := by
  refine ⟨?_⟩
  intro n k
  cases k with
  | zero => simpa [retainedRows] using hbase n
  | succ k => simpa [retainedRows] using hsuccessor k n

/-- A vanishing estimate on each selected terminal base and its marked
endpoint gives the full retained-row/column defect required by Harnack
closure.  The depth-zero distance is identically zero. -/
theorem retainedRows_defect_tendsto_zero
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2)
    {rho : ℕ → ℕ → ℝ}
    (hrho : ∀ n, Tendsto (rho n) atTop (nhds 0))
    (hterminal : ∀ n k,
      dist ((chosenColumn B M k).step.richStage n).terminalBase
        ((chosenColumn B M k).step.next n) ≤ rho n k) :
    ∀ n, Tendsto
      (fun k => dist (retainedRows B M n k) (columns B M k n))
      atTop (nhds 0) := by
  intro n
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hrho n) eps heps
  refine ⟨N + 1, fun m hm => ?_⟩
  have hm0 : m ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hk : N ≤ k := by omega
  have hr := hN k hk
  rw [Real.dist_eq, sub_zero] at hr
  have hbound := hterminal n k
  rw [EnrichedPhysicalChosenRichFamily.columns_succ]
  change dist
      (dist ((chosenColumn B M k).step.richStage n).terminalBase
        ((chosenColumn B M k).step.next n)) 0 < eps
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  exact hbound.trans_lt ((le_abs_self (rho n k)).trans_lt hr)

/-- One-call provider-level Harnack closure from the exact fields naturally
retained by the base and mapped enriched stages. -/
def harnackClosed_of_provider_certificates
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
    (hbaseTube : ∀ n, IsTubeMember cb 0 db (Q n))
    (hterminalTube : ∀ k n,
      IsTubeMember cb 0 db ((chosenColumn B M k).step.richStage n).terminalBase)
    (hbasePhysical : ∀ n, Nonempty (PhysicalRearLimitKinematics kh
      ((chosenColumn B M 0).step.richStage n).terminalBase (Q (n + 1))))
    (hsuccessorPhysical : ∀ k n, Nonempty (PhysicalRearLimitKinematics kh
      ((chosenColumn B M (k + 1)).step.richStage n).terminalBase
      ((chosenColumn B M k).step.richStage (n + 1)).terminalBase))
    {rho : ℕ → ℕ → ℝ}
    (hrho : ∀ n, Tendsto (rho n) atTop (nhds 0))
    (hterminalDefect : ∀ n k,
      dist ((chosenColumn B M k).step.richStage n).terminalBase
        ((chosenColumn B M k).step.next n) ≤ rho n k) :
    ∀ n x, Tendsto (fun k => columns B M k n) atTop (nhds x) →
      (∀ k, ArclengthHarnackCertificate (columns B M k n)) →
      ArclengthHarnackCertificate x :=
  harnackClosed_of_providers B M hkh0 hkh1 hcb hdb
    (retainedRows_tube B M hbaseTube hterminalTube)
    (finite_of_provider_edges B M hbasePhysical hsuccessorPhysical)
    (retainedRows_defect_tendsto_zero B M hrho hterminalDefect)

end EnrichedPhysicalHarnackClosureAdapters
