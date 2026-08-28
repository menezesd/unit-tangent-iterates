import UnitTangentIterates.EnrichedPhysicalChosenRichFamily
import UnitTangentIterates.PhysicalRearLimitHarnackAdapter

/-!
# Harnack closure before assembling an enriched construction

The enriched chosen-family record asks for Harnack closure while its physical
certificates are retained by the providers used to build that record.  This
module states the closure directly on those providers, avoiding a circular
assumption of an already assembled `Construction`.
-/

noncomputable section

open Filter Topology MarkedSpace PathMetric

namespace EnrichedPhysicalHarnackClosure

open EnrichedPhysicalChosenRichFamily
  TriangularMarkedRecursiveChoiceVariableTerminalConstructor
  VariableMarkedTube

/-- The ordinary physical rows retained by the enriched provider recursion.
Depth zero is the configured base curve; depth `k+1` is the terminal base of
the rich stage selected at depth `k`. -/
def retainedRows
    {Q : ℕ → Data} {e : ℕ → ℕ → ℝ}
    {P0 P1 khat G1 Cg C : ℕ → ℝ} {c dlt : ℝ}
    {period : ℕ → ℕ → ℝ} {diagonal : ℕ → ℝ}
    {GaugeCertificate : GaugeFamily Q e P0 P1 khat G1 Cg C c dlt}
    {a MA NA : ℕ → ℕ → ℝ} {K0 K1 K2 : ℝ}
    (B : BaseProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate)
    (M : MapProvider Q e P0 P1 khat G1 Cg C c dlt
      period diagonal GaugeCertificate a MA NA K0 K1 K2) :
    ℕ → ℕ → Data
  | n, 0 => Q n
  | n, k + 1 => ((chosenColumn B M k).step.richStage n).terminalBase

/-- A row of retained physical bases has the same limit as its marked column
when their marked distance tends to zero. -/
theorem tendsto_retained_of_column_and_defect
    {B P : ℕ → Data} {x : Data}
    (hP : Tendsto P atTop (nhds x))
    (hdefect : Tendsto (fun k => dist (B k) (P k)) atTop (nhds 0)) :
    Tendsto B atTop (nhds x) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  have heps2 : 0 < eps / 2 := by linarith
  obtain ⟨NP, hNP⟩ := Metric.tendsto_atTop.1 hP (eps / 2) heps2
  obtain ⟨ND, hND⟩ := Metric.tendsto_atTop.1 hdefect (eps / 2) heps2
  refine ⟨max NP ND, fun k hk => ?_⟩
  have hkP : NP ≤ k := (le_max_left _ _).trans hk
  have hkD : ND ≤ k := (le_max_right _ _).trans hk
  have hclose := hND k hkD
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at hclose
  calc
    dist (B k) x ≤ dist (B k) (P k) + dist (P k) x := dist_triangle _ _ _
    _ < eps / 2 + eps / 2 := add_lt_add hclose (hNP k hkP)
    _ = eps := by ring

/-- Row-local form of the finite-pullback strictness theorem.  The proof of
strictness in row `n` uses convergence only of the retained rear row; its
finite fronts need tube membership but need not converge. -/
def limitStrictnessDataH_of_finitePullbackRowLimit
    {kh cb db : ℝ} {B : ℕ → ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hcb : 0 < cb)
    (htube : ∀ i k, IsTubeMember cb 0 db (B i k))
    (finite : FinitePullbackPhysicalRearKinematics kh B)
    {n : ℕ} {x : Data} (hX : Tendsto (B n) atTop (nhds x)) :
    UnconditionalAssembly.LimitStrictnessDataH x := by
  have hXmem : IsTubeMember cb 0 db x :=
    (isClosed_tube cb 0 db).mem_of_tendsto hX
      (Eventually.of_forall (htube n))
  have hXshift : Tendsto (fun k => B n (k + 1)) atTop (nhds x) :=
    hX.comp (tendsto_add_atTop_nat 1)
  apply UnconditionalAssembly.limitStrictnessDataH_of_limit'
    (P := fun k => B n (k + 1)) hcb hXmem hXshift
  intro k a b hab
  let K := Nonempty.some (finite.stage n k)
  let S := K.toStageComponents hkh0 hkh1 hcb (htube (n + 1) k)
  let D := S.limitStrictness hcb (htube (n + 1) k)
  let DH := D.toH (fun s => (D.curvature_deriv s).differentiableAt)
  have hcurv : ∀ s, D.k s = UnconditionalAssembly.arcCurv (B n (k + 1)) s :=
    RearTrackEmbedded.curvature_eq_arcCurv hcb (htube n (k + 1))
      D.curve_deriv D.angle_deriv
  have hH := DH.curvature_harnack a b hab
  change Real.exp (a - b) *
      (D.k a / Real.sqrt (1 + D.k a ^ 2)) ≤
    D.k b / Real.sqrt (1 + D.k b ^ 2) at hH
  simpa only [hcurv a, hcurv b] using hH

/-- Corrected finite physical rows close Harnack on any marked column limit
which is approached by those same rows.  The finite-column Harnack premise is
kept in the result's callback signature for direct use in `Construction`. -/
def harnackClosed_of_providers
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
      (∀ k, ArclengthHarnackCertificate (columns B M k n)) →
      ArclengthHarnackCertificate x := by
  intro n x hcolumn _
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

end EnrichedPhysicalHarnackClosure
