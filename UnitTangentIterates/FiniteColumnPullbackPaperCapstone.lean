import UnitTangentIterates.FiniteColumnStablePhysicalComponentCompactness
import UnitTangentIterates.PullbackUnitTangentRangeOrbit
import UnitTangentIterates.PaperFacingVariableTerminalOutput
import UnitTangentIterates.TubeHarnackStrictness

/-!
# Paper capstone for finite canonical pullback columns

This interface is independent of a recursive composition core.  It consumes
the canonical triangular pullback grid, summable direct metric increments,
and the physical facts retained by each finite column.  Exact range edges
pass to the limit by marked continuity.  The mismatch between a transported
gauge endpoint and the next canonical datum occurs only in the supplied
summable increment bound.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open VariableMarkedTube UnconditionalAssembly

namespace FiniteColumnPullbackPaperCapstone

def grid (kh : ℝ) (Q : ℕ → Data) (n k : ℕ) : Data :=
  TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k

def dummyP0 : ℕ → ℝ := fun _ => 1
def dummyZero : ℕ → ℝ := fun _ => 0

@[simp] theorem dummy_rowC (n : ℕ) :
    TriangularMarkedPathSchemeVariableTerminal.rowC dummyP0 dummyZero
      dummyZero dummyZero dummyZero n = 1 := by
  norm_num [TriangularMarkedPathSchemeVariableTerminal.rowC, dummyP0,
    dummyZero, NormalPathC2IncrementVariableSpeed.c2ConstVar,
    NormalPathC2Increment.velConst,
    NormalPathC2IncrementVariableSpeed.accConstVar]

/-- Minimal physical and metric information retained from finite columns. -/
structure Provider (kh : ℝ) (Q : ℕ → Data) (w : ℕ → ℕ → ℝ)
    (c dlt : ℝ) where
  X : ℕ → Data
  error_nonnegative : ∀ n k, 0 ≤ w n k
  error_summable : ∀ n, Summable (w n)
  step_dist : ∀ n k,
    dist (grid kh Q n k) (grid kh Q n (k + 1)) ≤ w n k
  finite_tube : ∀ n k, IsTubeMember c 0 dlt (grid kh Q n k)
  limit_tube : ∀ n, IsTubeMember c 0 dlt (X n)
  row_limit : ∀ n, Tendsto (grid kh Q n) atTop (nhds (X n))
  finite_range : ∀ n k,
    range (ev (grid kh Q (n + 1) k)) =
      range (UnitTangent.unitTangentMap
        (ev (SelectedInverseMap.selInv kh (grid kh Q (n + 1) k))))
  finite_harnack : ∀ n k a b, a ≤ b →
    Real.exp (a - b) *
        (arcCurv (grid kh Q n k) a /
          Real.sqrt (1 + arcCurv (grid kh Q n k) a ^ 2)) ≤
      arcCurv (grid kh Q n k) b /
        Real.sqrt (1 + arcCurv (grid kh Q n k) b ^ 2)

/-- A compactness output may be combined with the finite-column sidecars
without exposing the analytic construction that produced it. -/
def Provider.ofCompactnessOutput
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (L : FiniteColumnStablePhysicalComponentCompactness.LimitOutput
      (grid kh Q) c 0 dlt)
    (error_nonnegative : ∀ n k, 0 ≤ w n k)
    (error_summable : ∀ n, Summable (w n))
    (step_dist : ∀ n k,
      dist (grid kh Q n k) (grid kh Q n (k + 1)) ≤ w n k)
    (finite_tube : ∀ n k, IsTubeMember c 0 dlt (grid kh Q n k))
    (finite_range : ∀ n k,
      range (ev (grid kh Q (n + 1) k)) =
        range (UnitTangent.unitTangentMap
          (ev (SelectedInverseMap.selInv kh (grid kh Q (n + 1) k)))))
    (finite_harnack : ∀ n k a b, a ≤ b →
      Real.exp (a - b) *
          (arcCurv (grid kh Q n k) a /
            Real.sqrt (1 + arcCurv (grid kh Q n k) a ^ 2)) ≤
        arcCurv (grid kh Q n k) b /
          Real.sqrt (1 + arcCurv (grid kh Q n k) b ^ 2)) :
    Provider kh Q w c dlt where
  X := L.X
  error_nonnegative := error_nonnegative
  error_summable := error_summable
  step_dist := step_dist
  finite_tube := finite_tube
  limit_tube := L.limit_tube
  row_limit := L.row_limit
  finite_range := finite_range
  finite_harnack := finite_harnack

theorem Provider.row_cauchy
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (F : Provider kh Q w c dlt) (n : ℕ) : CauchySeq (grid kh Q n) :=
  cauchySeq_of_dist_le_of_summable (w n) (F.step_dist n)
    (F.error_summable n)

theorem Provider.shadow_dist
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (F : Provider kh Q w c dlt) (n : ℕ) :
    dist (Q n) (F.X n) ≤ ShadowingTails.tail (w n) 0 := by
  simpa [grid, ShadowingTails.tail] using
    dist_le_tsum_of_dist_le_of_tendsto (w n) (F.step_dist n)
      (F.error_summable n) (F.row_limit n) 0

theorem geometricUnitTangent_eq_normalized_of_tube
    {c dlt : ℝ} {p : Data}
    (hp : IsTubeMember c 0 dlt p) :
    geometricUnitTangent p = normalizedUnitTangent p := by
  funext u
  rw [geometricUnitTangent, normalizedUnitTangent,
    norm_vel_eq_perim hp u]

/-- The selected-inverse finite identity passes to the row limits. -/
theorem Provider.range_orbit
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (F : Provider kh Q w c dlt) (hc : 0 < c) (n : ℕ) :
    GeometricUnitTangentRangeEdge (F.X (n + 1)) (F.X n) := by
  have H := PullbackUnitTangentRangeOrbit.selectedInverse_orbitRange_of_finiteRange
    hc F.finite_tube F.limit_tube F.row_limit F.finite_range n
  rw [GeometricUnitTangentRangeEdge,
    ← MarkedSpace.range_ev hc (F.limit_tube (n + 1)),
    geometricUnitTangent_eq_normalized_of_tube (F.limit_tube n),
    ← MarkedSpace.range_unitTangentMap_ev_eq_normalized hc (F.limit_tube n)]
  exact H

def Provider.limitStrictness
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (F : Provider kh Q w c dlt) (hc : 0 < c) (n : ℕ) :
    UnconditionalAssembly.LimitStrictnessDataH (F.X n) :=
  UnconditionalAssembly.limitStrictnessDataH_of_limit' hc
    (F.limit_tube n) (F.row_limit n) (F.finite_harnack n)

def Provider.orientedRepresentative
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (F : Provider kh Q w c dlt) (hc : 0 < c) (hdlt : 0 < dlt)
    (n : ℕ) : OrientedArclengthRepresentative (F.X n) where
  q := F.X n
  c := c
  dlt := dlt
  c_pos := hc
  dlt_pos := hdlt
  tube := F.limit_tube n
  same_range := rfl
  strictness := F.limitStrictness hc n
  unitTangent_range := by
    rw [MarkedSpace.range_unitTangentMap_ev_eq_normalized hc (F.limit_tube n),
      ← geometricUnitTangent_eq_normalized_of_tube (F.limit_tube n)]
  physical_length :=
    VariableMarkedPhysicalLength.totalLength_eq_perim_of_tube (F.limit_tube n)

/-- Package the canonical pullback limits into the standard terminal output.
The dummy row coefficient is one, so its shadow radius is exactly the supplied
summable metric tail. -/
def Provider.toLimitOutput
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (F : Provider kh Q w c dlt) (hc : 0 < c) (hdlt : 0 < dlt) :
    TriangularMarkedPathSchemeVariableTerminal.LimitOutput
      Q (grid kh Q) w dummyP0 dummyZero dummyZero dummyZero dummyZero
        (fun n => perim (F.X n)) c dlt where
  X := F.X
  row_cauchy := F.row_cauchy
  row_limit := F.row_limit
  limit_tube := fun n => VariableMarkedTube.ofTubeMember (F.limit_tube n)
  shadow_dist := fun n => by simpa using F.shadow_dist n
  shadow_totalLength := fun n =>
    (VariableMarkedPhysicalLength.abs_totalLength_sub_le_dist
      (F.X n) (Q n)).trans (by
        simpa [dist_comm] using F.shadow_dist n)
  shadow_range := fun n => by
    rw [dummy_rowC, one_mul]
    apply CurveDistance.hausdorffDist_range_le
      (ShadowingTails.tail_nonneg (F.error_nonnegative n) 0)
    intro u
    exact (dist_apply_le (F.X n) (Q n) u).trans (by
      simpa [dist_comm] using F.shadow_dist n)
  range_orbit := fun n => F.range_orbit hc n
  geometric_oval := fun n =>
    isGeometricOval_of_arclengthHarnack
      (F.orientedRepresentative hc hdlt n).toArclengthHarnackCertificate

/-- Full paper-facing closing output from an abstract finite-column provider. -/
theorem Provider.exists_paperFacingOutput
    {kh : ℝ} {Q : ℕ → Data} {w : ℕ → ℕ → ℝ} {c dlt : ℝ}
    (F : Provider kh Q w c dlt) (hc : 0 < c) (hdlt : 0 < dlt)
    {direction : ℂ} (hdirection : ‖direction‖ = 1)
    {modelWidth H : ℝ}
    (hQbounded : Bornology.IsBounded (range (⇑(Q 0).1)))
    (hQwidth : Width.width (range (⇑(Q 0).1)) direction ≤ modelWidth)
    (hQlength : 2 * H ≤
      MarkedReparam.totalLength (fun u => (Q 0).2.1 u))
    (hgap : modelWidth + 2 *
        PaperFacingVariableTerminalOutput.shadowSize (F.toLimitOutput hc hdlt) <
      (2 * H - PaperFacingVariableTerminalOutput.shadowSize
        (F.toLimitOutput hc hdlt)) / Real.pi) :
    Nonempty (PaperFacingVariableTerminalOutput.Output
      (F.toLimitOutput hc hdlt) direction modelWidth H) := by
  exact ⟨PaperFacingVariableTerminalOutput.output_of_orientedRepresentatives
    (F.toLimitOutput hc hdlt) (F.orientedRepresentative hc hdlt)
    hdirection hQbounded hQwidth hQlength hgap⟩

/-- Direct metric error furnished by stable physical components followed by
the canonical endpoint cap. -/
def componentError
    (componentConst conversionConst : ℕ → ℝ)
    (defect cap : ℕ → ℕ → ℝ) (n k : ℕ) : ℝ :=
  conversionConst n * ((4 * componentConst n) * defect n k) + cap n k

/-- Stable finite-column physical components, a summable canonical endpoint
cap, and the retained geometric sidecars produce the abstract provider in one
step. -/
theorem exists_provider_of_stable_components
    {kh : ℝ} {Q : ℕ → Data} {g : ℕ → ℕ → Data}
    {Gamma : ∀ n k, NormalPath (grid kh Q n k) (g n k)}
    {period P0 P1 khat G1 Cg defect cap : ℕ → ℕ → ℝ}
    {componentConst conversionConst : ℕ → ℝ} {c dlt : ℝ}
    (hmem : ∀ n k, IsTubeMember c 0 dlt (grid kh Q n k))
    (hg : ∀ n k u, HasDerivAt (⇑(g n k).1) ((g n k).2.1 u) u)
    (hgv : ∀ n k u, HasDerivAt (⇑(g n k).2.1) ((g n k).2.2 u) u)
    (hgeom : ∀ n k,
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        (P0 n k) (P1 n k) (khat n k) (G1 n k) (Cg n k) (Gamma n k))
    (Hcomp : ∀ n k,
      FiniteColumnStablePhysicalComponentCompactness.StablePhysicalComponents
        (Gamma n k) (period n k) (componentConst n) (defect n k))
    (hcomponent : ∀ n, 0 ≤ componentConst n)
    (hconversionConst : ∀ n, 0 ≤ conversionConst n)
    (hdefect : ∀ n k, 0 ≤ defect n k)
    (hconversion : ∀ n k,
      NormalPathC2IncrementVariableSpeed.c2ConstVar
        (P0 n k) (P1 n k) (khat n k) (G1 n k) (Cg n k) ≤
          conversionConst n)
    (hcap : ∀ n k, dist (g n k) (grid kh Q n (k + 1)) ≤ cap n k)
    (hsumDefect : ∀ n, Summable (defect n))
    (hsumCap : ∀ n, Summable (cap n))
    (finite_range : ∀ n k,
      range (ev (grid kh Q (n + 1) k)) =
        range (UnitTangent.unitTangentMap
          (ev (SelectedInverseMap.selInv kh (grid kh Q (n + 1) k)))))
    (finite_harnack : ∀ n k a b, a ≤ b →
      Real.exp (a - b) *
          (arcCurv (grid kh Q n k) a /
            Real.sqrt (1 + arcCurv (grid kh Q n k) a ^ 2)) ≤
        arcCurv (grid kh Q n k) b /
          Real.sqrt (1 + arcCurv (grid kh Q n k) b ^ 2)) :
    Nonempty (Provider kh Q
      (componentError componentConst conversionConst defect cap) c dlt) := by
  obtain ⟨L⟩ :=
    FiniteColumnStablePhysicalComponentCompactness.exists_limitOutput
      (Gamma := Gamma) (period := period) (P0 := P0) (P1 := P1)
      (khat := khat) (G1 := G1) (Cg := Cg) (defect := defect)
      (cap := cap) (componentConst := componentConst)
      (conversionConst := conversionConst) hmem hg hgv hgeom Hcomp
      hcomponent hconversionConst hdefect hconversion hcap
      hsumDefect hsumCap
  have hcap0 : ∀ n k, 0 ≤ cap n k := fun n k =>
    dist_nonneg.trans (hcap n k)
  have herr0 : ∀ n k,
      0 ≤ componentError componentConst conversionConst defect cap n k := by
    intro n k
    exact add_nonneg
      (mul_nonneg (hconversionConst n)
        (mul_nonneg (mul_nonneg (by norm_num) (hcomponent n))
          (hdefect n k)))
      (hcap0 n k)
  have herrSum : ∀ n,
      Summable (componentError componentConst conversionConst defect cap n) := by
    intro n
    exact (((hsumDefect n).mul_left (4 * componentConst n)).mul_left
      (conversionConst n)).add (hsumCap n)
  have hstep : ∀ n k,
      dist (grid kh Q n k) (grid kh Q n (k + 1)) ≤
        componentError componentConst conversionConst defect cap n k := by
    intro n k
    exact FiniteColumnStablePhysicalComponentCompactness.canonical_increment_le
      (hmem n k).hasDerivAt_curve (hmem n k).hasDerivAt_vel
      (hg n k) (hgv n k) (hgeom n k) (Hcomp n k)
      (hcomponent n) (hdefect n k) (hconversionConst n)
      (hconversion n k) (hcap n k)
  exact ⟨Provider.ofCompactnessOutput L herr0 herrSum hstep hmem
    finite_range finite_harnack⟩

end FiniteColumnPullbackPaperCapstone
