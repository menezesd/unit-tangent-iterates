import Mathlib
import UnitTangentIterates.GaugeGeometryPathVariable
import UnitTangentIterates.PathMetricRescale

/-!
# The path pseudodistance bound in the gauge parameter, for slices of changing length

`GaugeGeometryPathVariable.exists_normalPath_of_gauge_geometry_var` produces,
from the geometry of the slices and *without* assuming that the rear arclength
period is the same at every time, a normal path of selected rears whose cost is
the gauge distortion of the uniform arclength constants times the cost of the
front path.

This file turns that statement about costs into a statement about the path
pseudodistance of `PathMetric`, the way
`SelectedInversePathGeometry.pathDist_le_of_geometry` does for the chain in the
arclength parameter:

* `pathDist_le_of_gauge_geometry_var` — the *single path* bound: the selected
  rears of one normal path of fronts are at path pseudodistance at most the
  gauge constant times the cost of that path.  (The gauge constants depend on
  the duration of the path through the distortion `exp(L T)` of the gauge flow,
  so this is the sharpest form available for a single path.)
* `pathDist_le_of_gauge_costs_var` — the Lipschitz bound for a map of marked
  curves, when the gauge constants are held fixed: if every normal path from
  `p` to `q` is taken to a normal path of cost at most
  `jacobiConst (gaugeCW …) (gaugeC0 …) (gaugeC1 …) (gaugeC2 …)` times as large,
  the map is Lipschitz for `pathDist` with that constant.

The nonnegativity of the four distorted constants (`gaugeCW_nonneg`, …) is
established first; it is what both statements need.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse

namespace GaugePathDistVariable

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugeGeometryPathVariable

/-! ### Nonnegativity of the distorted constants -/

variable {CW C0 C1 C2 L R2 T Q : ℝ}

theorem gaugeCW_nonneg (hCW : 0 ≤ CW) (hQ : 0 < Q) : 0 ≤ gaugeCW CW L T Q := by
  unfold gaugeCW
  have : (0:ℝ) < Real.exp (L * T) := Real.exp_pos _
  positivity

theorem gaugeC0_nonneg (hC0 : 0 ≤ C0) : 0 ≤ gaugeC0 C0 := hC0

theorem gaugeC1_nonneg (hC1 : 0 ≤ C1) (hQ : 0 ≤ Q) : 0 ≤ gaugeC1 C1 L T Q := by
  unfold gaugeC1
  have : (0:ℝ) < Real.exp (L * T) := Real.exp_pos _
  positivity

theorem gaugeC2_nonneg (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hR2 : 0 ≤ R2) (hT : 0 ≤ T) :
    0 ≤ gaugeC2 C1 C2 L R2 T Q := by
  unfold gaugeC2
  have h1 : (0:ℝ) < Real.exp (L * T) := Real.exp_pos _
  have h2 : (0:ℝ) < Real.exp (2 * L * T) := Real.exp_pos _
  have hsq : (0:ℝ) ≤ (Q * Real.exp (L * T)) ^ 2 := sq_nonneg _
  have ha : 0 ≤ C2 * (Q * Real.exp (L * T)) ^ 2 := mul_nonneg hC2 hsq
  have hb : 0 ≤ C1 * (R2 * Q ^ 2 * T * Real.exp (2 * L * T)) := by positivity
  linarith

/-! ### The bound for a single path -/

/-- **The path pseudodistance of the selected rears of one normal path of
fronts**, for a family of slices whose length changes.

Under exactly the hypotheses of
`GaugeGeometryPathVariable.exists_normalPath_of_gauge_geometry_var` — in
particular with the rear arclength period `Qf` allowed to vary in the time, and
only assumed differentiable — the two ends `p'`, `q'` of the family of selected
rears are at path pseudodistance at most the gauge distortion, computed with the
reference period `Qf 0`, of the uniform arclength constants times the cost of
the given path of fronts. -/
theorem pathDist_le_of_gauge_geometry_var {p q p' q' : Data} (Γ : NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {XR nuR : ℝ → ℝ → ℂ}
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hetaRper : ∀ t, Function.Periodic (etaR t) (Qf t))
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hvper : ∀ t, Function.Periodic (D.v t) (Qf t))
    (hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, etaR t = fun _ => 0) :
    pathDist p' q' ≤
      jacobiConst
        (gaugeCW (uarcW P1) D.rateLip Γ.T (Qf 0))
        (gaugeC0 (uarc0 P1 (Real.sqrt (1 - kh ^ 2) * P0)))
        (gaugeC1 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
          D.rateLip Γ.T (Qf 0))
        (gaugeC2 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
          (uarc2 P0 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)) kh)
          D.rateLip D.rateBound2 Γ.T (Qf 0))
        * cost Γ := by
  obtain ⟨Δ, -, hcost⟩ := exists_normalPath_of_gauge_geometry_var Γ D hP0 hkh0 hkh1 hPl hPu
    hsteer hstrip0 hstrip1 hdper hK hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd
    hetaRper hetaC2 hlink hvper hxiqp hPhid hPhi0 hstart hfinish hderiv hcont hnu hrest
  calc pathDist p' q' ≤ cost Δ := pathDist_le_cost Δ
    _ = _ := hcost

/-! ### The Lipschitz bound for a map of marked curves -/

/-- **The Lipschitz bound for the path pseudodistance in the gauge parameter.**

If a map `F` of marked curves takes every normal path from `p` to `q` to a
normal path from `F p` to `F q` of cost at most the gauge constant times as
large — as `exists_normalPath_of_gauge_geometry_var` provides, for slices of
changing length, once the gauge distortion is bounded uniformly over the paths
considered — then `F` is Lipschitz for the path pseudodistance with that
constant. -/
theorem pathDist_le_of_gauge_costs_var {F : Data → Data} {p q : Data} {P0 P1 kh : ℝ}
    {L R2 T Q : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQ : 0 < Q) (hR2 : 0 ≤ R2) (hT : 0 ≤ T)
    (h : ∀ Γ : NormalPath p q, ∃ Δ : NormalPath (F p) (F q),
      cost Δ ≤ jacobiConst (gaugeCW (uarcW P1) L T Q)
        (gaugeC0 (uarc0 P1 (Real.sqrt (1 - kh ^ 2) * P0)))
        (gaugeC1 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2))) L T Q)
        (gaugeC2 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
          (uarc2 P0 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)) kh) L R2 T Q)
        * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤
      jacobiConst (gaugeCW (uarcW P1) L T Q)
        (gaugeC0 (uarc0 P1 (Real.sqrt (1 - kh ^ 2) * P0)))
        (gaugeC1 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2))) L T Q)
        (gaugeC2 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
          (uarc2 P0 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)) kh) L R2 T Q)
        * pathDist p q := by
  have hkh2 : (0:ℝ) < 1 - kh ^ 2 := by nlinarith
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr hkh2
  have hl0 : 0 < Real.sqrt (1 - kh ^ 2) * P0 := by positivity
  exact pathDist_le_of_jacobi
    (gaugeCW_nonneg (uarcW_nonneg hP1) hQ)
    (gaugeC0_nonneg (uarc0_nonneg hP1 hl0))
    (gaugeC1_nonneg (uarc1_nonneg hP1 hl0 hcpos) hQ.le)
    (gaugeC2_nonneg (uarc1_nonneg hP1 hl0 hcpos) (uarc2_nonneg hP0 hP1 hl0 hcpos) hR2 hT)
    h hne

/-! ### The Lipschitz bound tested on the paths of duration one -/

/-- The gauge constant of the whole chain: the `jacobiConst` of the four
distorted uniform arclength constants. -/
def gaugeJacobiConst (P0 P1 kh L R2 T Q : ℝ) : ℝ :=
  jacobiConst (gaugeCW (uarcW P1) L T Q)
    (gaugeC0 (uarc0 P1 (Real.sqrt (1 - kh ^ 2) * P0)))
    (gaugeC1 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2))) L T Q)
    (gaugeC2 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
      (uarc2 P0 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)) kh) L R2 T Q)

theorem gaugeJacobiConst_nonneg {P0 P1 kh L R2 T Q : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hQ : 0 < Q) (hR2 : 0 ≤ R2) (hT : 0 ≤ T) :
    0 ≤ gaugeJacobiConst P0 P1 kh L R2 T Q := by
  have hkh2 : (0:ℝ) < 1 - kh ^ 2 := by nlinarith
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr hkh2
  have hl0 : 0 < Real.sqrt (1 - kh ^ 2) * P0 := by positivity
  exact jacobiConst_nonneg
    (gaugeCW_nonneg (uarcW_nonneg hP1) hQ)
    (gaugeC0_nonneg (uarc0_nonneg hP1 hl0))
    (gaugeC1_nonneg (uarc1_nonneg hP1 hl0 hcpos) hQ.le)
    (gaugeC2_nonneg (uarc1_nonneg hP1 hl0 hcpos) (uarc2_nonneg hP0 hP1 hl0 hcpos) hR2 hT)

/-- **The uniform Lipschitz bound in the gauge parameter, for slices of changing
length.**

The gauge constants grow with the duration of the path, through the distortion
`exp(L T)` of the gauge flow, so a bound valid for *every* normal path from `p`
to `q` cannot be read off directly from
`pathDist_le_of_gauge_geometry_var`.  It does not have to be: by
`PathMetric.NormalPath.cost_rescale` the cost of a normal path is unchanged when
the time is rescaled, so the path pseudodistance is already the infimum over the
paths of duration one (`PathMetric.pathDist_eq_sInf_unitTime`).  It is therefore
enough to control the image of the paths with `Γ.T = 1`, and the constant is the
gauge constant at `T = 1` — exactly the constant that
`pathDist_le_of_gauge_geometry_var` produces for such a path. -/
theorem pathDist_le_of_gauge_unitTime_var {F : Data → Data} {p q : Data} {P0 P1 kh : ℝ}
    {L R2 Q : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hQ : 0 < Q) (hR2 : 0 ≤ R2)
    (h : ∀ Γ : NormalPath p q, Γ.T = 1 → ∃ Δ : NormalPath (F p) (F q),
      cost Δ ≤ gaugeJacobiConst P0 P1 kh L R2 1 Q * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ gaugeJacobiConst P0 P1 kh L R2 1 Q * pathDist p q :=
  pathDist_le_mul_of_maps_unitTime_paths
    (gaugeJacobiConst_nonneg hP0 hP1 hkh0 hkh1 hQ hR2 zero_le_one) h hne

end GaugePathDistVariable
