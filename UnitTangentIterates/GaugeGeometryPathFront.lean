import Mathlib
import UnitTangentIterates.GaugeGeometryPathClosing
import UnitTangentIterates.SelectedPathData

/-!
# The normal path of selected rears, with the regularity of the rear velocity
supplied by the front

`GaugeGeometryPathClosing.pathDist_le_of_gauge_geometry_closing` asks, among its
hypotheses on the family of selected rears, that the rear normal velocity be of
class `C²` in the rear arclength (`hetaC2`).  That hypothesis is redundant:
`SelectedPathData.contDiff_two_of_jacobi_ode` shows that *any* solution of the
inverse Jacobi ODE is automatically `C²` as soon as the front curvature is
continuous and the front normal velocity is `C¹` — the two derivatives of `η_R`
come from the equation itself.

This file records the resulting statements, in which the only regularity
demanded is regularity of the **front** data.

Main results: `exists_normalPath_of_gauge_geometry_front` and
`pathDist_le_of_gauge_geometry_front`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse

namespace GaugeGeometryPathFront

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugeGeometryPathVariable GaugePathDistVariable GaugeGeometryPathClosing

/-- **The selected rears of a path of fronts, in the gauge parameter, with all
the regularity coming from the front.**

Same conclusion as
`GaugeGeometryPathClosing.exists_normalPath_of_gauge_geometry_closing`, with the
hypothesis that the rear normal velocity is `C²` replaced by continuity of the
front curvature. -/
theorem exists_normalPath_of_gauge_geometry_front {p q p' q' : Data} (Γ : NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {XR nuR : ℝ → ℝ → ℂ} {Y tauY : ℝ → ℝ → ℂ} {etaY : ℝ → ℝ → ℝ}
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hetaRper : ∀ t, Function.Periodic (etaR t) (Qf t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (Function.uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaY t x : ℂ) * (Complex.I * tauY t x)) t)
    (htau0 : ∀ t x, tauY t x ≠ 0)
    (htauper : ∀ t, Function.Periodic (tauY t) (Qf t))
    (hclose : ∀ t x, Y t (x + Qf t) = Y t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, etaR t = fun _ => 0) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      cost Δ = jacobiConst
        (gaugeCW (uarcW P1) D.rateLip Γ.T (Qf 0))
        (gaugeC0 (uarc0 P1 (Real.sqrt (1 - kh ^ 2) * P0)))
        (gaugeC1 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
          D.rateLip Γ.T (Qf 0))
        (gaugeC2 (uarc1 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)))
          (uarc2 P0 P1 (Real.sqrt (1 - kh ^ 2) * P0) (Real.sqrt (1 - kh ^ 2)) kh)
          D.rateLip D.rateBound2 Γ.T (Qf 0))
        * cost Γ :=
  exists_normalPath_of_gauge_geometry_closing Γ D hP0 hkh0 hkh1 hPl hPu hsteer hstrip0
    hstrip1 hdper hK hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd hetaRper
    (fun t => SelectedPathData.contDiff_two_of_jacobi_ode hkh0 hkh1 (hKc t) (hsteer t)
      (hstrip0 t) (hstrip1 t) (hetaFd t) (hetaFsc t) (hsfinv t) (hetaR t))
    hlink hv1 hY hYx hYt htau0 htauper hclose hPhid hPhi0 hstart hfinish hderiv hcont
    hnu hrest

/-- **The path pseudodistance of the selected rears, with all the regularity
coming from the front.** -/
theorem pathDist_le_of_gauge_geometry_front {p q p' q' : Data} (Γ : NormalPath p q)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {XR nuR : ℝ → ℝ → ℂ} {Y tauY : ℝ → ℝ → ℂ} {etaY : ℝ → ℝ → ℝ}
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hetaRper : ∀ t, Function.Periodic (etaR t) (Qf t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (Function.uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaY t x : ℂ) * (Complex.I * tauY t x)) t)
    (htau0 : ∀ t x, tauY t x ≠ 0)
    (htauper : ∀ t, Function.Periodic (tauY t) (Qf t))
    (hclose : ∀ t x, Y t (x + Qf t) = Y t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, etaR t = fun _ => 0) :
    pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T (Qf 0) * cost Γ :=
  pathDist_le_of_gauge_geometry_closing Γ D hP0 hkh0 hkh1 hPl hPu hsteer hstrip0
    hstrip1 hdper hK hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd hetaRper
    (fun t => SelectedPathData.contDiff_two_of_jacobi_ode hkh0 hkh1 (hKc t) (hsteer t)
      (hstrip0 t) (hstrip1 t) (hetaFd t) (hetaFsc t) (hsfinv t) (hetaR t))
    hlink hv1 hY hYx hYt htau0 htauper hclose hPhid hPhi0 hstart hfinish hderiv hcont
    hnu hrest

end GaugeGeometryPathFront
