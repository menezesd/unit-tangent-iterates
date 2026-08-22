import Mathlib
import UnitTangentIterates.GaugeNormalPathVariable
import UnitTangentIterates.JacobiArclengthUniform

/-!
# The gauge normal path from the arclength Jacobi estimates, with a changing period

This is `GaugeJacobiAssembly.exists_normalPath_of_arclength_jacobi` for a family
whose slices change length: the arclength period of the rear slice at time `t`
is a differentiable function `Qf t` rather than a constant, the `L¹` estimate is
taken over one period of the current slice, and the distortion constants of the
gauge flow are those of the reference length `Qf 0`.

The two ingredients are unchanged:

* `JacobiArclengthUniform.jacobi_estimates_arclength_uniform` turns the scalar
  hypotheses of the paper's lemma *Inverse Jacobi estimates* at one time — with
  the rear velocity in the arclength of its own slice, of period `Qf t` — into
  the four estimates against the normalized front slice, with constants that no
  longer mention the front period;

* `GaugeNormalPathVariable.exists_normalPath_of_gauge_jacobi_var` turns those
  four estimates, holding at every time with fixed constants, into a
  `PathMetric.NormalPath` in the gauge parameter.

Main result: `exists_normalPath_of_arclength_jacobi_var`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath

namespace GaugeJacobiAssemblyVariable

open UniformFrameBounds GaugeNormalPath GaugeNormalPathVariable JacobiArclengthUniform
  PathMetricJacobi

/-- **From the scalar inverse Jacobi estimates to a normal path of rears, for a
family whose slices change length.**

Same as `GaugeJacobiAssembly.exists_normalPath_of_arclength_jacobi`, with the
constant rear period replaced by the differentiable function `Qf`: the frame
data of the rear family obeys the closing relations of a family of period
`Qf t`, the rear velocity at time `t` is `Qf t`-periodic, and its `L¹` density
is taken over one period of the slice at time `t`. -/
theorem exists_normalPath_of_arclength_jacobi_var {p q p' q' : Data} (Γ : NormalPath p q)
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hQpos : ∀ t, 0 < Qf t) (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hvper : ∀ t, Function.Periodic (D.v t) (Qf t))
    (hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    {XR nuR : ℝ → ℝ → ℂ} {etaR etaR1 etaR2 etaF : ℝ → ℝ → ℝ}
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hetaper : ∀ t, Function.Periodic (etaR t) (Qf t))
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, etaR t = fun _ => 0)
    -- the geometry of the front and of the rear
    {P : ℝ → ℝ} {P0 P1 l0 c kh : ℝ} {SF0 SF1 : ℝ → ℝ}
    (hP0 : 0 < P0) (hP1 : 0 < P1) (hl0 : 0 < l0) (hc : 0 < c)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hR1 : ∀ t x, HasDerivAt (etaR t) (etaR1 t x) x)
    (hR2 : ∀ t x, HasDerivAt (etaR1 t) (etaR2 t x) x)
    (hSF0nn : ∀ t, 0 ≤ SF0 t)
    -- the four scalar estimates, in arclength, at every time of the interval
    (hWa : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      (∫ x in (0:ℝ)..(Qf t), |etaR t x|) ≤ ∫ s in (0:ℝ)..P t, |etaF t s|)
    (hS0a : ∀ t ∈ Ioo (0:ℝ) Γ.T, ∀ x,
      |etaR t x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|)
    (hS1a : ∀ t ∈ Ioo (0:ℝ) Γ.T, ∀ x,
      |etaR1 t x| ≤ SF0 t / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|)
    (hS2a : ∀ t ∈ Ioo (0:ℝ) Γ.T, ∀ x,
      |etaR2 t x| ≤ SF1 t / c ^ 2 + 2 * kh ^ 2 * SF0 t / c ^ 3
        + (SF0 t / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|))
    (hn0 : ∀ t ∈ Ioo (0:ℝ) Γ.T, SF0 t ≤ supNorm (Γ.eta t))
    (hn1 : ∀ t ∈ Ioo (0:ℝ) Γ.T, P t * SF1 t ≤ supNorm (iteratedDeriv 1 (Γ.eta t))) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      cost Δ = jacobiConst
        (gaugeCW (uarcW P1) D.rateLip Γ.T (Qf 0))
        (gaugeC0 (uarc0 P1 l0))
        (gaugeC1 (uarc1 P1 l0 c) D.rateLip Γ.T (Qf 0))
        (gaugeC2 (uarc1 P1 l0 c) (uarc2 P0 P1 l0 c kh) D.rateLip D.rateBound2 Γ.T (Qf 0))
        * cost Γ := by
  -- the four uniform estimates, at every time of the interval
  have key : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      (∫ x in (0:ℝ)..(Qf t), |etaR t x|) ≤ uarcW P1 * ∫ u in (0:ℝ)..1, |Γ.eta t u|
        ∧ supNorm (etaR t) ≤ uarc0 P1 l0 * ∫ u in (0:ℝ)..1, |Γ.eta t u|
        ∧ supNorm (deriv (etaR t)) ≤ uarc1 P1 l0 c * ((∫ u in (0:ℝ)..1, |Γ.eta t u|)
            + supNorm (Γ.eta t))
        ∧ supNorm (deriv (deriv (etaR t))) ≤ uarc2 P0 P1 l0 c kh
            * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)
              + supNorm (iteratedDeriv 1 (Γ.eta t))) := by
    intro t ht
    exact jacobi_estimates_arclength_uniform (l := Qf t) (kh := kh) hP0 (hPl t) (hPu t) hl0 hc
      (hR1 t) (hR2 t) (hSF0nn t) (hWa t ht) (hS0a t ht) (hS1a t ht) (hS2a t ht)
      (hn0 t ht) (hn1 t ht) (fun u => hlink t u)
  exact exists_normalPath_of_gauge_jacobi_var Γ D hQpos hQd hvper hxiqp hPhid hPhi0
    hetaC2 hetaper hstart hfinish hderiv hcont hnu hrest
    (uarcW_nonneg hP1) (uarc0_nonneg hP1 hl0) (uarc1_nonneg hP1 hl0 hc)
    (uarc2_nonneg hP0 hP1 hl0 hc)
    (fun t ht => (key t ht).1) (fun t ht => (key t ht).2.1)
    (fun t ht => (key t ht).2.2.1) (fun t ht => (key t ht).2.2.2)

end GaugeJacobiAssemblyVariable
