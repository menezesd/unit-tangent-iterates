import Mathlib
import UnitTangentIterates.GaugeNormalPath
import UnitTangentIterates.JacobiArclengthUniform

/-!
# Assembling the gauge normal path from the arclength Jacobi estimates

Two pieces are now in place:

* `JacobiArclengthUniform.jacobi_estimates_arclength_uniform` turns the
  scalar hypotheses of the paper's lemma *Inverse Jacobi estimates* — at one
  time of the path, with the rear velocity in its own arclength — into the four
  estimates against the normalized front slice, with constants `uarcW`, `uarc0`,
  `uarc1`, `uarc2` that no longer mention the front period and hence are the
  same at every time.

* `GaugeNormalPath.exists_normalPath_of_gauge_jacobi` turns those four
  arclength estimates, holding at every time with fixed constants, into a
  `PathMetric.NormalPath` in the gauge parameter, of cost `jacobiConst` of the
  gauge-distorted constants times the cost of the front path.

This file composes them: from the per-time scalar estimates, the two-sided
bounds `P₀ ≤ P t ≤ P₁` on the front period and the link
`Γ.eta t u = η_F(t, P t · u)` between the normalized front slice and the front
velocity in arclength, one obtains the normal path of rears directly.

Main result: `exists_normalPath_of_arclength_jacobi`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath

namespace GaugeJacobiAssembly

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi

/-- **From the scalar inverse Jacobi estimates to a normal path of rears.**

`Γ` is a normal path of fronts whose slice at time `t` is the normalized reading
`Γ.eta t u = η_F(t, P t · u)` of the front velocity `η_F(t, ·)` in the front
arclength, the front period `P t` lying between `P₀` and `P₁`.  `XR` is a family
of curves moving with the normal velocity `η_R(t, Φ(t,u)) ν`, `Φ` the gauge flow
of the closed family described by `D`, at rest outside the time interval.  If at
every time of the interval the rear velocity obeys the four scalar estimates of
the paper's lemma *Inverse Jacobi estimates* against the front velocity in
arclength, then `XR` is a normal path whose cost is a fixed constant — the
gauge distortion of the uniform arclength constants — times the cost of `Γ`. -/
theorem exists_normalPath_of_arclength_jacobi {p q p' q' : Data} (Γ : NormalPath p q)
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q)
    (hxiper : ∀ a, Function.Periodic (D.xi a) Q) (hvper : ∀ a, Function.Periodic (D.v a) Q)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q * u)
    {XR nuR : ℝ → ℝ → ℂ} {etaR etaR1 etaR2 etaF : ℝ → ℝ → ℝ}
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hetaper : ∀ t, Function.Periodic (etaR t) Q)
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
      (∫ x in (0:ℝ)..Q, |etaR t x|) ≤ ∫ s in (0:ℝ)..P t, |etaF t s|)
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
        (gaugeCW (uarcW P1) D.rateLip Γ.T Q)
        (gaugeC0 (uarc0 P1 l0))
        (gaugeC1 (uarc1 P1 l0 c) D.rateLip Γ.T Q)
        (gaugeC2 (uarc1 P1 l0 c) (uarc2 P0 P1 l0 c kh) D.rateLip D.rateBound2 Γ.T Q)
        * cost Γ := by
  -- the four uniform estimates, at every time of the interval
  have key : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      (∫ x in (0:ℝ)..Q, |etaR t x|) ≤ uarcW P1 * ∫ u in (0:ℝ)..1, |Γ.eta t u|
        ∧ supNorm (etaR t) ≤ uarc0 P1 l0 * ∫ u in (0:ℝ)..1, |Γ.eta t u|
        ∧ supNorm (deriv (etaR t)) ≤ uarc1 P1 l0 c * ((∫ u in (0:ℝ)..1, |Γ.eta t u|)
            + supNorm (Γ.eta t))
        ∧ supNorm (deriv (deriv (etaR t))) ≤ uarc2 P0 P1 l0 c kh
            * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)
              + supNorm (iteratedDeriv 1 (Γ.eta t))) := by
    intro t ht
    exact jacobi_estimates_arclength_uniform (l := Q) (kh := kh) hP0 (hPl t) (hPu t) hl0 hc
      (hR1 t) (hR2 t) (hSF0nn t) (hWa t ht) (hS0a t ht) (hS1a t ht) (hS2a t ht)
      (hn0 t ht) (hn1 t ht) (fun u => hlink t u)
  exact exists_normalPath_of_gauge_jacobi Γ D hQ hxiper hvper hPhid hPhi0 hetaC2 hetaper
    hstart hfinish hderiv hcont hnu hrest
    (uarcW_nonneg hP1) (uarc0_nonneg hP1 hl0) (uarc1_nonneg hP1 hl0 hc)
    (uarc2_nonneg hP0 hP1 hl0 hc)
    (fun t ht => (key t ht).1) (fun t ht => (key t ht).2.1)
    (fun t ht => (key t ht).2.2.1) (fun t ht => (key t ht).2.2.2)

/-- **The hypotheses are consistent.**  The constant path of any marked curve —
front period one throughout, front velocity zero — with the trivial frame data
and a rear family at rest satisfies all of them. -/
example (p p' : Data) :
    ∃ Δ : NormalPath p' p', Δ.T = (NormalPath.const p).T ∧
      cost Δ = jacobiConst
        (gaugeCW (uarcW 1) trivialFrame.rateLip (NormalPath.const p).T 1)
        (gaugeC0 (uarc0 1 1))
        (gaugeC1 (uarc1 1 1 1) trivialFrame.rateLip (NormalPath.const p).T 1)
        (gaugeC2 (uarc1 1 1 1) (uarc2 1 1 1 1 0) trivialFrame.rateLip
          trivialFrame.rateBound2 (NormalPath.const p).T 1)
        * cost (NormalPath.const p) := by
  have hrate : GaugeRate.gaugeRate trivialFrame.xi trivialFrame.v = fun _ _ => (0:ℝ) := by
    funext t x
    simp [GaugeRate.gaugeRate, trivialFrame]
  refine exists_normalPath_of_arclength_jacobi (Γ := NormalPath.const p) (D := trivialFrame)
    (Phi := fun _ u => 1 * u) (Q := 1) one_pos (fun _ _ => rfl) (fun _ _ => rfl)
    ?_ (fun _ => rfl) (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    (etaR := fun _ _ => 0) (etaR1 := fun _ _ => 0) (etaR2 := fun _ _ => 0)
    (etaF := fun _ _ => 0) (P := fun _ => 1) (SF0 := fun _ => 0) (SF1 := fun _ => 0)
    (fun _ => contDiff_const) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ?_ ?_ (fun _ _ => by simp) (fun _ _ => rfl)
    one_pos one_pos one_pos one_pos (fun _ => le_rfl) (fun _ => le_rfl) (fun _ _ => rfl)
    (fun _ x => hasDerivAt_const x 0) (fun _ x => hasDerivAt_const x 0) (fun _ => le_rfl)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro u t
    rw [hrate]
    simpa using hasDerivAt_const t (1 * u)
  · intro t u
    simpa using hasDerivAt_const t (p'.1 u)
  · intro u
    simpa using continuous_const
  · intro t _; simp
  · intro t _ x; simp
  · intro t _ x; simp
  · intro t _ x; simp
  · intro t _; simpa using supNorm_nonneg ((NormalPath.const p).eta t)
  · intro t _
    simpa using supNorm_nonneg (iteratedDeriv 1 ((NormalPath.const p).eta t))

end GaugeJacobiAssembly
