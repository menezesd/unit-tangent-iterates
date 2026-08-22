import Mathlib
import UnitTangentIterates.GaugeJacobiAssembly
import UnitTangentIterates.ArclengthReparamEstimates

/-!
# The gauge normal path for a family whose slices change length

`GaugeJacobiAssembly.exists_normalPath_of_arclength_jacobi` reads the rear
normal velocity in a single coordinate of period `Q`, and consumes the four
inverse Jacobi estimates in that same coordinate.  What the geometry supplies is
the estimates in the **arclength of each slice**, and those two readings agree
only when every slice has the same length.

This file removes that restriction.  Writing `φ_t` for the arclength of the
slice at time `t` as a function of the material coordinate — so that
`φ_t(0) = 0`, `φ_t(Q) = L t` is the length of the slice, and
`m ≤ φ_t' ≤ M`, `|φ_t''| ≤ N` uniformly in `t` — the estimates transport by
`ArclengthReparamEstimates.estimates_reparam`, and the four constants pick up
the factors `1/m`, `1`, `M`, `M² (+ N on the first-order constant)` before the
gauge distortion of `GaugeNormalPath.lean` is applied.

Main result: `exists_normalPath_of_reparam_jacobi`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath

namespace GaugeReparamAssembly

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform ArclengthReparamEstimates
  PathMetricJacobi

/-- **The normal path of rears of a family whose slices change length.**

The rear normal velocity is `η_A(t, ·)` in the arclength of the slice at time
`t`, and it is read in the material coordinate through the change of parameter
`φ_t`, whose derivative lies between `m > 0` and `M` and whose second derivative
is bounded by `N`, uniformly in `t`.  Given the four scalar inverse Jacobi
estimates in the slice arclength at every time, two-sided bounds on the front
period, and the gauge flow of the rear family, the rears form a normal path
whose cost is a fixed constant times the cost of the front path. -/
theorem exists_normalPath_of_reparam_jacobi {p q p' q' : Data} (Γ : NormalPath p q)
    (D : GaugeFrameData) {Phi : ℝ → ℝ → ℝ} {Q : ℝ} (hQ : 0 < Q)
    (hxiper : ∀ a, Function.Periodic (D.xi a) Q) (hvper : ∀ a, Function.Periodic (D.v a) Q)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Q * u)
    {XR nuR : ℝ → ℝ → ℂ} {etaA etaA1 etaA2 phi phi1 phi2 etaF : ℝ → ℝ → ℝ} {L : ℝ → ℝ}
    {m M N : ℝ} (hm : 0 < m)
    -- the rear velocity in the arclength of its slice
    (hA1 : ∀ t x, HasDerivAt (etaA t) (etaA1 t x) x)
    (hA2 : ∀ t x, HasDerivAt (etaA1 t) (etaA2 t x) x)
    (hbdd : ∀ t, BddAbove (Set.range fun x => |etaA t x|))
    (hbdd1 : ∀ t, BddAbove (Set.range fun x => |etaA1 t x|))
    (hbdd2 : ∀ t, BddAbove (Set.range fun x => |etaA2 t x|))
    -- the change of parameter to the material coordinate
    (hphi1 : ∀ t u, HasDerivAt (phi t) (phi1 t u) u)
    (hphi2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u)
    (hphi1c : ∀ t, Continuous (phi1 t))
    (hlow : ∀ t u, m ≤ phi1 t u) (hM : ∀ t u, |phi1 t u| ≤ M) (hN : ∀ t u, |phi2 t u| ≤ N)
    (hphi0 : ∀ t, phi t 0 = 0) (hphiQ : ∀ t, phi t Q = L t)
    -- the structural data of the rear family, in the material coordinate
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) fun x => etaA t (phi t x))
    (hetaper : ∀ t, Function.Periodic (fun x => etaA t (phi t x)) Q)
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u)
      ((etaA t (phi t (Phi t u)) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaA t (phi t (Phi t u)) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hrest : ∀ t ∉ Ioo (0:ℝ) Γ.T, (fun x => etaA t (phi t x)) = fun _ => 0)
    -- the geometry of the front
    {P : ℝ → ℝ} {P0 P1 l0 c kh : ℝ} {SF0 SF1 : ℝ → ℝ}
    (hP0 : 0 < P0) (hP1 : 0 < P1) (hl0 : 0 < l0) (hc : 0 < c)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hSF0nn : ∀ t, 0 ≤ SF0 t)
    -- the four scalar estimates, in the arclength of each slice
    (hWa : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      (∫ x in (0:ℝ)..L t, |etaA t x|) ≤ ∫ s in (0:ℝ)..P t, |etaF t s|)
    (hS0a : ∀ t ∈ Ioo (0:ℝ) Γ.T, ∀ x,
      |etaA t x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|)
    (hS1a : ∀ t ∈ Ioo (0:ℝ) Γ.T, ∀ x,
      |etaA1 t x| ≤ SF0 t / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|)
    (hS2a : ∀ t ∈ Ioo (0:ℝ) Γ.T, ∀ x,
      |etaA2 t x| ≤ SF1 t / c ^ 2 + 2 * kh ^ 2 * SF0 t / c ^ 3
        + (SF0 t / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P t, |etaF t s|))
    (hn0 : ∀ t ∈ Ioo (0:ℝ) Γ.T, SF0 t ≤ supNorm (Γ.eta t))
    (hn1 : ∀ t ∈ Ioo (0:ℝ) Γ.T, P t * SF1 t ≤ supNorm (iteratedDeriv 1 (Γ.eta t))) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      cost Δ = jacobiConst
        (gaugeCW (reparamCW (uarcW P1) m) D.rateLip Γ.T Q)
        (gaugeC0 (reparamC0 (uarc0 P1 l0)))
        (gaugeC1 (reparamC1 (uarc1 P1 l0 c) M) D.rateLip Γ.T Q)
        (gaugeC2 (reparamC1 (uarc1 P1 l0 c) M)
          (reparamC2 (uarc1 P1 l0 c) (uarc2 P0 P1 l0 c kh) M N)
          D.rateLip D.rateBound2 Γ.T Q)
        * cost Γ := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 0)
  have hN0 : 0 ≤ N := le_trans (abs_nonneg _) (hN 0 0)
  have hu1 : 0 ≤ uarc1 P1 l0 c := uarc1_nonneg hP1 hl0 hc
  have hu2 : 0 ≤ uarc2 P0 P1 l0 c kh := uarc2_nonneg hP0 hP1 hl0 hc
  -- the transported estimates, at every time of the interval
  have key : ∀ t ∈ Ioo (0:ℝ) Γ.T,
      (∫ x in (0:ℝ)..Q, |etaA t (phi t x)|)
          ≤ reparamCW (uarcW P1) m * ∫ u in (0:ℝ)..1, |Γ.eta t u|
        ∧ supNorm (fun x => etaA t (phi t x))
            ≤ reparamC0 (uarc0 P1 l0) * ∫ u in (0:ℝ)..1, |Γ.eta t u|
        ∧ supNorm (deriv fun x => etaA t (phi t x))
            ≤ reparamC1 (uarc1 P1 l0 c) M
              * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t))
        ∧ supNorm (deriv (deriv fun x => etaA t (phi t x)))
            ≤ reparamC2 (uarc1 P1 l0 c) (uarc2 P0 P1 l0 c kh) M N
              * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + supNorm (Γ.eta t)
                + supNorm (iteratedDeriv 1 (Γ.eta t))) := by
    intro t ht
    obtain ⟨e1, e2, e3, e4⟩ :=
      jacobi_estimates_arclength_uniform (l := L t) (kh := kh) (etaN := Γ.eta t)
        hP0 (hPl t) (hPu t) hl0 hc (hA1 t) (hA2 t) (hSF0nn t) (hWa t ht) (hS0a t ht)
        (hS1a t ht) (hS2a t ht) (hn0 t ht) (hn1 t ht) (hlink t)
    exact estimates_reparam (Q := Q) (L := L t) hm hQ.le (hA1 t) (hA2 t)
      (hbdd t) (hbdd1 t) (hbdd2 t) (hphi1 t) (hphi2 t) (hphi1c t)
      (hlow t) (hM t) (hN t) (hphi0 t) (hphiQ t) (supNorm_nonneg _) hu1 e1 e2 e3 e4
  -- feed them into the gauge normal path
  exact exists_normalPath_of_gauge_jacobi Γ D hQ hxiper hvper hPhid hPhi0
    (etaR := fun t x => etaA t (phi t x))
    hetaC2 hetaper hstart hfinish hderiv hcont hnu hrest
    (by
      have : 0 ≤ uarcW P1 := uarcW_nonneg hP1
      unfold reparamCW; positivity)
    (uarc0_nonneg hP1 hl0)
    (by unfold reparamC1; positivity)
    (by unfold reparamC2; positivity)
    (fun t ht => (key t ht).1) (fun t ht => (key t ht).2.1)
    (fun t ht => (key t ht).2.2.1) (fun t ht => (key t ht).2.2.2)

/-- **The hypotheses are consistent.**  The constant path of any marked curve,
the identity change of parameter, the trivial frame data and a rear family at
rest satisfy all of them. -/
example (p p' : Data) :
    ∃ Δ : NormalPath p' p', Δ.T = (NormalPath.const p).T ∧
      cost Δ = jacobiConst
        (gaugeCW (reparamCW (uarcW 1) 1) trivialFrame.rateLip (NormalPath.const p).T 1)
        (gaugeC0 (reparamC0 (uarc0 1 1)))
        (gaugeC1 (reparamC1 (uarc1 1 1 1) 1) trivialFrame.rateLip
          (NormalPath.const p).T 1)
        (gaugeC2 (reparamC1 (uarc1 1 1 1) 1)
          (reparamC2 (uarc1 1 1 1) (uarc2 1 1 1 1 0) 1 0)
          trivialFrame.rateLip trivialFrame.rateBound2 (NormalPath.const p).T 1)
        * cost (NormalPath.const p) := by
  have hzbdd : BddAbove (Set.range fun _ : ℝ => |(0:ℝ)|) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    simp
  have hrate : GaugeRate.gaugeRate trivialFrame.xi trivialFrame.v = fun _ _ => (0:ℝ) := by
    funext t x
    simp [GaugeRate.gaugeRate, trivialFrame]
  refine exists_normalPath_of_reparam_jacobi (Γ := NormalPath.const p) (D := trivialFrame)
    (Phi := fun _ u => 1 * u) (Q := 1) one_pos (fun _ _ => rfl) (fun _ _ => rfl)
    ?_ (fun _ => rfl) (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    (etaA := fun _ _ => 0) (etaA1 := fun _ _ => 0) (etaA2 := fun _ _ => 0)
    (phi := fun _ x => x) (phi1 := fun _ _ => 1) (phi2 := fun _ _ => 0)
    (etaF := fun _ _ => 0) (L := fun _ => 1) (m := 1) (M := 1) (N := 0)
    (P := fun _ => 1) (SF0 := fun _ => 0) (SF1 := fun _ => 0)
    one_pos (fun _ x => hasDerivAt_const x 0) (fun _ x => hasDerivAt_const x 0)
    (fun _ => hzbdd) (fun _ => hzbdd) (fun _ => hzbdd)
    (fun _ u => hasDerivAt_id u) (fun _ u => hasDerivAt_const u 1) (fun _ => continuous_const)
    (fun _ _ => le_rfl) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ => rfl) (fun _ => rfl)
    (fun _ => contDiff_const) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    ?_ ?_ (fun _ _ => by simp) (fun _ _ => rfl)
    one_pos one_pos one_pos one_pos (fun _ => le_rfl) (fun _ => le_rfl) (fun _ _ => rfl)
    (fun _ => le_rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro u t
    rw [hrate]
    exact hasDerivAt_const t (1 * u)
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

end GaugeReparamAssembly
