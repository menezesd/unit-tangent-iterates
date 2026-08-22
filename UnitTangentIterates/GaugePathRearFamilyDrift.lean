import Mathlib
import UnitTangentIterates.GaugePathRearFamilyDefect
import UnitTangentIterates.GaugeBaseDrift

/-!
# The path-distance bound and the defect of its gauge marking, with a drifting base point

`GaugePathRearFamilyDefect.pathDist_and_defect_le_of_rear_family` states the
path pseudodistance bound of `GaugePathRearFamily.pathDist_le_of_rear_family`
together with the defect of the gauge marking in which the distance is read.
Both are stated there under the *gauge normalization* `ξ(t, 0) = 0`: the
tangential component of the motion of the family of selected rears vanishes at
the base point, so that the gauge flow fixes the base point.

`RearBaseDrift.lean` traces that hypothesis back to the marked point of the path
of fronts being at rest, and `PinchedPathRigidity.lean` shows that a path of
constant speed whose marked point is at rest is stationary.  So the normalized
statement, although true, applies only to stationary paths.

This file removes the normalization.  What replaces it is a *two-sided window
estimate* for the tangential component,

```
  |x| ≤ L_max  →  |ξ(t, x)| ≤ Cx t ≤ rr · m t ,
```

which `RearBaseDriftBound.abs_frameTangential_le_cost_on_window_free` supplies
with no hypothesis on the marked point.  The bootstrap
`GaugeBaseDrift.abs_gaugeFlow_base_le_window` then shows that, as long as the
whole budget `rr · cost Γ` is smaller than the window, the base point of the
gauge flow never leaves the window and

```
  |Φ(t, 0)| ≤ rr · ∫₀^t m ≤ rr · cost Γ .
```

The marking therefore reads one period *up to that drift*,
`Φ_t(1) = Φ_t(0) + Q t`, and its defect at the final time is at most
`2 L_max κ · cost Γ + rr · cost Γ` — the extra term being, like the main term,
of first order in the cost, so that the Lipschitz character of the estimate is
untouched.

Main result: `pathDist_and_defect_le_of_rear_family_drift`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse

namespace GaugePathRearFamilyDrift

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugeGeometryPathVariable GaugePathDistVariable GaugeGeometryPathFront GaugePathRearFamily

/-- **The cost accumulated up to an intermediate time is at most the whole
cost.** -/
theorem integral_m_le_cost {p q : Data} (Γ : NormalPath p q) {t : ℝ}
    (htT : t ≤ Γ.T) : (∫ r in (0:ℝ)..t, Γ.m r) ≤ cost Γ := by
  have hsplit : cost Γ = (∫ r in (0:ℝ)..t, Γ.m r) + ∫ r in t..Γ.T, Γ.m r :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Γ.cont_m.intervalIntegrable 0 t) (Γ.cont_m.intervalIntegrable t Γ.T)).symm
  have hnn : 0 ≤ ∫ r in t..Γ.T, Γ.m r :=
    intervalIntegral.integral_nonneg htT fun r _ => Γ.m_nonneg r
  rw [hsplit]
  linarith

/-- **The path pseudodistance of the selected rears, together with the defect of
the gauge marking in which it is read, with no hypothesis on the marked point.**

This is `GaugePathRearFamilyDefect.pathDist_and_defect_le_of_rear_family` with
the gauge normalization `ξ(t, 0) = 0` deleted.  In its place, the tangential
component is bounded on the window `|x| ≤ L_max` by `Cx t ≤ rr·m t`, and the
budget `rr · cost Γ` is required to be smaller than the window — a smallness
condition on the cost of the path, not a restriction on the family.

The conclusion is correspondingly weakened: the gauge marking no longer fixes
the base point, but its base point drifts by at most `rr · cost Γ`; it no longer
reads exactly one period, but reads one period from wherever its base point
currently is; and the defect at the final time acquires the extra first-order
term `rr · cost Γ`. -/
theorem pathDist_and_defect_le_of_rear_family_drift {p q : Data} (Γ : NormalPath p q)
    (p' : Data)
    {P0 P1 kh : ℝ} {P : ℝ → ℝ} {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    {Y tauY : ℝ → ℝ → ℂ}
    (D : GaugeFrameData) {Qf Qf' : ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    -- the steering equation on the selected strip
    (hsteer : ∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    -- the front normal velocity
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    -- the change of variable and the inverse Jacobi ODE
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, etaR t = fun _ => 0)
    -- the rear period
    (hQdef : ∀ t, Qf t = rearArclength (delta t) (P t))
    (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    -- the family of rear tracks, in its own arclength
    (hv1 : ∀ t x, D.v t x = 1)
    (hY : ContDiff ℝ (1 : ℕ) (uncurry Y))
    (hYx : ∀ t x, HasDerivAt (Y t) (tauY t x) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x)
      ((D.xi t x : ℂ) * tauY t x + (etaR t x : ℂ) * (Complex.I * tauY t x)) t)
    (htaunorm : ∀ t x, ‖tauY t x‖ = 1)
    (hclose : ∀ t x, Y t (x + Qf t) = Y t x)
    (hstart : ∀ u, p'.1 u = Y 0 (Qf 0 * u))
    -- the window estimate for the tangential component
    {Cx : ℝ → ℝ} {Lmax kappa rr : ℝ}
    (hxiW : ∀ t x, |x| ≤ Lmax → |D.xi t x| ≤ Cx t) (hCxcont : Continuous Cx)
    (hxiR : ∀ t, Cx t ≤ rr * Γ.m t) (hrr : 0 ≤ rr)
    (hLmax0 : 0 < Lmax) (hsmall : rr * cost Γ < Lmax)
    (hQmax : ∀ t, Qf t + rr * cost Γ ≤ Lmax)
    (hcost : ∀ t, Cx t / Lmax ≤ kappa * Γ.m t) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Qf 0 * u) ∧
      (∀ t ∈ Icc (0:ℝ) Γ.T, |Phi t 0| ≤ rr * cost Γ) ∧
      (∀ t, Phi t 1 = Phi t 0 + Qf t) ∧
      (∀ u, |Phi Γ.T u - Qf Γ.T * u| ≤ 2 * Lmax * kappa * cost Γ + rr * cost Γ) ∧
      ∀ q' : Data, (∀ u, q'.1 u = Y Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤
          gaugeJacobiConst P0 P1 kh D.rateLip D.rateBound2 Γ.T (Qf 0) * cost Γ := by
  -- the tangent never vanishes
  have htau0 : ∀ t x, tauY t x ≠ 0 := by
    intro t x h
    have hn := htaunorm t x
    rw [h] at hn
    simp at hn
  -- the tangent is periodic with the rear period, by differentiating the closing relation
  have htauper : ∀ t, Function.Periodic (tauY t) (Qf t) := by
    intro t x
    have hshift : HasDerivAt (fun y => Y t (y + Qf t)) (tauY t (x + Qf t)) x :=
      HasDerivAt.comp_add_const x (Qf t) (hYx t (x + Qf t))
    have hfun : (fun y => Y t (y + Qf t)) = Y t := funext fun y => hclose t y
    rw [hfun] at hshift
    exact hshift.unique (hYx t x)
  -- the normal velocity is periodic with the rear period, by the closing relations
  have hetaRper : ∀ t, Function.Periodic (etaR t) (Qf t) := fun t x =>
    (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose hQd t x).2
  -- the rear period at time zero is positive
  have hQ0 : 0 < Qf 0 := by
    rw [hQdef 0]
    exact SelectedPathData.rearPeriod_pos (lt_of_lt_of_le hP0 (hPl 0)) hkh0 hkh1
      (SelectedPathData.continuous_of_steering (hsteer 0)) (hstrip0 0) (hstrip1 0)
  -- the gauge flow
  obtain ⟨Phi, hPhi0, hPhid⟩ := exists_gaugeFlow_of_frameData D hQ0
  have hPhic : ∀ u, Continuous fun t => Phi t u := by
    intro u
    have hd : Differentiable ℝ fun t => Phi t u := fun t => (hPhid u t).differentiableAt
    exact hd.continuous
  -- the moving marked curve and its unit normal
  set XR : ℝ → ℝ → ℂ := fun t u => Y t (Phi t u) with hXRdef
  set nuR : ℝ → ℝ → ℂ := fun t u => Complex.I * tauY t (Phi t u) with hnuRdef
  have hnu : ∀ t u, ‖nuR t u‖ = 1 := by
    intro t u
    rw [hnuRdef]
    simp [htaunorm]
  -- the velocity of the moving marked curve is normal
  have hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (Phi t u) : ℂ) * nuR t u) t := by
    intro t u
    have h := hasDerivAt_along_curve (Y := Y) (tauY := tauY)
      (Yt := fun t x => (D.xi t x : ℂ) * tauY t x + (etaR t x : ℂ) * (Complex.I * tauY t x))
      hY hYx hYt (hPhid u t)
    refine h.congr_deriv ?_
    rw [hnuRdef, GaugeRate.gaugeRate, hv1]
    simp only [div_one, Complex.real_smul, Complex.ofReal_neg]
    ring
  -- and it depends continuously on the time
  have hetaRc : Continuous (uncurry etaR) :=
    continuous_normal_component hY hYx hYt htau0
  have htauc : Continuous (uncurry tauY) := continuous_partial_space hY hYx
  have hcont : ∀ u, Continuous fun t => (etaR t (Phi t u) : ℂ) * nuR t u := by
    intro u
    have h1 : Continuous fun t => etaR t (Phi t u) :=
      hetaRc.comp (continuous_id.prodMk (hPhic u))
    have h2 : Continuous fun t => tauY t (Phi t u) :=
      htauc.comp (continuous_id.prodMk (hPhic u))
    rw [hnuRdef]
    exact (Complex.continuous_ofReal.comp h1).mul (continuous_const.mul h2)
  -- the tangential component is quasi-periodic, by the closing relation
  have hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x := by
    intro t x
    have h := (GaugeClosingRelations.closing_relations hY hYx hYt htau0 htauper hclose hQd
      t x).1
    rw [hv1 t x, mul_one]
    exact h
  have hvper : ∀ t, Function.Periodic (D.v t) (Qf t) := by
    intro t x
    rw [hv1 t (x + Qf t), hv1 t x]
  -- the base point of the gauge flow never leaves the window, and drifts at most the cost
  have hxiWm : ∀ t x, |x| ≤ Lmax → |D.xi t x| ≤ rr * Γ.m t := fun t x hx =>
    le_trans (hxiW t x hx) (hxiR t)
  have hsmall' : rr * (∫ r in (0:ℝ)..Γ.T, Γ.m r) < Lmax := by
    rwa [show (∫ r in (0:ℝ)..Γ.T, Γ.m r) = cost Γ from rfl]
  have hbasew : ∀ t ∈ Icc (0:ℝ) Γ.T, |Phi t 0| ≤ rr * ∫ r in (0:ℝ)..t, Γ.m r :=
    fun t ht => GaugeBaseDrift.abs_gaugeFlow_base_le_window D (fun r => hPhid 0 r)
      (by simp [hPhi0 0]) hv1 Γ.cont_m Γ.m_nonneg hrr hLmax0 hxiWm hsmall' ht.1 ht.2
  have hbase : ∀ t ∈ Icc (0:ℝ) Γ.T, |Phi t 0| ≤ rr * cost Γ := fun t ht =>
    le_trans (hbasew t ht) (mul_le_mul_of_nonneg_left (integral_m_le_cost Γ ht.2) hrr)
  have hbaseL : ∀ t ∈ Icc (0:ℝ) Γ.T, |Phi t 0| ≤ Lmax := fun t ht =>
    le_trans (hbase t ht) hsmall.le
  -- the marking reads one period from wherever its base point currently is
  have hone : ∀ t, Phi t 1 = Phi t 0 + Qf t := fun t =>
    GaugeMarkingDefectFrame.flow_one_eq_period_drift D hQd hvper hxiqp hPhid hPhi0 t
  have honeL : ∀ t ∈ Icc (0:ℝ) Γ.T, Phi t 1 ≤ Lmax := by
    intro t ht
    rw [hone t]
    have h1 : Phi t 0 ≤ rr * cost Γ := le_trans (le_abs_self _) (hbase t ht)
    have h2 := hQmax t
    linarith
  -- the defect at the final time, with the extra drift term
  have hdefect : ∀ u, |Phi Γ.T u - Qf Γ.T * u|
      ≤ 2 * Lmax * kappa * cost Γ + rr * cost Γ := fun u =>
    GaugeMarkingDefectFrame.gauge_marking_defect_le_cost_drift Γ D hQd hvper hxiqp hPhid
      hPhi0 hQ0 hbaseL (hbase Γ.T ⟨Γ.T_pos.le, le_rfl⟩) hxiW hCxcont one_pos
      (fun t x => by rw [hv1 t x]; norm_num) hLmax0 honeL
      (fun t => by simpa using hcost t) u
  refine ⟨Phi, fun u => hPhi0 u, hbase, hone, hdefect, ?_⟩
  intro q' hq'
  exact pathDist_le_of_gauge_geometry_front (etaY := etaR) (sf := sf) (etaFs := etaFs)
    (K := K) (XR := XR) (nuR := nuR) (Qf' := Qf') Γ D hP0 hkh0 hkh1 hPl hPu hsteer hstrip0
    hstrip1 hdper hK hKc hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd hetaRper hlink hv1
    hY hYx hYt htau0 htauper hclose hPhid hPhi0
    (fun u => by simp only [hXRdef]; rw [hPhi0 u, hstart u])
    (fun u => by simp only [hXRdef]; rw [hq' u]) hderiv hcont hnu hrest

end GaugePathRearFamilyDrift
