import Mathlib
import UnitTangentIterates.GaugePathRearFamily
import UnitTangentIterates.GaugeMarkingDefectFrame

/-!
# The path-distance bound and the defect of its gauge marking, together

`GaugePathRearFamily.pathDist_le_of_rear_family` produces the gauge marking `Φ`
of a family of rear tracks written in its own arclength and bounds the path
pseudodistance from the initial slice to the terminal slice *read in that
marking*.  What the marking is worth as a parametrization is not part of its
conclusion, and that is the one thing the comparison of the two marked selected
inverses needs (`SelInvMarkingDefect.lean`, `SelInvMarkingDefectCost.lean`).

This file states the two together, for the same `Φ`.  The extra hypotheses are
the gauge normalization `ξ(t, 0) = 0` — which already appears in
`pathDist_le_of_rear_family` as the condition for the marking to fix the base
point — a bound `C t` for the arclength derivative of the tangential component
with `C t ≤ κ·m t`, and an upper bound `L_max` for the rear period.  Everything
else is read off the family: the closing relation of `GaugeClosingRelations`
makes the tangential component quasi-periodic, so the marking translates by the
current period and `Φ_t(1) = Q t`, and `GaugeMarkingDefectFrame.lean` then
bounds the defect by `2 L_max κ · cost Γ`.

Main result: `pathDist_and_defect_le_of_rear_family`.
-/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric PathMetric.NormalPath
  RearTrack ArclengthInverse

namespace GaugePathRearFamilyDefect

open UniformFrameBounds GaugeNormalPath JacobiArclengthUniform PathMetricJacobi
  GaugeGeometryPathVariable GaugePathDistVariable GaugeGeometryPathFront GaugePathRearFamily

/-- **The path pseudodistance of the selected rears, together with the defect of
the gauge marking in which it is read.**

Under the hypotheses of `GaugePathRearFamily.pathDist_le_of_rear_family`, with
the tangential component vanishing at the base point, its arclength derivative
bounded by `C t ≤ κ·m t` and the rear period bounded by `L_max`, the gauge
marking `Φ` fixes the base point, reads exactly one period (`Φ_t(1) = Q t`),
deviates from the affine marking of the terminal period by at most
`2 L_max κ · cost Γ`, and the path pseudodistance from the initial slice to the
terminal slice read in `Φ` is at most `gaugeJacobiConst … · cost Γ`. -/
theorem pathDist_and_defect_le_of_rear_family {p q : Data} (Γ : NormalPath p q) (p' : Data)
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
    -- the gauge normalization and the growth of the tangential component
    (hxi0 : ∀ t, D.xi t 0 = 0) {C : ℝ → ℝ} {Lmax kappa : ℝ}
    (hxi1bd : ∀ t x, |D.xi1 t x| ≤ C t) (hCcont : Continuous C)
    (hQmax : ∀ t, Qf t ≤ Lmax) (hcost : ∀ t, C t ≤ kappa * Γ.m t) :
    ∃ Phi : ℝ → ℝ → ℝ, (∀ u, Phi 0 u = Qf 0 * u) ∧ (∀ t, Phi t 0 = 0) ∧
      (∀ t, Phi t 1 = Qf t) ∧
      (∀ u, |Phi Γ.T u - Qf Γ.T * u| ≤ 2 * Lmax * kappa * cost Γ) ∧
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
  -- the base point is fixed
  have hbase : ∀ t, Phi t 0 = 0 :=
    GaugeBaseFlow.gaugeFlow_base_fixed D (fun r => hPhid 0 r) (by simp [hPhi0 0]) hxi0
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
  -- so the marking reads exactly one period, and its defect is bounded by the cost
  have hone : ∀ t, Phi t 1 = Qf t :=
    fun t => GaugeMarkingDefectFrame.flow_one_eq_period D hQd hvper hxiqp hPhid hPhi0 hbase t
  have hdefect : ∀ u, |Phi Γ.T u - Qf Γ.T * u| ≤ 2 * Lmax * kappa * cost Γ := fun u =>
    GaugeMarkingDefectFrame.gauge_marking_defect_le_cost Γ D hQd hvper hxiqp hPhid hPhi0 hQ0
      hxi0 hxi1bd hCcont one_pos (fun t x => by rw [hv1 t x]; norm_num) hQmax
      (fun t => by simpa using hcost t) u
  refine ⟨Phi, fun u => hPhi0 u, hbase, hone, hdefect, ?_⟩
  intro q' hq'
  exact pathDist_le_of_gauge_geometry_front (etaY := etaR) (sf := sf) (etaFs := etaFs)
    (K := K) (XR := XR) (nuR := nuR) (Qf' := Qf') Γ D hP0 hkh0 hkh1 hPl hPu hsteer hstrip0
    hstrip1 hdper hK hKc hetaFd hetaFsc hetaFper hsfinv hetaR hQdef hQd hetaRper hlink hv1
    hY hYx hYt htau0 htauper hclose hPhid hPhi0
    (fun u => by simp only [hXRdef]; rw [hPhi0 u, hstart u])
    (fun u => by simp only [hXRdef]; rw [hq' u]) hderiv hcont hnu hrest

end GaugePathRearFamilyDefect
