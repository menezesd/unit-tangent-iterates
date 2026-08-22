import Mathlib
import UnitTangentIterates.RearOwnPathDistFrameBounds
import UnitTangentIterates.RearOwnPathDistDefect

/-!
# The path pseudodistance with explicit constants, together with the defect of
its gauge marking

`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds` prescribes the
two gauge constants `rL`, `rB` and builds the gauge frame bundle from them.
This file adds to that conclusion, for the same marking `Φ`, the three facts
the comparison of the two marked selected inverses needs: `Φ` fixes the base
point, it reads exactly one rear period, and it deviates from the affine
marking of the terminal period by at most `2 L_max κ · cost Γ`.

The extra input is a *time-dependent* bound `C t` for the arclength derivative
of the tangential component, continuous and at most `κ` times the cost density
of the path — the uniform bound `rL` is what the gauge constants of the
pseudodistance need, the slice-wise bound `C t` is what the defect needs — an
upper bound `L_max` for the rear period, and the vanishing of the base drift of
the front, which is what makes the gauge fix the base point.

Main result: `pathDist_and_defect_le_of_front_frame_bounds`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistFrameBoundsDefect

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameDrift

/-- **The first arclength derivative of the tangential component of a bundle
built on it.**  If the tangential component of a `C¹` bundle is a given `C¹`
function of the pair, then the bundle's recorded arclength derivative is the
partial derivative of that function. -/
theorem xi1_eq_partialX {xi : ℝ → ℝ → ℝ} (D : GaugeFrameData)
    (hxiC : ContDiff ℝ 1 (uncurry xi)) (hxiD : ∀ a x, D.xi a x = xi a x) (a x : ℝ) :
    D.xi1 a x = partialX xi a x := by
  have h1 : HasDerivAt (D.xi a) (D.xi1 a x) x := D.hxi a x
  have hfun : D.xi a = xi a := funext fun y => hxiD a y
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_partialX hxiC a x)

/-- **The path pseudodistance of the selected rears with the two gauge constants
prescribed, together with the defect of the gauge marking in which it is read.**

The hypotheses are those of
`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds`, with the base
drift of the front assumed to vanish and with a continuous, time-dependent
bound `C t ≤ κ·m t` for the arclength derivative of the tangential component
and an upper bound `L_max` for the rear period.  The marking then fixes the
base point, reads exactly one rear period and deviates from the affine marking
of the terminal period by at most `2 L_max κ · cost Γ`. -/
theorem pathDist_and_defect_le_of_front_frame_bounds {p q : Data} (Γ : NormalPath p q)
    (p' : Data) {P0 P1 kh rL rB : ℝ} {P Qf' : ℝ → ℝ}
    {F Fdot Fdots Ydot : ℝ → ℝ → ℂ}
    {Θ δ K etaF etaFs sf sft dt Θdot w Θdots ws : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh) (hKc : ∀ t, Continuous (K t))
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFC : ContDiff ℝ 1 (uncurry F)) (hΘC : ContDiff ℝ 1 (uncurry Θ))
    (hδC : ContDiff ℝ 1 (uncurry δ))
    (hδt : ∀ t s, HasDerivAt (fun r => δ r s) (dt t s) t)
    (hdtc : Continuous (uncurry dt))
    (hetaFdef : ∀ t s, etaF t s = frontNormalVelocityAt Fdot Θ δ t s)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t))
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hsft : ∀ t x, HasDerivAt (fun r => sf r x) (sft t x) t)
    (hFa : ∀ t s, HasDerivAt (fun r => F r s) (Fdot t s) t)
    (hΘa : ∀ t s, HasDerivAt (fun r => Θ r s) (Θdot t s) t)
    (hδa : ∀ t s, HasDerivAt (fun r => δ r s) (w t s) t)
    (hFdots : ∀ t s, HasDerivAt (Fdot t) (Fdots t s) s)
    (hΘdots : ∀ t s, HasDerivAt (Θdot t) (Θdots t s) s)
    (hws : ∀ t s, HasDerivAt (w t) (ws t s) s)
    (hFc2 : ContDiff ℝ (2 : ℕ) (uncurry F)) (hΘc2 : ContDiff ℝ (2 : ℕ) (uncurry Θ))
    (hδc2 : ContDiff ℝ (2 : ℕ) (uncurry δ))
    (hYdot : ∀ t x, Ydot t x = trackVelocity Fdot Θdot w Θ δ t (sf t x) + (sft t x) •
      ((Real.cos (δ t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) (sf t x) : ℂ))))
    (hQd : ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t)
    (hYdotC : ContDiff ℝ (3 : ℕ) (uncurry Ydot))
    (hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Θ δ sf)))
    (hrL : ∀ t x, |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x| ≤ rL)
    (hrB : ∀ t x,
      |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x| ≤ rB)
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T,
      (fun x => frameNormal Ydot (rearOwnAngle Θ δ sf) t x) = fun _ => 0)
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    -- the gauge normalization and the slice-wise growth of the tangential component
    (hdrift : ∀ t, RearBaseDrift.frontBaseDrift Fdot Θ δ t = 0)
    {C : ℝ → ℝ} {Lmax kappa : ℝ}
    (hsliceC : ∀ t x, |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x| ≤ C t)
    (hCcont : Continuous C)
    (hQmax : ∀ t, rearArclength (δ t) (P t) ≤ Lmax)
    (hcost : ∀ t, C t ≤ kappa * Γ.m t) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * Lmax * kappa * cost Γ) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh rL rB Γ.T
          (rearArclength (δ 0) (P 0)) * cost Γ := by
  obtain ⟨D, hv1, hxiD, hDL, hDB⟩ :=
    exists_gaugeFrameData_frameTangential_of_bounds hYdotC hangC hrL hrB
  -- the bundle's recorded arclength derivative is the partial derivative
  have hxiC1 : ContDiff ℝ 1 (uncurry (frameTangential Ydot (rearOwnAngle Θ δ sf))) :=
    RearOwnFrameData.contDiff_frameTangential
      (hYdotC.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)))
      (hangC.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)))
  have hxi1bd : ∀ t x, |D.xi1 t x| ≤ C t := by
    intro t x
    rw [xi1_eq_partialX D hxiC1 hxiD t x]
    exact hsliceC t x
  have h := RearOwnPathDistDefect.pathDist_and_defect_le_of_front_smoothDependence Γ p'
    (Fdot := Fdot) (Fdots := Fdots) (Ydot := Ydot) (Qf' := Qf')
    (Θdot := Θdot) (w := w) (Θdots := Θdots) (ws := ws) (dt := dt) (sft := sft)
    (K := K) (etaF := etaF) (etaFs := etaFs) (C := C) (Lmax := Lmax) (kappa := kappa)
    D hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hv1 hxiD hrest hQd hstart
    hdrift hxi1bd hCcont hQmax hcost
  rw [hDL, hDB] at h
  exact h

end RearOwnPathDistFrameBoundsDefect
