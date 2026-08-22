import Mathlib
import UnitTangentIterates.RearOwnPathDistFrameBounds
import UnitTangentIterates.RearOwnPathDistDefectC2

/-!
# The path pseudodistance with explicit constants, together with the `C²`
defect of its gauge marking

`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds` prescribes the
two gauge constants `rL`, `rB` and builds the gauge frame bundle from them.
This file adds to that conclusion, for the same marking `Φ`, everything the
`C²` comparison of the two marked selected inverses needs: `Φ` fixes the base
point, it reads exactly one rear period, it deviates from the affine marking of
the terminal period by at most `2 L_max κ · cost Γ`, and the terminal slice read
in it is at marked distance at most `markingC2Bound …` from that slice itself.

The extra input is a *time-dependent* bound `C t` for the arclength derivative
of the tangential component, continuous and at most `κ` times the cost density
of the path — the uniform bound `rL` is what the gauge constants of the
pseudodistance need, the slice-wise bound `C t` is what the defect needs — the
same for the second arclength derivative with `C₂ t ≤ κ₂·m t`, an upper bound
`L_max` for the rear period, the vanishing of the base drift of the front, which
is what makes the gauge fix the base point, and a member of the tube tracing the
terminal slice.

Main result: `pathDist_and_distC2_le_of_front_frame_bounds`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistFrameBoundsDefectC2

open UniformFrameBounds GaugePathDistVariable RearOwnPathDist RearOwnFrameDrift
  MarkingDeviationC2 MarkingFlowDefectC2 RearOwnHigherRegularity

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

/-- **The second arclength derivative of the tangential component of a bundle
built on it.**  The companion of `xi1_eq_partialX` one derivative up. -/
theorem xi2_eq_partialX {xi : ℝ → ℝ → ℝ} (D : GaugeFrameData)
    (hxiC : ContDiff ℝ 2 (uncurry xi)) (hxiD : ∀ a x, D.xi a x = xi a x) (a x : ℝ) :
    D.xi2 a x = partialX (partialX xi) a x := by
  have hxiC1 : ContDiff ℝ 1 (uncurry xi) := hxiC.of_le (by exact_mod_cast (by norm_num :
    (1 : ℕ) ≤ 2))
  have hpxC : ContDiff ℝ 1 (uncurry (partialX xi)) :=
    contDiff_partialX (n := 1) (by exact_mod_cast hxiC)
  have h1 : HasDerivAt (D.xi1 a) (D.xi2 a x) x := D.hxi1 a x
  have hfun : D.xi1 a = partialX xi a :=
    funext fun y => xi1_eq_partialX D hxiC1 hxiD a y
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_partialX hpxC a x)

/-- **The path pseudodistance of the selected rears with the two gauge constants
prescribed, together with the `C²` defect of the gauge marking in which it is
read.**

The hypotheses are those of
`RearOwnPathDistFrameBounds.pathDist_le_of_front_frame_bounds`, with the base
drift of the front assumed to vanish and with a continuous, time-dependent
bound `C t ≤ κ·m t` for the arclength derivative of the tangential component
and an upper bound `L_max` for the rear period.  The marking then fixes the
base point, reads exactly one rear period and deviates from the affine marking
of the terminal period by at most `2 L_max κ · cost Γ`. -/
theorem pathDist_and_distC2_le_of_front_frame_bounds {p q : Data} (Γ : NormalPath p q)
    (p' b : Data) {P0 P1 kh rL rB : ℝ} {P Qf' : ℝ → ℝ}
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
    {C C2 : ℝ → ℝ} {Lmax kappa kappa2 : ℝ}
    (hsliceC : ∀ t x, |partialX (frameTangential Ydot (rearOwnAngle Θ δ sf)) t x| ≤ C t)
    (hCcont : Continuous C)
    (hQmax : ∀ t, rearArclength (δ t) (P t) ≤ Lmax)
    (hcost : ∀ t, C t ≤ kappa * Γ.m t)
    (hsliceC2 : ∀ t x,
      |partialX (partialX (frameTangential Ydot (rearOwnAngle Θ δ sf))) t x| ≤ C2 t)
    (hC2cont : Continuous C2) (hcost2 : ∀ t, C2 t ≤ kappa2 * Γ.m t)
    -- the terminal curve, a member of the tube tracing the terminal slice
    {cq kminq dltq kb kL : ℝ} {Θb kb' : ℝ → ℝ}
    (hcq : 0 < cq) (hb : IsTubeMember cq kminq dltq b)
    (hperimb : perim b = rearArclength (δ Γ.T) (P Γ.T))
    (hevb : ∀ x, ev b x = rearOwn F Θ δ sf Γ.T x)
    (hevd : ∀ s, HasDerivAt (ev b) (Complex.exp (Complex.I * (Θb s : ℂ))) s)
    (hΘb : ∀ s, HasDerivAt Θb (kb' s) s) (hkbd : ∀ s, |kb' s| ≤ kb)
    (hklip : ∀ s t, |kb' s - kb' t| ≤ kL * |s - t|) :
    ∃ Phi : ℝ → ℝ → ℝ,
      (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
      (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
      (∀ u t, HasDerivAt (fun r => Phi r u)
        (-frameTangential (partialTime (rearOwn F Θ δ sf)) (rearOwnAngle Θ δ sf) t
          (Phi t u)) t) ∧
      (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
        ≤ 2 * Lmax * kappa * cost Γ) ∧
      (∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
        (∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u) → (∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) →
        dist q' b ≤ markingC2Bound (2 * Lmax * kappa * cost Γ)
          (flowDefectC1Int (rearArclength (δ 0) (P 0)) (kappa * cost Γ))
          (flowDefectC2Int (rearArclength (δ 0) (P 0)) (kappa * cost Γ) (kappa2 * cost Γ))
          (rearArclength (δ Γ.T) (P Γ.T)) kb kL) ∧
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
  have hxiC2 : ContDiff ℝ 2 (uncurry (frameTangential Ydot (rearOwnAngle Θ δ sf))) :=
    RearOwnFrameData.contDiff_frameTangential
      (hYdotC.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)))
      (hangC.of_le (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)))
  have hxi2bd : ∀ t x, |D.xi2 t x| ≤ C2 t := by
    intro t x
    rw [xi2_eq_partialX D hxiC2 hxiD t x]
    exact hsliceC2 t x
  have h := RearOwnPathDistDefectC2.pathDist_and_distC2_le_of_front_smoothDependence Γ p' b
    (Fdot := Fdot) (Fdots := Fdots) (Ydot := Ydot) (Qf' := Qf')
    (Θdot := Θdot) (w := w) (Θdots := Θdots) (ws := ws) (dt := dt) (sft := sft)
    (K := K) (etaF := etaF) (etaFs := etaFs) (C := C) (Lmax := Lmax) (kappa := kappa)
    (C2 := C2) (kappa2 := kappa2)
    D hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hK hKc hFper hΘper
    hFC hΘC hδC hδt hdtc hetaFdef hetaFd hetaFsc hetaFper hlink hsfinv hsft
    hFa hΘa hδa hFdots hΘdots hws hFc2 hΘc2 hδc2 hYdot hv1 hxiD hrest hQd hstart
    hdrift hxi1bd hCcont hQmax hcost hxi2bd hC2cont hcost2 hcq hb hperimb hevb hevd hΘb
    hkbd hklip
  rw [hDL, hDB] at h
  exact h

end RearOwnPathDistFrameBoundsDefectC2
