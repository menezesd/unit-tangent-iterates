import Mathlib
import UnitTangentIterates.InterpolationSelectedRearRegularity
import UnitTangentIterates.RearOwnMotion
import UnitTangentIterates.RearOwnHigherRegularity
import UnitTangentIterates.MixedPartials
import UnitTangentIterates.RearOwnIsFront

/-!
# Qualitative gauge and Jacobi data of a smooth selected-rear family

This module removes the auxiliary velocity functions from the qualitative
part of the variable-speed front-to-rear interface.  All of them are chosen as
canonical partial derivatives of the given smooth family.  The only hypotheses
left to later shadowing assemblies are closing conditions and quantitative
bounds.
-/

noncomputable section

open Function Set Complex

namespace SelectedRearGaugeQualitative

open RearTrack RearOwnArclength RearOwnMotion RearOwnHigherRegularity
  RearFamilyFrame

variable {F : ℝ → ℝ → ℂ} {Theta delta K sf : ℝ → ℝ → ℝ} {kh : ℝ}

/-- **Canonical velocity, frame regularity, and inverse Jacobi equation.**

For a jointly `C³` front and tangent angle and jointly `C⁴` selected steering
family and inverse rear-arclength map, the velocity of the rear family is
canonically its time partial derivative.  It is jointly `C²`; the rear tangent
angle is jointly `C²`; the rear curvature `tan(delta ∘ sf)` is jointly `C¹`; and the normal
component of the velocity satisfies the inverse Jacobi ODE with transported
front-normal source.
-/
theorem exists_canonical_gauge_jacobi_data
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hF3 : ContDiff ℝ (3 : ℕ) (uncurry F))
    (hTheta3 : ContDiff ℝ (3 : ℕ) (uncurry Theta))
    (hdelta4 : ContDiff ℝ (4 : ℕ) (uncurry delta))
    (hsf4 : ContDiff ℝ (4 : ℕ) (uncurry sf))
    (hfront : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Theta t s : ℂ))) s)
    (hTheta : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x) :
    ∃ Ydot : ℝ → ℝ → ℂ,
      (∀ t x, HasDerivAt (fun r => rearOwn F Theta delta sf r x) (Ydot t x) t) ∧
      ContDiff ℝ (2 : ℕ) (uncurry Ydot) ∧
      ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Theta delta sf)) ∧
      ContDiff ℝ (1 : ℕ)
        (uncurry fun t x => Real.tan (delta t (sf t x))) ∧
      (∀ t x, HasDerivAt
        (fun x' => frameNormal Ydot (rearOwnAngle Theta delta sf) t x')
        (frontNormalVelocityAt (partialTime F) Theta delta t (sf t x)
            / Real.cos (delta t (sf t x))
          - frameNormal Ydot (rearOwnAngle Theta delta sf) t x) x) := by
  let Fdot : ℝ → ℝ → ℂ := partialTime F
  let Thetadot : ℝ → ℝ → ℝ := partialTime Theta
  let w : ℝ → ℝ → ℝ := partialTime delta
  let sft : ℝ → ℝ → ℝ := partialTime sf
  let Ydot : ℝ → ℝ → ℂ := fun t x =>
    trackVelocity Fdot Thetadot w Theta delta t (sf t x)
      + (sft t x) • ((Real.cos (delta t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Theta t) (delta t) (sf t x) : ℂ)))
  have hFdiff : Differentiable ℝ (uncurry F) := hF3.differentiable (by norm_num)
  have hThetadiff : Differentiable ℝ (uncurry Theta) :=
    hTheta3.differentiable (by norm_num)
  have hdeltadiff : Differentiable ℝ (uncurry delta) :=
    hdelta4.differentiable (by norm_num)
  have hsfdiff : Differentiable ℝ (uncurry sf) := hsf4.differentiable (by norm_num)
  have hFdot2 : ContDiff ℝ (2 : ℕ) (uncurry Fdot) := by
    exact contDiff_partialTime_self hF3
  have hThetadot2 : ContDiff ℝ (2 : ℕ) (uncurry Thetadot) := by
    exact contDiff_partialTime_self hTheta3
  have hw2 : ContDiff ℝ (2 : ℕ) (uncurry w) := by
    exact (contDiff_partialTime_self hdelta4).of_le (by norm_num)
  have hsft2 : ContDiff ℝ (2 : ℕ) (uncurry sft) := by
    exact (contDiff_partialTime_self hsf4).of_le (by norm_num)
  have hdelta2 : ContDiff ℝ (2 : ℕ) (uncurry delta) := hdelta4.of_le (by norm_num)
  have hsf2 : ContDiff ℝ (2 : ℕ) (uncurry sf) := hsf4.of_le (by norm_num)
  have hYdot2 : ContDiff ℝ (2 : ℕ) (uncurry Ydot) :=
    contDiff_rearOwnVelocity (hTheta3.of_le (by norm_num)) hdelta2 hsf2
      hFdot2 hThetadot2 hw2 hsft2
      (fun _ _ => rfl)
  have hang2 : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Theta delta sf)) :=
    contDiff_rearOwnAngle (hTheta3.of_le (by norm_num)) hdelta2 hsf2
  have hcos : ∀ t s, Real.cos (delta t s) ≠ 0 := fun t s => by
    exact ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1
      (hstrip0 t) (hstrip1 t) s)
  have hcomp1 : ContDiff ℝ (1 : ℕ)
      (fun p : ℝ × ℝ => (p.1, uncurry sf p)) :=
    contDiff_fst.prodMk (hsf4.of_le (by norm_num))
  have hdcomp1 : ContDiff ℝ (1 : ℕ)
      (fun p : ℝ × ℝ => uncurry delta (p.1, uncurry sf p)) :=
    (hdelta4.of_le (by norm_num)).comp hcomp1
  have htan1 : ContDiff ℝ (1 : ℕ)
      (uncurry fun t x => Real.tan (delta t (sf t x))) := by
    have hsin := Real.contDiff_sin.comp hdcomp1
    have hcosC := Real.contDiff_cos.comp hdcomp1
    simpa [Real.tan_eq_sin_div_cos] using hsin.div hcosC (fun p => hcos p.1 (sf p.1 p.2))
  have hfrontTrack1 : ContDiff ℝ (1 : ℕ)
      (uncurry (frontParamTrack F Theta delta)) := by
    simpa [frontParamTrack] using contDiff_one_rearTrackFamily
      (hF3.of_le (by norm_num)) (hTheta3.of_le (by norm_num))
      (hdelta4.of_le (by norm_num))
  have htrackSpace : ∀ t s, HasDerivAt (frontParamTrack F Theta delta t)
      ((Real.cos (delta t s) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Theta t) (delta t) s : ℂ))) s :=
    fun t s => hasDerivAt_rearTrack (hfront t s) (hTheta t s) (hsteer t s)
  have htrackTime : ∀ t s, HasDerivAt
      (fun r => frontParamTrack F Theta delta r s)
      (trackVelocity Fdot Thetadot w Theta delta t s) t :=
    fun t s => hasDerivAt_frontParamTrack_time
      (hasDerivAt_partialTime hFdiff) (hasDerivAt_partialTime hThetadiff)
      (hasDerivAt_partialTime hdeltadiff) t s
  have hYtime : ∀ t x,
      HasDerivAt (fun r => rearOwn F Theta delta sf r x) (Ydot t x) t := by
    intro t x
    exact hasDerivAt_rearOwn_time hfrontTrack1 htrackSpace htrackTime
      (hasDerivAt_partialTime hsfdiff) t x
  have hFdotdiff : Differentiable ℝ (uncurry Fdot) :=
    hFdot2.differentiable (by norm_num)
  have hThetadotdiff : Differentiable ℝ (uncurry Thetadot) :=
    hThetadot2.differentiable (by norm_num)
  have hwdiff : Differentiable ℝ (uncurry w) := hw2.differentiable (by norm_num)
  have hjac : ∀ t x, HasDerivAt
      (fun x' => frameNormal Ydot (rearOwnAngle Theta delta sf) t x')
      (frontNormalVelocityAt Fdot Theta delta t (sf t x)
          / Real.cos (delta t (sf t x))
        - frameNormal Ydot (rearOwnAngle Theta delta sf) t x) x := by
    intro t x
    exact hasDerivAt_rearOwn_normal_jacobi_of_smoothDependence
      (Fdot := Fdot) (Θdot := Thetadot) (w := w) (sft := sft)
      (Fdots := partialArc Fdot) (Θdots := partialArc Thetadot)
      (ws := partialArc w) (Ydot := Ydot)
      hfront hTheta hsteer
      (SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hdelta4.continuous
        hstrip0 hstrip1 hsfinv)
      hcos (hasDerivAt_partialTime hFdiff) (hasDerivAt_partialTime hThetadiff)
      (hasDerivAt_partialTime hdeltadiff) (hasDerivAt_partialArc hFdotdiff)
      (hasDerivAt_partialArc hThetadotdiff) (hasDerivAt_partialArc hwdiff)
      (hF3.of_le (by norm_num)) (hTheta3.of_le (by norm_num))
      (hdelta4.of_le (by norm_num)) (fun _ _ => rfl) t x
  exact ⟨Ydot, hYtime, hYdot2, hang2, htan1, hjac⟩

/-- Same qualitative package with one higher order of regularity. For jointly
`C⁴` front and tangent-angle data (and `C⁴` steering/rear-arclength map), the
selected rear velocity and rear angle are both `C³`. -/
theorem exists_canonical_gauge_jacobi_data_c3
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hF4 : ContDiff ℝ (4 : ℕ) (uncurry F))
    (hTheta4 : ContDiff ℝ (4 : ℕ) (uncurry Theta))
    (hdelta4 : ContDiff ℝ (4 : ℕ) (uncurry delta))
    (hsf4 : ContDiff ℝ (4 : ℕ) (uncurry sf))
    (hfront : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Theta t s : ℂ))) s)
    (hTheta : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x) :
    ∃ Ydot : ℝ → ℝ → ℂ,
      (∀ t x, HasDerivAt (fun r => rearOwn F Theta delta sf r x) (Ydot t x) t) ∧
      ContDiff ℝ (3 : ℕ) (uncurry Ydot) ∧
      ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Theta delta sf)) ∧
      ContDiff ℝ (1 : ℕ)
        (uncurry fun t x => Real.tan (delta t (sf t x))) ∧
      (∀ t x, HasDerivAt
        (fun x' => frameNormal Ydot (rearOwnAngle Theta delta sf) t x')
        (frontNormalVelocityAt (partialTime F) Theta delta t (sf t x)
            / Real.cos (delta t (sf t x))
          - frameNormal Ydot (rearOwnAngle Theta delta sf) t x) x) := by
  let Fdot : ℝ → ℝ → ℂ := partialTime F
  let Thetadot : ℝ → ℝ → ℝ := partialTime Theta
  let w : ℝ → ℝ → ℝ := partialTime delta
  let sft : ℝ → ℝ → ℝ := partialTime sf
  let Ydot : ℝ → ℝ → ℂ := fun t x =>
    trackVelocity Fdot Thetadot w Theta delta t (sf t x)
      + (sft t x) • ((Real.cos (delta t (sf t x)) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Theta t) (delta t) (sf t x) : ℂ)))
  have hFdiff : Differentiable ℝ (uncurry F) := hF4.differentiable (by norm_num)
  have hThetadiff : Differentiable ℝ (uncurry Theta) :=
    hTheta4.differentiable (by norm_num)
  have hdeltadiff : Differentiable ℝ (uncurry delta) :=
    hdelta4.differentiable (by norm_num)
  have hsfdiff : Differentiable ℝ (uncurry sf) := hsf4.differentiable (by norm_num)
  have hFdot3 : ContDiff ℝ (3 : ℕ) (uncurry Fdot) :=
    contDiff_partialTime_self hF4
  have hThetadot3 : ContDiff ℝ (3 : ℕ) (uncurry Thetadot) :=
    contDiff_partialTime_self hTheta4
  have hw3 : ContDiff ℝ (3 : ℕ) (uncurry w) :=
    (contDiff_partialTime_self hdelta4).of_le (by norm_num)
  have hsft3 : ContDiff ℝ (3 : ℕ) (uncurry sft) :=
    (contDiff_partialTime_self hsf4).of_le (by norm_num)
  have hdelta3 : ContDiff ℝ (3 : ℕ) (uncurry delta) := hdelta4.of_le (by norm_num)
  have hsf3 : ContDiff ℝ (3 : ℕ) (uncurry sf) := hsf4.of_le (by norm_num)
  have hYdot3 : ContDiff ℝ (3 : ℕ) (uncurry Ydot) :=
    contDiff_rearOwnVelocity (hTheta4.of_le (by norm_num)) hdelta3 hsf3
      hFdot3 hThetadot3 hw3 hsft3 (fun _ _ => rfl)
  have hang3 : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Theta delta sf)) :=
    contDiff_rearOwnAngle (hTheta4.of_le (by norm_num)) hdelta3 hsf3
  have hcos : ∀ t s, Real.cos (delta t s) ≠ 0 := fun t s => by
    exact ne_of_gt (SelectedPathData.cos_steering_pos hkh0 hkh1
      (hstrip0 t) (hstrip1 t) s)
  have hcomp1 : ContDiff ℝ (1 : ℕ)
      (fun p : ℝ × ℝ => (p.1, uncurry sf p)) :=
    contDiff_fst.prodMk (hsf4.of_le (by norm_num))
  have hdcomp1 : ContDiff ℝ (1 : ℕ)
      (fun p : ℝ × ℝ => uncurry delta (p.1, uncurry sf p)) :=
    (hdelta4.of_le (by norm_num)).comp hcomp1
  have htan1 : ContDiff ℝ (1 : ℕ)
      (uncurry fun t x => Real.tan (delta t (sf t x))) := by
    have hsin := Real.contDiff_sin.comp hdcomp1
    have hcosC := Real.contDiff_cos.comp hdcomp1
    simpa [Real.tan_eq_sin_div_cos] using hsin.div hcosC (fun p => hcos p.1 (sf p.1 p.2))
  have hfrontTrack1 : ContDiff ℝ (1 : ℕ)
      (uncurry (frontParamTrack F Theta delta)) := by
    simpa [frontParamTrack] using contDiff_one_rearTrackFamily
      (hF4.of_le (by norm_num)) (hTheta4.of_le (by norm_num))
      (hdelta4.of_le (by norm_num))
  have htrackSpace : ∀ t s, HasDerivAt (frontParamTrack F Theta delta t)
      ((Real.cos (delta t s) : ℂ)
        * Complex.exp (Complex.I * (rearAngle (Theta t) (delta t) s : ℂ))) s :=
    fun t s => hasDerivAt_rearTrack (hfront t s) (hTheta t s) (hsteer t s)
  have htrackTime : ∀ t s, HasDerivAt
      (fun r => frontParamTrack F Theta delta r s)
      (trackVelocity Fdot Thetadot w Theta delta t s) t :=
    fun t s => hasDerivAt_frontParamTrack_time
      (hasDerivAt_partialTime hFdiff) (hasDerivAt_partialTime hThetadiff)
      (hasDerivAt_partialTime hdeltadiff) t s
  have hYtime : ∀ t x,
      HasDerivAt (fun r => rearOwn F Theta delta sf r x) (Ydot t x) t := by
    intro t x
    exact hasDerivAt_rearOwn_time hfrontTrack1 htrackSpace htrackTime
      (hasDerivAt_partialTime hsfdiff) t x
  have hFdotdiff : Differentiable ℝ (uncurry Fdot) :=
    hFdot3.differentiable (by norm_num)
  have hThetadotdiff : Differentiable ℝ (uncurry Thetadot) :=
    hThetadot3.differentiable (by norm_num)
  have hwdiff : Differentiable ℝ (uncurry w) := hw3.differentiable (by norm_num)
  have hjac : ∀ t x, HasDerivAt
      (fun x' => frameNormal Ydot (rearOwnAngle Theta delta sf) t x')
      (frontNormalVelocityAt Fdot Theta delta t (sf t x)
          / Real.cos (delta t (sf t x))
        - frameNormal Ydot (rearOwnAngle Theta delta sf) t x) x := by
    intro t x
    exact hasDerivAt_rearOwn_normal_jacobi_of_smoothDependence
      (Fdot := Fdot) (Θdot := Thetadot) (w := w) (sft := sft)
      (Fdots := partialArc Fdot) (Θdots := partialArc Thetadot)
      (ws := partialArc w) (Ydot := Ydot)
      hfront hTheta hsteer
      (SelectedChangeOfVariable.hasDerivAt_sf_space hkh0 hkh1 hdelta4.continuous
        hstrip0 hstrip1 hsfinv)
      hcos (hasDerivAt_partialTime hFdiff) (hasDerivAt_partialTime hThetadiff)
      (hasDerivAt_partialTime hdeltadiff) (hasDerivAt_partialArc hFdotdiff)
      (hasDerivAt_partialArc hThetadotdiff) (hasDerivAt_partialArc hwdiff)
      (hF4.of_le (by norm_num)) (hTheta4.of_le (by norm_num))
      (hdelta4.of_le (by norm_num)) (fun _ _ => rfl) t x
  exact ⟨Ydot, hYtime, hYdot3, hang3, htan1, hjac⟩

/-- Canonical time derivatives of the rear tangent angle and rear curvature,
with their spatial compatibility supplied by Clairaut's theorem. -/
theorem exists_canonical_angle_time_data
    (hTheta : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hang2 : ContDiff ℝ (2 : ℕ) (uncurry (rearOwnAngle Theta delta sf)))
    (hk1 : ContDiff ℝ (1 : ℕ)
      (uncurry fun t x => Real.tan (delta t (sf t x)))) :
    ∃ alphaT kT : ℝ → ℝ → ℝ,
      (∀ t x, HasDerivAt (fun r => rearOwnAngle Theta delta sf r x)
        (alphaT t x) t) ∧
      (∀ t x, HasDerivAt
        (fun r => Real.tan (delta r (sf r x))) (kT t x) t) ∧
      Continuous (uncurry alphaT) ∧ Continuous (uncurry kT) ∧
      (∀ t x, HasDerivAt (alphaT t) (kT t x) x) := by
  let psi : ℝ → ℝ → ℝ := rearOwnAngle Theta delta sf
  let kap : ℝ → ℝ → ℝ := fun t x => Real.tan (delta t (sf t x))
  let alphaT : ℝ → ℝ → ℝ := partialTime psi
  let kT : ℝ → ℝ → ℝ := partialTime kap
  have hpsidiff : Differentiable ℝ (uncurry psi) :=
    hang2.differentiable (by norm_num)
  have hkapdiff : Differentiable ℝ (uncurry kap) :=
    hk1.differentiable (by norm_num)
  have ha : ∀ t x, HasDerivAt (fun r => psi r x) (alphaT t x) t :=
    hasDerivAt_partialTime hpsidiff
  have hk : ∀ t x, HasDerivAt (fun r => kap r x) (kT t x) t :=
    hasDerivAt_partialTime hkapdiff
  have haC : Continuous (uncurry alphaT) :=
    (contDiff_partialTime_self (n := 1) hang2).continuous
  have hkC : Continuous (uncurry kT) :=
    (contDiff_partialTime_self (n := 0) hk1).continuous
  have hpsix : ∀ t x, HasDerivAt (psi t) (kap t x) x := by
    intro t x
    exact RearOwnIsFront.hasDerivAt_rearOwnAngle hTheta hsteer hsf t x
  refine ⟨alphaT, kT, ha, hk, haC, hkC, ?_⟩
  intro t x
  have hcomm := MixedPartials.deriv_partial_comm hang2 t x
  have hleft : deriv (fun r => deriv (fun y => psi r y) x) t = kT t x := by
    have heq : (fun r => deriv (fun y => psi r y) x) = fun r => kap r x := by
      funext r
      exact (hpsix r x).deriv
    rw [heq, (hk t x).deriv]
  have hright : deriv (fun y => deriv (fun r => psi r y) t) x = deriv (alphaT t) x := by
    have heq : (fun y => deriv (fun r => psi r y) t) = alphaT t := by
      funext y
      exact (ha t y).deriv
    rw [heq]
  have had : HasDerivAt (alphaT t) (partialArc alphaT t x) x :=
    hasDerivAt_partialArc
      ((contDiff_partialTime_self (n := 1) hang2).differentiable (by norm_num)) t x
  apply had.congr_deriv
  have hpa : partialArc alphaT t x = deriv (alphaT t) x := had.deriv.symm
  rw [hpa, ← hright, ← hleft, hcomm]

/-- Clairaut and frame reconstruction supply the mixed derivative witness used
by the gauge rear-family construction. -/
theorem exists_mixed_frame_witness
    {Y Ydot : ℝ → ℝ → ℂ} {psi : ℝ → ℝ → ℝ}
    (hY2 : ContDiff ℝ 2 (uncurry Y))
    (hYdot1 : ContDiff ℝ 1 (uncurry Ydot))
    (hT1 : ContDiff ℝ 1
      (uncurry fun t x => Complex.exp (Complex.I * (psi t x : ℂ))))
    (hYx : ∀ t x, HasDerivAt (Y t)
      (Complex.exp (Complex.I * (psi t x : ℂ))) x)
    (hYt : ∀ t x, HasDerivAt (fun r => Y r x) (Ydot t x) t) :
    ∀ t x, ∃ W : ℂ,
      HasDerivAt (fun r => Complex.exp (Complex.I * (psi r x : ℂ))) W t ∧
      HasDerivAt (fun y =>
        (frameTangential Ydot psi t y : ℂ) *
            Complex.exp (Complex.I * (psi t y : ℂ)) +
        (frameNormal Ydot psi t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I * (psi t y : ℂ)))) W x := by
  intro t x
  let W : ℂ := deriv (Ydot t) x
  have hYdotd : HasDerivAt (Ydot t) W x := by
    have h := RearOwnHigherRegularity.hasDerivAt_partialArc
      (hYdot1.differentiable (by norm_num)) t x
    exact h.congr_deriv h.deriv.symm
  have hframe : (fun y =>
      (frameTangential Ydot psi t y : ℂ) * Complex.exp (Complex.I * (psi t y : ℂ)) +
      (frameNormal Ydot psi t y : ℂ) *
        (Complex.I * Complex.exp (Complex.I * (psi t y : ℂ)))) = Ydot t := by
    funext y
    have h := RearFamilyFrame.frame_reconstruct (Ydot t y) (psi t y)
    simp only [frameTangential, frameNormal]
    conv_rhs => rw [← h]
    ring
  have hright : HasDerivAt (fun y =>
      (frameTangential Ydot psi t y : ℂ) * Complex.exp (Complex.I * (psi t y : ℂ)) +
      (frameNormal Ydot psi t y : ℂ) *
        (Complex.I * Complex.exp (Complex.I * (psi t y : ℂ)))) W x := by
    rw [hframe]
    exact hYdotd
  have hcomm := MixedPartials.deriv_partial_comm hY2 t x
  have hL : (fun r => deriv (fun y => Y r y) x) =
      fun r => Complex.exp (Complex.I * (psi r x : ℂ)) := by
    funext r
    exact (hYx r x).deriv
  have hR : (fun y => deriv (fun r => Y r y) t) = Ydot t := by
    funext y
    exact (hYt t y).deriv
  rw [hL, hR] at hcomm
  have hleft0 := RearOwnHigherRegularity.hasDerivAt_partialTime
    (hT1.differentiable (by norm_num)) t x
  have hleft : HasDerivAt
      (fun r => Complex.exp (Complex.I * (psi r x : ℂ))) W t := by
    apply hleft0.congr_deriv
    rw [← hleft0.deriv, hcomm, hYdotd.deriv]
  exact ⟨W, hleft, hright⟩

end SelectedRearGaugeQualitative
