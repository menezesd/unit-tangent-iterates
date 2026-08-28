import UnitTangentIterates.RearOwnMixedOfInverseTimeSpatial
import UnitTangentIterates.GeneralVariation

/-!
# The inverse Jacobi identity from the exact C1 rear velocity

This avoids the older joint-C2 frozen-family argument.  Once the exact rear
velocity has its spatial derivative, the normal-frame derivative is a
pointwise frame computation.
-/

noncomputable section

open Function

namespace RearOwnC1JacobiOfVelocitySpace

open RearTrack RearOwnArclength RearOwnMotion RearFamilyFrame
  RearOwnMixedOfInverseTimeSpatial SelectedInverseJacobiODE
  RearOwnHigherRegularity

variable {Fdot : ℝ → ℝ → ℂ}
  {ThetaT deltaT Theta delta sf etaF : ℝ → ℝ → ℝ}

/-- The C1 inverse-Jacobi ODE, obtained from the exact spatial derivative of
the inverse-arclength rear velocity and the front-normal source identity. -/
theorem jacobi
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0)
    (hnormal : ∀ t s,
      frontNormalVelocity (Fdot t s) (Theta t s - delta t s) (delta t s) =
        etaF t s)
    (hspace : ∀ t x, HasDerivAt
      (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf t)
      (Complex.I * (rearAngleTime ThetaT deltaT delta sf t x : ℂ) *
        Complex.exp (Complex.I *
          (rearOwnAngle Theta delta sf t x : ℂ))) x)
    (hpsiS : ∀ t x, HasDerivAt (rearOwnAngle Theta delta sf t)
      (Real.tan (delta t (sf t x))) x) :
    ∀ t x, HasDerivAt
      (frameNormal (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf)
        (rearOwnAngle Theta delta sf) t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) -
        frameNormal (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf)
          (rearOwnAngle Theta delta sf) t x) x := by
  intro t x
  let s := sf t x
  let d := delta t s
  let psi := rearOwnAngle Theta delta sf t x
  let E := Complex.exp (Complex.I * (psi : ℂ))
  let u := partialTime sf t x
  let A := ThetaT t s - deltaT t s
  let z := Fdot t s * (starRingEnd ℂ) E
  let xiF := z.re
  let etaFp := z.im
  have hpsi : psi = Theta t s - delta t s := by
    rfl
  have hunit : E * (starRingEnd ℂ) E = 1 := by
    exact RearSmoothDependence.exp_mul_conj psi
  have hfront : etaF t s = etaFp * Real.cos d - xiF * Real.sin d := by
    have hrec := frame_reconstruct (Fdot t s) psi
    have hfn := GeneralVariation.front_normal_velocity_general psi d xiF etaFp
    have heq : frontNormalVelocity (Fdot t s) psi d =
        etaFp * Real.cos d - xiF * Real.sin d := by
      rw [← hrec]
      simpa [frontNormalVelocity, xiF, etaFp, z] using hfn
    rw [← hnormal t s, ← hpsi]
    exact heq
  have hYframe :
      rearOwnVelocity Fdot ThetaT deltaT Theta delta sf t x *
          (starRingEnd ℂ) E =
        z - Complex.I * (A : ℂ) + (u * Real.cos d : ℂ) := by
    simp only [rearOwnVelocity, trackVelocity, rearOwnAngle]
    have hcompact : (Fdot t s - Complex.I * (A : ℂ) * E +
        (u * Real.cos d : ℂ) * E) * (starRingEnd ℂ) E =
        z - Complex.I * (A : ℂ) + (u * Real.cos d : ℂ) := by
      calc
        _ = z + (-Complex.I * (A : ℂ) + (u * Real.cos d : ℂ)) *
            (E * (starRingEnd ℂ) E) := by ring
        _ = z - Complex.I * (A : ℂ) + (u * Real.cos d : ℂ) := by
          rw [hunit]
          ring
    simpa only [s, d, psi, E, u, A, z, rearOwnAngle,
      Complex.ofReal_mul] using hcompact
  have hxi :
      frameTangential
          (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf)
          (rearOwnAngle Theta delta sf) t x =
        xiF + u * Real.cos d := by
    simp only [frameTangential, psi, E]
    rw [hYframe]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero, zero_add]
    exact rfl
  have heta :
      frameNormal
          (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf)
          (rearOwnAngle Theta delta sf) t x = etaFp - A := by
    simp only [frameNormal, psi, E]
    rw [hYframe]
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero, zero_add, mul_zero]
    exact rfl
  have hframe := RearFrameRegularity.hasDerivAt_frameNormal_space
    (hspace t x) (hpsiS t x)
  apply hframe.congr_deriv
  have hrot :
      ((Complex.I * (rearAngleTime ThetaT deltaT delta sf t x : ℂ) * E) *
          (starRingEnd ℂ) E).im =
        rearAngleTime ThetaT deltaT delta sf t x := by
    rw [mul_assoc, hunit, mul_one]
    simp
  rw [hrot, hxi, heta, hfront]
  change A + u * Real.sin d - Real.tan d * (xiF + u * Real.cos d) =
    (etaFp * Real.cos d - xiF * Real.sin d) / Real.cos d - (etaFp - A)
  rw [Real.tan_eq_sin_div_cos]
  have hc : Real.cos d ≠ 0 := hcos t s
  field_simp [hc]
  ring

end RearOwnC1JacobiOfVelocitySpace
