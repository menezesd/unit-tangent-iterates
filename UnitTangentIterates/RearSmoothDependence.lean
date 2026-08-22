import Mathlib
import UnitTangentIterates.RearTrack
import UnitTangentIterates.SteeringSmoothDependence

/-!
# Smooth dependence of the selected rear on the front

`SteeringSmoothDependence.lean` proves that the selected steering angle `δ`
depends differentiably on the path parameter, with derivative the periodic
solution `w` of the linearized steering equation.  This file carries that
differentiability over to the geometric data of the **rear track**
`R = F - e^{iΨ}`, `Ψ = Θ - δ`, of `RearTrack.lean`:

* `hasDerivAt_rearAngle_param` — the rear tangent angle `Ψ` moves at rate
  `Θ̇ - w`;
* `hasDerivAt_rear_curvature` — the rear curvature `tan δ` moves at rate
  `w / cos²δ`;
* `hasDerivAt_rearTrack_param` — the rear track itself moves at rate
  `Ḟ - i(Θ̇ - w) e^{iΨ}`;
* `rear_normal_velocity` — hence its **normal velocity**, the quantity the
  path metric of `PathMetric.lean` measures, is
  `⟨Ḟ, i e^{iΨ}⟩ - (Θ̇ - w)`.

Together with `SteeringSmoothDependence.hasDerivAt_selected_steering` this is
the paper's lemma *Smooth dependence of the selected rear*: a differentiable
path of fronts induces a differentiable path of selected rears, whose velocity
is computed from the linearized steering equation.
-/

noncomputable section

open Real Complex

namespace RearSmoothDependence

open RearTrack

variable {F : ℝ → ℝ → ℂ} {Θ delta : ℝ → ℝ → ℝ} {Fdot : ℝ → ℂ} {Θdot w : ℝ → ℝ}
  {a0 s : ℝ}

/-- **The rear tangent angle depends differentiably on the path parameter**,
at rate `Θ̇ - w`. -/
theorem hasDerivAt_rearAngle_param
    (hTheta : HasDerivAt (fun a => Θ a s) (Θdot s) a0)
    (hd : HasDerivAt (fun a => delta a s) (w s) a0) :
    HasDerivAt (fun a => rearAngle (Θ a) (delta a) s) (Θdot s - w s) a0 := by
  simpa [rearAngle] using hTheta.sub hd

/-- **The rear curvature depends differentiably on the path parameter.**  The
rear curvature is `tan δ` (`RearTrack.rear_curvature_eq_tan`), so it moves at
rate `w / cos²δ`. -/
theorem hasDerivAt_rear_curvature
    (hd : HasDerivAt (fun a => delta a s) (w s) a0)
    (hcos : Real.cos (delta a0 s) ≠ 0) :
    HasDerivAt (fun a => Real.tan (delta a s)) (w s / Real.cos (delta a0 s) ^ 2) a0 := by
  have h := (Real.hasDerivAt_tan hcos).comp a0 hd
  refine h.congr_deriv ?_
  field_simp

/-- The complex unit tangent of the rear moves at rate `i(Θ̇ - w) e^{iΨ}`. -/
theorem hasDerivAt_expRearAngle_param
    (hTheta : HasDerivAt (fun a => Θ a s) (Θdot s) a0)
    (hd : HasDerivAt (fun a => delta a s) (w s) a0) :
    HasDerivAt (fun a => Complex.exp (Complex.I * ((rearAngle (Θ a) (delta a) s : ℝ) : ℂ)))
      (Complex.I * ((Θdot s - w s : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((rearAngle (Θ a0) (delta a0) s : ℝ) : ℂ))) a0 := by
  have hang := hasDerivAt_rearAngle_param (Θ := Θ) (delta := delta) hTheta hd
  have hc : HasDerivAt (fun a => ((rearAngle (Θ a) (delta a) s : ℝ) : ℂ))
      (((Θdot s - w s : ℝ) : ℂ)) a0 := by
    simpa using hang.ofReal_comp
  have hmul : HasDerivAt (fun a => Complex.I * ((rearAngle (Θ a) (delta a) s : ℝ) : ℂ))
      (Complex.I * ((Θdot s - w s : ℝ) : ℂ)) a0 := hc.const_mul Complex.I
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.cexp

/-- **The rear track depends differentiably on the path parameter**, and its
velocity is `Ḟ - i(Θ̇ - w) e^{iΨ}`. -/
theorem hasDerivAt_rearTrack_param
    (hF : HasDerivAt (fun a => F a s) (Fdot s) a0)
    (hTheta : HasDerivAt (fun a => Θ a s) (Θdot s) a0)
    (hd : HasDerivAt (fun a => delta a s) (w s) a0) :
    HasDerivAt (fun a => rearTrack (F a) (Θ a) (delta a) s)
      (Fdot s - Complex.I * ((Θdot s - w s : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((rearAngle (Θ a0) (delta a0) s : ℝ) : ℂ))) a0 := by
  have h := hF.sub (hasDerivAt_expRearAngle_param (Θ := Θ) (delta := delta) hTheta hd)
  simpa [rearTrack] using h

/-- The unit tangent of the rear has modulus one. -/
theorem exp_mul_conj (psi : ℝ) :
    Complex.exp (Complex.I * (psi : ℂ)) * (starRingEnd ℂ) (Complex.exp (Complex.I * (psi : ℂ)))
      = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

/-- **The normal velocity of the selected rear.**  The rear's unit normal is
`i e^{iΨ}`, so the normal component of the rear velocity of
`hasDerivAt_rearTrack_param` is `⟨Ḟ, i e^{iΨ}⟩ - (Θ̇ - w)`: the front's own
normal velocity, corrected by the rotation rate of the rear tangent. -/
theorem rear_normal_velocity (psi : ℝ) (V : ℂ) (c : ℝ) :
    ((V - Complex.I * (c : ℂ) * Complex.exp (Complex.I * (psi : ℂ)))
        * (starRingEnd ℂ) (Complex.I * Complex.exp (Complex.I * (psi : ℂ)))).re
      = (V * (starRingEnd ℂ) (Complex.I * Complex.exp (Complex.I * (psi : ℂ)))).re - c := by
  set E : ℂ := Complex.exp (Complex.I * (psi : ℂ)) with hE
  have hEE : E * (starRingEnd ℂ) E = 1 := exp_mul_conj psi
  have hI : (starRingEnd ℂ) (Complex.I * E) = -Complex.I * (starRingEnd ℂ) E := by
    simp [Complex.conj_I]
  have hexpand : (V - Complex.I * (c : ℂ) * E) * (starRingEnd ℂ) (Complex.I * E)
      = V * (starRingEnd ℂ) (Complex.I * E)
        - (c : ℂ) * (Complex.I * (-Complex.I)) * (E * (starRingEnd ℂ) E) := by
    rw [hI]; ring
  rw [hexpand, hEE]
  have : Complex.I * (-Complex.I) = 1 := by simp [Complex.I_mul_I]
  rw [this]
  simp

/-- **Smooth dependence of the selected rear.**  Combining
`SteeringSmoothDependence.hasDerivAt_selected_steering` with
`hasDerivAt_rearTrack_param`: for a differentiable path of fronts whose radius
of curvature satisfies the hypotheses of the steering lemma, the selected rear
track is differentiable in the path parameter, with velocity
`Ḟ - i(Θ̇ - w) e^{iΨ}` where `w` is the periodic solution of the linearized
steering equation. -/
theorem hasDerivAt_selected_rearTrack
    {q : ℝ → ℝ → ℝ} {qdot : ℝ → ℝ} {P kap Q Qd Qlip Cq : ℝ}
    (hP : 0 < P) (hkap : 0 < kap) (hkap1 : kap < 1)
    (hsol : ∀ a x, HasDerivAt (delta a) (1 - q a x * Real.sin (delta a x)) x)
    (hper : ∀ a, Function.Periodic (delta a) P)
    (hstrip : ∀ a x, delta a x ∈ Set.Icc (0:ℝ) (Real.arcsin kap))
    (hqlow : ∀ a x, kap⁻¹ ≤ q a x) (hqup : ∀ a x, q a x ≤ Q)
    (hqlip : ∀ a x, |q a x - q a0 x| ≤ Qlip * |a - a0|)
    (hqtaylor : ∀ a x, |q a x - q a0 x - (a - a0) * qdot x| ≤ Cq * (a - a0) ^ 2)
    (hqdot : ∀ x, |qdot x| ≤ Qd) (hCq : 0 ≤ Cq)
    (hw : ∀ x, HasDerivAt w
      (-(q a0 x * Real.cos (delta a0 x)) * w x - qdot x * Real.sin (delta a0 x)) x)
    (hwper : Function.Periodic w P)
    (hF : HasDerivAt (fun a => F a s) (Fdot s) a0)
    (hTheta : HasDerivAt (fun a => Θ a s) (Θdot s) a0) :
    HasDerivAt (fun a => rearTrack (F a) (Θ a) (delta a) s)
      (Fdot s - Complex.I * ((Θdot s - w s : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((rearAngle (Θ a0) (delta a0) s : ℝ) : ℂ))) a0 :=
  hasDerivAt_rearTrack_param hF hTheta
    (SteeringSmoothDependence.hasDerivAt_selected_steering hP hkap hkap1 hsol hper hstrip
      hqlow hqup hqlip hqtaylor hqdot hCq hw hwper s)

end RearSmoothDependence
