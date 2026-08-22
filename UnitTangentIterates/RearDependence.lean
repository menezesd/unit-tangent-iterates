import Mathlib
import UnitTangentIterates.RearTrack
import UnitTangentIterates.SelectedRear

/-!
# Continuous dependence of the selected rear on the front, in `C²`

The lemma *Selected inverse on the closed strip* of *A Noncircular Oval with
Convex Unit-Tangent Iterates* ends with

> When the perimeter varies, write the equation in normalized arclength.
> Continuous dependence for this scalar periodic ODE then gives convergence of
> `δ`, the coordinate change `x`, and the reconstructed rear.

`SelectedRear.steering_sup_dist_le` is the continuous dependence of the
steering angle itself, `‖δ¹ − δ²‖_∞ ≤ ‖K¹ − K²‖_∞ / √(1 − κ̂²)`.  This file
propagates it to the reconstructed rear: in one common parameter, closeness of
the two fronts (position, tangent angle and curvature) gives closeness of the
rears in position, unit tangent, speed and curvature — the `C²` dependence.

Main results:

* `norm_expI_sub_expI_le` : `s ↦ e^{is}` is `1`-Lipschitz;
* `abs_tan_sub_tan_le` : `tan` is Lipschitz on the selected strip with constant
  `1/(1 − κ̂²)`, which converts closeness of the steering angles into closeness
  of the rear curvatures;
* `rear_depends_continuously` : the five resulting bounds.
-/

noncomputable section

open Real Set Complex

namespace RearDependence

/-- The complex unit tangent `s ↦ e^{is}` is `1`-Lipschitz. -/
theorem norm_expI_sub_expI_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤ |x - y| := by
  have hd : ∀ t : ℝ, HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
      (Complex.I * Complex.exp (Complex.I * (t : ℂ))) t := by
    intro t
    have h1 : HasDerivAt (fun r : ℝ => Complex.I * (r : ℂ)) Complex.I t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
    simpa [mul_comm] using h1.cexp
  have hdiff : ∀ t ∈ (univ : Set ℝ),
      DifferentiableAt ℝ (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) t :=
    fun t _ => (hd t).differentiableAt
  have hbound : ∀ t ∈ (univ : Set ℝ),
      ‖deriv (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ))) t‖ ≤ 1 := by
    intro t _
    rw [(hd t).deriv, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
    simp
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
    (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- **`tan` is Lipschitz on the selected strip** `[0, arcsin κ̂]`, with constant
`1/(1 − κ̂²)`: the rear curvature depends Lipschitz-continuously on the steering
angle. -/
theorem abs_tan_sub_tan_le {kap a b : ℝ} (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (ha : a ∈ Icc (0:ℝ) (arcsin kap)) (hb : b ∈ Icc (0:ℝ) (arcsin kap)) :
    |Real.tan a - Real.tan b| ≤ |a - b| / (1 - kap ^ 2) := by
  have hk2 : (0:ℝ) < 1 - kap ^ 2 := by nlinarith
  have hcos : ∀ x ∈ Icc (0:ℝ) (arcsin kap), Real.sqrt (1 - kap ^ 2) ≤ Real.cos x := by
    intro x hx
    exact Shadowing.cos_ge_of_mem_strip hx.1 hx.2
  have hspos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr hk2
  have hcos2 : ∀ x ∈ Icc (0:ℝ) (arcsin kap), 1 - kap ^ 2 ≤ Real.cos x ^ 2 := by
    intro x hx
    nlinarith [hcos x hx, Real.sq_sqrt hk2.le]
  have hdiff : ∀ x ∈ Icc (0:ℝ) (arcsin kap), DifferentiableAt ℝ Real.tan x := by
    intro x hx
    have hne : Real.cos x ≠ 0 := by nlinarith [hcos x hx]
    exact (Real.hasDerivAt_tan hne).differentiableAt
  have hbound : ∀ x ∈ Icc (0:ℝ) (arcsin kap), ‖deriv Real.tan x‖ ≤ 1 / (1 - kap ^ 2) := by
    intro x hx
    rw [Real.deriv_tan, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (by norm_num) hk2 (hcos2 x hx)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Icc _ _) hb ha
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |Real.tan a - Real.tan b| ≤ 1 / (1 - kap ^ 2) * |a - b| := h
    _ = |a - b| / (1 - kap ^ 2) := by ring

/-- **`C²` continuous dependence of the selected rear on the front.**  If two
fronts are close in position, tangent angle and curvature, then the rears
reconstructed from their periodic steering angles in the closed strip are close
in position, unit tangent, speed and curvature. -/
theorem rear_depends_continuously {F1 F2 : ℝ → ℂ} {Θ1 Θ2 d1 d2 K1 K2 : ℝ → ℝ}
    {P kap epsK epsT epsF : ℝ} (hP : 0 < P) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (h1 : ∀ s, HasDerivAt d1 (K1 s - Real.sin (d1 s)) s)
    (h2 : ∀ s, HasDerivAt d2 (K2 s - Real.sin (d2 s)) s)
    (hp1 : Function.Periodic d1 P) (hp2 : Function.Periodic d2 P)
    (hs1 : ∀ s, d1 s ∈ Icc (0:ℝ) (arcsin kap)) (hs2 : ∀ s, d2 s ∈ Icc (0:ℝ) (arcsin kap))
    (hK : ∀ s, |K1 s - K2 s| ≤ epsK)
    (hT : ∀ s, |Θ1 s - Θ2 s| ≤ epsT)
    (hF : ∀ s, ‖F1 s - F2 s‖ ≤ epsF) :
    (∀ s, |d1 s - d2 s| ≤ epsK / Real.sqrt (1 - kap ^ 2)) ∧
    (∀ s, |RearTrack.rearAngle Θ1 d1 s - RearTrack.rearAngle Θ2 d2 s|
        ≤ epsT + epsK / Real.sqrt (1 - kap ^ 2)) ∧
    (∀ s, ‖Complex.exp (Complex.I * (RearTrack.rearAngle Θ1 d1 s : ℂ))
          - Complex.exp (Complex.I * (RearTrack.rearAngle Θ2 d2 s : ℂ))‖
        ≤ epsT + epsK / Real.sqrt (1 - kap ^ 2)) ∧
    (∀ s, ‖RearTrack.rearTrack F1 Θ1 d1 s - RearTrack.rearTrack F2 Θ2 d2 s‖
        ≤ epsF + (epsT + epsK / Real.sqrt (1 - kap ^ 2))) ∧
    (∀ s, |Real.cos (d1 s) - Real.cos (d2 s)| ≤ epsK / Real.sqrt (1 - kap ^ 2)) ∧
    (∀ s, |Real.tan (d1 s) - Real.tan (d2 s)|
        ≤ epsK / Real.sqrt (1 - kap ^ 2) / (1 - kap ^ 2)) := by
  have hk2 : (0:ℝ) < 1 - kap ^ 2 := by nlinarith
  have hdelta := SelectedRear.steering_sup_dist_le hP hkap1 hkap0 h1 h2 hp1 hp2 hs1 hs2 hK
  have hangle : ∀ s, |RearTrack.rearAngle Θ1 d1 s - RearTrack.rearAngle Θ2 d2 s|
      ≤ epsT + epsK / Real.sqrt (1 - kap ^ 2) := by
    intro s
    have : RearTrack.rearAngle Θ1 d1 s - RearTrack.rearAngle Θ2 d2 s
        = (Θ1 s - Θ2 s) - (d1 s - d2 s) := by simp [RearTrack.rearAngle]; ring
    rw [this]
    calc |(Θ1 s - Θ2 s) - (d1 s - d2 s)| ≤ |Θ1 s - Θ2 s| + |d1 s - d2 s| := abs_sub _ _
      _ ≤ epsT + epsK / Real.sqrt (1 - kap ^ 2) := add_le_add (hT s) (hdelta s)
  refine ⟨hdelta, hangle, fun s => ?_, fun s => ?_, fun s => ?_, fun s => ?_⟩
  · exact le_trans (norm_expI_sub_expI_le _ _) (hangle s)
  · have hsplit : RearTrack.rearTrack F1 Θ1 d1 s - RearTrack.rearTrack F2 Θ2 d2 s
        = (F1 s - F2 s) - (Complex.exp (Complex.I * (RearTrack.rearAngle Θ1 d1 s : ℂ))
          - Complex.exp (Complex.I * (RearTrack.rearAngle Θ2 d2 s : ℂ))) := by
      simp [RearTrack.rearTrack]; ring
    rw [hsplit]
    exact le_trans (norm_sub_le _ _)
      (add_le_add (hF s) (le_trans (norm_expI_sub_expI_le _ _) (hangle s)))
  · have h := Real.lipschitzWith_cos.dist_le_mul (d1 s) (d2 s)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    exact le_trans h (hdelta s)
  · have h := abs_tan_sub_tan_le hkap0 hkap1 (hs1 s) (hs2 s)
    have hd := hdelta s
    have hmono : |d1 s - d2 s| / (1 - kap ^ 2)
        ≤ epsK / Real.sqrt (1 - kap ^ 2) / (1 - kap ^ 2) :=
      by gcongr
    exact le_trans h hmono

end RearDependence
