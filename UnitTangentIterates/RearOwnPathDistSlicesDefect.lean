import Mathlib
import UnitTangentIterates.RearOwnPathDistSlices
import UnitTangentIterates.RearOwnPathDistIntrinsicDefect

/-!
# The path pseudodistance for the path of fronts itself, together with the defect
of its gauge marking

`RearOwnPathDistSlices.pathDist_le_of_front_slices` identifies the moving marked
curve of the normal path with the family of fronts in the normalized parameter.
This file restates it with the extra conclusions about the gauge marking `Φ` in
which the pseudodistance is read — `Φ` fixes the base point, reads exactly one
rear period, and deviates from the affine marking of the terminal period by at
most `2 P₁ κ̂/(1 − κ̂²) · cost Γ`.

Here the extra hypothesis is the geometric one already used to fix the base
point in the original statement: the path does not move at its marked point,
`η(t, 0) = 0`.

Main result: `pathDist_and_defect_le_of_front_slices`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistSlicesDefect

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  RearOwnPathDistSlices

variable {F : ℝ → ℝ → ℂ} {Θ δ : ℝ → ℝ → ℝ} {P : ℝ → ℝ}

/-- **The path pseudodistance of the selected rears for the path of fronts
itself, together with the defect of its gauge marking.**
`RearOwnPathDistSlices.pathDist_le_of_front_slices` with the three extra
conclusions about the marking. -/
theorem pathDist_and_defect_le_of_front_slices {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {P0 P1 kh Md Klip CK : ℝ} {K Kd sf : ℝ → ℝ → ℝ}
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
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hKdper : ∀ t, Function.Periodic (Kd t) (P t))
    (hKdbd : ∀ t s, |Kd t s| ≤ Md)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hPC3 : ContDiff ℝ (3 : ℕ) P) (hKC3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKdC3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)))
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u))
    (hmark : ∀ t, Γ.eta t 0 = 0) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        (∀ t, Phi t 0 = 0) ∧ (∀ t, Phi t 1 = rearArclength (δ t) (P t)) ∧
        (∀ u, |Phi Γ.T u - rearArclength (δ Γ.T) (P Γ.T) * u|
          ≤ 2 * P1 * (kh / (1 - kh ^ 2)) * cost Γ) ∧
        ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
          pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
              (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hFdiff : Differentiable ℝ (uncurry F) := hFc4.differentiable (by norm_num)
  have hPdiff : Differentiable ℝ P := hPC3.differentiable (by norm_num)
  have hlink : ∀ t u,
      Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u) :=
    fun t u => eta_eq_frontNormalVelocity (δ := δ) Γ hFdiff hF hPdiff hX hnu t u
  have hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0 :=
    fun t ht s => frontNormalVelocity_eq_zero_of_rest Γ hPpos hlink ht s
  -- the front does not move at the marked point, so the base drift vanishes there
  have hdrift : ∀ t, RearBaseDrift.frontBaseDrift (partialTime F) Θ δ t = 0 := by
    intro t
    have hXF : (fun r => Γ.X r 0) = fun r => F r 0 := by
      funext r
      rw [hX r 0, mul_zero]
    have hd := Γ.hasDerivAt_time t 0
    rw [hXF, hmark t] at hd
    simp only [Complex.ofReal_zero, zero_mul] at hd
    have hFdot : partialTime F t 0 = 0 :=
      (hasDerivAt_partialTime hFdiff t 0).unique hd
    exact RearBaseDrift.frontBaseDrift_eq_zero_of_velocity_zero hFdot
  exact RearOwnPathDistIntrinsicDefect.pathDist_and_defect_le_of_front_intrinsic Γ p'
    hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0
      hstrip1 hdper hK hKc hFper hΘper hFc4 hΘc4 hKdper hKdbd hKlip hKtaylor hCK hPC3 hKC3
      hKdC3 hsfinv hlink hFrest hstart hdrift

end RearOwnPathDistSlicesDefect
