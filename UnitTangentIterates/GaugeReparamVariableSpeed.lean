import Mathlib
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed

/-!
# A family of unit-speed curves read in a marking is a variable-speed family

The `C²` comparison of the two marked selected inverses needs, besides the
marking defect, a normal path of *variable-speed* slices reaching the curve read
in the gauge marking (`NormalPathC2IncrementVariableSpeed.lean`).  The slices of
that path are the rear curves `Y t` — parametrized by their own arclength, hence
of unit speed and with tangent angle `α t` and curvature `k t` — read in the
gauge marking `Φ`:

```
  X t u = Y t (Φ t u) .
```

This file identifies the eight auxiliary functions of `IsVariableSpeedFamily`
for such a family and reduces the whole hypothesis block to the corresponding
statements about `Φ` and about the geometry of the slices:

* the speed is `g = ∂_uΦ` and the speed derivative is `g_u = ∂²_uΦ`;
* the tangent angle is `θ(t,u) = α(t, Φ(t,u))` and the curvature is
  `κ(t,u) = k(t, Φ(t,u))`, because `∂_uθ = ∂_uΦ · k = g κ`;
* the four time derivatives are those of `∂_uΦ`, of `∂²_uΦ`, of `α ∘ Φ` and of
  `k ∘ Φ`.

Nothing analytic happens here: the content is the chain rule, applied twice, and
the point is that the remaining work — bounding those four time derivatives by
multiples of the cost density — is now stated on the marking and on the frame
data of the slices alone.

Main result: `isVariableSpeedFamily_of_reparam`.
-/

noncomputable section

open Set Function

namespace GaugeReparamVariableSpeed

open NormalPathC2IncrementVariableSpeed

/-- **A family of unit-speed curves read in a marking is a variable-speed
family.**  If `Y t` is parametrized by arclength with tangent angle `α t` and
curvature `k t`, and `Φ` is a marking with first and second parameter
derivatives `Φ_u` and `Φ_uu`, then `X t u = Y t (Φ t u)` is a variable-speed
family with speed `Φ_u`, tangent angle `α ∘ Φ` and curvature `k ∘ Φ`, as soon as
the four time derivatives of those data are bounded by the multiples of the cost
density that `IsVariableSpeedFamily` prescribes. -/
theorem isVariableSpeedFamily_of_reparam
    {Y : ℝ → ℝ → ℂ} {alpha k Phi Phiu Phiuu Phiut Phiuut alphat kappat : ℝ → ℝ → ℝ}
    {m : ℝ → ℝ} {P0 P1 khat G1 Cg : ℝ}
    -- the slices, parametrized by their own arclength
    (hY : ∀ t s, HasDerivAt (Y t) (Complex.exp (Complex.I * (alpha t s : ℂ))) s)
    (halpha : ∀ t s, HasDerivAt (alpha t) (k t s) s)
    -- the marking and its two parameter derivatives
    (hPhiu : ∀ t u, HasDerivAt (Phi t) (Phiu t u) u)
    (hPhiuu : ∀ t u, HasDerivAt (Phiu t) (Phiuu t u) u)
    -- the uniform bounds
    (hg0 : ∀ t u, 0 ≤ Phiu t u) (hg1 : ∀ t u, Phiu t u ≤ P1)
    (hgu : ∀ t u, |Phiuu t u| ≤ G1) (hk : ∀ t u, |k t (Phi t u)| ≤ khat)
    -- the time derivative of the speed
    (hgt : ∀ t u, HasDerivAt (fun r => Phiu r u) (Phiut t u) t)
    (hgtc : ∀ u, Continuous fun t => Phiut t u)
    (hgtbd : ∀ t u, |Phiut t u| ≤ khat * P1 * m t)
    -- the time derivative of the speed derivative
    (hgut : ∀ t u, HasDerivAt (fun r => Phiuu r u) (Phiuut t u) t)
    (hgutc : ∀ u, Continuous fun t => Phiuut t u)
    (hgutbd : ∀ t u, |Phiuut t u| ≤ Cg * m t)
    -- the time derivative of the tangent angle
    (hthetat : ∀ t u, HasDerivAt (fun r => alpha r (Phi r u)) (alphat t u) t)
    (hthetatc : ∀ u, Continuous fun t => alphat t u)
    (hthetatbd : ∀ t u, |alphat t u| ≤ 1 / P0 * m t)
    -- the time derivative of the curvature
    (hkappat : ∀ t u, HasDerivAt (fun r => k r (Phi r u)) (kappat t u) t)
    (hkappatc : ∀ u, Continuous fun t => kappat t u)
    (hkappatbd : ∀ t u, |kappat t u| ≤ (1 / P0 ^ 2 + khat ^ 2) * m t) :
    IsVariableSpeedFamily P0 P1 khat G1 Cg (fun t u => Y t (Phi t u)) m := by
  refine ⟨Phiu, Phiuu, Phiut, Phiuut, fun t u => alpha t (Phi t u),
    fun t u => k t (Phi t u), alphat, kappat, hg0, hg1, hgu, hk, ?_, hPhiuu, ?_,
    hgt, hgtc, hgtbd, hgut, hgutc, hgutbd, hthetat, hthetatc, hthetatbd,
    hkappat, hkappatc, hkappatbd⟩
  · -- the velocity of a slice: the chain rule for `u ↦ Y t (Φ t u)`
    intro t u
    have h := (hY t (Phi t u)).scomp u (hPhiu t u)
    have hsmul : Phiu t u • Complex.exp (Complex.I * (alpha t (Phi t u) : ℂ))
        = (Phiu t u : ℂ) * Complex.exp (Complex.I * (alpha t (Phi t u) : ℂ)) := by
      simp [Complex.real_smul]
    rw [hsmul] at h
    exact h
  · -- the tangent angle of a slice turns at the rate `speed × curvature`
    intro t u
    have h := (halpha t (Phi t u)).comp u (hPhiu t u)
    simpa [mul_comm] using h

end GaugeReparamVariableSpeed
