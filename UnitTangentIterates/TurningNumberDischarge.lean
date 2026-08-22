import Mathlib
import UnitTangentIterates.TurningNumber
import UnitTangentIterates.ConvexFromTurning
import UnitTangentIterates.ConvexEmbedded

/-!
# Unconditional discharge of the 2π turning number for pinched tube curves

This file formalizes the discharge of the 2π turning number hypothesis for
closed plane curves whose curvature is pinched in a tube `kmin ≤ K ≤ kmax` with
`kmax · L < 4π`.

Under these quantitative bounds, `TurningNumber.turning_eq_two_pi_of_pinched`
shows that the tangent angle unconditionally turns by exactly `2π` over one
period:

```
  Θ(s + L) = Θ(s) + 2π   for all s
```

Combined with `ConvexEmbedded.injOn_Ico_of_turning_one`, this unconditionally
proves that the curve is embedded (simple closed curve).
-/

noncomputable section

open Real Set

namespace TurningNumberDischarge

/-- **Unconditional 2π turning number for pinched curves.**  A regular closed
curve of period `L > 0` with unit tangent `e^{iΘ}` and curvature `K = Θ'`
pinched by `0 < kmin ≤ K ≤ kmax` with `kmax · L < 4π` turns by exactly `2π`
over every period. -/
theorem turning_two_pi_of_tube {X : ℝ → ℂ} {Θ K : ℝ → ℝ} {L kmin kmax : ℝ}
    (hL : 0 < L)
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hth : ∀ s, HasDerivAt Θ (K s) s)
    (hper : Function.Periodic X L)
    (hKc : Continuous K)
    (hkmin : 0 < kmin) (hlow : ∀ s, kmin ≤ K s) (hhigh : ∀ s, K s ≤ kmax)
    (hsmall : kmax * L < 4 * π) (s : ℝ) :
    Θ (s + L) = Θ s + 2 * π :=
  TurningNumber.turning_eq_two_pi_of_pinched hL hX hth hper hKc hkmin hlow hhigh hsmall s

/-- **Unconditional embeddedness for pinched convex curves.**  Any strictly
convex closed curve of period `L` with curvature pinched in `(0, kmax]` with
`kmax · L < 4π` is embedded on every period interval `[a, a + L)`. -/
theorem embedded_of_tube {X : ℝ → ℂ} {Θ K : ℝ → ℝ} {L kmin kmax : ℝ}
    (hL : 0 < L)
    (hX : ∀ s, HasDerivAt X (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hth : ∀ s, HasDerivAt Θ (K s) s)
    (hper : Function.Periodic X L)
    (hKc : Continuous K)
    (hkmin : 0 < kmin) (hlow : ∀ s, kmin ≤ K s) (hhigh : ∀ s, K s ≤ kmax)
    (hsmall : kmax * L < 4 * π)
    (hmono : StrictMono Θ) (a : ℝ) :
    InjOn X (Ico a (a + L)) := by
  have hturn : ∀ s, Θ (s + L) = Θ s + 2 * π := fun s =>
    turning_two_pi_of_tube hL hX hth hper hKc hkmin hlow hhigh hsmall s
  have hcont : Continuous Θ :=
    continuous_iff_continuousAt.mpr fun s => (hth s).differentiableAt.continuousAt
  have hX_speed : ∀ s, HasDerivAt X ((1 : ℝ) • Complex.exp (Complex.I * (Θ s : ℂ))) s := by
    intro s
    simpa using hX s
  have hX_speed' : ∀ s, HasDerivAt X (((1 : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ s : ℂ))) s := by
    intro s
    simpa using hX s
  exact ConvexEmbedded.injOn_Ico_of_turning_one hX_speed' (fun _ => one_pos) hcont hmono hturn hper a

end TurningNumberDischarge
