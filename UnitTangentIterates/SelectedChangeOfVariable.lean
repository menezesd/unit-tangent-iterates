import Mathlib
import UnitTangentIterates.ParametricPrimitive
import UnitTangentIterates.GlobalInverseSmooth
import UnitTangentIterates.SelectedPathData

/-!
# The change of variable of the selected inverse, along a path of fronts

Along a path of fronts the rear tracks are written in the rear arclength

`A(t, s) = ∫₀ˢ cos δ(t, u) du`

of the *same* time, and the family of rears in its own arclength is obtained by
composing with the inverse `sf(t, ·)` of `A(t, ·)`.  This file proves that both
are as regular as the steering family:

* `contDiff_one_rearArclengthFamily` — `A` is jointly `C¹` as soon as the
  steering angle is jointly continuous with a jointly continuous time
  derivative;
* `contDiff_one_sf` — the family of inverses is then jointly `C¹` (the space
  derivative of `A` being `cos δ ≥ √(1-κ̂²) > 0` on the selected strip);
* `hasDerivAt_sf_space` — its space derivative is `sec δ`;
* `exists_sf_family` — such a family of inverses always exists.
-/

noncomputable section

open Function Set MeasureTheory intervalIntegral RearTrack ArclengthInverse

namespace SelectedChangeOfVariable

variable {delta dt : ℝ → ℝ → ℝ} {kap : ℝ}

/-- The time derivative of the rear speed `cos δ`. -/
def cosTimeDeriv (delta dt : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t u => -Real.sin (delta t u) * dt t u

theorem continuous_cos_delta (hdc : Continuous (uncurry delta)) :
    Continuous (uncurry fun t u => Real.cos (delta t u)) :=
  Real.continuous_cos.comp hdc

theorem continuous_cosTimeDeriv (hdc : Continuous (uncurry delta))
    (hdtc : Continuous (uncurry dt)) : Continuous (uncurry (cosTimeDeriv delta dt)) :=
  ((Real.continuous_sin.comp hdc).neg).mul hdtc

theorem hasDerivAt_cos_delta (hdt : ∀ t s, HasDerivAt (fun r => delta r s) (dt t s) t)
    (t u : ℝ) :
    HasDerivAt (fun r => Real.cos (delta r u)) (cosTimeDeriv delta dt t u) t :=
  (hdt t u).cos

/-- The rear arclength of the family, as a function of the two variables. -/
theorem rearArclength_eq (t s : ℝ) :
    rearArclength (delta t) s = ∫ u in (0:ℝ)..s, Real.cos (delta t u) := rfl

/-- **The rear arclength of a `C¹` family of steering angles is jointly
`C¹`.** -/
theorem contDiff_one_rearArclengthFamily (hdc : Continuous (uncurry delta))
    (hdt : ∀ t s, HasDerivAt (fun r => delta r s) (dt t s) t)
    (hdtc : Continuous (uncurry dt)) :
    ContDiff ℝ 1 (uncurry fun t s => rearArclength (delta t) s) :=
  ParametricPrimitive.contDiff_one_primitive (continuous_cos_delta hdc)
    (hasDerivAt_cos_delta hdt) (continuous_cosTimeDeriv hdc hdtc)

/-- The time derivative of the rear arclength, under the integral sign. -/
theorem hasDerivAt_rearArclength_time (hdc : Continuous (uncurry delta))
    (hdt : ∀ t s, HasDerivAt (fun r => delta r s) (dt t s) t)
    (hdtc : Continuous (uncurry dt)) (t s : ℝ) :
    HasDerivAt (fun r => rearArclength (delta r) s)
      (∫ u in (0:ℝ)..s, cosTimeDeriv delta dt t u) t :=
  ParametricPrimitive.hasDerivAt_primitive_param (continuous_cos_delta hdc)
    (hasDerivAt_cos_delta hdt) (continuous_cosTimeDeriv hdc hdtc) t s

/-- The space derivative of the rear arclength is the rear speed. -/
theorem hasDerivAt_rearArclength_space (hdc : Continuous (uncurry delta)) (t s : ℝ) :
    HasDerivAt (fun y => rearArclength (delta t) y) (Real.cos (delta t s)) s :=
  ParametricPrimitive.hasDerivAt_primitive_space (continuous_cos_delta hdc) t s

/-- **The family of inverses of the rear arclength is jointly `C¹`.**  On the
selected strip `0 ≤ δ ≤ arcsin κ̂` with `κ̂ < 1`, the change of variable from
the rear to the front arclength inherits the regularity of the steering
family. -/
theorem contDiff_one_sf (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hdc : Continuous (uncurry delta))
    (hdt : ∀ t s, HasDerivAt (fun r => delta r s) (dt t s) t)
    (hdtc : Continuous (uncurry dt))
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kap)
    {sf : ℝ → ℝ → ℝ} (hsf : ∀ t x, rearArclength (delta t) (sf t x) = x) :
    ContDiff ℝ 1 (uncurry sf) := by
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  refine GlobalInverseSmooth.contDiff_one_inverse_family
    (A := fun t s => rearArclength (delta t) s)
    (At := fun t s => ∫ u in (0:ℝ)..s, cosTimeDeriv delta dt t u)
    (a := fun t s => Real.cos (delta t s)) hcpos
    (hasDerivAt_rearArclength_time hdc hdt hdtc)
    (hasDerivAt_rearArclength_space hdc) ?_ (continuous_cos_delta hdc)
    (fun t s => Shadowing.cos_ge_of_mem_strip (hstrip0 t s) (hstrip1 t s)) hsf
  exact continuous_parametric_primitive_of_continuous (f := cosTimeDeriv delta dt) (a₀ := 0)
    (continuous_cosTimeDeriv hdc hdtc)

/-- The space derivative of the change of variable is `sec δ`. -/
theorem hasDerivAt_sf_space (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hdc : Continuous (uncurry delta))
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kap)
    {sf : ℝ → ℝ → ℝ} (hsf : ∀ t x, rearArclength (delta t) (sf t x) = x) (t x : ℝ) :
    HasDerivAt (sf t) (1 / Real.cos (delta t (sf t x))) x := by
  have hcpos : 0 < Real.sqrt (1 - kap ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  exact hasDerivAt_of_rightInverse hcpos (hasDerivAt_rearArclength_space hdc t)
    (fun s => Shadowing.cos_ge_of_mem_strip (hstrip0 t s) (hstrip1 t s)) (hsf t) x

/-- **A family of inverses of the rear arclength always exists**, so assuming
one is no restriction. -/
theorem exists_sf_family (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hdc : Continuous (uncurry delta))
    (hstrip0 : ∀ t s, 0 ≤ delta t s) (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kap) :
    ∃ sf : ℝ → ℝ → ℝ, ∀ t x, rearArclength (delta t) (sf t x) = x := by
  have hslice : ∀ t : ℝ, ∃ f : ℝ → ℝ, ∀ x, rearArclength (delta t) (f x) = x := by
    intro t
    exact exists_inverse_rearArclength hkap0 hkap1
      (hdc.comp (continuous_const.prodMk continuous_id)) (hstrip0 t) (hstrip1 t)
  choose f hf using hslice
  exact ⟨f, hf⟩

end SelectedChangeOfVariable
