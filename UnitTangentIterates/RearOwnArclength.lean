import Mathlib
import UnitTangentIterates.SelectedChangeOfVariable
import UnitTangentIterates.RearFamilyFrame

/-!
# The family of rear tracks in its own arclength

The path-metric assembly of the selected inverse
(`GaugePathRearFamily.pathDist_le_of_rear_family`) asks of the family `Y` of
rear tracks that it be

* jointly `C¹`,
* written in its own arclength (unit tangent at every time),
* closing up with the rear period `Q t`, and
* moving with normal velocity the solution of the inverse Jacobi ODE.

This file produces such a family from the front data of the path.  The family
is

`Y(t, x) = R(t, sf(t, x))`,  `R(t, s) = F(t,s) - e^{iΨ(t,s)}`,  `Ψ = Θ - δ`,

with `sf(t, ·)` the inverse of the rear arclength *at the same time* `t`
(`SelectedChangeOfVariable.lean`), so that each slice is written in its own
arclength — as opposed to the family of `RearFamilyFrame.lean`, where a single
reparametrization, that of the reference time, is used for all times.

* `rearOwn` — the family;
* `hasDerivAt_rearOwn_space`, `norm_rearOwn_tangent` — its unit tangent
  `e^{iΨ(t, sf(t,x))}`, so that each slice is written in its own arclength;
* `contDiff_one_rearOwn` — joint `C¹` regularity, from that of the front data
  and of the change of variable;
* `rearOwn_closing` — the closing relation with the rear period
  `Q t = ∫₀^{P t} cos δ(t, ·)`, from the closing relation of the front.
-/

noncomputable section

open Function Set Complex RearTrack ArclengthInverse

namespace RearOwnArclength

variable {F : ℝ → ℝ → ℂ} {Θ δ K dt sf : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {kap : ℝ}

/-- The family of rear tracks, each slice written in its **own** arclength. -/
def rearOwn (F : ℝ → ℝ → ℂ) (Θ δ sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun t x => rearTrack (F t) (Θ t) (δ t) (sf t x)

/-- The rear tangent angle of the family, in its own arclength. -/
def rearOwnAngle (Θ δ sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x => rearAngle (Θ t) (δ t) (sf t x)

/-- The unit tangent of the family. -/
def rearOwnTangent (Θ δ sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun t x => Complex.exp (Complex.I * (rearOwnAngle Θ δ sf t x : ℂ))

/-- **Each slice is written in its own arclength**: the space derivative of the
family is the unit tangent `e^{iΨ}`. -/
theorem hasDerivAt_rearOwn_space
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hδ : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (δ t (sf t x))) x)
    (hcos : ∀ t s, Real.cos (δ t s) ≠ 0) (t x : ℝ) :
    HasDerivAt (rearOwn F Θ δ sf t) (rearOwnTangent Θ δ sf t x) x := by
  have h := (hasDerivAt_rearTrack (F := F t) (Θ := Θ t) (δ := δ t) (K := K t)
    (hF t (sf t x)) (hΘ t (sf t x)) (hδ t (sf t x))).scomp x (hsf t x)
  refine h.congr_deriv ?_
  simp only [rearOwnTangent, rearOwnAngle, Complex.real_smul]
  rw [show ((1 / Real.cos (δ t (sf t x)) : ℝ) : ℂ)
      = 1 / ((Real.cos (δ t (sf t x)) : ℝ) : ℂ) by push_cast; ring]
  have hne : ((Real.cos (δ t (sf t x)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hcos t (sf t x))
  field_simp

/-- The tangent of the family is a unit vector. -/
theorem norm_rearOwn_tangent (t x : ℝ) : ‖rearOwnTangent Θ δ sf t x‖ = 1 := by
  simp [rearOwnTangent, Complex.norm_exp, mul_comm]

/-- The family of rear tracks, in the **front** arclength, is jointly `C¹`. -/
theorem contDiff_one_rearTrackFamily (hFC : ContDiff ℝ 1 (uncurry F))
    (hΘC : ContDiff ℝ 1 (uncurry Θ)) (hδC : ContDiff ℝ 1 (uncurry δ)) :
    ContDiff ℝ 1 (uncurry fun t s => rearTrack (F t) (Θ t) (δ t) s) := by
  have hang : ContDiff ℝ 1 (uncurry fun t s => rearAngle (Θ t) (δ t) s) := by
    simpa [rearAngle, uncurry] using hΘC.sub hδC
  have hexp : ContDiff ℝ 1
      (uncurry fun t s => Complex.exp (Complex.I * (rearAngle (Θ t) (δ t) s : ℂ))) := by
    have hcast : ContDiff ℝ 1 fun p : ℝ × ℝ =>
        (((uncurry fun t s => rearAngle (Θ t) (δ t) s) p : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp hang
    have h : ContDiff ℝ 1 fun p : ℝ × ℝ =>
        Complex.I * (((uncurry fun t s => rearAngle (Θ t) (δ t) s) p : ℝ) : ℂ) :=
      contDiff_const.mul hcast
    simpa [uncurry] using Complex.contDiff_exp.comp h
  simpa [rearTrack, uncurry] using hFC.sub hexp

/-- **The family is jointly `C¹`** as soon as the front data and the change of
variable are. -/
theorem contDiff_one_rearOwn (hFC : ContDiff ℝ 1 (uncurry F))
    (hΘC : ContDiff ℝ 1 (uncurry Θ)) (hδC : ContDiff ℝ 1 (uncurry δ))
    (hsfC : ContDiff ℝ 1 (uncurry sf)) :
    ContDiff ℝ 1 (uncurry (rearOwn F Θ δ sf)) := by
  have hR := contDiff_one_rearTrackFamily hFC hΘC hδC
  have hcomp : ContDiff ℝ 1 fun p : ℝ × ℝ => (p.1, uncurry sf p) :=
    contDiff_fst.prodMk hsfC
  simpa [rearOwn, uncurry, Function.comp_def] using hR.comp hcomp

/-- **The closing relation of the family.**  If the front closes up with period
`P t` — the front track being `P t`-periodic, the steering angle `P t`-periodic
and the tangent angle increasing by `2π` — then each slice of the family closes
up with the rear period `Q t = ∫₀^{P t} cos δ(t, ·)`. -/
theorem rearOwn_closing (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hdc : ∀ t, Continuous (δ t))
    (hstrip0 : ∀ t s, 0 ≤ δ t s) (hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kap)
    (hdper : ∀ t, Function.Periodic (δ t) (P t))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi) (t x : ℝ) :
    rearOwn F Θ δ sf t (x + rearArclength (δ t) (P t)) = rearOwn F Θ δ sf t x := by
  have hshift : sf t (x + rearArclength (δ t) (P t)) = sf t x + P t :=
    SelectedPathData.sf_add_rearPeriod hkap0 hkap1 (hdc t) (hstrip0 t) (hstrip1 t)
      (hdper t) (hsfinv t) x
  simp only [rearOwn, rearTrack, hshift]
  rw [hFper t (sf t x),
    rearTangent_periodic (Θ := Θ t) (δ := δ t) (hdper t) (hΘper t) (sf t x)]

end RearOwnArclength
