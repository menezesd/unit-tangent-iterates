import Mathlib
import UnitTangentIterates.SelInvFrontMotionC2
import UnitTangentIterates.SelInvPerimBound

/-!
# The admissible paths of the pinched pseudometric are stationary

This file analyses the class of paths `SelInvTubePathDist.IsPinchedPath` — the
paths over which the pinched pseudodistance `PinchedPathBasic.pinchedDist` is
taken, and the hypothesis block of the `C²` selected-inverse estimate — and
shows that it is **rigid**.

Three of its conditions are in conflict.  A `PathMetric.NormalPath` moves in
normal gauge, `X_t = η ν`; `IsPinchedPath` asks in addition that every slice
have constant speed in the path parameter (`speed`) and that the marked point
be at rest (`rest`).  Equality of the mixed partial derivatives of `X` gives
the classical speed equation

```
  ∂_t |X_u| = - κ η |X_u| ,
```

so a family whose speed does not depend on the point has `κ η` independent of
the point as well (`eta_mul_curv_eq`).  If moreover the marked point is at
rest, then `κ η ≡ 0`, and since the curvature of the slices of an admissible
path is bounded below by `kminP > 0`, the normal velocity vanishes identically:
the path does not move at all (`eta_eq_zero`, `X_eq_of_isPinchedPath`).

Consequently an admissible path joins a marked curve to itself
(`curve_eq_of_isPinchedPath`, `eq_of_isPinchedPath`), the pinched pseudodistance
is `0` whenever it is taken over a nonempty set of paths, and the Lipschitz
estimates stated against it — `PinchedPathMetric.dist_selInv_le_pinchedDist`,
`SelInvPerimBound.dist_selInv_le_pinchedDist_universal` and the `C²` estimate
`SelInvPathTubeBaseC2.dist_selInv_le_modulus_of_path_tube_base_C2` itself — are
true but empty: both of their sides vanish
(`dist_selInv_eq_zero_of_isPinchedPath`).

The conflict is one of conventions rather than of mathematics: the paper's
paths are written in normal gauge in a *transported* periodic parameter, which
is in general not proportional to arclength, while the constant-speed condition
belongs to the arclength normalization.  The two coexist only for a family that
does not move (or, without the marked point at rest, only for the
one-parameter family of motions with `η = -(log P)'/κ`, by `eta_mul_curv_eq`).

Main results: `eta_mul_curv_eq`, `eta_eq_zero`, `X_eq_of_isPinchedPath`,
`curve_eq_of_isPinchedPath`, `eq_of_isPinchedPath`,
`dist_selInv_eq_zero_of_isPinchedPath`, `pinchedDist_eq_zero`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath

namespace PinchedPathRigidity

open RearOwnHigherRegularity FrontFromPath SelInvPathRegularityC2
  SelInvPathCurvatureC2 SelInvPathPerimC2 SelInvTubePathDist SelInvFrontMotionC2
  PinchedPath

variable {p q : Data} {kminP kh : ℝ}

/-! ### The normal rate of a path, as a function of its curve alone -/

/-- The **normal rate** `w = η/P` of a normal path, written directly in terms of
the moving curve.  Unlike the field `η` of the structure, this expression is as
regular as the family, which is what lets it be differentiated in the
parameter. -/
def normalRate (Γ : NormalPath p q) : ℝ → ℝ → ℝ := fun t u =>
  ((pathVel Γ.X t u).re * (partialTime Γ.X t u).im
      - (pathVel Γ.X t u).im * (partialTime Γ.X t u).re)
    / Complex.normSq (pathVel Γ.X t u)

/-- The parameter derivative of the family is the normal velocity times the
unit normal. -/
theorem partialTime_eq (Γ : NormalPath p q) (hX : Differentiable ℝ (uncurry Γ.X)) (t u : ℝ) :
    partialTime Γ.X t u = (Γ.eta t u : ℂ) * Γ.nu t u :=
  (hasDerivAt_partialTime hX t u).unique (Γ.hasDerivAt_time t u)

/-- The parameter derivative of the family, with the unit normal read off from
the velocity: `X_t = (η/P) · (i · X_u)`. -/
theorem partialTime_eq_ratio (Γ : NormalPath p q) (hX : Differentiable ℝ (uncurry Γ.X))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hP : ∀ t, pathPerim Γ.X t ≠ 0) (t u : ℝ) :
    partialTime Γ.X t u
      = ((Γ.eta t u / pathPerim Γ.X t : ℝ) : ℂ) * (Complex.I * pathVel Γ.X t u) := by
  have hpt := partialTime_eq Γ hX t u
  rw [hnu t u] at hpt
  have hPc : ((pathPerim Γ.X t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP t
  rw [hpt]
  push_cast
  field_simp

/-- **The normal rate is `η/P`.** -/
theorem normalRate_eq (Γ : NormalPath p q) (hX : Differentiable ℝ (uncurry Γ.X))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hP : ∀ t, pathPerim Γ.X t ≠ 0) (hV : ∀ t u, pathVel Γ.X t u ≠ 0) (t u : ℝ) :
    normalRate Γ t u = Γ.eta t u / pathPerim Γ.X t := by
  have hns : Complex.normSq (pathVel Γ.X t u) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hV t u
  have hnum : ((pathVel Γ.X t u).re * (partialTime Γ.X t u).im
        - (pathVel Γ.X t u).im * (partialTime Γ.X t u).re)
      = (Γ.eta t u / pathPerim Γ.X t) * Complex.normSq (pathVel Γ.X t u) := by
    rw [partialTime_eq_ratio Γ hX hnu hP t u]
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring
  unfold normalRate
  rw [hnum]
  field_simp

/-- With the unit normal read off from the velocity, the parameter derivative is
`w · (i · X_u)`. -/
theorem partialTime_eq_normalRate (Γ : NormalPath p q) (hX : Differentiable ℝ (uncurry Γ.X))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hP : ∀ t, pathPerim Γ.X t ≠ 0) (hV : ∀ t u, pathVel Γ.X t u ≠ 0) (t u : ℝ) :
    partialTime Γ.X t u
      = ((normalRate Γ t u : ℝ) : ℂ) * (Complex.I * pathVel Γ.X t u) := by
  rw [normalRate_eq Γ hX hnu hP hV t u, partialTime_eq_ratio Γ hX hnu hP t u]

/-! ### Regularity of the normal rate -/

section Smooth

variable (Γ : NormalPath p q)

theorem contDiff_pathVel (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X)) :
    ContDiff ℝ (1 : ℕ) (uncurry (pathVel Γ.X)) := contDiff_partialArc_self (n := 1) hX

theorem contDiff_partialTime_X (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X)) :
    ContDiff ℝ (1 : ℕ) (uncurry (partialTime Γ.X)) := contDiff_partialTime_self (n := 1) hX

/-- **The normal rate of a `C²` family is differentiable**, the field `η` of the
structure being recovered from the curve by an explicit formula. -/
theorem differentiable_normalRate (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X))
    (hV : ∀ t u, pathVel Γ.X t u ≠ 0) :
    Differentiable ℝ (uncurry (normalRate Γ)) := by
  have hVd : Differentiable ℝ (uncurry (pathVel Γ.X)) :=
    (contDiff_pathVel Γ hX).differentiable (by norm_num)
  have hPd : Differentiable ℝ (uncurry (partialTime Γ.X)) :=
    (contDiff_partialTime_X Γ hX).differentiable (by norm_num)
  have hre : Differentiable ℝ (fun z : ℝ × ℝ => (uncurry (pathVel Γ.X) z).re) :=
    Complex.reCLM.differentiable.comp hVd
  have him : Differentiable ℝ (fun z : ℝ × ℝ => (uncurry (pathVel Γ.X) z).im) :=
    Complex.imCLM.differentiable.comp hVd
  have hre' : Differentiable ℝ (fun z : ℝ × ℝ => (uncurry (partialTime Γ.X) z).re) :=
    Complex.reCLM.differentiable.comp hPd
  have him' : Differentiable ℝ (fun z : ℝ × ℝ => (uncurry (partialTime Γ.X) z).im) :=
    Complex.imCLM.differentiable.comp hPd
  have hne : ∀ z : ℝ × ℝ, (uncurry (pathVel Γ.X) z).re * (uncurry (pathVel Γ.X) z).re
      + (uncurry (pathVel Γ.X) z).im * (uncurry (pathVel Γ.X) z).im ≠ 0 := by
    rintro ⟨t, u⟩
    have h := hV t u
    have : Complex.normSq (pathVel Γ.X t u) ≠ 0 := by
      simpa [Complex.normSq_eq_zero] using h
    simpa [Complex.normSq_apply, Function.uncurry] using this
  have heq : uncurry (normalRate Γ) = fun z : ℝ × ℝ =>
      ((uncurry (pathVel Γ.X) z).re * (uncurry (partialTime Γ.X) z).im
          - (uncurry (pathVel Γ.X) z).im * (uncurry (partialTime Γ.X) z).re)
        / ((uncurry (pathVel Γ.X) z).re * (uncurry (pathVel Γ.X) z).re
          + (uncurry (pathVel Γ.X) z).im * (uncurry (pathVel Γ.X) z).im) := by
    funext z
    obtain ⟨t, u⟩ := z
    simp [normalRate, Complex.normSq_apply, Function.uncurry]
  rw [heq]
  intro z
  have hnum : DifferentiableAt ℝ (fun z : ℝ × ℝ =>
      (uncurry (pathVel Γ.X) z).re * (uncurry (partialTime Γ.X) z).im
        - (uncurry (pathVel Γ.X) z).im * (uncurry (partialTime Γ.X) z).re) z :=
    ((hre z).mul (him' z)).sub ((him z).mul (hre' z))
  have hden : DifferentiableAt ℝ (fun z : ℝ × ℝ =>
      (uncurry (pathVel Γ.X) z).re * (uncurry (pathVel Γ.X) z).re
        + (uncurry (pathVel Γ.X) z).im * (uncurry (pathVel Γ.X) z).im) z :=
    ((hre z).mul (hre z)).add ((him z).mul (him z))
  simpa [div_eq_mul_inv] using hnum.mul (hden.inv (hne z))

theorem hasDerivAt_normalRate (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X))
    (hV : ∀ t u, pathVel Γ.X t u ≠ 0) (t u : ℝ) :
    HasDerivAt (normalRate Γ t) (partialArc (normalRate Γ) t u) u :=
  hasDerivAt_partialArc (differentiable_normalRate Γ hX hV) t u

/-! ### Clairaut's theorem for the family -/

/-- **The parameter derivative of the velocity.**  Differentiating
`X_t = w · (i X_u)` in the parameter and using the symmetry of the mixed partial
derivatives. -/
theorem partialTime_pathVel_eq (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hP : ∀ t, pathPerim Γ.X t ≠ 0) (hV : ∀ t u, pathVel Γ.X t u ≠ 0) (t u : ℝ) :
    partialTime (pathVel Γ.X) t u
      = ((partialArc (normalRate Γ) t u : ℝ) : ℂ) * (Complex.I * pathVel Γ.X t u)
        + ((normalRate Γ t u : ℝ) : ℂ) * (Complex.I * pathAcc Γ.X t u) := by
  have hXd : Differentiable ℝ (uncurry Γ.X) := hX.differentiable (by norm_num)
  have hVd : Differentiable ℝ (uncurry (pathVel Γ.X)) :=
    (contDiff_pathVel Γ hX).differentiable (by norm_num)
  have hclair : HasDerivAt (partialTime Γ.X t) (partialTime (pathVel Γ.X) t u) u :=
    hasDerivAt_partialTime_arc (f := Γ.X) (fx := pathVel Γ.X) (by exact_mod_cast hX)
      (fun t' s => hasDerivAt_partialArc hXd t' s) t u
  have hfun : partialTime Γ.X t
      = fun v => ((normalRate Γ t v : ℝ) : ℂ) * (Complex.I * pathVel Γ.X t v) :=
    funext (fun v => partialTime_eq_normalRate Γ hXd hnu hP hV t v)
  rw [hfun] at hclair
  have h1 : HasDerivAt (fun v => ((normalRate Γ t v : ℝ) : ℂ))
      ((partialArc (normalRate Γ) t u : ℝ) : ℂ) u :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_normalRate Γ hX hV t u)
  have h2 : HasDerivAt (fun v => Complex.I * pathVel Γ.X t v)
      (Complex.I * pathAcc Γ.X t u) u :=
    (hasDerivAt_partialArc hVd t u).const_mul Complex.I
  exact hclair.unique (h1.mul h2)

/-- The parameter derivative of the squared speed. -/
theorem hasDerivAt_normSq_pathVel (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X)) (t u : ℝ) :
    HasDerivAt (fun r => Complex.normSq (pathVel Γ.X r u))
      (2 * ((pathVel Γ.X t u).re * (partialTime (pathVel Γ.X) t u).re
          + (pathVel Γ.X t u).im * (partialTime (pathVel Γ.X) t u).im)) t := by
  have hVd : Differentiable ℝ (uncurry (pathVel Γ.X)) :=
    (contDiff_pathVel Γ hX).differentiable (by norm_num)
  have hd : HasDerivAt (fun r => pathVel Γ.X r u) (partialTime (pathVel Γ.X) t u) t :=
    hasDerivAt_partialTime hVd t u
  have hre : HasDerivAt (fun r => (pathVel Γ.X r u).re)
      ((partialTime (pathVel Γ.X) t u).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have him : HasDerivAt (fun r => (pathVel Γ.X r u).im)
      ((partialTime (pathVel Γ.X) t u).im) t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
  have h := (hre.mul hre).add (him.mul him)
  have heq : (fun r => Complex.normSq (pathVel Γ.X r u))
      = fun r => (pathVel Γ.X r u).re * (pathVel Γ.X r u).re
        + (pathVel Γ.X r u).im * (pathVel Γ.X r u).im := by
    funext r; simp [Complex.normSq_apply]
  rw [heq]
  convert h using 1
  ring

end Smooth

/-! ### The speed equation -/

/-- The imaginary part of `conj X_u · X_{uu}` is the curvature times the cube of
the speed. -/
theorem im_eq_pathKn (Γ : NormalPath p q) (hP : ∀ t, pathPerim Γ.X t ≠ 0) (t σ : ℝ) :
    ((starRingEnd ℂ) (pathVel Γ.X t σ) * pathAcc Γ.X t σ).im
      = pathKn Γ.X (pathPerim Γ.X) t σ * pathPerim Γ.X t ^ 3 := by
  unfold pathKn curvOfPath
  rw [mul_div_cancel_right₀ _ (hP t)]
  field_simp
  rw [mul_div_assoc, div_self (hP t), mul_one]

/-- The parameter derivative of the squared speed, in terms of the normal rate
and the curvature: this is the speed equation `∂_t|X_u|² = -2 κ η |X_u|²`. -/
theorem deriv_normSq_eq (Γ : NormalPath p q) (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hP : ∀ t, pathPerim Γ.X t ≠ 0) (hV : ∀ t u, pathVel Γ.X t u ≠ 0) (t u : ℝ) :
    2 * ((pathVel Γ.X t u).re * (partialTime (pathVel Γ.X) t u).re
        + (pathVel Γ.X t u).im * (partialTime (pathVel Γ.X) t u).im)
      = -(2 * (normalRate Γ t u
          * ((starRingEnd ℂ) (pathVel Γ.X t u) * pathAcc Γ.X t u).im)) := by
  rw [partialTime_pathVel_eq Γ hX hnu hP hV t u]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **The mixed-partial identity.**  For a family whose slices all have the same
speed, the product of the normal velocity with the curvature does not depend on
the point. -/
theorem eta_mul_curv_eq (Γ : NormalPath p q) (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X))
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hslit : ∀ t, pathVel Γ.X t 0 ≠ 0) (t u : ℝ) :
    Γ.eta t u * pathKn Γ.X (pathPerim Γ.X) t u
      = Γ.eta t 0 * pathKn Γ.X (pathPerim Γ.X) t 0 := by
  have hXd : Differentiable ℝ (uncurry Γ.X) := hX.differentiable (by norm_num)
  have hP : ∀ t, pathPerim Γ.X t ≠ 0 := fun t => by
    simpa [pathPerim, norm_ne_zero_iff] using hslit t
  have hV : ∀ t v, pathVel Γ.X t v ≠ 0 := by
    intro t v
    have h := hconst t v
    have : ‖pathVel Γ.X t v‖ ≠ 0 := by
      rw [h]; simpa [norm_ne_zero_iff] using hslit t
    simpa [norm_ne_zero_iff] using this
  -- the squared speed is the same function of the time at `u` and at `0`
  have hfun : (fun r => Complex.normSq (pathVel Γ.X r u))
      = fun r => Complex.normSq (pathVel Γ.X r 0) := by
    funext r
    have h := hconst r u
    have h1 : Complex.normSq (pathVel Γ.X r u) = ‖pathVel Γ.X r u‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    have h2 : Complex.normSq (pathVel Γ.X r 0) = ‖pathVel Γ.X r 0‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    rw [h1, h2, h]
  have h1 := hasDerivAt_normSq_pathVel Γ hX t u
  rw [hfun] at h1
  have h2 := hasDerivAt_normSq_pathVel Γ hX t 0
  have hderiv := h1.unique h2
  rw [deriv_normSq_eq Γ hX hnu hP hV t u, deriv_normSq_eq Γ hX hnu hP hV t 0] at hderiv
  -- rewrite both sides in terms of `η` and the curvature
  have hw : ∀ v, normalRate Γ t v = Γ.eta t v / pathPerim Γ.X t :=
    fun v => normalRate_eq Γ hXd hnu hP hV t v
  rw [hw u, hw 0, im_eq_pathKn Γ hP t u, im_eq_pathKn Γ hP t 0] at hderiv
  have hPpos : (0 : ℝ) < pathPerim Γ.X t ^ 2 := by
    have := hP t
    positivity
  have hkey : Γ.eta t u * pathKn Γ.X (pathPerim Γ.X) t u * pathPerim Γ.X t ^ 2
      = Γ.eta t 0 * pathKn Γ.X (pathPerim Γ.X) t 0 * pathPerim Γ.X t ^ 2 := by
    field_simp at hderiv
    nlinarith [hderiv, hP t]
  exact mul_right_cancel₀ (ne_of_gt hPpos) hkey

/-! ### Rigidity of the admissible paths -/

/-- **A constant-speed normal path of positively curved slices whose marked
point is at rest does not move.**  These are exactly the hypotheses that the
`C²` selected-inverse estimate
`SelInvPathTubeBaseC2.dist_selInv_le_modulus_of_path_tube_base_C2` places on the
path: the speed equation makes `κ η` vanish identically, and the curvature is
bounded below by `kminP > 0`. -/
theorem eta_eq_zero_of_speed_rest {Γ : NormalPath p q} (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X))
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hkminP : 0 < kminP)
    (hKnmin : ∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ)
    (hslit : ∀ t, pathVel Γ.X t 0 ≠ 0) (hmark : ∀ t, Γ.eta t 0 = 0) (t u : ℝ) :
    Γ.eta t u = 0 := by
  have hkey := eta_mul_curv_eq Γ hX hconst hnu hslit t u
  rw [hmark t, zero_mul] at hkey
  have hkpos : 0 < pathKn Γ.X (pathPerim Γ.X) t u := lt_of_lt_of_le hkminP (hKnmin t u)
  rcases mul_eq_zero.1 hkey with h | h
  · exact h
  · exact absurd h (ne_of_gt hkpos)

/-- **An admissible path does not move.**  The marked point is at rest, so the
speed equation makes `κ η` vanish identically, and the curvature of the slices is
bounded below by `kminP > 0`. -/
theorem eta_eq_zero {Γ : NormalPath p q} (hΓ : IsPinchedPath kminP kh Γ)
    (hkminP : 0 < kminP) (t u : ℝ) : Γ.eta t u = 0 :=
  eta_eq_zero_of_speed_rest (hΓ.smooth.of_le (by norm_num)) hΓ.speed hΓ.normal hkminP hΓ.kmin
    (fun t => Complex.slitPlane_ne_zero (hΓ.slit t)) hΓ.rest t u

/-- A normal path whose normal velocity vanishes is stationary. -/
theorem X_eq_of_eta_eq_zero {Γ : NormalPath p q} (heta : ∀ t u, Γ.eta t u = 0) (t u : ℝ) :
    Γ.X t u = Γ.X 0 u := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r' => Γ.X r' u) 0 r := by
    intro r
    have h := Γ.hasDerivAt_time r u
    rwa [heta r u, Complex.ofReal_zero, zero_mul] at h
  have hdiff : Differentiable ℝ (fun r' => Γ.X r' u) := fun r => (hd r).differentiableAt
  have hderiv : ∀ r : ℝ, deriv (fun r' => Γ.X r' u) r = 0 := fun r => (hd r).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv t 0

/-- **The curve of an admissible path is the same at every time.** -/
theorem X_eq_of_isPinchedPath {Γ : NormalPath p q} (hΓ : IsPinchedPath kminP kh Γ)
    (hkminP : 0 < kminP) (t u : ℝ) : Γ.X t u = Γ.X 0 u :=
  X_eq_of_eta_eq_zero (fun r v => eta_eq_zero hΓ hkminP r v) t u

/-- **The two ends of a constant-speed normal path of positively curved slices
whose marked point is at rest carry the same curve.**  This is the hypothesis
block of the `C²` selected-inverse estimate. -/
theorem curve_eq_of_speed_rest {Γ : NormalPath p q} (hX : ContDiff ℝ (2 : ℕ) (uncurry Γ.X))
    (hconst : ∀ t u, ‖(pathVel Γ.X) t u‖ = ‖pathVel Γ.X t 0‖)
    (hnu : ∀ t u, Γ.nu t u = Complex.I * ((pathVel Γ.X) t u / ((pathPerim Γ.X) t : ℂ)))
    (hkminP : 0 < kminP)
    (hKnmin : ∀ t σ, kminP ≤ pathKn Γ.X (pathPerim Γ.X) t σ)
    (hslit : ∀ t, pathVel Γ.X t 0 ≠ 0) (hmark : ∀ t, Γ.eta t 0 = 0) :
    (p.1 : ℝ → ℂ) = q.1 := by
  funext u
  have hstat := X_eq_of_eta_eq_zero
    (fun r v => eta_eq_zero_of_speed_rest hX hconst hnu hkminP hKnmin hslit hmark r v)
  rw [← Γ.start u, ← Γ.finish u, hstat Γ.T u]

/-- **The two ends of an admissible path carry the same curve.** -/
theorem curve_eq_of_isPinchedPath {Γ : NormalPath p q} (hΓ : IsPinchedPath kminP kh Γ)
    (hkminP : 0 < kminP) : (p.1 : ℝ → ℂ) = q.1 := by
  funext u
  have h0 : Γ.X 0 u = p.1 u := Γ.start u
  have hT : Γ.X Γ.T u = q.1 u := Γ.finish u
  rw [← h0, ← hT, X_eq_of_isPinchedPath hΓ hkminP Γ.T u]

/-- **The two ends of an admissible path are the same marked curve**, once the
velocity and the acceleration are the derivatives of the curve. -/
theorem eq_of_isPinchedPath {Γ : NormalPath p q} (hΓ : IsPinchedPath kminP kh Γ)
    (hkminP : 0 < kminP)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u) (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u) (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u) :
    p = q := by
  have h1 : (p.1 : ℝ → ℂ) = q.1 := curve_eq_of_isPinchedPath hΓ hkminP
  have h21 : (p.2.1 : ℝ → ℂ) = q.2.1 := by
    funext u
    have hp := hpd u
    rw [h1] at hp
    exact hp.unique (hqd u)
  have h22 : (p.2.2 : ℝ → ℂ) = q.2.2 := by
    funext u
    have hp := hpd2 u
    rw [h21] at hp
    exact hp.unique (hqd2 u)
  have e1 : p.1 = q.1 := DFunLike.ext _ _ (congrFun h1)
  have e21 : p.2.1 = q.2.1 := DFunLike.ext _ _ (congrFun h21)
  have e22 : p.2.2 = q.2.2 := DFunLike.ext _ _ (congrFun h22)
  exact Prod.ext e1 (Prod.ext e21 e22)

/-! ### The estimates stated against the pinched pseudometric are empty -/

/-- **The pinched pseudodistance only ever compares a marked curve with
itself.**  If some admissible path joins `p` to `q`, the two carry the same
curve. -/
theorem curve_eq_of_pinchedSet_nonempty (hkminP : 0 < kminP)
    (hne : (pinchedSet kminP kh p q).Nonempty) : (p.1 : ℝ → ℂ) = q.1 := by
  obtain ⟨c, Γ, -, hΓ⟩ := hne
  exact curve_eq_of_isPinchedPath hΓ hkminP

/-- **Both sides of the Lipschitz estimate vanish.**  Whenever the set of
admissible paths joining the two marked curves is nonempty, and the two carry
their velocity and acceleration as derivatives, the two marked selected inverses
coincide and the pinched pseudodistance is zero. -/
theorem dist_selInv_eq_zero_of_pinchedSet (hkminP : 0 < kminP)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u) (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u) (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u)
    (hne : (pinchedSet kminP kh p q).Nonempty) :
    dist (SelectedInverseMap.selInv kh q) (SelectedInverseMap.selInv kh p) = 0
      ∧ pinchedDist kminP kh p q = 0 := by
  obtain ⟨c, Γ, -, hΓ⟩ := hne
  have hpq : p = q := eq_of_isPinchedPath hΓ hkminP hpd hpd2 hqd hqd2
  subst hpq
  refine ⟨by simp, ?_⟩
  exact pinchedDist_self (PinchedPath.isPinchedCurve_start hΓ)

/-- **The pinched pseudodistance vanishes identically.**  Either no admissible
path joins the two marked curves, and the infimum is taken over the empty set,
or one does, and then the two curves agree and the constant path witnesses the
value zero.  So the pseudometric of `PinchedPathBasic.lean` carries no
information, and the Lipschitz estimates stated against it are empty. -/
theorem pinchedDist_eq_zero (hkminP : 0 < kminP)
    (hpd : ∀ u, HasDerivAt (⇑p.1) (p.2.1 u) u) (hpd2 : ∀ u, HasDerivAt (⇑p.2.1) (p.2.2 u) u)
    (hqd : ∀ u, HasDerivAt (⇑q.1) (q.2.1 u) u) (hqd2 : ∀ u, HasDerivAt (⇑q.2.1) (q.2.2 u) u) :
    pinchedDist kminP kh p q = 0 := by
  rcases eq_empty_or_nonempty (pinchedSet kminP kh p q) with h | h
  · rw [pinchedDist, h, Real.sInf_empty]
  · exact (dist_selInv_eq_zero_of_pinchedSet hkminP hpd hpd2 hqd hqd2 h).2

end PinchedPathRigidity
