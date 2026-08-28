import Mathlib
import UnitTangentIterates.InterpolationGauge
import UnitTangentIterates.ParametricPrimitiveSmooth

/-!
# Higher joint regularity of curvature interpolation

The normal-gauge construction needs substantially more than the joint `C¹`
statement supplied by `InterpolationGauge.lean` when it is used as input to
the selected-rear estimates.  This file upgrades the explicit reconstruction:
if both endpoint curvatures are `C^(n+1)`, then the interpolated tangent angle
and the reconstructed front are jointly `C^(n+1)` in interpolation time and
arclength.

`ParametricPrimitiveSmooth` is real-valued.  The only extra point needed here
is that its result applies componentwise to a complex family; the two
component primitives reassemble to the complex interval integral.
-/

noncomputable section

open Function MeasureTheory intervalIntegral

namespace InterpolationSmooth

open CurvatureInterpolation

variable {k0 k1 : ℝ → ℝ} {theta0 L : ℝ}

/-- The affine interpolation of two `C^(n+1)` curvatures is jointly
`C^(n+1)` in its interpolation parameter and arclength. -/
theorem contDiff_succ_uncurry_kappaInterp {n : ℕ}
    (hk0 : ContDiff ℝ ((n : ℕ) + 1) k0)
    (hk1 : ContDiff ℝ ((n : ℕ) + 1) k1) :
    ContDiff ℝ ((n : ℕ) + 1)
      (fun p : ℝ × ℝ => kappaInterp k0 k1 p.1 p.2) := by
  simp only [kappaInterp]
  exact ((contDiff_const.sub contDiff_fst).mul (hk0.comp contDiff_snd)).add
    (contDiff_fst.mul (hk1.comp contDiff_snd))

/-- The angle of the affine curvature interpolation is jointly as smooth as
the endpoint curvatures. -/
theorem contDiff_succ_uncurry_tangentAngle {n : ℕ}
    (hk0 : ContDiff ℝ ((n : ℕ) + 1) k0)
    (hk1 : ContDiff ℝ ((n : ℕ) + 1) k1) :
    ContDiff ℝ ((n : ℕ) + 1)
      (fun p : ℝ × ℝ => tangentAngle (kappaInterp k0 k1 p.1) theta0 p.2) := by
  have hprim := ParametricPrimitiveSmooth.contDiff_primitive n
    (g := fun t s => kappaInterp k0 k1 t s)
    (contDiff_succ_uncurry_kappaInterp (k0 := k0) (k1 := k1) hk0 hk1)
  simpa [tangentAngle] using contDiff_const.add hprim

/-- A complex-valued parametric primitive is jointly as smooth as its
integrand.  This is the componentwise extension of
`ParametricPrimitiveSmooth.contDiff_primitive`. -/
theorem contDiff_succ_uncurry_complexPrimitive {n : ℕ} {g : ℝ → ℝ → ℂ}
    (hg : ContDiff ℝ ((n : ℕ) + 1) (uncurry g)) :
    ContDiff ℝ ((n : ℕ) + 1)
      (uncurry fun t s => ∫ u in (0 : ℝ)..s, g t u) := by
  have hRe : ContDiff ℝ ((n : ℕ) + 1) (uncurry fun t s => (g t s).re) :=
    Complex.reCLM.contDiff.comp hg
  have hIm : ContDiff ℝ ((n : ℕ) + 1) (uncurry fun t s => (g t s).im) :=
    Complex.imCLM.contDiff.comp hg
  have hPrimRe := ParametricPrimitiveSmooth.contDiff_primitive n hRe
  have hPrimIm := ParametricPrimitiveSmooth.contDiff_primitive n hIm
  have hComb : ContDiff ℝ ((n : ℕ) + 1) (fun p : ℝ × ℝ =>
      ((∫ u in (0 : ℝ)..p.2, (g p.1 u).re : ℝ) : ℂ)
        + (∫ u in (0 : ℝ)..p.2, (g p.1 u).im : ℝ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp hPrimRe).add
      ((Complex.ofRealCLM.contDiff.comp hPrimIm).mul contDiff_const)
  have heq : (uncurry fun t s => ∫ u in (0 : ℝ)..s, g t u) =
      fun p : ℝ × ℝ =>
        ((∫ u in (0 : ℝ)..p.2, (g p.1 u).re : ℝ) : ℂ)
          + (∫ u in (0 : ℝ)..p.2, (g p.1 u).im : ℝ) * Complex.I := by
    funext p
    have hcont : Continuous fun u => g p.1 u :=
      hg.continuous.comp (continuous_const.prodMk continuous_id)
    have hint : IntervalIntegrable (fun u => g p.1 u) volume 0 p.2 :=
      hcont.intervalIntegrable 0 p.2
    have hre := Complex.reCLM.intervalIntegral_comp_comm hint
    have him := Complex.imCLM.intervalIntegral_comp_comm hint
    apply Complex.ext
    · simpa using hre.symm
    · simpa using him.symm
  rw [heq]
  exact hComb

/-- The tangent vector of the curvature interpolation is jointly as smooth as
the endpoint curvatures. -/
theorem contDiff_succ_uncurry_interpTangent {n : ℕ}
    (hk0 : ContDiff ℝ ((n : ℕ) + 1) k0)
    (hk1 : ContDiff ℝ ((n : ℕ) + 1) k1) :
    ContDiff ℝ ((n : ℕ) + 1) (fun p : ℝ × ℝ =>
      tau (tangentAngle (kappaInterp k0 k1 p.1) theta0 p.2)) := by
  have hang := contDiff_succ_uncurry_tangentAngle (k0 := k0) (k1 := k1)
    (theta0 := theta0) hk0 hk1
  simpa [tau] using Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp hang).mul contDiff_const)

/-- **Higher regularity of the explicit front reconstruction.**  A pair of
`C^(n+1)` endpoint curvatures produces a jointly `C^(n+1)` interpolation path.
-/
theorem contDiff_succ_uncurry_interpCurve {n : ℕ}
    (hk0 : ContDiff ℝ ((n : ℕ) + 1) k0)
    (hk1 : ContDiff ℝ ((n : ℕ) + 1) k1) :
    ContDiff ℝ ((n : ℕ) + 1)
      (uncurry fun t s => interpCurve (kappaInterp k0 k1 t) theta0 L s) := by
  have htau := contDiff_succ_uncurry_interpTangent (k0 := k0) (k1 := k1)
    (theta0 := theta0) hk0 hk1
  have hprim := contDiff_succ_uncurry_complexPrimitive
    (n := n) (g := fun t s =>
      tau (tangentAngle (kappaInterp k0 k1 t) theta0 s)) htau
  change ContDiff ℝ ((n : ℕ) + 1) (fun p : ℝ × ℝ =>
    (∫ r in (0 : ℝ)..p.2,
        tau (tangentAngle (kappaInterp k0 k1 p.1) theta0 r))
      - (1 / 2 : ℂ) * ∫ r in (0 : ℝ)..L,
        tau (tangentAngle (kappaInterp k0 k1 p.1) theta0 r))
  exact hprim.sub (contDiff_const.mul
    (hprim.comp (contDiff_fst.prodMk contDiff_const)))

/-- In particular, `C³` endpoint curvatures give the joint `C³` front
regularity required by the higher selected-rear estimates. -/
theorem contDiff_three_uncurry_interpCurve
    (hk0 : ContDiff ℝ (3 : ℕ) k0) (hk1 : ContDiff ℝ (3 : ℕ) k1) :
    ContDiff ℝ (3 : ℕ)
      (uncurry fun t s => interpCurve (kappaInterp k0 k1 t) theta0 L s) := by
  simpa using contDiff_succ_uncurry_interpCurve (n := 2) (theta0 := theta0)
    (L := L) (k0 := k0) (k1 := k1) (by simpa using hk0) (by simpa using hk1)

end InterpolationSmooth
