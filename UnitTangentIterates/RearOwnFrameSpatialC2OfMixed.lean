import UnitTangentIterates.RearOwnFrameDrift
import UnitTangentIterates.RearFrameRegularity
import UnitTangentIterates.RearOwnTangential

/-!
# Spatial frame regularity from a mixed witness

This is the range-local replacement for joint `C^2` regularity.  It uses only
the mixed tangent/velocity identity, the inverse Jacobi equation, and first
spatial derivatives of the rear curvature and Jacobi source.
-/

noncomputable section

open Function

namespace RearOwnFrameSpatialC2OfMixed

open RearFamilyFrame RearOwnFrameDrift

variable {Ydot : ℝ → ℝ → ℂ}
  {psi kap alphaT g gS kapS : ℝ → ℝ → ℝ}

/-- The mixed identity forces the first-variation equation
`xi_x = eta * kap` without joint `C^2` regularity of the rear family. -/
theorem hasDerivAt_frameTangential_of_mixed
    (hpsiS : ∀ t x, HasDerivAt (psi t) (kap t x) x)
    (hpsiT : ∀ t x, HasDerivAt (fun r ↦ psi r x) (alphaT t x) t)
    (hmixed : ∀ t x, ∃ Z : ℂ,
      HasDerivAt
        (fun r ↦ Complex.exp (Complex.I * (psi r x : ℂ))) Z t ∧
      HasDerivAt
        (fun y ↦
          (frameTangential Ydot psi t y : ℂ) *
              Complex.exp (Complex.I * (psi t y : ℂ)) +
          (frameNormal Ydot psi t y : ℂ) *
              (Complex.I * Complex.exp (Complex.I * (psi t y : ℂ)))) Z x) :
    ∀ t x, HasDerivAt (frameTangential Ydot psi t)
      (frameNormal Ydot psi t x * kap t x) x := by
  intro t x
  obtain ⟨Z, hZt, hZx⟩ := hmixed t x
  have hvel : (fun y ↦
      (frameTangential Ydot psi t y : ℂ) *
          Complex.exp (Complex.I * (psi t y : ℂ)) +
      (frameNormal Ydot psi t y : ℂ) *
          (Complex.I * Complex.exp (Complex.I * (psi t y : ℂ)))) = Ydot t := by
    funext y
    have h := frame_reconstruct (Ydot t y) (psi t y)
    simp only [frameTangential, frameNormal]
    conv_rhs => rw [← h]
    ring
  rw [hvel] at hZx
  have hexp := (((hpsiT t x).ofReal_comp.const_mul Complex.I).cexp)
  have hZ : Z = Complex.I * (alphaT t x : ℂ) *
      Complex.exp (Complex.I * (psi t x : ℂ)) := by
    apply hZt.unique
    convert hexp using 1 <;> ring
  have hframe := RearFrameRegularity.hasDerivAt_frameTangential_space
    hZx (hpsiS t x)
  apply hframe.congr_deriv
  rw [hZ]
  have hunit := RearSmoothDependence.exp_mul_conj (psi t x)
  simp only [mul_assoc]
  rw [hunit]
  simp
  ring

/-- Both frame components carry spatial `C^2` certificates once the Jacobi
source and rear curvature have one spatial derivative. -/
def spatialC2
    (hYdotC : Continuous (uncurry Ydot))
    (hpsiC : Continuous (uncurry psi))
    (hkapC : Continuous (uncurry kap))
    (halphaTC : Continuous (uncurry alphaT))
    (hgC : Continuous (uncurry g))
    (hgSC : Continuous (uncurry gS))
    (hkapSC : Continuous (uncurry kapS))
    (hpsiS : ∀ t x, HasDerivAt (psi t) (kap t x) x)
    (hpsiT : ∀ t x, HasDerivAt (fun r ↦ psi r x) (alphaT t x) t)
    (hmixed : ∀ t x, ∃ Z : ℂ,
      HasDerivAt
        (fun r ↦ Complex.exp (Complex.I * (psi r x : ℂ))) Z t ∧
      HasDerivAt
        (fun y ↦
          (frameTangential Ydot psi t y : ℂ) *
              Complex.exp (Complex.I * (psi t y : ℂ)) +
          (frameNormal Ydot psi t y : ℂ) *
              (Complex.I * Complex.exp (Complex.I * (psi t y : ℂ)))) Z x)
    (hjac : ∀ t x, HasDerivAt (frameNormal Ydot psi t)
      (g t x - frameNormal Ydot psi t x) x)
    (hgS : ∀ t x, HasDerivAt (g t) (gS t x) x)
    (hkapS : ∀ t x, HasDerivAt (kap t) (kapS t x) x) :
    SpatialC2 (frameTangential Ydot psi) ×
      SpatialC2 (frameNormal Ydot psi) := by
  have hxiC : Continuous (uncurry (frameTangential Ydot psi)) :=
    RearOwnTangential.contDiff_frameTangential
      (n := 0) ((contDiff_zero (𝕜 := ℝ)).mpr hYdotC)
      ((contDiff_zero (𝕜 := ℝ)).mpr hpsiC) |>.continuous
  have hetaC : Continuous (uncurry (frameNormal Ydot psi)) :=
    RearOwnTangential.contDiff_frameNormal
      (n := 0) ((contDiff_zero (𝕜 := ℝ)).mpr hYdotC)
      ((contDiff_zero (𝕜 := ℝ)).mpr hpsiC) |>.continuous
  let xi1 : ℝ → ℝ → ℝ := fun t x ↦
    frameNormal Ydot psi t x * kap t x
  let xi2 : ℝ → ℝ → ℝ := fun t x ↦
    (g t x - frameNormal Ydot psi t x) * kap t x +
      frameNormal Ydot psi t x * kapS t x
  let eta1 : ℝ → ℝ → ℝ := fun t x ↦
    g t x - frameNormal Ydot psi t x
  let eta2 : ℝ → ℝ → ℝ := fun t x ↦
    gS t x - eta1 t x
  have hxi1C : Continuous (uncurry xi1) := hetaC.mul hkapC
  have hxi2C : Continuous (uncurry xi2) :=
    (hgC.sub hetaC).mul hkapC |>.add (hetaC.mul hkapSC)
  have heta1C : Continuous (uncurry eta1) := hgC.sub hetaC
  have heta2C : Continuous (uncurry eta2) := hgSC.sub heta1C
  refine ⟨
    { xi1 := xi1
      xi2 := xi2
      deriv1 := hasDerivAt_frameTangential_of_mixed hpsiS hpsiT hmixed
      deriv2 := ?_
      continuous0 := hxiC
      continuous1 := hxi1C
      continuous2 := hxi2C },
    { xi1 := eta1
      xi2 := eta2
      deriv1 := hjac
      deriv2 := ?_
      continuous0 := hetaC
      continuous1 := heta1C
      continuous2 := heta2C }⟩
  · intro t x
    exact (hjac t x).mul (hkapS t x)
  · intro t x
    exact (hgS t x).sub (hjac t x)

end RearOwnFrameSpatialC2OfMixed
