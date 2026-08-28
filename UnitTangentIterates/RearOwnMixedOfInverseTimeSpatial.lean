import UnitTangentIterates.RearArclengthInverseTimeSpatial
import UnitTangentIterates.RearOwnMotion

/-!
# The exact mixed witness after inverse rear-arclength reparametrization

The time-dependent inverse rear arclength contributes a tangential sliding
term to the velocity.  Its spatial derivative cancels the extra term produced
by the Green equation for the selected steering variation.  This gives the
mixed witness for the rear family using only the retained `C^1` data.
-/

noncomputable section

open Function

namespace RearOwnMixedOfInverseTimeSpatial

open RearTrack RearOwnArclength RearOwnMotion RearFamilyFrame
  RearArclengthInverseTimeSpatial SelectedChangeOfVariable RearOwnHigherRegularity

variable {F Fdot : ℝ → ℝ → ℂ}
  {Theta delta sf K ThetaT deltaT KT : ℝ → ℝ → ℝ}

/-- The canonical time derivative of the rear tangent angle in its own
arclength. -/
def rearAngleTime (ThetaT deltaT delta sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦
    ThetaT t (sf t x) - deltaT t (sf t x) +
      partialTime sf t x * Real.sin (delta t (sf t x))

/-- The exact velocity of the rear family in its own arclength. -/
def rearOwnVelocity (Fdot : ℝ → ℝ → ℂ)
    (ThetaT deltaT Theta delta sf : ℝ → ℝ → ℝ) : ℝ → ℝ → ℂ :=
  fun t x ↦
    trackVelocity Fdot ThetaT deltaT Theta delta t (sf t x) +
      ((partialTime sf t x * Real.cos (delta t (sf t x)) : ℝ) : ℂ) *
        Complex.exp (Complex.I *
          (rearOwnAngle Theta delta sf t x : ℂ))

/-- The spatial derivative of the coefficient of the sliding tangent is
`deltaT * tan delta`.  This is the differentiated inverse-arclength formula. -/
theorem hasDerivAt_slidingCoefficient
    (hdeltaC : ContDiff ℝ 1 (uncurry delta))
    (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hdeltaT : ∀ t s, HasDerivAt (fun r ↦ delta r s) (deltaT t s) t)
    (hdeltaTC : Continuous (uncurry deltaT))
    (hsfS : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0) (t x : ℝ) :
    HasDerivAt
      (fun y ↦ partialTime sf t y * Real.cos (delta t (sf t y)))
      (deltaT t (sf t x) * Real.tan (delta t (sf t x))) x := by
  let At : ℝ → ℝ := fun s ↦ arclengthTime delta deltaT t s
  have hAt : HasDerivAt At (cosTimeDeriv delta deltaT t (sf t x)) (sf t x) := by
    exact intervalIntegral.integral_hasDerivAt_right
      ((continuous_cosTimeDeriv hdeltaC.continuous hdeltaTC).comp
        (continuous_const.prodMk continuous_id) |>.intervalIntegrable 0 (sf t x))
      (((continuous_cosTimeDeriv hdeltaC.continuous hdeltaTC).comp
        (continuous_const.prodMk continuous_id)).stronglyMeasurableAtFilter _ _)
      ((continuous_cosTimeDeriv hdeltaC.continuous hdeltaTC).comp
        (continuous_const.prodMk continuous_id)).continuousAt
  have hcomp := (hAt.comp x (hsfS t x)).neg
  have heq :
      (fun y ↦ partialTime sf t y * Real.cos (delta t (sf t y))) =
        fun y ↦ -At (sf t y) := by
    funext y
    rw [partialTime_sf_eq_formula hdeltaC hsfC hdeltaT hdeltaTC hinv hcos t y]
    simp only [sfTimeFormula, At]
    field_simp [hcos t (sf t y)]
  rw [heq]
  apply hcomp.congr_deriv
  simp only [cosTimeDeriv]
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- Chain rule for the rear tangent angle along the moving inverse arclength. -/
theorem hasDerivAt_rearOwnAngle_time
    (hThetaC : ContDiff ℝ 1 (uncurry Theta))
    (hdeltaC : ContDiff ℝ 1 (uncurry delta))
    (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hThetaS : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hThetaT : ∀ t s, HasDerivAt (fun r ↦ Theta r s) (ThetaT t s) t)
    (hdeltaT : ∀ t s, HasDerivAt (fun r ↦ delta r s) (deltaT t s) t)
    (t x : ℝ) :
    HasDerivAt (fun r ↦ rearOwnAngle Theta delta sf r x)
      (rearAngleTime ThetaT deltaT delta sf t x) t := by
  have hsft : HasDerivAt (fun r ↦ sf r x) (partialTime sf t x) t :=
    hasDerivAt_partialTime (hsfC.differentiable (by norm_num)) t x
  have hThetaComp := hasDerivAt_comp_partials
    (hThetaC.differentiable (by norm_num)) hsft
  have hdeltaComp := hasDerivAt_comp_partials
    (hdeltaC.differentiable (by norm_num)) hsft
  have hThetaPt : partialTime Theta t (sf t x) = ThetaT t (sf t x) :=
    (hasDerivAt_partialTime (hThetaC.differentiable (by norm_num)) t (sf t x)).unique
      (hThetaT t (sf t x))
  have hThetaPx : partialArc Theta t (sf t x) = K t (sf t x) :=
    (hasDerivAt_partialArc (hThetaC.differentiable (by norm_num)) t (sf t x)).unique
      (hThetaS t (sf t x))
  have hdeltaPt : partialTime delta t (sf t x) = deltaT t (sf t x) :=
    (hasDerivAt_partialTime (hdeltaC.differentiable (by norm_num)) t (sf t x)).unique
      (hdeltaT t (sf t x))
  have hdeltaPx : partialArc delta t (sf t x) =
      K t (sf t x) - Real.sin (delta t (sf t x)) :=
    (hasDerivAt_partialArc (hdeltaC.differentiable (by norm_num)) t (sf t x)).unique
      (hsteer t (sf t x))
  have h := hThetaComp.sub hdeltaComp
  convert h using 1 <;>
    simp [rearOwnAngle, rearAngle, rearAngleTime, hThetaPt, hThetaPx,
      hdeltaPt, hdeltaPx, smul_eq_mul] <;> ring

/-- The rear velocity is the actual time derivative of the rear family. -/
theorem hasDerivAt_rearOwn_time
    (hFC : ContDiff ℝ 1 (uncurry F))
    (hThetaC : ContDiff ℝ 1 (uncurry Theta))
    (hdeltaC : ContDiff ℝ 1 (uncurry delta))
    (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hFS : ∀ t s, HasDerivAt (F t)
      (Complex.exp (Complex.I * (Theta t s : ℂ))) s)
    (hThetaS : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hFT : ∀ t s, HasDerivAt (fun r ↦ F r s) (Fdot t s) t)
    (hThetaT : ∀ t s, HasDerivAt (fun r ↦ Theta r s) (ThetaT t s) t)
    (hdeltaT : ∀ t s, HasDerivAt (fun r ↦ delta r s) (deltaT t s) t)
    (t x : ℝ) :
    HasDerivAt (fun r ↦ rearOwn F Theta delta sf r x)
      (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf t x) t := by
  have htrackC := contDiff_one_rearTrackFamily hFC hThetaC hdeltaC
  have htrackS : ∀ a s, HasDerivAt (frontParamTrack F Theta delta a)
      ((Real.cos (delta a s) : ℂ) *
        Complex.exp (Complex.I * (rearAngle (Theta a) (delta a) s : ℂ))) s := by
    intro a s
    exact RearTrack.hasDerivAt_rearTrack (hFS a s) (hThetaS a s) (hsteer a s)
  have htrackT : ∀ a s, HasDerivAt (fun r ↦ frontParamTrack F Theta delta r s)
      (trackVelocity Fdot ThetaT deltaT Theta delta a s) a :=
    hasDerivAt_frontParamTrack_time hFT hThetaT hdeltaT
  have h := RearOwnMotion.hasDerivAt_rearOwn_time htrackC htrackS htrackT
    (hasDerivAt_partialTime (hsfC.differentiable (by norm_num))) t x
  apply h.congr_deriv
  simp only [rearOwnVelocity, rearOwnAngle, Complex.real_smul]
  rw [Complex.ofReal_mul]
  ring

/-- Spatial derivative of the exact rear velocity.  The hypothesis `hfrontMixed`
is precisely the retained mixed witness for the front, while `hdeltaTSpatial`
is the Green ODE for the selected steering variation. -/
theorem hasDerivAt_rearOwnVelocity_space
    (hdeltaC : ContDiff ℝ 1 (uncurry delta))
    (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hThetaS : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hThetaT : ∀ t s, HasDerivAt (fun r ↦ Theta r s) (ThetaT t s) t)
    (hdeltaT : ∀ t s, HasDerivAt (fun r ↦ delta r s) (deltaT t s) t)
    (hdeltaTC : Continuous (uncurry deltaT))
    (hThetaTSpatial : ∀ t s, HasDerivAt (ThetaT t) (KT t s) s)
    (hdeltaTSpatial : ∀ t s, HasDerivAt (deltaT t)
      (-Real.cos (delta t s) * deltaT t s + KT t s) s)
    (hsfS : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0)
    (hfrontMixed : ∀ t s, ∃ Z : ℂ,
      HasDerivAt (fun r ↦ Complex.exp (Complex.I * (Theta r s : ℂ))) Z t ∧
      HasDerivAt (Fdot t) Z s)
    (t x : ℝ) :
    HasDerivAt (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf t)
      (Complex.I * (rearAngleTime ThetaT deltaT delta sf t x : ℂ) *
        Complex.exp (Complex.I *
          (rearOwnAngle Theta delta sf t x : ℂ))) x := by
  let s := sf t x
  let d := delta t s
  let c := Real.cos d
  let E := Complex.exp (Complex.I * (rearAngle (Theta t) (delta t) s : ℂ))
  obtain ⟨Z, hZT, hZS⟩ := hfrontMixed t s
  have hfrontT : HasDerivAt
      (fun r ↦ Complex.exp (Complex.I * (Theta r s : ℂ)))
      (Complex.I * (ThetaT t s : ℂ) *
        Complex.exp (Complex.I * (Theta t s : ℂ))) t := by
    have h := ((hThetaT t s).ofReal_comp.const_mul Complex.I).cexp
    convert h using 1 <;> ring
  have hZ : Z = Complex.I * (ThetaT t s : ℂ) *
      Complex.exp (Complex.I * (Theta t s : ℂ)) := hZT.unique hfrontT
  have hZS' : HasDerivAt (Fdot t) Z (sf t x) := by simpa [s] using hZS
  have hFcomp := hZS'.scomp x (hsfS t x)
  rw [hZ] at hFcomp
  have hA := (hThetaTSpatial t s).sub (hdeltaTSpatial t s)
  have hAcomp := hA.comp x (hsfS t x)
  have hAcomp' : HasDerivAt
      (fun y ↦ ThetaT t (sf t y) - deltaT t (sf t y))
      (deltaT t s) x := by
    apply hAcomp.congr_deriv
    dsimp [s, c]
    field_simp [hcos t (sf t x)]
    ring
  have hE0 := RearTrack.hasDerivAt_expRearAngle
    (hThetaS t s) (hsteer t s)
  have hEcomp := hE0.scomp x (hsfS t x)
  have hEcomp' : HasDerivAt
      (fun y ↦ Complex.exp (Complex.I *
        (rearOwnAngle Theta delta sf t y : ℂ)))
      (Complex.I * (Real.tan d : ℂ) * E) x := by
    apply hEcomp.congr_deriv
    simp only [rearOwnAngle, s, d, E]
    rw [Real.tan_eq_sin_div_cos]
    have hr : (1 / Real.cos (delta t (sf t x))) *
        Real.sin (delta t (sf t x)) =
        Real.sin (delta t (sf t x)) / Real.cos (delta t (sf t x)) := by
      field_simp [hcos t (sf t x)]
    rw [Complex.real_smul, ← hr, Complex.ofReal_mul]
    ring
  have hslide := hasDerivAt_slidingCoefficient hdeltaC hsfC hdeltaT hdeltaTC
    hsfS hinv hcos t x
  have htrack : HasDerivAt
      (fun y ↦ trackVelocity Fdot ThetaT deltaT Theta delta t (sf t y))
      ((1 / c : ℝ) • (Complex.I * (ThetaT t s : ℂ) *
          Complex.exp (Complex.I * (Theta t s : ℂ))) -
        Complex.I * ((deltaT t s : ℂ) * E +
          ((ThetaT t s - deltaT t s : ℝ) : ℂ) *
            (Complex.I * (Real.tan d : ℂ) * E))) x := by
    have hprod := hAcomp'.ofReal_comp.mul hEcomp'
    have hterm := hprod.const_mul Complex.I
    have hsub := hFcomp.sub hterm
    convert hsub using 1
    funext y
    simp [trackVelocity, rearOwnAngle, mul_assoc]
  have hcorrection := hslide.ofReal_comp.mul hEcomp'
  have hsum := htrack.add hcorrection
  apply hsum.congr_deriv
  have hfrontE : Complex.exp (Complex.I * (Theta t s : ℂ)) =
      ((Real.cos d : ℝ) : ℂ) * E +
        Complex.I * ((Real.sin d : ℝ) : ℂ) * E := by
    calc
      Complex.exp (Complex.I * (Theta t s : ℂ)) =
          Complex.exp (Complex.I * (d : ℂ) +
            Complex.I * (rearAngle (Theta t) (delta t) s : ℂ)) := by
              congr 2
              simp only [rearAngle, d]
              push_cast
              ring
      _ = Complex.exp (Complex.I * (d : ℂ)) * E := by
            rw [Complex.exp_add]
      _ = ((Real.cos d : ℝ) : ℂ) * E +
          Complex.I * ((Real.sin d : ℝ) : ℂ) * E := by
            rw [mul_comm Complex.I (d : ℂ), Complex.exp_mul_I]
            push_cast
            ring
  have hfrontE' : Complex.exp (Complex.I * (Theta t (sf t x) : ℂ)) =
      ((Real.cos (delta t (sf t x)) : ℝ) : ℂ) *
          Complex.exp (Complex.I *
            (rearAngle (Theta t) (delta t) (sf t x) : ℂ)) +
        Complex.I * ((Real.sin (delta t (sf t x)) : ℝ) : ℂ) *
          Complex.exp (Complex.I *
            (rearAngle (Theta t) (delta t) (sf t x) : ℂ)) := by
    simpa only [s, d, E] using hfrontE
  simp only [rearOwnVelocity, rearAngleTime, rearOwnAngle, s, d, c, E]
  rw [hfrontE', Real.tan_eq_sin_div_cos]
  simp only [Complex.real_smul]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_inv]
  have hcC : ((Real.cos (delta t (sf t x)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hcos t (sf t x)
  field_simp [hcC]
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  norm_num
  ring

/-- The exact mixed witness in the frame-reconstructed form consumed by
`ConfiguredBaseProfiledResidualConstructor.Transport`. -/
theorem mixed
    (hdeltaC : ContDiff ℝ 1 (uncurry delta))
    (hsfC : ContDiff ℝ 1 (uncurry sf))
    (hThetaC : ContDiff ℝ 1 (uncurry Theta))
    (hThetaS : ∀ t s, HasDerivAt (Theta t) (K t s) s)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hThetaT : ∀ t s, HasDerivAt (fun r ↦ Theta r s) (ThetaT t s) t)
    (hdeltaT : ∀ t s, HasDerivAt (fun r ↦ delta r s) (deltaT t s) t)
    (hdeltaTC : Continuous (uncurry deltaT))
    (hThetaTSpatial : ∀ t s, HasDerivAt (ThetaT t) (KT t s) s)
    (hdeltaTSpatial : ∀ t s, HasDerivAt (deltaT t)
      (-Real.cos (delta t s) * deltaT t s + KT t s) s)
    (hsfS : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x)
    (hinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hcos : ∀ t s, Real.cos (delta t s) ≠ 0)
    (hfrontMixed : ∀ t s, ∃ Z : ℂ,
      HasDerivAt (fun r ↦ Complex.exp (Complex.I * (Theta r s : ℂ))) Z t ∧
      HasDerivAt (Fdot t) Z s) :
    ∀ t x, ∃ Z : ℂ,
      HasDerivAt
        (fun r ↦ Complex.exp (Complex.I *
          (rearOwnAngle Theta delta sf r x : ℂ))) Z t ∧
      HasDerivAt
        (fun y ↦
          (frameTangential
              (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf)
              (rearOwnAngle Theta delta sf) t y : ℂ) *
              Complex.exp (Complex.I *
                (rearOwnAngle Theta delta sf t y : ℂ)) +
          (frameNormal
              (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf)
              (rearOwnAngle Theta delta sf) t y : ℂ) *
              (Complex.I * Complex.exp (Complex.I *
                (rearOwnAngle Theta delta sf t y : ℂ)))) Z x := by
  intro t x
  let Z := Complex.I * (rearAngleTime ThetaT deltaT delta sf t x : ℂ) *
    Complex.exp (Complex.I * (rearOwnAngle Theta delta sf t x : ℂ))
  refine ⟨Z, ?_, ?_⟩
  · have hang := hasDerivAt_rearOwnAngle_time hThetaC hdeltaC hsfC
      hThetaS hsteer hThetaT hdeltaT t x
    have h := (hang.ofReal_comp.const_mul Complex.I).cexp
    convert h using 1 <;> simp [Z] <;> ring
  · have hv := hasDerivAt_rearOwnVelocity_space hdeltaC hsfC hThetaS hsteer
      hThetaT hdeltaT hdeltaTC hThetaTSpatial hdeltaTSpatial hsfS hinv hcos
      hfrontMixed t x
    have hframe : (fun y ↦
        (frameTangential
            (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf)
            (rearOwnAngle Theta delta sf) t y : ℂ) *
            Complex.exp (Complex.I *
              (rearOwnAngle Theta delta sf t y : ℂ)) +
        (frameNormal
            (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf)
            (rearOwnAngle Theta delta sf) t y : ℂ) *
            (Complex.I * Complex.exp (Complex.I *
              (rearOwnAngle Theta delta sf t y : ℂ)))) =
          rearOwnVelocity Fdot ThetaT deltaT Theta delta sf t := by
      funext y
      have h := frame_reconstruct
        (rearOwnVelocity Fdot ThetaT deltaT Theta delta sf t y)
        (rearOwnAngle Theta delta sf t y)
      rw [← h]
      simp only [frameTangential, frameNormal]
      ring
    rw [hframe]
    exact hv

end RearOwnMixedOfInverseTimeSpatial
