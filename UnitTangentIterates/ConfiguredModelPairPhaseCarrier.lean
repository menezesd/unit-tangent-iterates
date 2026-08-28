import UnitTangentIterates.ConstructedConfiguredSequenceWeighted
import UnitTangentIterates.CurvatureRigidity
import UnitTangentIterates.SelectedInverseCarrier
import UnitTangentIterates.TwoCapPairsAssembly

/-!
# Exact configured pair identification up to phase and rigid motion

The current side stored in configuration `n` is the next prescribed model
curvature after one common phase shift.  This module retains the corresponding
geometric statement: the current front is a rigid image of the shifted next
front, while its physical rear in rear arclength is a rigid image of the
canonical carrier of `(configs n).kH`.  The raw pair still satisfies the exact
unit-tangent equation pointwise.
-/

noncomputable section

open Function ModelOrbitDefect CurvatureInterpolation RearTrack

namespace ConfiguredModelPairPhaseCarrier

open TwoCapPairsAssembly SelectedInverseCarrier CurvatureRigidity

variable (D : ConstructedConfiguredSequenceWeighted.Data)

def currentCurvature (n : ℕ) : ℝ → ℝ :=
  modelCurvature (D.model.configs n).y (D.model.configs n).yd (D.Hs (n + 1))

def currentFront (n : ℕ) : ℝ → ℂ :=
  front (currentCurvature D n) D.model.thetaBase (D.Hs (n + 1))

def currentAngle (n : ℕ) : ℝ → ℝ :=
  frontAngle (currentCurvature D n) D.model.thetaBase

def currentSteering (n : ℕ) : ℝ → ℝ :=
  modelSteering (D.model.configs n).Y

def currentRearOwn (n : ℕ) : ℝ → ℂ := fun x =>
  rearTrack (currentFront D n) (currentAngle D n) (currentSteering D n)
    ((D.model.configs n).sf x)

def currentRearOwnAngle (n : ℕ) : ℝ → ℝ := fun x =>
  rearAngle (currentAngle D n) (currentSteering D n)
    ((D.model.configs n).sf x)

/-- The complete exact analytic identification of configured edge `n`.

The first rigid motion identifies the current front with the next prescribed
front in the retained phase.  The second identifies the physical rear in its
own arclength with the canonical reconstruction of `kH`.  The last field is
the unnormalized pointwise selected-inverse equation. -/
structure Identity (n : ℕ) where
  frontTranslation : ℂ
  frontRotation : ℂ
  frontRotation_norm : ‖frontRotation‖ = 1
  front_eq_next_shift : ∀ s,
    currentFront D n s = frontTranslation + frontRotation *
      front (D.kappas (n + 1)) D.model.thetaBase (D.Hs (n + 1))
        (s + D.phase)
  rearTranslation : ℂ
  rearRotation : ℂ
  rearRotation_norm : ‖rearRotation‖ = 1
  rearOwn_eq_carrier : ∀ x,
    currentRearOwn D n x = rearTranslation + rearRotation *
      interpCurve (D.model.configs n).kH D.model.thetaBase (D.Hs n) x
  unitTangent_exact : ∀ s,
    rear (currentCurvature D n) (currentSteering D n)
          D.model.thetaBase (D.Hs (n + 1)) s +
        deriv (rear (currentCurvature D n) (currentSteering D n)
          D.model.thetaBase (D.Hs (n + 1))) s /
          ‖deriv (rear (currentCurvature D n) (currentSteering D n)
            D.model.thetaBase (D.Hs (n + 1))) s‖ =
      currentFront D n s

/-- Every configured edge has the exact rigid/phase carrier identity. -/
theorem exists_identity (n : ℕ) : Nonempty (Identity D n) := by
  let c := D.model.configs n
  let H := D.Hs (n + 1)
  let K := currentCurvature D n
  let kNext := D.kappas (n + 1)
  let q := D.phase
  let X : ℝ → ℂ := fun s => currentFront D n (s - q)
  let Theta : ℝ → ℝ := fun s => currentAngle D n (s - q)
  have hKshift : ∀ s, K (s - q) = kNext s := by
    intro s
    simpa [K, kNext, q, currentCurvature] using
      D.model_current_curvature_eq_next_shift n (s - D.phase)
  have hX : ∀ s, HasDerivAt X (tau (Theta s)) s := by
    intro s
    have hi : HasDerivAt (fun u : ℝ => u - q) 1 s := by
      simpa using (hasDerivAt_id s).sub_const q
    rw [SelectedInverseCarrier.tau_eq_exp]
    simpa [X, Theta, currentFront, currentAngle, currentCurvature, K, c, H,
      Function.comp_def] using
      (front_hasDerivAt (theta0 := D.model.thetaBase) (H := H)
        c.continuous_frontCurvature (s - q)).scomp s hi
  have hTheta : ∀ s, HasDerivAt Theta (kNext s) s := by
    intro s
    have hi : HasDerivAt (fun u : ℝ => u - q) 1 s := by
      simpa using (hasDerivAt_id s).sub_const q
    have h := (hasDerivAt_tangentAngle (θ₀ := D.model.thetaBase)
      c.continuous_frontCurvature (s - q)).scomp s hi
    have h' : HasDerivAt Theta (K (s - q)) s := by
      simpa [Theta, K, currentAngle, currentCurvature, c,
        TwoCapPairsAssembly.frontAngle, Function.comp_def] using h
    rw [hKshift s] at h'
    exact h'
  obtain ⟨aF, wF, hwF, hfront⟩ :=
    exists_rigid_interpCurve D.model.thetaBase H
      (D.model.curvature_continuous (n + 1)) hX hTheta
  have hfront' : ∀ s, currentFront D n s = aF + wF *
      front kNext D.model.thetaBase H (s + q) := by
    intro s
    have h := hfront (s + q)
    simpa [X, q, kNext, H, TwoCapPairsAssembly.front] using h
  have hmatch : ∀ t,
      c.kH (rearArclength (currentSteering D n) t) *
          Real.cos (currentSteering D n t) =
        Real.sin (currentSteering D n t) := by
    intro t
    change c.kH (modelRearArclength c.Y t) *
        Real.cos (modelSteering c.Y t) = Real.sin (modelSteering c.Y t)
    rw [cos_modelSteering,
      sin_modelSteering c.ha1.le (c.hYa t)]
    exact c.hk t
  have hrearCarrier := rearOwn_carrier
    (c := Real.sqrt (1 - D.model.a ^ 2))
    (F := currentFront D n) (Θ := currentAngle D n)
    (K := currentCurvature D n) (dl := currentSteering D n)
    (sf := c.sf) (kH := c.kH)
    (sqrt_one_sub_sq_pos c.ha0 c.ha1) c.continuous_dl c.cos_dl_ge
    c.sf_rightInverse
    (fun s => front_hasDerivAt c.continuous_frontCurvature s)
    (fun s => hasDerivAt_tangentAngle c.continuous_frontCurvature s)
    c.hasDerivAt_dl hmatch
  obtain ⟨aR, wR, hwR, hrear⟩ :=
    exists_rigid_interpCurve D.model.thetaBase (D.Hs n) c.continuous_kH
      hrearCarrier.1 hrearCarrier.2
  refine ⟨{
    frontTranslation := aF
    frontRotation := wF
    frontRotation_norm := hwF
    front_eq_next_shift := ?_
    rearTranslation := aR
    rearRotation := wR
    rearRotation_norm := hwR
    rearOwn_eq_carrier := hrear
    unitTangent_exact := ?_ }⟩
  · intro s
    simpa [K, kNext, H, q] using hfront' s
  · intro s
    exact unitTangentMap_rear_eq_front c.continuous_frontCurvature
      (c.hasDerivAt_dl s) (c.cos_dl_pos s)

end ConfiguredModelPairPhaseCarrier
