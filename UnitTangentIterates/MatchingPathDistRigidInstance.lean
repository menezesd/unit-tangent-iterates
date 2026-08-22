import Mathlib
import UnitTangentIterates.MatchingPathDistRigid

/-!
# The transfer to arbitrary carriers is not vacuous

`MatchingPathDistRigid.pathDistRigid_le_of_carriers` transports a bound proved
for the two curves reconstructed from two curvatures to arbitrary marked curves
carrying those curvatures, the comparison being taken modulo a rigid motion of
the plane.  This file checks that its hypotheses can be met by curves which are
*not* the reconstructions: the circle of curvature `1/2` and the oval of
curvature `1/2 + (cos s)/4` of `InterpolationEstimate.lean`, each moved by its
own rigid motion — the first rotated by `+π/2` and translated by `1`, the second
rotated by `−π/2` and translated by `−1`.

`pathDistRigid_le_of_carriers_instance` produces the two marked curves and the
bound.
-/

noncomputable section

open Real MeasureTheory Set MarkedSpace PathMetric

namespace MatchingPathDistRigidInstance

open CurvatureInterpolation CurvatureRigidity MarkedRigid InterpolationEstimate
  InterpolationSecondOrder InterpolationPathDist MatchingPathDistRigid

/-! ### The two quarter turns -/

theorem tau_pi_div_two : tau (Real.pi / 2) = Complex.I := by
  rw [tau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

theorem tau_neg_pi_div_two : tau (-(Real.pi / 2)) = -Complex.I := by
  rw [tau, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

/-! ### The two moved curves -/

/-- The circle of curvature `1/2`, rotated by a quarter turn and translated. -/
def circMoved (s : ℝ) : ℂ := 1 + Complex.I * interpCurve kcirc 0 (2 * Real.pi) s

/-- Its tangent angle. -/
def circAngle (s : ℝ) : ℝ := tangentAngle kcirc 0 s + Real.pi / 2

/-- The oval of curvature `1/2 + (cos s)/4`, rotated by the opposite quarter
turn and translated the other way. -/
def waveMoved (s : ℝ) : ℂ := -1 + (-Complex.I) * interpCurve kwave 0 (2 * Real.pi) s

/-- Its tangent angle. -/
def waveAngle (s : ℝ) : ℝ := tangentAngle kwave 0 s + -(Real.pi / 2)

theorem hasDerivAt_circMoved (s : ℝ) : HasDerivAt circMoved (tau (circAngle s)) s := by
  have h : HasDerivAt circMoved (Complex.I * tau (tangentAngle kcirc 0 s)) s :=
    ((hasDerivAt_interpCurve (θ₀ := 0) (L := 2 * Real.pi) continuous_kcirc s).const_mul
      Complex.I).const_add 1
  rwa [circAngle, tau_add, tau_pi_div_two, mul_comm]

theorem hasDerivAt_circAngle (s : ℝ) : HasDerivAt circAngle (kcirc s) s :=
  (hasDerivAt_tangentAngle (θ₀ := 0) continuous_kcirc s).add_const _

theorem hasDerivAt_waveMoved (s : ℝ) : HasDerivAt waveMoved (tau (waveAngle s)) s := by
  have h : HasDerivAt waveMoved (-Complex.I * tau (tangentAngle kwave 0 s)) s :=
    ((hasDerivAt_interpCurve (θ₀ := 0) (L := 2 * Real.pi) continuous_kwave s).const_mul
      (-Complex.I)).const_add (-1)
  rwa [waveAngle, tau_add, tau_neg_pi_div_two, mul_comm]

theorem hasDerivAt_waveAngle (s : ℝ) : HasDerivAt waveAngle (kwave s) s :=
  (hasDerivAt_tangentAngle (θ₀ := 0) continuous_kwave s).add_const _

/-! ### The instance -/

/-- **The transfer to arbitrary carriers is not vacuous.**  Two rigidly moved
copies of the circle of curvature `1/2` and of the oval of curvature
`1/2 + (cos s)/4` exist as marked curves, and their path pseudodistance modulo a
rigid motion obeys the interpolation bound of `pathDist_le_interpPathCost`. -/
theorem pathDistRigid_le_of_carriers_instance :
    ∃ (psi : ℝ → ℝ) (p' q' : Data),
      (∀ u, psi (u + 1) = psi u + 2 * (2 * Real.pi)) ∧
      (∀ u, p'.1 u = circMoved (2 * (2 * Real.pi) * u)) ∧
      (∀ u, q'.1 u = waveMoved (psi u)) ∧
      pathDistRigid p' q'
        ≤ interpPathCost (3/4) (1/4) (1/4) (2 * Real.pi) (curvDist kcirc kwave (2 * Real.pi)) := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨psi, hcont, htrans, hmain⟩ :=
    pathDist_le_interpPathCost (θ₀ := 0) (kstar := 3/4) (kd := 1/4) (dsup := 1/4)
      continuous_kcirc continuous_kwave continuous_const (by unfold kwave'; fun_prop)
      kcirc_periodic kwave_periodic kcirc_total kwave_total hpi
      hasDerivAt_kcirc hasDerivAt_kwave
      (fun r => by
        have h1 := Real.neg_one_le_cos r
        have h2 := Real.cos_le_one r
        rw [abs_le]
        constructor <;> simp only [kcirc, kwave] <;> linarith)
      (fun r => by norm_num)
      (fun r => by
        have h1 := Real.neg_one_le_sin r
        have h2 := Real.sin_le_one r
        rw [abs_le]
        constructor <;> simp only [kwave'] <;> linarith)
      kcirc_nonneg kwave_nonneg kcirc_le kwave_le
  -- the two moved curves are continuous and of period one in the normalized parameter
  have hcirccont : Continuous circMoved :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_circMoved s).continuousAt
  have hwavecont : Continuous waveMoved :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_waveMoved s).continuousAt
  have hcircper : Function.Periodic circMoved (2 * (2 * Real.pi)) := by
    intro s
    simp only [circMoved]
    rw [interpCurve_periodic (θ₀ := 0) continuous_kcirc kcirc_periodic kcirc_total s]
  have hwaveper : Function.Periodic waveMoved (2 * (2 * Real.pi)) := by
    intro s
    simp only [waveMoved]
    rw [interpCurve_periodic (θ₀ := 0) continuous_kwave kwave_periodic kwave_total s]
  obtain ⟨p', hp'⟩ := exists_data_of_periodic_curve
    (g := fun u => circMoved (2 * (2 * Real.pi) * u))
    (hcirccont.comp (continuous_const.mul continuous_id)) (fun u => by
      have h : 2 * (2 * Real.pi) * (u + 1) = 2 * (2 * Real.pi) * u + 2 * (2 * Real.pi) := by ring
      simp only [h]
      exact hcircper _)
  obtain ⟨q', hq'⟩ := exists_data_of_periodic_curve
    (g := fun u => waveMoved (psi u))
    (hwavecont.comp hcont) (fun u => by
      simp only [htrans u]
      exact hwaveper _)
  refine ⟨psi, p', q', htrans, hp', hq', ?_⟩
  exact pathDistRigid_le_of_carriers (θ₀ := 0) continuous_kcirc continuous_kwave
    kcirc_periodic kwave_periodic kcirc_total kwave_total hcont htrans hmain
    hasDerivAt_circMoved hasDerivAt_circAngle hasDerivAt_waveMoved hasDerivAt_waveAngle
    hp' hq'

end MatchingPathDistRigidInstance
