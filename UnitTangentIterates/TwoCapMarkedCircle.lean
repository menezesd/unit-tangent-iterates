import Mathlib
import UnitTangentIterates.TwoCapMarked
import UnitTangentIterates.SelectedInverseCircle

/-!
# The two-cap pair of the circle, as a pair of marked curves

`TwoCapMarked.exists_marked_two_cap_pair` puts an exact two-cap pair into the
space of marked curves of `MarkedSpace.lean`.  Besides the embeddedness of the
front — checked there for the constant curvature `1/2` — it carries one further
global hypothesis: that *every* rear track built from an admissible steering
angle of the front is embedded.

This file discharges that hypothesis for the constant curvature `1/2` with
half-period `2π`, whose front is the circle of radius `2`:

* `hasDerivAt_front_kcirc` : the unit tangent of that front is `e^{is/2}`;
* `front_kcirc_eq` : the front is the circle `s ↦ c − 2i e^{is/2}`;
* `injOn_rearTrack_front_kcirc` : every admissible steering angle of it is the
  constant `arcsin(1/2) = π/6`, so its rear track is again a circle, hence
  embedded;
* `marked_two_cap_pair_circle` : consequently the hypotheses of
  `TwoCapMarked.exists_marked_two_cap_pair` are **not vacuous**, and the
  two-cap pair of the circle of radius `2` is a pair of marked curves.
-/

noncomputable section

open Set Function MarkedSpace

namespace TwoCapMarkedCircle

open TwoCapPairsAssembly CurvatureInterpolation TwoCapMarked

/-- The unit tangent of the constant-curvature front is `e^{is/2}`. -/
theorem hasDerivAt_front_kcirc (s : ℝ) :
    HasDerivAt (front kcirc 0 (2 * Real.pi))
      (Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))) s := by
  have h := front_hasDerivAt (kappa := kcirc) (theta0 := 0) (H := 2 * Real.pi)
    continuous_kcirc s
  simpa [frontAngle, tangentAngle_kcirc] using h

/-- The angle `s ↦ s/2` turns at the constant rate `1/2`. -/
theorem hasDerivAt_halfAngle (s : ℝ) :
    HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) s :=
  (hasDerivAt_id s).div_const 2

/-- The constant-curvature front is the circle of radius `2` centred at
`F 0 + 2i`. -/
theorem front_kcirc_eq (s : ℝ) :
    front kcirc 0 (2 * Real.pi) s
      = (front kcirc 0 (2 * Real.pi) 0 + 2 * Complex.I)
        - (2 * Complex.I) * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)) := by
  have h := front_kcirc_sub s 0
  have h0 : tau ((0 : ℝ) / 2) = 1 := by simp [tau]
  have hs : tau (s / 2) = Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)) := by
    rw [tau]; ring_nf
  rw [h0, hs] at h
  linear_combination h

/-- **Every rear track of the constant-curvature front is embedded.**  The
front's curvature is the constant `1/2`, so the only admissible steering angle
is the constant `arcsin(1/2)` and the rear track is again a circle. -/
theorem injOn_rearTrack_front_kcirc (Θ K dl : ℝ → ℝ)
    (hX : ∀ s, HasDerivAt (front kcirc 0 (2 * Real.pi))
      (Complex.exp (Complex.I * (Θ s : ℂ))) s)
    (hΘ : ∀ s, HasDerivAt Θ (K s) s)
    (hdlper : Periodic dl (2 * (2 * Real.pi)))
    (hdlmem : ∀ s, dl s ∈ Icc 0 (Real.arcsin (1 / 2)))
    (hdlode : ∀ s, HasDerivAt dl (K s - Real.sin (dl s)) s) :
    InjOn (RearTrack.rearTrack (front kcirc 0 (2 * Real.pi)) Θ dl)
      (Ico 0 (2 * (2 * Real.pi))) := by
  have hpi := Real.pi_pos
  -- the curvature of the front is the constant `1/2`
  have hKeq : ∀ s, K s = 1 / 2 := fun s =>
    SelectedInverseTube.curvature_unique hX hasDerivAt_front_kcirc hΘ
      (fun t => hasDerivAt_halfAngle t) s
  -- the steering angle is the constant `arcsin (1/2)`
  set d0 : ℝ := Real.arcsin (1 / 2) with hd0
  have hsin : Real.sin d0 = 1 / 2 := Real.sin_arcsin (by norm_num) (by norm_num)
  have hd0nonneg : 0 ≤ d0 := Real.arcsin_nonneg.mpr (by norm_num)
  have hd0le : d0 ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hdlconst : dl = fun _ => d0 := by
    refine Shadowing.steering_unique (K := K) (by linarith) hdlode ?_ hdlper
      (fun s => by simp) ?_ ?_
    · intro s
      have h : K s - Real.sin d0 = 0 := by rw [hKeq s, hsin]; ring
      rw [h]
      exact hasDerivAt_const s d0
    · exact fun s => ⟨by linarith [(hdlmem s).1], le_trans (hdlmem s).2 hd0le⟩
    · exact fun _ => ⟨by linarith, hd0le⟩
  rw [hdlconst]
  -- the rear track is the circle of radius `‖−2i − e^{−i d₀}‖`
  set c : ℂ := front kcirc 0 (2 * Real.pi) 0 + 2 * Complex.I with hc
  set w : ℂ := -(2 * Complex.I) - Complex.exp (Complex.I * ((-d0 : ℝ) : ℂ)) with hw
  have hexp : ∀ s, Complex.exp (Complex.I * (Θ s : ℂ))
      = Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)) :=
    fun s => (hX s).unique (hasDerivAt_front_kcirc s)
  have hform : ∀ s, RearTrack.rearTrack (front kcirc 0 (2 * Real.pi)) Θ (fun _ => d0) s
      = c + Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)) * w := by
    intro s
    have hsplit : ((Θ s - d0 : ℝ) : ℂ) = (Θ s : ℂ) + ((-d0 : ℝ) : ℂ) := by push_cast; ring
    simp only [RearTrack.rearTrack, RearTrack.rearAngle]
    rw [hsplit, mul_add, Complex.exp_add, hexp s, front_kcirc_eq s, hw, ← hc]
    ring
  have hwne : w ≠ 0 := by
    have h1 : ‖Complex.exp (Complex.I * ((-d0 : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have h2 : ‖(-(2 * Complex.I) : ℂ)‖ = 2 := by
      simp
    have h3 : ‖(-(2 * Complex.I) : ℂ)‖ - ‖Complex.exp (Complex.I * ((-d0 : ℝ) : ℂ))‖ ≤ ‖w‖ :=
      norm_sub_norm_le _ _
    rw [h1, h2] at h3
    intro hzero
    rw [hzero] at h3
    simp at h3
  intro s1 h1 s2 h2 heq
  rw [hform s1, hform s2] at heq
  have hcancel : Complex.exp (Complex.I * ((s1 / 2 : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((s2 / 2 : ℝ) : ℂ)) :=
    mul_right_cancel₀ hwne (by linear_combination heq)
  have hdom : Ico (0 : ℝ) (2 * (2 * Real.pi)) = Ico (0 : ℝ) (2 * Real.pi * 2) := by
    ring_nf
  rw [hdom] at h1 h2
  exact SelectedInverseCircle.injOn_expCircle (r := 2) (by norm_num) h1 h2 hcancel

/-- **The hypotheses of `TwoCapMarked.exists_marked_two_cap_pair` are not
vacuous.**  For the constant curvature `1/2` with half-period `2π` — whose
front is the circle of radius `2` and whose rear track is the circle of radius
`√3` — both members of the two-cap pair are members of the tube of marked
curves. -/
theorem marked_two_cap_pair_circle :
    ∃ (qF qR : Data) (dF dR LR : ℝ),
      0 < dF ∧ IsTubeMember (2 * (2 * Real.pi)) (1 / 2) dF qF ∧
        perim qF = 2 * (2 * Real.pi) ∧ ev qF = front kcirc 0 (2 * Real.pi) ∧
      0 < LR ∧ 0 < dR ∧
        IsTubeMember LR ((1 / 2) / Real.sqrt (1 - (1 / 2 : ℝ) ^ 2)) dR qR ∧
        perim qR = LR ∧ LR ≤ 2 * (2 * Real.pi) ∧
        MainTheoremConditional.IsOval (ev qR) ∧
        range (UnitTangent.unitTangentMap (ev qR)) = range (front kcirc 0 (2 * Real.pi)) :=
  exists_marked_two_cap_pair (kmin := 1 / 2) (kap := 1 / 2) (by positivity)
    continuous_kcirc kcirc_periodic (by norm_num) (by norm_num)
    (fun _ => le_rfl) (fun _ => le_rfl) kcirc_total injOn_front_kcirc
    (fun Θ K dl hX hΘ hdlper hdlmem hdlode =>
      injOn_rearTrack_front_kcirc Θ K dl hX hΘ hdlper hdlmem hdlode)

end TwoCapMarkedCircle
