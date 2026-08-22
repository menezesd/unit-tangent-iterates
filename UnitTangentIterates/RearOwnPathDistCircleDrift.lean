import Mathlib
import UnitTangentIterates.RearOwnPathDistFrameDrift
import UnitTangentIterates.MarkedSpaceCircle

/-!
# A genuine instance of the path-distance assembly with the rear length free

`RearOwnPathDistFrameDrift.pathDist_le_of_front_frame_variable` bounds the path
pseudodistance of the selected rears of a path of fronts by hypotheses which are
all on the front data, and which no longer force the arclength period of the
rear to be constant: it is only asked to be differentiable in the time.  Those
hypotheses are many, so it is worth checking that they can all be met at once.

They can, by the same front as in `RearOwnPathDistCircle.lean`: the circle of
curvature `1/2`, at rest, with tangent angle `Θ(s) = s/2`, selected steering
angle `arcsin ½`, period `4π` and change of variable `x ↦ x sec(arcsin ½)`.  Its
rear period is the constant `4π cos(arcsin ½)`, which is in particular
differentiable with derivative zero, and the conclusion obtained is again that
the selected rear does not move.

Main result: `restingCircle_instance_variable`.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric RearTrack RearFamilyFrame
  RearOwnArclength RearOwnMotion

namespace RearOwnPathDistCircleDrift

open UniformFrameBounds RearOwnPathDistFrameDrift

/-- **The hypotheses of the path-distance assembly with the rear length free
are met by a genuine instance.**  The resting circle of curvature `1/2`
produces a front to which
`RearOwnPathDistFrameDrift.pathDist_le_of_front_frame_variable` applies — every
one of its hypotheses, geometric, regular and dynamical, holds for it — and the
bound it gives, the cost of the constant path being zero, is that the selected
rear does not move.  The witnesses are explicit: the rear period `Q = 4π cos(arcsin ½)` is
positive, the gauge parameter starts as the rescaled arclength, and the marked
curve `p'` is the selected rear of the circle. -/
theorem restingCircle_instance_variable :
    ∃ (F : ℝ → ℝ → ℂ) (Θ δ sf : ℝ → ℝ → ℝ) (Q : ℝ) (p' : Data) (Phi : ℝ → ℝ → ℝ),
      0 < Q ∧ (∀ u, Phi 0 u = Q * u) ∧ (∀ u, p'.1 u = rearOwn F Θ δ sf 0 (Q * u)) ∧
      ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf 1 (Phi 1 u)) →
        pathDist p' q' ≤ 0 := by
  have hpi := Real.pi_pos
  set A : ℝ := Real.arcsin (1 / 2) with hA
  set c : ℝ := Real.cos A with hc
  have hsinA : Real.sin A = 1 / 2 := Real.sin_arcsin (by norm_num) (by norm_num)
  have hcval : c = Real.sqrt (1 - (1 / 2 : ℝ) ^ 2) := by rw [hc, hA, Real.cos_arcsin]
  have hcpos : 0 < c := by rw [hcval]; positivity
  have hcne : c ≠ 0 := ne_of_gt hcpos
  -- the front data of the resting circle
  set Ff : ℝ → ℝ → ℂ := fun _ s => -2 * Complex.I * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))
    with hFf
  set Th : ℝ → ℝ → ℝ := fun _ s => s / 2 with hTh
  set de : ℝ → ℝ → ℝ := fun _ _ => A with hde
  set sff : ℝ → ℝ → ℝ := fun _ x => x / c with hsff
  set Q : ℝ := 4 * Real.pi * c with hQ
  have hQpos : 0 < Q := by rw [hQ]; positivity
  -- the marked curve reached at time zero
  set Cc : ℂ := -2 * Complex.I - Complex.exp (-(Complex.I * (A : ℂ))) with hCc
  set pf : BoundedContinuousFunction ℝ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u => Cc * normExp u) (by unfold normExp; fun_prop) ‖Cc‖ (fun u => by simp) with hpf
  set p' : Data := (pf, 0, 0) with hp'
  -- the constant path of fronts
  set Γ : NormalPath (circleData 1) (circleData 1) :=
    PathMetric.NormalPath.const (circleData 1) with hΓ
  -- the regularity of the front data
  have hexpC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) (uncurry Ff) := by
    intro n
    have h1 : ContDiff ℝ (n : ℕ) fun p : ℝ × ℝ => Complex.I * ((p.2 / 2 : ℝ) : ℂ) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_snd.div_const 2))
    have h2 := (Complex.contDiff_exp.comp h1).const_smul (-2 * Complex.I)
    have heq : uncurry Ff
        = fun p : ℝ × ℝ => (-2 * Complex.I) • Complex.exp (Complex.I * ((p.2 / 2 : ℝ) : ℂ)) := by
      funext p; simp [hFf, uncurry]
    rw [heq]
    exact h2
  have hThC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) (uncurry Th) := fun n =>
    contDiff_snd.div_const 2
  have hdeC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) (uncurry de) := fun n => contDiff_const
  -- the front is a unit-speed curve with tangent angle `Θ`
  have hF : ∀ t s, HasDerivAt (Ff t) (Complex.exp (Complex.I * (Th t s : ℂ))) s := by
    intro t s
    simp only [hTh]
    have h1 : HasDerivAt (fun s : ℝ => Complex.I * ((s / 2 : ℝ) : ℂ))
        (Complex.I * (1 / 2 : ℂ)) s := by
      have h0 : HasDerivAt (fun s : ℝ => ((s / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ)) s := by
        simpa using (((hasDerivAt_id s).div_const 2)).ofReal_comp
      simpa using h0.const_mul Complex.I
    have h3 := (h1.cexp).const_mul (-2 * Complex.I)
    refine h3.congr_deriv ?_
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hΘd : ∀ t s, HasDerivAt (Th t) ((fun _ _ : ℝ => (1 / 2 : ℝ)) t s) s := by
    intro t s; simpa using (hasDerivAt_id s).div_const 2
  have hsteer : ∀ t s, HasDerivAt (de t)
      ((fun _ _ : ℝ => (1 / 2 : ℝ)) t s - Real.sin (de t s)) s := by
    intro t s; simpa [hde, hsinA] using hasDerivAt_const s A
  -- the change of variable
  have hsfinv : ∀ t x, rearArclength (de t) (sff t x) = x := by
    intro t x
    show rearArclength (fun _ => A) (x / c) = x
    simp only [rearArclength]
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, ← hc]
    field_simp
  have hQconst : ∀ t, rearArclength (de t) ((fun _ => 4 * Real.pi) t) = Q := by
    intro t
    show rearArclength (fun _ => A) (4 * Real.pi) = Q
    simp only [rearArclength]
    rw [intervalIntegral.integral_const]
    simp [← hc, hQ]
  have hQd : ∀ t, HasDerivAt (fun r => rearArclength (de r) ((fun _ => 4 * Real.pi) r))
      ((fun _ => (0 : ℝ)) t) t := by
    intro t
    have hcst : (fun r => rearArclength (de r) ((fun _ => 4 * Real.pi) r)) = fun _ : ℝ => Q :=
      funext hQconst
    rw [hcst]
    exact hasDerivAt_const t Q
  -- the closing relations of the front
  have hFper : ∀ t s, Ff t (s + (fun _ => 4 * Real.pi) t) = Ff t s := by
    intro t s
    show -2 * Complex.I * Complex.exp (Complex.I * (((s + 4 * Real.pi) / 2 : ℝ) : ℂ))
      = -2 * Complex.I * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))
    have hsplit : ((s + 4 * Real.pi) / 2 : ℝ) = (s / 2 : ℝ) + 2 * Real.pi := by ring
    rw [hsplit]
    push_cast
    rw [mul_add, Complex.exp_add,
      show Complex.I * (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I from by ring,
      Complex.exp_two_pi_mul_I, mul_one]
  have hΘper : ∀ t s, Th t (s + (fun _ => 4 * Real.pi) t) = Th t s + 2 * Real.pi := by
    intro t s; show (s + 4 * Real.pi) / 2 = s / 2 + 2 * Real.pi; ring
  -- the rear tangent angle
  have hangC : ContDiff ℝ (3 : ℕ) (uncurry (rearOwnAngle Th de sff)) := by
    have heq : uncurry (rearOwnAngle Th de sff) = fun p : ℝ × ℝ => p.2 / c / 2 - A := rfl
    rw [heq]
    exact ((contDiff_snd.div_const c).div_const 2).sub contDiff_const
  -- the marked curve at time zero is the selected rear of the circle
  have hstart : ∀ u, p'.1 u = rearOwn Ff Th de sff 0 (Q * u) := by
    intro u
    have hs : sff 0 (Q * u) = 4 * Real.pi * u := by
      show Q * u / c = 4 * Real.pi * u
      rw [hQ]; field_simp
    show Cc * normExp u = rearOwn Ff Th de sff 0 (Q * u)
    rw [rearOwn, rearTrack, hs]
    show Cc * normExp u
      = -2 * Complex.I * Complex.exp (Complex.I * (((4 * Real.pi * u) / 2 : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((((4 * Real.pi * u) / 2 : ℝ) - A : ℝ) : ℂ))
    have hhalf : ((4 * Real.pi * u) / 2 : ℝ) = 2 * Real.pi * u := by ring
    rw [hhalf, normExp_eq, hCc]
    push_cast
    rw [show Complex.I * ((2 : ℂ) * (Real.pi : ℂ) * (u : ℂ) - (A : ℂ))
        = Complex.I * ((2 : ℂ) * (Real.pi : ℂ) * (u : ℂ)) + -(Complex.I * (A : ℂ)) from by ring,
      Complex.exp_add,
      show ((2 : ℂ) * (Real.pi : ℂ) * (u : ℂ)) * Complex.I
        = Complex.I * ((2 : ℂ) * (Real.pi : ℂ) * (u : ℂ)) from by ring]
    ring
  -- the assembly
  have hQ0 : rearArclength (de 0) (4 * Real.pi) = Q := hQconst 0
  rw [← hQ0] at hstart
  refine ⟨Ff, Th, de, sff, Q, p', ?_⟩
  obtain ⟨rL, rB, Phi, hPhi0, -, hPhi⟩ := pathDist_le_of_front_frame_variable
    (P0 := 4 * Real.pi)
    (P1 := 4 * Real.pi) (kh := 1 / 2) (Qf' := fun _ => 0) (P := fun _ => 4 * Real.pi)
    (F := Ff) (Fdot := fun _ _ => 0) (Fdots := fun _ _ => 0) (Ydot := fun _ _ => 0)
    (Θ := Th) (δ := de) (K := fun _ _ => 1 / 2) (etaF := fun _ _ => 0)
    (etaFs := fun _ _ => 0) (sf := sff) (sft := fun _ _ => 0) (dt := fun _ _ => 0)
    (Θdot := fun _ _ => 0) (w := fun _ _ => 0) (Θdots := fun _ _ => 0) (ws := fun _ _ => 0)
    Γ p' (by positivity) (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
    hF hΘd hsteer (fun t s => Real.arcsin_nonneg.mpr (by norm_num)) (fun t s => le_rfl)
    (fun t s => rfl) (fun t s => by norm_num) (fun t => continuous_const)
    hFper hΘper (hexpC 1) (hThC 1) (hdeC 1)
    (fun t s => by exact hasDerivAt_const _ _) continuous_const
    (fun t s => by simp [frontNormalVelocityAt, SelectedInverseJacobiODE.frontNormalVelocity])
    (fun t s => hasDerivAt_const s (0 : ℝ)) (fun t => continuous_const) (fun t s => rfl)
    (fun t u => rfl) hsfinv (fun t x => by exact hasDerivAt_const _ _)
    (fun t s => by exact hasDerivAt_const _ _) (fun t s => by exact hasDerivAt_const _ _)
    (fun t s => by exact hasDerivAt_const _ _) (fun t s => hasDerivAt_const s (0 : ℂ))
    (fun t s => hasDerivAt_const s (0 : ℝ)) (fun t s => hasDerivAt_const s (0 : ℝ))
    (hexpC 2) (hThC 2) (hdeC 2)
    (fun t x => by simp [trackVelocity])
    hQd contDiff_const hangC (fun a x => rfl) (fun a x => rfl)
    (fun t _ => by funext x; simp [frameNormal])
    hstart
  rw [hQ0] at hPhi0 hstart
  refine ⟨Phi, hQpos, hPhi0, hstart, fun q' hq' => ?_⟩
  have h := hPhi q' hq'
  rw [hΓ, PathMetric.NormalPath.cost_const, mul_zero] at h
  exact h

end RearOwnPathDistCircleDrift
