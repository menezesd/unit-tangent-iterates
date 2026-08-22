import Mathlib
import UnitTangentIterates.SelectedInverseFrontPathSmooth
import UnitTangentIterates.SteeringArclengthSmooth
import UnitTangentIterates.SelectedSteeringFamily

/-!
# The selected steering data of a smooth family of fronts

`UnitTangentIterates/SelectedInverseFrontPathSmooth.lean` produces the normal path of
selected rears of a normal path of fronts, from data attached to the family: a
steering angle `δ`, its derivative `w` in the path parameter, the change of
variable `σ` inverting the rear arclength, and the joint `C²` regularity of `δ`.

This file **produces all of that data** from the front curvatures alone.  For a
family of front curvatures `K(a, s)`, `P`-periodic in `s`, pinched by
`0 ≤ K ≤ κ̂ < 1`, jointly `C³` together with its derivative `K̇` in the path
parameter (with the usual Lipschitz and Taylor bounds relating the two):

* `exists_selected_steering_smooth` — there are a selected steering angle `δ`
  and a change of variable `σ` such that `δ(a, ·)` is the `P`-periodic solution
  of `δ_s = K − sin δ` in the selected strip `0 ≤ δ ≤ arcsin κ̂`, `δ` is jointly
  `C⁴`, its derivative in the path parameter is the Green solution
  `w = 𝒢_{cos δ}(K̇)` of the linearized equation `w_s + cos δ · w = K̇`, and
  `σ(a, ·)` inverts the rear arclength `x(s) = ∫₀ˢ cos δ(a, ·)` and is
  differentiable with derivative `1/cos δ`.

* `exists_steering_and_normalPath_smooth` — the composition with
  `SelectedInverseFrontPathSmooth.exists_normalPath_of_front_path_smooth`: for a
  normal path of fronts of a common period `P` given by such a curvature family,
  the selected rears form a normal path whose cost is the uniform constant of
  `PathMetricJacobi` times the cost of the front path.  Nothing about the
  steering angle is assumed any more; only the front family, the front normal
  velocity and the rear data in normal gauge enter the hypotheses.
-/

noncomputable section

open Function Set Real

namespace SelectedInverseSteeringSmooth

open RearTrack RearFamilyFrame RearFrameRegularity SteeringArclengthJointC1

variable {K Kd : ℝ → ℝ → ℝ} {P kh Klip CK : ℝ}

/-- **The selected steering data of a smooth family of fronts exists, and is as
smooth as the curvature family.**  The steering angle is the `P`-periodic
solution of `δ_s = K − sin δ` in the selected strip, it is jointly `C⁴`, its
derivative in the path parameter is the Green solution of the linearized
equation, and the rear arclength has a differentiable inverse. -/
theorem exists_selected_steering_smooth (hP : 0 < P) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hKper : ∀ a, Function.Periodic (K a) P) (hK0 : ∀ a s, 0 ≤ K a s)
    (hKk : ∀ a s, K a s ≤ kh) (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hK3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKd3 : ContDiff ℝ (3 : ℕ) (uncurry Kd)) :
    ∃ delta σ : ℝ → ℝ → ℝ,
      (∀ a, Function.Periodic (delta a) P) ∧
      (∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kh)) ∧
      (∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s) ∧
      (∀ a s, HasDerivAt (fun b => delta b s) (arcVariation Kd delta P a s) a) ∧
      (∀ a s, HasDerivAt (arcVariation Kd delta P a)
        (-Real.cos (delta a s) * arcVariation Kd delta P a s + Kd a s) s) ∧
      ContDiff ℝ (4 : ℕ) (uncurry delta) ∧
      (∀ a x, rearArclength (delta a) (σ a x) = x) ∧
      (∀ a x, HasDerivAt (σ a) (1 / Real.cos (delta a (σ a x))) x) := by
  have hKc : ∀ a, Continuous (K a) := fun a =>
    hK3.continuous.comp (continuous_const.prodMk continuous_id)
  -- the steering angle of each slice
  have hex : ∀ a, ∃ d : ℝ → ℝ, Function.Periodic d P ∧
      (∀ s, d s ∈ Icc 0 (arcsin kh)) ∧
      (∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (d s)) ∧
      (∀ s, HasDerivAt d (K a s - Real.sin (d s)) s) := fun a =>
    SteeringExistence.exists_periodic_steering hP (hKc a) (hKper a) hkh0 hkh1.le
      (hK0 a) (hKk a)
  choose delta hper hrange hcosge hode using hex
  have hdc : ∀ a, Continuous (delta a) := fun a =>
    Differentiable.continuous fun s => (hode a s).differentiableAt
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  -- the change of variable
  have hinv : ∀ a, ∃ g : ℝ → ℝ, ∀ x, rearArclength (delta a) (g x) = x := fun a =>
    ArclengthInverse.exists_inverse_rearArclength hkh0 hkh1 (hdc a)
      (fun s => (hrange a s).1) (fun s => (hrange a s).2)
  choose σ hσinv using hinv
  refine ⟨delta, σ, hper, hrange, hode, ?_, ?_, ?_, hσinv, ?_⟩
  · exact fun a s => hasDerivAt_param_arc hP hkh0 hkh1 hKd3.continuous hode hper hrange
      hKdper hKlip hKtaylor hCK a s
  · exact fun a s => hasDerivAt_arcVariation hP hkh0 hkh1 hKd3.continuous hode hrange hper
      hKdper a s
  · exact SteeringArclengthSmooth.contDiff_four_uncurry_delta_arc hP hkh0 hkh1 hode hper
      hrange hKdper hKlip hKtaylor hCK hK3 hKd3
  · intro a x
    exact ArclengthInverse.hasDerivAt_of_rightInverse hcpos
      (fun s => hasDerivAt_rearArclength (hdc a) s) (fun s => hcosge a s) (hσinv a) x

/-- **The selected rears of a smooth path of fronts form a normal path**, with
the steering data produced rather than assumed.  The fronts `F(a, ·)` are
unit-speed curves of tangent angle `Θ(a, ·)` and curvature `K(a, ·)`, all of the
common period `P`, depending smoothly on the path parameter `a`; the curvatures
satisfy the tube bounds `0 ≤ K ≤ κ̂ < 1`.  Then there are a selected steering
angle `δ` and a change of variable `σ` as in
`exists_selected_steering_smooth`, and for any rear family in normal gauge whose
normal velocity is the one computed from the front data, the rears form a normal
path of cost the uniform constant of `PathMetricJacobi` times the cost of the
front path. -/
theorem exists_steering_and_normalPath_smooth {p q p' q' : MarkedSpace.Data}
    (Γ : PathMetric.NormalPath p q)
    {Θ Θdot Θdots : ℝ → ℝ → ℝ} {F Fdot Fdots : ℝ → ℝ → ℂ}
    (hP : 0 < P) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hKper : ∀ a, Function.Periodic (K a) P) (hK0 : ∀ a s, 0 ≤ K a s)
    (hKk : ∀ a s, K a s ≤ kh) (hKdper : ∀ a, Function.Periodic (Kd a) P)
    (hKlip : ∀ a b s, |K a s - K b s| ≤ Klip * |a - b|)
    (hKtaylor : ∀ a b s, |K a s - K b s - (a - b) * Kd b s| ≤ CK * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hK3 : ContDiff ℝ (3 : ℕ) (uncurry K))
    (hKd3 : ContDiff ℝ (3 : ℕ) (uncurry Kd))
    (hF : ∀ a s, HasDerivAt (F a) (Complex.exp (Complex.I * (Θ a s : ℂ))) s)
    (hΘ : ∀ a s, HasDerivAt (Θ a) (K a s) s)
    (hFa : ∀ a s, HasDerivAt (fun b => F b s) (Fdot a s) a)
    (hΘa : ∀ a s, HasDerivAt (fun b => Θ b s) (Θdot a s) a)
    (hFdots : ∀ a s, HasDerivAt (Fdot a) (Fdots a s) s)
    (hΘdots : ∀ a s, HasDerivAt (Θdot a) (Θdots a s) s)
    (hFc2 : ContDiff ℝ (2 : ℕ) (uncurry F))
    (hΘc2 : ContDiff ℝ (2 : ℕ) (uncurry Θ)) :
    ∃ delta σ : ℝ → ℝ → ℝ,
      (∀ a, Function.Periodic (delta a) P) ∧
      (∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin kh)) ∧
      (∀ a s, HasDerivAt (delta a) (K a s - Real.sin (delta a s)) s) ∧
      (∀ a x, rearArclength (delta a) (σ a x) = x) ∧
      ∀ (etaFs : ℝ → ℝ → ℝ) (XR nuR : ℝ → ℝ → ℂ),
        (∀ t s, HasDerivAt (frontNormalVelocityAt Fdot Θ delta t) (etaFs t s) s) →
        (∀ t, Continuous (etaFs t)) →
        (∀ t, Function.Periodic (frontNormalVelocityAt Fdot Θ delta t) P) →
        (∀ t, Function.Periodic
          (fun x => frameNormal
            (frameRdot Fdot Θdot (arcVariation Kd delta P) Θ delta (σ t))
            (frameAngle Θ delta (σ t)) t x)
          (rearArclength (delta t) P)) →
        (∀ t u, Γ.eta t u = frontNormalVelocityAt Fdot Θ delta t (P * u)) →
        (∀ u, XR 0 u = p'.1 u) → (∀ u, XR Γ.T u = q'.1 u) →
        (∀ t u, HasDerivAt (fun r => XR r u)
          ((frameNormal (frameRdot Fdot Θdot (arcVariation Kd delta P) Θ delta (σ t))
            (frameAngle Θ delta (σ t)) t (rearArclength (delta t) P * u) : ℂ) * nuR t u) t) →
        (∀ u, Continuous fun t =>
          (frameNormal (frameRdot Fdot Θdot (arcVariation Kd delta P) Θ delta (σ t))
            (frameAngle Θ delta (σ t)) t (rearArclength (delta t) P * u) : ℂ) * nuR t u) →
        (∀ t u, ‖nuR t u‖ = 1) →
        ∃ Δ : PathMetric.NormalPath p' q', Δ.T = Γ.T ∧
          PathMetric.NormalPath.cost Δ = PathMetricJacobi.jacobiConst
            (SelectedInversePathGeometry.uconstW P P (Real.sqrt (1 - kh ^ 2)))
            (SelectedInversePathGeometry.uconst0 P P (Real.sqrt (1 - kh ^ 2)))
            (SelectedInversePathGeometry.uconst1 P P (Real.sqrt (1 - kh ^ 2)))
            (SelectedInversePathGeometry.uconst2 P P (Real.sqrt (1 - kh ^ 2)) kh)
            * PathMetric.NormalPath.cost Γ := by
  obtain ⟨delta, σ, hper, hrange, hode, hdpar, hwode, hd4, hσinv, hσd⟩ :=
    exists_selected_steering_smooth hP hkh0 hkh1 hKper hK0 hKk hKdper hKlip hKtaylor hCK
      hK3 hKd3
  refine ⟨delta, σ, hper, hrange, hode, hσinv, ?_⟩
  intro etaFs XR nuR hetaFd hetaFsc hetaFper hetaRper hlink hstart hfinish hderiv hcont hnu
  have hcpos : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcosne : ∀ t y, Real.cos (delta t y) ≠ 0 := by
    intro t y
    exact ne_of_gt (lt_of_lt_of_le hcpos
      (Shadowing.cos_ge_of_mem_strip (hrange t y).1 (hrange t y).2))
  have hd2 : ContDiff ℝ (2 : ℕ) (uncurry delta) := by
    refine hd4.of_le ?_
    exact_mod_cast (by norm_num : ((2 : ℕ) : ℕ) ≤ (4 : ℕ))
  exact SelectedInverseFrontPathSmooth.exists_normalPath_of_front_path_smooth Γ
    (P0 := P) (P1 := P) (kh := kh) (P := fun _ => P)
    (F := fun _ => F) (Θ := fun _ => Θ) (δ := fun _ => delta) (K := fun _ => K)
    (σ := σ) (Fdot := fun _ => Fdot) (Θdot := fun _ => Θdot)
    (w := fun _ => arcVariation Kd delta P)
    (Fdots := Fdots) (Θdots := Θdots)
    (ws := fun t s => -Real.cos (delta t s) * arcVariation Kd delta P t s + Kd t s)
    (etaFs := etaFs) (XR := XR) (nuR := nuR)
    hP hkh0 hkh1 (fun _ => le_rfl) (fun _ => le_rfl)
    (fun t s => (hrange t s).1) (fun t s => (hrange t s).2) (fun t => hper t)
    (fun t s => abs_le.mpr ⟨by linarith [hK0 t s, hKk t s], hKk t s⟩)
    hcosne (fun t x => hσinv t x) (fun t x => hσd t x)
    (fun _ a s => hF a s) (fun _ a s => hΘ a s) (fun _ a s => hode a s)
    (fun _ a s => hFa a s) (fun _ a s => hΘa a s) (fun _ a s => hdpar a s)
    (fun t s => hFdots t s) (fun t s => hΘdots t s) (fun t s => hwode t s)
    (fun _ => hFc2) (fun _ => hΘc2) (fun _ => hd2)
    hetaFd hetaFsc hetaFper hetaRper hlink hstart hfinish hderiv hcont hnu

/-! ### Non-vacuity -/

/-- **The hypotheses of `exists_selected_steering_smooth` allow a front
curvature that is not constant along the front and genuinely moves with the path
parameter**: they hold for `K(a, s) = 1/4 + (cos a · sin s)/8`, of period `2π`,
with `κ̂ = 1/2`.  So the steering data produced above is not the data of a path
of circles. -/
theorem exists_selected_steering_smooth_nonconstant :
    ∃ delta σ : ℝ → ℝ → ℝ,
      (∀ a, Function.Periodic (delta a) (2 * π)) ∧
      (∀ a s, delta a s ∈ Icc (0 : ℝ) (arcsin (1 / 2))) ∧
      (∀ a s, HasDerivAt (delta a)
        ((1 / 4 + Real.cos a * Real.sin s / 8) - Real.sin (delta a s)) s) ∧
      ContDiff ℝ (4 : ℕ) (uncurry delta) ∧
      (∀ a x, rearArclength (delta a) (σ a x) = x) := by
  have hcos_taylor : ∀ a b : ℝ, |Real.cos a - Real.cos b + Real.sin b * (a - b)|
      ≤ (a - b) ^ 2 := by
    intro a b
    have h := SteeringSmoothDependence.abs_sin_taylor (b + π / 2) (a - b)
    have h1 : b + π / 2 + (a - b) = a + π / 2 := by ring
    rw [h1, Real.sin_add_pi_div_two, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two] at h
    calc |Real.cos a - Real.cos b + Real.sin b * (a - b)|
        = |Real.cos a - Real.cos b - -Real.sin b * (a - b)| := by ring_nf
      _ ≤ (a - b) ^ 2 := h
  obtain ⟨delta, σ, hper, hrange, hode, -, -, hd4, hσinv, -⟩ :=
    exists_selected_steering_smooth (K := fun a s => 1 / 4 + Real.cos a * Real.sin s / 8)
      (Kd := fun a s => -(Real.sin a * Real.sin s / 8)) (P := 2 * π) (kh := 1 / 2)
      (Klip := 1 / 8) (CK := 1 / 8)
      (by positivity) (by norm_num) (by norm_num)
      (fun a s => by simp [Real.sin_add_two_pi])
      (fun a s => by
        have h1 := Real.neg_one_le_cos a
        have h2 := Real.neg_one_le_sin s
        nlinarith [Real.cos_le_one a, Real.sin_le_one s, abs_nonneg (Real.cos a),
          abs_le.mpr ⟨Real.neg_one_le_cos a, Real.cos_le_one a⟩,
          abs_le.mpr ⟨Real.neg_one_le_sin s, Real.sin_le_one s⟩,
          abs_mul (Real.cos a) (Real.sin s), le_abs_self (Real.cos a * Real.sin s)])
      (fun a s => by
        nlinarith [abs_mul (Real.cos a) (Real.sin s), le_abs_self (Real.cos a * Real.sin s),
          abs_le.mpr ⟨Real.neg_one_le_cos a, Real.cos_le_one a⟩,
          abs_le.mpr ⟨Real.neg_one_le_sin s, Real.sin_le_one s⟩,
          abs_nonneg (Real.cos a), abs_nonneg (Real.sin s)])
      (fun a s => by simp [Real.sin_add_two_pi])
      (fun a b s => by
        have h : (1 / 4 + Real.cos a * Real.sin s / 8) - (1 / 4 + Real.cos b * Real.sin s / 8)
            = (Real.cos a - Real.cos b) * Real.sin s / 8 := by ring
        rw [h, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (8:ℝ))]
        have hs : |Real.sin s| ≤ 1 := Real.abs_sin_le_one s
        have hc : |Real.cos a - Real.cos b| ≤ |a - b| := by
          have := Real.lipschitzWith_cos.dist_le_mul a b
          simpa [Real.dist_eq] using this
        have h0 : 0 ≤ |Real.cos a - Real.cos b| := abs_nonneg _
        have : |Real.cos a - Real.cos b| * |Real.sin s| ≤ |a - b| * 1 :=
          mul_le_mul hc hs (abs_nonneg _) (abs_nonneg _)
        linarith)
      (fun a b s => by
        have h : (1 / 4 + Real.cos a * Real.sin s / 8) - (1 / 4 + Real.cos b * Real.sin s / 8)
              - (a - b) * -(Real.sin b * Real.sin s / 8)
            = (Real.cos a - Real.cos b + Real.sin b * (a - b)) * Real.sin s / 8 := by ring
        rw [h, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (8:ℝ))]
        have hs : |Real.sin s| ≤ 1 := Real.abs_sin_le_one s
        have h0 : 0 ≤ |Real.cos a - Real.cos b + Real.sin b * (a - b)| := abs_nonneg _
        have := mul_le_mul (hcos_taylor a b) hs (abs_nonneg _) (by positivity)
        simp only [mul_one] at this
        linarith)
      (by norm_num) (by fun_prop) (by fun_prop)
  exact ⟨delta, σ, hper, hrange, hode, hd4, hσinv⟩

/-- **The hypotheses of `exists_steering_and_normalPath_smooth` are
consistent.**  They hold for the constant path of the circle of radius `2`,
`F(a, s) = -2i e^{is/2}`, of curvature `1/2`, with `κ̂ = 1/2`; the selected
steering angle it produces is a genuine periodic solution of the steering
equation. -/
theorem steering_normalPath_smooth_nonvacuous {P : ℝ} (hP : 0 < P)
    {p q : MarkedSpace.Data} (Γ : PathMetric.NormalPath p q) :
    ∃ delta σ : ℝ → ℝ → ℝ, (∀ a, Function.Periodic (delta a) P) ∧
      (∀ a s, HasDerivAt (delta a) ((1 / 2 : ℝ) - Real.sin (delta a s)) s) ∧
      ∀ a x, rearArclength (delta a) (σ a x) = x := by
  have hFront : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => -2 * Complex.I
      * Complex.exp (Complex.I * ((s' / 2 : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))) s := by
    intro s
    have hlin : HasDerivAt (fun s' : ℝ => Complex.I * ((s' / 2 : ℝ) : ℂ))
        (Complex.I * (1 / 2 : ℂ)) s := by
      have h : HasDerivAt (fun s' : ℝ => ((s' / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ)) s := by
        simpa using (((hasDerivAt_id s).div_const 2).ofReal_comp)
      simpa using h.const_mul Complex.I
    have hexp := hlin.cexp
    refine (hexp.const_mul (-2 * Complex.I)).congr_deriv ?_
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hco : ContDiff ℝ (2 : ℕ) fun p : ℝ × ℝ => ((p.2 / 2 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_snd.div_const 2)
  have hFc2 : ContDiff ℝ (2 : ℕ) (uncurry fun (_ s : ℝ) =>
      -2 * Complex.I * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ))) :=
    contDiff_const.mul
      (((Complex.contDiff_exp (𝕜 := ℂ) (n := (2 : ℕ))).restrict_scalars ℝ).comp
        (contDiff_const.mul hco))
  obtain ⟨delta, σ, hper, -, hode, hσinv, -⟩ :=
    exists_steering_and_normalPath_smooth (p' := p) (q' := p) Γ
      (K := fun _ _ => 1 / 2) (Kd := fun _ _ => 0) (Klip := 0) (CK := 0)
      (Θ := fun _ s => s / 2) (Θdot := fun _ _ => 0) (Θdots := fun _ _ => 0)
      (F := fun _ s => -2 * Complex.I * Complex.exp (Complex.I * ((s / 2 : ℝ) : ℂ)))
      (Fdot := fun _ _ => 0) (Fdots := fun _ _ => 0)
      hP (by norm_num) (by norm_num)
      (fun _ _ => rfl) (fun _ _ => by norm_num) (fun _ _ => le_rfl) (fun _ _ => rfl)
      (fun a b s => by simp) (fun a b s => by simp) le_rfl
      (by fun_prop) (by fun_prop)
      (fun _ s => hFront s) (fun _ s => by simpa using ((hasDerivAt_id s).div_const 2))
      (fun a s => hasDerivAt_const a _) (fun a s => hasDerivAt_const a _)
      (fun a s => hasDerivAt_const s (0 : ℂ)) (fun a s => hasDerivAt_const s (0 : ℝ))
      hFc2 (by fun_prop)
  exact ⟨delta, σ, hper, hode, hσinv⟩

end SelectedInverseSteeringSmooth
