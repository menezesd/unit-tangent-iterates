import UnitTangentIterates.ConstructedProfileInterior
import UnitTangentIterates.PulseRelativeAssembly
import UnitTangentIterates.HairpinTailsInterior
import UnitTangentIterates.HairpinTails
import UnitTangentIterates.PulseRelativeInterior

/-!
# Discharging the relative bounds from the interior package

§34 showed the constructed profile supplies `InteriorPhaseData`, the barriers and
the order-zero curvature tail.  This file starts turning that package into the
`hrelj` hypotheses themselves, rather than assuming them.

* `harnack_shift_of_interior` — the bounded-shift Harnack comparison between
  the rear point `s + s₀` and the front point `x s`, with the constant explicit:

  ```
    K_*(θ(s+s₀)) ≤ (Am/m)·exp((|s₀| + A²M/2)/m) · K_*(θ(x s)).
  ```

  The shift bound `|s − x s| ≤ A²M/2` is the interior difference form of §17.

* `rel_pulse_one_of_interior` — order one of `hrelj`, with **every** hypothesis
  of `rel_pulse_one_of_identity` discharged from the interior package: the
  identity from `front_curvature_identity_shifted` applied to the
  `InteriorPhaseData`, the uniform bound `sup y ≤ 1/√(1+m²) < 1` from the
  barrier, and the Harnack comparison above.

Orders two to four need the same treatment, with the additional derivative
witnesses and constants their lemmas take.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Set Real HairpinRelative

open scoped ContDiff


/-- The bounded shift and the Harnack comparison, for interior data. -/
theorem harnack_shift_of_interior {f theta x : ℝ → ℝ} {m Am A M s0 : ℝ}
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M) :
    ∀ s, curvField f (theta (s + s0))
      ≤ (Am / m) * Real.exp ((|s0| + A ^ 2 * M / 2) / m)
        * curvField f (theta (x s)) := by
  have hkc : Continuous fun u => curvField f (theta u) :=
    continuous_curv_along_theta hf hfpos hmem hderiv
  have hnn : ∀ u, 0 ≤ curvField f (theta u) := fun u =>
    (curvField_pos_interior hfpos (hmem u)).le
  intro s
  have hshift : |s - x s| ≤ A ^ 2 * M / 2 := by
    have h := HairpinTailsInterior.abs_frontArclength_sub_le_of_comp hkc hnn
      hdecay hM (x s)
    rw [hxinv s] at h
    exact h
  have hD : |s + s0 - x s| ≤ |s0| + A ^ 2 * M / 2 := by
    have : s + s0 - x s = s0 + (s - x s) := by ring
    rw [this]
    exact le_trans (abs_add_le _ _) (by linarith [le_of_eq (abs_of_nonneg (abs_nonneg s0)).symm])
  exact HairpinTails.curvField_shift_harnack_along_theta hm hmA hmem hderiv
    (fun t => hlow _ (hmem t)) (fun t => hupp _ (hmem t))
    (by positivity) hD

/-- **Order one of `hrelj`, for interior data.**  Every hypothesis of
`rel_pulse_one_of_identity` is discharged from the interior package. -/
theorem rel_pulse_one_of_interior {f theta x g gp yp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M)
    (hypd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s) :
    ∀ s, |yp s|
      ≤ ((Am / m) * Real.exp ((|Hairpin.hairpinArclength f (π / 2) (g (π / 2))|
            + A ^ 2 * M / 2) / m)
          / Real.sqrt (1 - (1 / Real.sqrt (1 + m ^ 2)) ^ 2) + 1)
        * pulseField f (theta (x s)) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  set s0 := Hairpin.hairpinArclength f (π / 2) (g (π / 2)) with hs0
  set b := 1 / Real.sqrt (1 + m ^ 2) with hbdef
  have hb0 : (0:ℝ) ≤ b := by positivity
  have hb1 : b < 1 := one_div_sqrt_one_add_sq_lt_one hm
  have hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)) := fun s =>
    pulseField_nonneg_interior hfpos (d.angle_mem (x s))
  have hsup : ∀ s, pulseField f (theta (x s)) ≤ b := fun s =>
    pulseField_le_of_barrier hm (hlow _ (d.angle_mem (x s))) (d.angle_mem (x s))
  have hKnn : ∀ s, 0 ≤ curvField f (theta (s + s0)) := fun s =>
    (curvField_pos_interior hfpos (d.angle_mem (s + s0))).le
  have hharn := harnack_shift_of_interior (s0 := s0) hm hmA hf hfpos hlow hupp
    d.angle_mem d.angle_deriv d.inverse_value hdecay hM
  have hCh : (0:ℝ) ≤ (Am / m) * Real.exp ((|s0| + A ^ 2 * M / 2) / m) := by
    have : (0:ℝ) ≤ Am / m := div_nonneg (le_trans hm.le hmA) hm.le
    positivity
  have hident : ∀ s, curvField f (theta (s + s0))
      = pulseField f (theta (x s))
        + FrontPeriodization.G (pulseField f (theta (x s))) * yp s := by
    intro s
    have h := CanonicalTranslatorLocalPhase.front_curvature_identity_shifted
      d d.x_zero hypd (s + s0)
    simpa [hs0] using h
  exact rel_pulse_one_of_identity hb0 hb1 hCh hy0 hsup hKnn hident hharn

/-- The front coordinate is surjective. -/
theorem surjective_x_of_inverse {f theta x : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s) :
    Function.Surjective x := by
  have hkc : Continuous fun u => curvField f (theta u) :=
    continuous_curv_along_theta hf hfpos hmem hderiv
  have hd := HairpinTailsInterior.hasDerivAt_frontArclength_of_comp hkc
  have hmono : StrictMono (frontArclength f theta) := by
    refine strictMono_of_deriv_pos fun u => ?_
    rw [(hd u).deriv]
    exact lt_of_lt_of_le one_pos
      (HairpinPulseIdentity.one_le_sqrt_one_add_curv_sq f (theta u))
  intro u
  refine ⟨frontArclength f theta u, ?_⟩
  exact hmono.injective (hxinv (frontArclength f theta u))

/-- The pulse state sweeps the whole open interval. -/
theorem surjective_pulseState {f theta x : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z) :
    ∀ z ∈ Ioo (0:ℝ) π, ∃ s, theta (x s) = z := by
  intro z hz
  obtain ⟨u, hu⟩ := hsurj z hz
  obtain ⟨s, hs⟩ := surjective_x_of_inverse hf hfpos hmem hderiv hxinv u
  exact ⟨s, by rw [hs, hu]⟩

/-- The flow identity for the pulse at order one. -/
theorem yp_eq_deriv_mul {f theta x yp : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hypd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s) :
    ∀ s, yp s = deriv (pulseField f) (theta (x s))
      * pulseField f (theta (x s)) := by
  intro s
  have hdiff : DifferentiableAt ℝ (pulseField f) (theta (x s)) :=
    ((contDiffOn_pulseField hf hfpos).contDiffAt
      (isOpen_Ioo.mem_nhds (hmem (x s)))).differentiableAt (by norm_num)
  have hchain := hdiff.hasDerivAt.comp s (hw s)
  exact (hypd s).unique hchain

/-- Hence the angle-derivative of the pulse field is bounded on `(0,π)`. -/
theorem abs_deriv_pulseField_le_of_flow {f theta x yp : ℝ → ℝ} {D1 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hypd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s)
    (hb : ∀ s, |yp s| ≤ D1 * pulseField f (theta (x s))) :
    ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ D1 := by
  intro t ht
  obtain ⟨s, hs⟩ := surjective_pulseState hf hfpos hmem hderiv hxinv hsurj t ht
  have hpos : 0 < pulseField f (theta (x s)) := by
    rw [hs]
    exact div_pos (curvField_pos_interior hfpos ht) (sqrt_one_add_sq_pos _)
  have h := hb s
  rw [yp_eq_deriv_mul hf hfpos hmem hw hypd s, abs_mul,
    abs_of_pos hpos] at h
  rw [← hs]
  exact le_of_mul_le_mul_right (by linarith) hpos

/-- The solved identity from the unsolved one. -/
theorem solved_of_ident {f theta x yp : ℝ → ℝ} {s0 : ℝ}
    (hident : ∀ s, curvField f (theta (s + s0))
      = pulseField f (theta (x s))
        + FrontPeriodization.G (pulseField f (theta (x s))) * yp s) :
    ∀ r, yp r = Real.sqrt (1 - pulseField f (theta (x r)) ^ 2)
      * (curvField f (theta (r + s0)) - pulseField f (theta (x r))) := by
  intro r
  have hsq := one_sub_pulseField_sq_pos f (theta (x r))
  have hs : 0 < Real.sqrt (1 - pulseField f (theta (x r)) ^ 2) :=
    Real.sqrt_pos.mpr hsq
  have h := hident r
  rw [FrontPeriodization.G] at h
  have h2 : curvField f (theta (r + s0)) - pulseField f (theta (x r))
      = (Real.sqrt (1 - pulseField f (theta (x r)) ^ 2))⁻¹ * yp r := by
    linarith [h]
  rw [h2]
  field_simp

/-- The order-one curvature bound in the shifted form the higher pulse orders
consume. -/
theorem hKd_bound_of_interior {f theta : ℝ → ℝ} {b D1 s0 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hyb : ∀ t ∈ Ioo (0:ℝ) π, |pulseField f t| ≤ b)
    (hdb : ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ D1)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) :
    ∀ s, |deriv (fun r => curvField f (theta (r + s0))) s|
      ≤ (D1 / Real.sqrt (1 - b ^ 2) ^ 3) * curvField f (theta (s + s0)) := by
  have hK := relK_of_pulse_deriv_bound hf hfpos hb0 hb1 hyb hdb hmem hderiv
  have h1 : ∀ u, |iteratedDeriv 1 (fun r => curvField f (theta r)) u|
      ≤ (D1 / Real.sqrt (1 - b ^ 2) ^ 3) * curvField f (theta u) := by
    intro u
    rw [iteratedDeriv_one]
    exact hK u
  intro s
  have h := shifted_curv_bound (s0 := s0) h1 s
  rwa [iteratedDeriv_one] at h

/-- The curvature along the shifted angle is differentiable. -/
theorem hasDerivAt_shifted_curv {f theta : ℝ → ℝ} {s0 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) (s : ℝ) :
    HasDerivAt (fun r => curvField f (theta (r + s0)))
      (deriv (fun r => curvField f (theta (r + s0))) s) s := by
  have hG : DifferentiableAt ℝ (curvField f) (theta (s + s0)) :=
    ((HairpinInteriorRegularity.contDiffOn_curvField hf hfpos).contDiffAt
      (isOpen_Ioo.mem_nhds (hmem (s + s0)))).differentiableAt (by norm_num)
  have hsh : HasDerivAt (fun r : ℝ => r + s0) 1 s := by
    simpa using (hasDerivAt_id s).add_const s0
  have h1 : DifferentiableAt ℝ (fun u => curvField f (theta u)) (s + s0) :=
    hG.comp _ (hderiv (s + s0)).differentiableAt
  have h2 := h1.comp s hsh.differentiableAt
  have h : DifferentiableAt ℝ (fun r => curvField f (theta (r + s0))) s := by
    simpa [Function.comp] using h2
  exact h.hasDerivAt

/-- **Order two of `hrelj`, discharged from the interior package.** -/
theorem rel_pulse_two_of_interior {f theta x g gp yp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hypd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s) :
    ∃ D2 : ℝ, 0 ≤ D2 ∧ ∀ s,
      |iteratedDeriv 2 (fun r => pulseField f (theta (x r))) s|
        ≤ D2 * pulseField f (theta (x s)) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  set s0 := Hairpin.hairpinArclength f (π / 2) (g (π / 2)) with hs0
  set b := 1 / Real.sqrt (1 + m ^ 2) with hbdef
  have hb0 : (0:ℝ) ≤ b := by positivity
  have hb1 : b < 1 := one_div_sqrt_one_add_sq_lt_one hm
  have hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)) := fun s =>
    pulseField_nonneg_interior hfpos (d.angle_mem (x s))
  have hsup : ∀ s, pulseField f (theta (x s)) ≤ b := fun s =>
    pulseField_le_of_barrier hm (hlow _ (d.angle_mem (x s))) (d.angle_mem (x s))
  have hKnn : ∀ s, 0 ≤ curvField f (theta (s + s0)) := fun s =>
    (curvField_pos_interior hfpos (d.angle_mem (s + s0))).le
  have hharnack := harnack_shift_of_interior (s0 := s0) hm hmA hf hfpos hlow hupp
    d.angle_mem d.angle_deriv d.inverse_value hdecay hM
  set Ch := (Am / m) * Real.exp ((|s0| + A ^ 2 * M / 2) / m) with hChdef
  have hCh : (0:ℝ) ≤ Ch := by
    have : (0:ℝ) ≤ Am / m := div_nonneg (le_trans hm.le hmA) hm.le
    positivity
  have hident : ∀ s, curvField f (theta (s + s0))
      = pulseField f (theta (x s))
        + FrontPeriodization.G (pulseField f (theta (x s))) * yp s := by
    intro s
    simpa [hs0] using
      CanonicalTranslatorLocalPhase.front_curvature_identity_shifted d d.x_zero
        hypd (s + s0)
  set D1 := Ch / Real.sqrt (1 - b ^ 2) + 1 with hD1def
  have hD1 : 0 ≤ D1 := by
    have : (0:ℝ) ≤ Ch / Real.sqrt (1 - b ^ 2) := by positivity
    linarith
  have hypb : ∀ s, |yp s| ≤ D1 * pulseField f (theta (x s)) :=
    rel_pulse_one_of_interior d hm hmA hf hlow hupp hdecay hM hypd
  -- the angle-variable pulse derivative bound
  have hdb : ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ D1 :=
    abs_deriv_pulseField_le_of_flow hf hfpos d.angle_mem d.angle_deriv
      d.inverse_value hsurj d.state_deriv hypd hypb
  have hyb : ∀ t ∈ Ioo (0:ℝ) π, |pulseField f t| ≤ b := by
    intro t ht
    rw [abs_of_nonneg (pulseField_nonneg_interior hfpos ht)]
    exact pulseField_le_of_barrier hm (hlow t ht) ht
  set E1 := D1 / Real.sqrt (1 - b ^ 2) ^ 3 with hE1def
  have hE1 : 0 ≤ E1 := by positivity
  have hKdb := hKd_bound_of_interior (s0 := s0) hf hfpos hb0 hb1 hyb hdb
    d.angle_mem d.angle_deriv
  have hKdd := hasDerivAt_shifted_curv (s0 := s0) hf hfpos d.angle_mem d.angle_deriv
  have hharn := harnack_pulse_form hb0 hb1 hCh hy0 hsup hharnack
  have hbound := rel_pulse_two_of_identity hb0 hb1 hCh hD1 hE1 hy0 hsup hKnn
    (solved_of_ident hident) hypd hKdd hypb hKdb hharn
  refine ⟨b ^ 2 * D1 * (Ch / Real.sqrt (1 - b ^ 2) + 1)
      / Real.sqrt (1 - b ^ 2) + E1 * Ch / Real.sqrt (1 - b ^ 2) + D1, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ Ch / Real.sqrt (1 - b ^ 2) := by positivity
    have h2 : (0:ℝ) ≤ b ^ 2 * D1 * (Ch / Real.sqrt (1 - b ^ 2) + 1)
        / Real.sqrt (1 - b ^ 2) := by positivity
    have h3 : (0:ℝ) ≤ E1 * Ch / Real.sqrt (1 - b ^ 2) := by positivity
    linarith
  · intro s
    rw [iteratedDeriv_two_eq hypd s]
    exact hbound s

/-- **Flow bound to coefficient bound, at every order.**  The relative bound
along the flow transfers to a bound on the flow coefficient over `(0,π)`,
because the pulse state is onto. -/
theorem abs_coeff_pulse_le_of_flow {f theta x : ℝ → ℝ} {D : ℝ} {j : ℕ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hb : ∀ s, |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
      ≤ D * pulseField f (theta (x s))) :
    ∀ t ∈ Ioo (0:ℝ) π, |RelativeDerivatives.coeff (pulseField f) j t| ≤ D := by
  intro t ht
  obtain ⟨s, hs⟩ := surjective_pulseState hf hfpos hmem hderiv hxinv hsurj t ht
  have hflow := RelativeDerivatives.iteratedDeriv_flow_of_isOpen isOpen_Ioo
    (contDiffOn_pulseField hf hfpos) (fun u => hmem (x u)) hw j
  have hpos : 0 < pulseField f t := by
    rw [pulseField]
    exact div_pos (curvField_pos_interior hfpos ht) (sqrt_one_add_sq_pos _)
  have h := hb s
  rw [congrFun hflow s, hs, abs_mul, abs_of_pos hpos] at h
  exact le_of_mul_le_mul_left (by linarith [h]) hpos

/-- `coeff (pulseField f) 2 = (y')² + y y''` on the open interval. -/
theorem coeff_pulseField_two_eq {f : ℝ → ℝ} {pd pdd : ℝ → ℝ}
    (hp : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pd (pdd r) r)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) π) :
    RelativeDerivatives.coeff (pulseField f) 2 t
      = pd t ^ 2 + pulseField f t * pdd t := by
  rw [coeff_two]
  have hev : (fun r => pulseField f r * deriv (pulseField f) r)
      =ᶠ[nhds t] fun r => pulseField f r * pd r := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    rw [(hp r hr).deriv]
  rw [hev.deriv_eq]
  have hmul : HasDerivAt (fun r => pulseField f r * pd r)
      (pd t * pd t + pulseField f t * pdd t) t := (hp t ht).mul (hpd t ht)
  rw [hmul.deriv]
  ring

theorem hasDerivAt_pulse_angle {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) :
    ∀ r ∈ Ioo (0:ℝ) π,
      HasDerivAt (pulseField f) (deriv (pulseField f) r) r := by
  intro r hr
  exact (((contDiffOn_pulseField hf hfpos).contDiffAt
    (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num)).hasDerivAt

theorem hasDerivAt_pulse_angle_two {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t) :
    ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (deriv (pulseField f))
      (deriv (deriv (pulseField f)) r) r := by
  intro r hr
  have h := contDiffOn_deriv_of_isOpen (isOpen_Ioo (a := (0:ℝ)) (b := π))
    (contDiffOn_pulseField hf hfpos)
  exact ((h.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt
    (by norm_num)).hasDerivAt

/-- The `E₂` hypothesis of order three, from the order-≤2 flow bounds. -/
theorem hKdd_bound_of_interior {f theta x : ℝ → ℝ} {b D1 D2 E2 s0 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy0 : ∀ r ∈ Ioo (0:ℝ) π, 0 ≤ pulseField f r)
    (hyb : ∀ r ∈ Ioo (0:ℝ) π, pulseField f r ≤ b)
    (h1 : ∀ s, |iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s|
      ≤ D1 * pulseField f (theta (x s)))
    (h2 : ∀ s, |iteratedDeriv 2 (fun r => pulseField f (theta (x r))) s|
      ≤ D2 * pulseField f (theta (x s)))
    (hE2 : D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6
      + (D2 + D1 ^ 2) / Real.sqrt (1 - b ^ 2) ^ 4
      + 3 * b ^ 2 * D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6 ≤ E2) :
    ∀ s, |iteratedDeriv 2 (fun r => curvField f (theta (r + s0))) s|
      ≤ E2 * curvField f (theta (s + s0)) := by
  have hp := hasDerivAt_pulse_angle hf hfpos
  have hpd := hasDerivAt_pulse_angle_two hf hfpos
  have hc1 : ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ D1 := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hf hfpos hmem hderiv hxinv hsurj hw h1 t ht
    rwa [coeff_one] at h
  have hc2 : ∀ t ∈ Ioo (0:ℝ) π,
      |pulseField f t * deriv (deriv (pulseField f)) t
        + deriv (pulseField f) t ^ 2| ≤ D2 := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hf hfpos hmem hderiv hxinv hsurj hw h2 t ht
    rw [coeff_pulseField_two_eq hp hpd ht] at h
    rwa [add_comm] at h
  have hK := abs_iteratedDeriv_two_curv_le hf hfpos hmem hderiv hp hpd hb0 hb1
    hy0 hyb hc1 hc2
  have hstep : ∀ u, |iteratedDeriv 2 (fun u => curvField f (theta u)) u|
      ≤ E2 * curvField f (theta u) := fun u =>
    le_trans (hK u) (mul_le_mul_of_nonneg_right hE2
      (curvField_pos_interior hfpos (hmem u)).le)
  exact fun s => shifted_curv_bound (s0 := s0) hstep s

theorem hasDerivAt_iteratedDeriv {g : ℝ → ℝ} {n m : ℕ} (hg : ContDiff ℝ n g)
    (hmn : m < n) (s : ℝ) :
    HasDerivAt (iteratedDeriv m g) (iteratedDeriv (m + 1) g s) s := by
  have hd := hg.differentiable_iteratedDeriv m (by exact_mod_cast hmn)
  rw [iteratedDeriv_succ]
  exact (hd s).hasDerivAt

/-- The curvature along the shifted angle is smooth of every finite order. -/
theorem contDiff_shifted_curv {f theta : ℝ → ℝ} {s0 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π) (hth : ContDiff ℝ ∞ theta) :
    ContDiff ℝ ∞ (fun r => curvField f (theta (r + s0))) := by
  have hcomp : ContDiff ℝ ∞ (fun u => curvField f (theta u)) :=
    HairpinInteriorRegularity.contDiff_comp_of_mapsTo
      (HairpinInteriorRegularity.contDiffOn_curvField hf hfpos) hth hmem
  exact hcomp.comp (contDiff_id.add contDiff_const)

/-- **Order three of `hrelj`, discharged from the interior package.** -/
theorem rel_pulse_three_of_interior {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z) :
    ∃ D3 : ℝ, 0 ≤ D3 ∧ ∀ s,
      |iteratedDeriv 3 (fun r => pulseField f (theta (x r))) s|
        ≤ D3 * pulseField f (theta (x s)) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  obtain ⟨hthC, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hthinf : ContDiff ℝ ∞ theta := contDiff_infty.mpr hthC
  set s0 := Hairpin.hairpinArclength f (π / 2) (g (π / 2)) with hs0
  have hKC : ContDiff ℝ ∞ (fun r => curvField f (theta (r + s0))) :=
    contDiff_shifted_curv hf hfpos d.angle_mem hthinf
  let Y : ℝ → ℝ := fun r => pulseField f (theta (x r))
  let K : ℝ → ℝ := fun r => curvField f (theta (r + s0))
  let yp := iteratedDeriv 1 Y
  let ypp := iteratedDeriv 2 Y
  let Kd := iteratedDeriv 1 K
  let Kdd := iteratedDeriv 2 K
  have hYd : ∀ s, HasDerivAt Y (yp s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (hyC 5) (show 0 < 5 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  have hypd : ∀ s, HasDerivAt yp (ypp s) s := fun s =>
    hasDerivAt_iteratedDeriv (hyC 5) (show 1 < 5 by norm_num) s
  have hKd1 : ∀ s, HasDerivAt K (Kd s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (n := 5) (contDiff_infty.mp hKC 5)
      (show 0 < 5 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  have hKd2 : ∀ s, HasDerivAt Kd (Kdd s) s := fun s =>
    hasDerivAt_iteratedDeriv (n := 5) (contDiff_infty.mp hKC 5)
      (show 1 < 5 by norm_num) s
  -- constants
  set b := 1 / Real.sqrt (1 + m ^ 2) with hbdef
  have hb0 : (0:ℝ) ≤ b := by positivity
  have hb1 : b < 1 := one_div_sqrt_one_add_sq_lt_one hm
  have hy0 : ∀ s, 0 ≤ Y s := fun s =>
    pulseField_nonneg_interior hfpos (d.angle_mem (x s))
  have hsup : ∀ s, Y s ≤ b := fun s =>
    pulseField_le_of_barrier hm (hlow _ (d.angle_mem (x s))) (d.angle_mem (x s))
  have hKnn : ∀ s, 0 ≤ K s := fun s =>
    (curvField_pos_interior hfpos (d.angle_mem (s + s0))).le
  have hharnack := harnack_shift_of_interior (s0 := s0) hm hmA hf hfpos hlow hupp
    d.angle_mem d.angle_deriv d.inverse_value hdecay hM
  set Ch := (Am / m) * Real.exp ((|s0| + A ^ 2 * M / 2) / m) with hChdef
  have hCh : (0:ℝ) ≤ Ch := by
    have : (0:ℝ) ≤ Am / m := div_nonneg (le_trans hm.le hmA) hm.le
    positivity
  have hharn := harnack_pulse_form hb0 hb1 hCh hy0 hsup hharnack
  have hident : ∀ s, K s = Y s + FrontPeriodization.G (Y s) * yp s := by
    intro s
    simpa [hs0] using
      CanonicalTranslatorLocalPhase.front_curvature_identity_shifted d d.x_zero
        hYd (s + s0)
  have hyp := solved_of_ident hident
  have hsqall : ∀ r, (0:ℝ) < 1 - Y r ^ 2 := fun r =>
    one_sub_pulseField_sq_pos f (theta (x r))
  have hform : ∀ r, ypp r
      = (-(Y r * yp r) / Real.sqrt (1 - Y r ^ 2)) * (K r - Y r)
        + Real.sqrt (1 - Y r ^ 2) * (Kd r - yp r) := fun r =>
    (hypd r).unique (hasDerivAt_yp_of_solved (hYd r) (hKd1 r) (hsqall r) hyp)
  set D1 := Ch / Real.sqrt (1 - b ^ 2) + 1 with hD1def
  have hD1 : 0 ≤ D1 := by
    have : (0:ℝ) ≤ Ch / Real.sqrt (1 - b ^ 2) := by positivity
    linarith
  have hypb : ∀ s, |yp s| ≤ D1 * Y s :=
    rel_pulse_one_of_interior d hm hmA hf hlow hupp hdecay hM hYd
  have h1it : ∀ s, |iteratedDeriv 1 Y s| ≤ D1 * Y s := hypb
  obtain ⟨D2, hD2, h2it⟩ := rel_pulse_two_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj hYd
  have hyppb : ∀ s, |ypp s| ≤ D2 * Y s := h2it
  have hyb : ∀ t ∈ Ioo (0:ℝ) π, pulseField f t ≤ b := fun t ht =>
    pulseField_le_of_barrier hm (hlow t ht) ht
  have hy0' : ∀ t ∈ Ioo (0:ℝ) π, 0 ≤ pulseField f t := fun t ht =>
    pulseField_nonneg_interior hfpos ht
  have hyabs : ∀ t ∈ Ioo (0:ℝ) π, |pulseField f t| ≤ b := fun t ht => by
    rw [abs_of_nonneg (hy0' t ht)]; exact hyb t ht
  have hdb : ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ D1 := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hf hfpos d.angle_mem d.angle_deriv
      d.inverse_value hsurj d.state_deriv h1it t ht
    rwa [coeff_one] at h
  set E1 := D1 / Real.sqrt (1 - b ^ 2) ^ 3 with hE1def
  have hE1 : 0 ≤ E1 := by positivity
  have hKdb : ∀ s, |Kd s| ≤ E1 * K s := by
    intro s
    have h := hKd_bound_of_interior (s0 := s0) hf hfpos hb0 hb1 hyabs hdb
      d.angle_mem d.angle_deriv s
    have he : Kd s = deriv (fun r => curvField f (theta (r + s0))) s :=
      ((hKd1 s).deriv).symm
    rw [he]
    exact h
  set E2 := D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6
    + (D2 + D1 ^ 2) / Real.sqrt (1 - b ^ 2) ^ 4
    + 3 * b ^ 2 * D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6 with hE2def
  have hE2 : 0 ≤ E2 := by positivity
  have hKddb : ∀ s, |Kdd s| ≤ E2 * K s := fun s =>
    hKdd_bound_of_interior hf hfpos d.angle_mem d.angle_deriv d.inverse_value
      hsurj d.state_deriv hb0 hb1 hy0' hyb h1it h2it (le_refl _) s
  exact ⟨_, by positivity,
    rel_pulse_three_of_identity hb0 hb1 hCh hD1 hD2 hE1 hE2 hy0 hsup hKnn
      hform hYd hypd hKd1 hKd2 hypb hyppb hKdb hKddb hharn⟩

theorem contDiffOn_iteratedDeriv_of_isOpen {G : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : ContDiffOn ℝ ∞ G s) : ∀ m : ℕ, ContDiffOn ℝ ∞ (iteratedDeriv m G) s
  | 0 => by simpa [iteratedDeriv_zero] using h
  | m + 1 => by
      rw [iteratedDeriv_succ]
      exact contDiffOn_deriv_of_isOpen hs
        (contDiffOn_iteratedDeriv_of_isOpen hs h m)

theorem hasDerivAt_iteratedDeriv_on {G : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h : ContDiffOn ℝ ∞ G s) (m : ℕ) {r : ℝ} (hr : r ∈ s) :
    HasDerivAt (iteratedDeriv m G) (iteratedDeriv (m + 1) G r) r := by
  have hd := contDiffOn_iteratedDeriv_of_isOpen hs h m
  have hdiff : DifferentiableAt ℝ (iteratedDeriv m G) r :=
    (hd.contDiffAt (hs.mem_nhds hr)).differentiableAt (by norm_num)
  rw [iteratedDeriv_succ]
  exact hdiff.hasDerivAt

/-- `coeff (pulseField f) 3 = (y')³ + 4y y' y'' + y² y'''` on `(0,π)`. -/
theorem coeff_pulseField_three_eq {f : ℝ → ℝ} {pd pdd pddd : ℝ → ℝ}
    (hp : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pd (pdd r) r)
    (hpdd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pdd (pddd r) r)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) π) :
    RelativeDerivatives.coeff (pulseField f) 3 t
      = pd t ^ 3 + 4 * pulseField f t * pd t * pdd t
        + pulseField f t ^ 2 * pddd t := by
  rw [coeff_three]
  have hev : (fun r => pulseField f r * RelativeDerivatives.coeff (pulseField f) 2 r)
      =ᶠ[nhds t] fun r => pulseField f r * (pd r ^ 2 + pulseField f r * pdd r) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    rw [coeff_pulseField_two_eq hp hpd hr]
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun r => pd r ^ 2) (2 * pd t * pdd t) t := by
    simpa [mul_comm] using (hpd t ht).pow 2
  have h2 : HasDerivAt (fun r => pulseField f r * pdd r)
      (pd t * pdd t + pulseField f t * pddd t) t := (hp t ht).mul (hpdd t ht)
  have hmul : HasDerivAt
      (fun r => pulseField f r * (pd r ^ 2 + pulseField f r * pdd r))
      (pd t * (pd t ^ 2 + pulseField f t * pdd t)
        + pulseField f t * (2 * pd t * pdd t
          + (pd t * pdd t + pulseField f t * pddd t))) t :=
    (hp t ht).mul (h1.add h2)
  rw [hmul.deriv]
  ring

/-- The `E₃` hypothesis of order four, from the order-≤3 flow bounds. -/
theorem hKddd_bound_of_interior {f theta x : ℝ → ℝ} {b D1 D2 D3 : ℝ} {s0 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hxinv : ∀ s, frontArclength f theta (x s) = s)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z)
    (hw : ∀ s, HasDerivAt (fun r => theta (x r)) (pulseField f (theta (x s))) s)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy0 : ∀ r ∈ Ioo (0:ℝ) π, 0 ≤ pulseField f r)
    (hyb : ∀ r ∈ Ioo (0:ℝ) π, pulseField f r ≤ b)
    (h1 : ∀ s, |iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s|
      ≤ D1 * pulseField f (theta (x s)))
    (h2 : ∀ s, |iteratedDeriv 2 (fun r => pulseField f (theta (x r))) s|
      ≤ D2 * pulseField f (theta (x s)))
    (h3 : ∀ s, |iteratedDeriv 3 (fun r => pulseField f (theta (x r))) s|
      ≤ D3 * pulseField f (theta (x s))) :
    ∃ E3 : ℝ, 0 ≤ E3 ∧ ∀ s,
      |iteratedDeriv 3 (fun r => curvField f (theta (r + s0))) s|
        ≤ E3 * curvField f (theta (s + s0)) := by
  have hG := contDiffOn_pulseField hf hfpos
  have hp : ∀ r ∈ Ioo (0:ℝ) π,
      HasDerivAt (pulseField f) (iteratedDeriv 1 (pulseField f) r) r := by
    intro r hr
    have h := hasDerivAt_iteratedDeriv_on isOpen_Ioo hG 0 hr
    rwa [iteratedDeriv_zero] at h
  have hpd : ∀ r ∈ Ioo (0:ℝ) π,
      HasDerivAt (iteratedDeriv 1 (pulseField f))
        (iteratedDeriv 2 (pulseField f) r) r := fun r hr =>
    hasDerivAt_iteratedDeriv_on isOpen_Ioo hG 1 hr
  have hpdd : ∀ r ∈ Ioo (0:ℝ) π,
      HasDerivAt (iteratedDeriv 2 (pulseField f))
        (iteratedDeriv 3 (pulseField f) r) r := fun r hr =>
    hasDerivAt_iteratedDeriv_on isOpen_Ioo hG 2 hr
  have hc1 : ∀ t ∈ Ioo (0:ℝ) π, |iteratedDeriv 1 (pulseField f) t| ≤ D1 := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hf hfpos hmem hderiv hxinv hsurj hw h1 t ht
    rwa [coeff_one, ← iteratedDeriv_one] at h
  have hD1 : 0 ≤ D1 := by
    have hpos : 0 < pulseField f (theta (x 0)) := by
      rw [pulseField]
      exact div_pos (curvField_pos_interior hfpos (hmem (x 0)))
        (sqrt_one_add_sq_pos _)
    have h := le_trans (abs_nonneg _) (h1 0)
    nlinarith [h, hpos]
  have hc2 : ∀ t ∈ Ioo (0:ℝ) π,
      |pulseField f t * iteratedDeriv 2 (pulseField f) t
        + iteratedDeriv 1 (pulseField f) t ^ 2| ≤ D2 := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hf hfpos hmem hderiv hxinv hsurj hw h2 t ht
    rw [coeff_pulseField_two_eq hp hpd ht] at h
    rwa [add_comm] at h
  have hQ : ∀ r ∈ Ioo (0:ℝ) π,
      |pulseField f r * iteratedDeriv 2 (pulseField f) r| ≤ D2 + D1 ^ 2 := by
    intro r hr
    have hsq : |iteratedDeriv 1 (pulseField f) r ^ 2| ≤ D1 ^ 2 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hc1 r hr) 2
    have h := hc2 r hr
    set P := pulseField f r * iteratedDeriv 2 (pulseField f) r with hP
    set Q := iteratedDeriv 1 (pulseField f) r ^ 2 with hQdef
    have hPeq : P = P + Q - Q := by ring
    rw [hPeq]
    calc |P + Q - Q| ≤ |P + Q| + |Q| := abs_sub _ _
      _ ≤ D2 + D1 ^ 2 := by linarith [h, hsq]
  have hc3 : ∀ t ∈ Ioo (0:ℝ) π,
      |iteratedDeriv 1 (pulseField f) t ^ 3
        + 4 * pulseField f t * iteratedDeriv 1 (pulseField f) t
          * iteratedDeriv 2 (pulseField f) t
        + pulseField f t ^ 2 * iteratedDeriv 3 (pulseField f) t| ≤ D3 := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hf hfpos hmem hderiv hxinv hsurj hw h3 t ht
    rwa [coeff_pulseField_three_eq hp hpd hpdd ht] at h
  have hR : ∀ r ∈ Ioo (0:ℝ) π,
      |pulseField f r ^ 2 * iteratedDeriv 3 (pulseField f) r|
        ≤ D3 + D1 ^ 3 + 4 * D1 * (D2 + D1 ^ 2) := by
    intro r hr
    have hpd3 : |iteratedDeriv 1 (pulseField f) r ^ 3| ≤ D1 ^ 3 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hc1 r hr) 3
    have hmid : |4 * pulseField f r * iteratedDeriv 1 (pulseField f) r
        * iteratedDeriv 2 (pulseField f) r| ≤ 4 * D1 * (D2 + D1 ^ 2) := by
      have he : 4 * pulseField f r * iteratedDeriv 1 (pulseField f) r
          * iteratedDeriv 2 (pulseField f) r
          = 4 * (iteratedDeriv 1 (pulseField f) r
            * (pulseField f r * iteratedDeriv 2 (pulseField f) r)) := by ring
      rw [he, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (4:ℝ)), abs_mul]
      have hprod := mul_le_mul (hc1 r hr) (hQ r hr) (abs_nonneg _) hD1
      linarith [hprod]
    have hsum := hc3 r hr
    set A := iteratedDeriv 1 (pulseField f) r ^ 3 with hA
    set B := 4 * pulseField f r * iteratedDeriv 1 (pulseField f) r
      * iteratedDeriv 2 (pulseField f) r with hB
    set C := pulseField f r ^ 2 * iteratedDeriv 3 (pulseField f) r with hC
    have hCeq : C = A + B + C - A - B := by ring
    rw [hCeq]
    calc |A + B + C - A - B| ≤ |A + B + C - A| + |B| := abs_sub _ _
      _ ≤ (|A + B + C| + |A|) + |B| := add_le_add (abs_sub _ _) (le_refl _)
      _ ≤ D3 + D1 ^ 3 + 4 * D1 * (D2 + D1 ^ 2) := by
          linarith [hsum, hpd3, hmid]
  have hD2 : 0 ≤ D2 := le_trans (abs_nonneg _) (hc2 _ (hmem (x 0)))
  have hD3 : 0 ≤ D3 := by
    have hpos : 0 < pulseField f (theta (x 0)) := by
      rw [pulseField]
      exact div_pos (curvField_pos_interior hfpos (hmem (x 0)))
        (sqrt_one_add_sq_pos _)
    have h := le_trans (abs_nonneg _) (h3 0)
    nlinarith [h, hpos]
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hSb : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr hsb
  have hW : ∀ r ∈ Ioo (0:ℝ) π,
      |iteratedDeriv 1 (pulseField f) r ^ 2
          / Real.sqrt (1 - pulseField f r ^ 2) ^ 6
        + pulseField f r * iteratedDeriv 2 (pulseField f) r
          / Real.sqrt (1 - pulseField f r ^ 2) ^ 4
        + 3 * pulseField f r ^ 2 * iteratedDeriv 1 (pulseField f) r ^ 2
          / Real.sqrt (1 - pulseField f r ^ 2) ^ 6|
      ≤ D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6
        + (D2 + D1 ^ 2) / Real.sqrt (1 - b ^ 2) ^ 4
        + 3 * b ^ 2 * D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6 := by
    intro r hr
    have hSbS : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - pulseField f r ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [hy0 r hr, hyb r hr])
    exact abs_coeff_curv_two_le hSb hSbS (hy0 r hr) (hyb r hr) hb0
      (hc1 r hr) (hc2 r hr)
  have hK := abs_iteratedDeriv_three_curv_le hf hfpos hmem hderiv hp hpd hpdd
    hb0 hb1 hy0 hyb hc1 hQ hR hW
  refine ⟨_, ?_, fun s => shifted_curv_bound (s0 := s0) hK s⟩
  have h1' : (0:ℝ) ≤ D2 + D1 ^ 2 := by positivity
  have h2' : (0:ℝ) ≤ D3 + D1 ^ 3 + 4 * D1 * (D2 + D1 ^ 2) := by positivity
  positivity

section Sub
variable {Y yp ypp yppp : ℝ} {b D1 D2 D3 : ℝ}

theorem sub_P (hb0 : 0 ≤ b) (hY0 : 0 ≤ Y) (hYb : Y ≤ b)
    (h1 : |yp| ≤ D1 * Y) (h2 : |ypp| ≤ D2 * Y) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) :
    |yp ^ 2 + Y * ypp| ≤ (D1 ^ 2 + D2) * b * Y := by
  have hyp2 : yp ^ 2 ≤ D1 ^ 2 * Y ^ 2 := by
    have h : |yp| ^ 2 ≤ (D1 * Y) ^ 2 := pow_le_pow_left₀ (abs_nonneg yp) h1 2
    rw [sq_abs] at h; nlinarith [h]
  have hYypp : |Y * ypp| ≤ D2 * Y ^ 2 := by
    rw [abs_mul, abs_of_nonneg hY0]; nlinarith [h2, abs_nonneg ypp, hY0]
  have hYY : Y ^ 2 ≤ b * Y := by nlinarith
  calc |yp ^ 2 + Y * ypp| ≤ |yp ^ 2| + |Y * ypp| := abs_add_le _ _
    _ ≤ (D1 ^ 2 + D2) * Y ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg yp)]; nlinarith [hyp2, hYypp]
    _ ≤ (D1 ^ 2 + D2) * b * Y := by nlinarith [hYY, hD1, hD2, sq_nonneg D1]

theorem sub_Pd (hb0 : 0 ≤ b) (hY0 : 0 ≤ Y) (hYb : Y ≤ b)
    (h1 : |yp| ≤ D1 * Y) (h2 : |ypp| ≤ D2 * Y) (h3 : |yppp| ≤ D3 * Y)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) :
    |3 * yp * ypp + Y * yppp| ≤ (3 * D1 * D2 * b + b * D3) * Y := by
  have ha : |3 * yp * ypp| ≤ 3 * D1 * D2 * Y ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (3:ℝ))]
    nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hD1 hY0),
      abs_nonneg yp, abs_nonneg ypp]
  have hYY0 : Y ^ 2 ≤ b * Y := by
    nlinarith [mul_nonneg hY0 (sub_nonneg.mpr hYb)]
  have hb : |Y * yppp| ≤ b * D3 * Y := by
    rw [abs_mul, abs_of_nonneg hY0]
    calc Y * |yppp| ≤ Y * (D3 * Y) := mul_le_mul_of_nonneg_left h3 hY0
      _ = D3 * Y ^ 2 := by ring
      _ ≤ D3 * (b * Y) := mul_le_mul_of_nonneg_left hYY0 hD3
      _ = b * D3 * Y := by ring
  calc |3 * yp * ypp + Y * yppp| ≤ |3 * yp * ypp| + |Y * yppp| := abs_add_le _ _
    _ ≤ 3 * D1 * D2 * Y ^ 2 + b * D3 * Y := by linarith
    _ ≤ (3 * D1 * D2 * b + b * D3) * Y := by
        nlinarith [mul_le_mul_of_nonneg_left hYY0
          (by positivity : (0:ℝ) ≤ 3 * D1 * D2)]

theorem sub_Q (hb0 : 0 ≤ b) (hY0 : 0 ≤ Y) (hYb : Y ≤ b)
    (h1 : |yp| ≤ D1 * Y) (hD1 : 0 ≤ D1) :
    |Y ^ 2 * yp ^ 2| ≤ b ^ 3 * D1 ^ 2 * Y := by
  have hyp2 : yp ^ 2 ≤ D1 ^ 2 * Y ^ 2 := by
    have h : |yp| ^ 2 ≤ (D1 * Y) ^ 2 := pow_le_pow_left₀ (abs_nonneg yp) h1 2
    rw [sq_abs] at h; nlinarith [h]
  rw [abs_mul, abs_of_nonneg (sq_nonneg Y), abs_of_nonneg (sq_nonneg yp)]
  have h3b : Y ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ hY0 hYb 3
  have h4 : Y ^ 4 ≤ b ^ 3 * Y := by
    calc Y ^ 4 = Y ^ 3 * Y := by ring
      _ ≤ b ^ 3 * Y := mul_le_mul_of_nonneg_right h3b hY0
  calc Y ^ 2 * yp ^ 2 ≤ Y ^ 2 * (D1 ^ 2 * Y ^ 2) :=
        mul_le_mul_of_nonneg_left hyp2 (sq_nonneg Y)
    _ = D1 ^ 2 * Y ^ 4 := by ring
    _ ≤ D1 ^ 2 * (b ^ 3 * Y) := mul_le_mul_of_nonneg_left h4 (sq_nonneg D1)
    _ = b ^ 3 * D1 ^ 2 * Y := by ring

theorem sub_Qd (hb0 : 0 ≤ b) (hY0 : 0 ≤ Y) (hYb : Y ≤ b)
    (h1 : |yp| ≤ D1 * Y) (h2 : |ypp| ≤ D2 * Y) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) :
    |2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)|
      ≤ (2 * b ^ 3 * D1 ^ 3 + 2 * b ^ 3 * D1 * D2) * Y := by
  have h3b : Y ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ hY0 hYb 3
  have h4 : Y ^ 4 ≤ b ^ 3 * Y := by
    calc Y ^ 4 = Y ^ 3 * Y := by ring
      _ ≤ b ^ 3 * Y := mul_le_mul_of_nonneg_right h3b hY0
  have hyp3 : |yp ^ 3| ≤ D1 ^ 3 * Y ^ 3 := by
    rw [abs_pow]
    calc |yp| ^ 3 ≤ (D1 * Y) ^ 3 := pow_le_pow_left₀ (abs_nonneg yp) h1 3
      _ = D1 ^ 3 * Y ^ 3 := by ring
  have ha : |2 * Y * yp ^ 3| ≤ 2 * D1 ^ 3 * Y ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)),
      abs_of_nonneg hY0]
    calc 2 * Y * |yp ^ 3| ≤ 2 * Y * (D1 ^ 3 * Y ^ 3) := by
          nlinarith [hyp3, hY0]
      _ = 2 * D1 ^ 3 * Y ^ 4 := by ring
  have hbb : |2 * Y ^ 2 * (yp * ypp)| ≤ 2 * D1 * D2 * Y ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)),
      abs_of_nonneg (sq_nonneg Y), abs_mul]
    have hprod : |yp| * |ypp| ≤ (D1 * Y) * (D2 * Y) :=
      mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hD1 hY0)
    calc 2 * Y ^ 2 * (|yp| * |ypp|) ≤ 2 * Y ^ 2 * ((D1 * Y) * (D2 * Y)) := by
          nlinarith [hprod, sq_nonneg Y]
      _ = 2 * D1 * D2 * Y ^ 4 := by ring
  calc |2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)|
      ≤ |2 * Y * yp ^ 3| + |2 * Y ^ 2 * (yp * ypp)| := abs_add_le _ _
    _ ≤ 2 * D1 ^ 3 * Y ^ 4 + 2 * D1 * D2 * Y ^ 4 := by linarith
    _ ≤ (2 * b ^ 3 * D1 ^ 3 + 2 * b ^ 3 * D1 * D2) * Y := by
        nlinarith [mul_le_mul_of_nonneg_left h4
            (by positivity : (0:ℝ) ≤ 2 * D1 ^ 3),
          mul_le_mul_of_nonneg_left h4
            (by positivity : (0:ℝ) ≤ 2 * D1 * D2)]

theorem sub_w {S : ℝ} (hS : 0 < S) (hSY : S ≤ Real.sqrt (1 - Y ^ 2))
    (hY0 : 0 ≤ Y) (hYb : Y ≤ b) (h1 : |yp| ≤ D1 * Y) (hD1 : 0 ≤ D1)
    (hb0 : 0 ≤ b) :
    |(-(Y * yp) / Real.sqrt (1 - Y ^ 2))| ≤ b * D1 / S * Y := by
  rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hY0,
    abs_of_pos (lt_of_lt_of_le hS hSY)]
  have hnum : Y * |yp| ≤ b * (D1 * Y) := by nlinarith [h1, abs_nonneg yp, hY0, hYb]
  refine le_trans (div_le_div₀ (by positivity) hnum hS hSY) ?_
  apply le_of_eq; field_simp

end Sub

/-- **Order four of `hrelj`, discharged from the interior package.** -/
theorem rel_pulse_four_of_interior {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z) :
    ∃ D4 : ℝ, 0 ≤ D4 ∧ ∀ s,
      |iteratedDeriv 4 (fun r => pulseField f (theta (x r))) s|
        ≤ D4 * pulseField f (theta (x s)) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  obtain ⟨hthC, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hthinf : ContDiff ℝ ∞ theta := contDiff_infty.mpr hthC
  set s0 := Hairpin.hairpinArclength f (π / 2) (g (π / 2)) with hs0
  have hKC : ContDiff ℝ ∞ (fun r => curvField f (theta (r + s0))) :=
    contDiff_shifted_curv hf hfpos d.angle_mem hthinf
  let Y : ℝ → ℝ := fun r => pulseField f (theta (x r))
  let K : ℝ → ℝ := fun r => curvField f (theta (r + s0))
  let yp := iteratedDeriv 1 Y
  let ypp := iteratedDeriv 2 Y
  let yppp := iteratedDeriv 3 Y
  let Kd := iteratedDeriv 1 K
  let Kdd := iteratedDeriv 2 K
  let Kddd := iteratedDeriv 3 K
  have hYd : ∀ s, HasDerivAt Y (yp s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (hyC 6) (show 0 < 6 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  have hypd : ∀ s, HasDerivAt yp (ypp s) s := fun s =>
    hasDerivAt_iteratedDeriv (hyC 6) (show 1 < 6 by norm_num) s
  have hyppd : ∀ s, HasDerivAt ypp (yppp s) s := fun s =>
    hasDerivAt_iteratedDeriv (hyC 6) (show 2 < 6 by norm_num) s
  have hKd1 : ∀ s, HasDerivAt K (Kd s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (n := 6) (contDiff_infty.mp hKC 6)
      (show 0 < 6 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  have hKd2 : ∀ s, HasDerivAt Kd (Kdd s) s := fun s =>
    hasDerivAt_iteratedDeriv (n := 6) (contDiff_infty.mp hKC 6)
      (show 1 < 6 by norm_num) s
  have hKd3 : ∀ s, HasDerivAt Kdd (Kddd s) s := fun s =>
    hasDerivAt_iteratedDeriv (n := 6) (contDiff_infty.mp hKC 6)
      (show 2 < 6 by norm_num) s
  set b := 1 / Real.sqrt (1 + m ^ 2) with hbdef
  have hb0 : (0:ℝ) ≤ b := by positivity
  have hb1 : b < 1 := one_div_sqrt_one_add_sq_lt_one hm
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hSb : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr hsb
  have hy0 : ∀ s, 0 ≤ Y s := fun s =>
    pulseField_nonneg_interior hfpos (d.angle_mem (x s))
  have hsup : ∀ s, Y s ≤ b := fun s =>
    pulseField_le_of_barrier hm (hlow _ (d.angle_mem (x s))) (d.angle_mem (x s))
  have hKnn : ∀ s, 0 ≤ K s := fun s =>
    (curvField_pos_interior hfpos (d.angle_mem (s + s0))).le
  have hsqall : ∀ r, (0:ℝ) < 1 - Y r ^ 2 := fun r =>
    one_sub_pulseField_sq_pos f (theta (x r))
  have hharnack := harnack_shift_of_interior (s0 := s0) hm hmA hf hfpos hlow hupp
    d.angle_mem d.angle_deriv d.inverse_value hdecay hM
  set Ch := (Am / m) * Real.exp ((|s0| + A ^ 2 * M / 2) / m) with hChdef
  have hCh : (0:ℝ) ≤ Ch := by
    have : (0:ℝ) ≤ Am / m := div_nonneg (le_trans hm.le hmA) hm.le
    positivity
  have hharn := harnack_pulse_form hb0 hb1 hCh hy0 hsup hharnack
  have hident : ∀ s, K s = Y s + FrontPeriodization.G (Y s) * yp s := by
    intro s
    simpa [hs0] using
      CanonicalTranslatorLocalPhase.front_curvature_identity_shifted d d.x_zero
        hYd (s + s0)
  have hyp := solved_of_ident hident
  set D1 := Ch / Real.sqrt (1 - b ^ 2) + 1 with hD1def
  have hD1 : 0 ≤ D1 := by
    have : (0:ℝ) ≤ Ch / Real.sqrt (1 - b ^ 2) := by positivity
    linarith
  have hypb : ∀ s, |yp s| ≤ D1 * Y s :=
    rel_pulse_one_of_interior d hm hmA hf hlow hupp hdecay hM hYd
  obtain ⟨D2, hD2, h2it⟩ := rel_pulse_two_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj hYd
  obtain ⟨D3, hD3, h3it⟩ := rel_pulse_three_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj
  have hyppb : ∀ s, |ypp s| ≤ D2 * Y s := h2it
  have hypppb : ∀ s, |yppp s| ≤ D3 * Y s := h3it
  -- the order-two form for ypp, and the order-three form for yppp
  have hform2 : ∀ r, ypp r
      = (-(Y r * yp r) / Real.sqrt (1 - Y r ^ 2)) * (K r - Y r)
        + Real.sqrt (1 - Y r ^ 2) * (Kd r - yp r) := fun r =>
    (hypd r).unique (hasDerivAt_yp_of_solved (hYd r) (hKd1 r) (hsqall r) hyp)
  have hu2d := fun r => hasDerivAt_u1 (Y := Y) (yp := yp) (ypp := ypp)
    (yppp := yppp) hYd hypd hyppd hsqall (s := r)
  have hform3 : ∀ r, yppp r
      = (-((yp r ^ 2 + Y r * ypp r) / Real.sqrt (1 - Y r ^ 2)
          + Y r ^ 2 * yp r ^ 2 / Real.sqrt (1 - Y r ^ 2) ^ 3)) * (K r - Y r)
        + 2 * (-(Y r * yp r) / Real.sqrt (1 - Y r ^ 2)) * (Kd r - yp r)
        + Real.sqrt (1 - Y r ^ 2) * (Kdd r - ypp r) := fun r =>
    (hyppd r).unique (hasDerivAt_ypp_of_solved hYd hypd hKd1 hKd2 hsqall
      hform2 (s := r))
  -- the curvature bounds
  have hyb : ∀ t ∈ Ioo (0:ℝ) π, pulseField f t ≤ b := fun t ht =>
    pulseField_le_of_barrier hm (hlow t ht) ht
  have hy0' : ∀ t ∈ Ioo (0:ℝ) π, 0 ≤ pulseField f t := fun t ht =>
    pulseField_nonneg_interior hfpos ht
  have hyabs : ∀ t ∈ Ioo (0:ℝ) π, |pulseField f t| ≤ b := fun t ht => by
    rw [abs_of_nonneg (hy0' t ht)]; exact hyb t ht
  have hdb : ∀ t ∈ Ioo (0:ℝ) π, |deriv (pulseField f) t| ≤ D1 := by
    intro t ht
    have h := abs_coeff_pulse_le_of_flow hf hfpos d.angle_mem d.angle_deriv
      d.inverse_value hsurj d.state_deriv hypb t ht
    rwa [coeff_one] at h
  set E1 := D1 / Real.sqrt (1 - b ^ 2) ^ 3 with hE1def
  have hE1 : 0 ≤ E1 := by positivity
  have hKdb : ∀ s, |Kd s| ≤ E1 * K s := by
    intro s
    have h := hKd_bound_of_interior (s0 := s0) hf hfpos hb0 hb1 hyabs hdb
      d.angle_mem d.angle_deriv s
    have he : Kd s = deriv (fun r => curvField f (theta (r + s0))) s :=
      ((hKd1 s).deriv).symm
    rw [he]; exact h
  set E2 := D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6
    + (D2 + D1 ^ 2) / Real.sqrt (1 - b ^ 2) ^ 4
    + 3 * b ^ 2 * D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6 with hE2def
  have hE2 : 0 ≤ E2 := by positivity
  have hKddb : ∀ s, |Kdd s| ≤ E2 * K s := fun s =>
    hKdd_bound_of_interior hf hfpos d.angle_mem d.angle_deriv d.inverse_value
      hsurj d.state_deriv hb0 hb1 hy0' hyb hypb h2it (le_refl _) s
  obtain ⟨E3, hE3, hKdddb⟩ := hKddd_bound_of_interior (s0 := s0) hf hfpos
    d.angle_mem d.angle_deriv d.inverse_value hsurj d.state_deriv hb0 hb1
    hy0' hyb hypb h2it h3it
  -- the coefficient bounds
  have hSc : ∀ s, Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - Y s ^ 2) := fun s =>
    Real.sqrt_le_sqrt (by nlinarith [hy0 s, hsup s])
  have hcpos : ∀ s, 0 < Real.sqrt (1 - Y s ^ 2) := fun s =>
    Real.sqrt_pos.mpr (hsqall s)
  have hc1 : ∀ s, Real.sqrt (1 - Y s ^ 2) ≤ 1 := fun s => by
    have h := Real.sqrt_le_sqrt (show 1 - Y s ^ 2 ≤ 1 by nlinarith [hy0 s])
    simpa using h
  have hG1 : ∀ s, |(-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
      + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3))|
      ≤ ((D1 ^ 2 + D2) / Real.sqrt (1 - b ^ 2)
        + b ^ 2 * D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 3) * b * Y s := fun s =>
    abs_u1_le hSb (hSc s) (hcpos s) (hy0 s) (hsup s) hb0 hD1 hD2
      (hypb s) (hyppb s)
  have hG2 : ∀ s, |_| ≤ _ := fun s =>
    abs_u2_le (b := b) hSb (hSc s) (hc1 s) (hcpos s) (hy0 s) (hsup s) hb0
      (by positivity) (by positivity) (by positivity)
      (sub_P hb0 (hy0 s) (hsup s) (hypb s) (hyppb s) hD1 hD2)
      (sub_Pd hb0 (hy0 s) (hsup s) (hypb s) (hyppb s) (hypppb s) hD1 hD2 hD3)
      (sub_Q hb0 (hy0 s) (hsup s) (hypb s) hD1)
      (sub_Qd hb0 (hy0 s) (hsup s) (hypb s) (hyppb s) hD1 hD2)
      (sub_w hSb (hSc s) (hy0 s) (hsup s) (hypb s) hD1 hb0)
  have hfinal := fun s => rel_pulse_four_of_identity hb0 hb1 hCh hD1 hD2 hD3
    hE1 hE2 hE3 (by positivity) (by positivity) hy0 hsup hKnn hform3 hYd hypd
    hyppd hKd1 hKd2 hKd3 hu2d hypb hyppb hypppb hKdb hKddb hKdddb hG1 hG2
    hharn s
  exact ⟨_, by positivity, hfinal⟩

/-- Order one, in the existential form the other orders use. -/
theorem rel_pulse_one_of_interior' {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M) {yp : ℝ → ℝ}
    (hypd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s) :
    ∃ D1 : ℝ, 0 ≤ D1 ∧ ∀ s, |yp s| ≤ D1 * pulseField f (theta (x s)) := by
  have hb1 : (1:ℝ) / Real.sqrt (1 + m ^ 2) < 1 :=
    one_div_sqrt_one_add_sq_lt_one hm
  have hb0 : (0:ℝ) ≤ 1 / Real.sqrt (1 + m ^ 2) := by positivity
  have hsb : (0:ℝ) < 1 - (1 / Real.sqrt (1 + m ^ 2)) ^ 2 := by nlinarith
  refine ⟨_, ?_, rel_pulse_one_of_interior d hm hmA hf hlow hupp hdecay hM hypd⟩
  have hCh : (0:ℝ) ≤ (Am / m) * Real.exp
      ((|Hairpin.hairpinArclength f (π / 2) (g (π / 2))| + A ^ 2 * M / 2) / m) := by
    have : (0:ℝ) ≤ Am / m := div_nonneg (le_trans hm.le hmA) hm.le
    positivity
  have hSb : 0 < Real.sqrt (1 - (1 / Real.sqrt (1 + m ^ 2)) ^ 2) :=
    Real.sqrt_pos.mpr hsb
  positivity

/-- **The relative bounds `hrelj` at every order `j ≤ 4`, from the interior
package.**  This is exactly the hypothesis
`PaperHairpinQuantitativeData.data_of_interior` consumes. -/
theorem hrelj_of_interior {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π))
    (hlow : ∀ t ∈ Ioo (0:ℝ) π, m ≤ f t) (hupp : ∀ t ∈ Ioo (0:ℝ) π, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M)
    (hsurj : ∀ z ∈ Ioo (0:ℝ) π, ∃ u, theta u = z) :
    ∃ relativeConst : ℕ → ℝ, (∀ j, 0 ≤ relativeConst j) ∧
      ∀ j ≤ 4, ∀ s,
        |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
          ≤ relativeConst j * pulseField f (theta (x s)) := by
  have hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  obtain ⟨-, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r)))
      (iteratedDeriv 1 (fun r => pulseField f (theta (x r))) s) s := fun s => by
    have h := hasDerivAt_iteratedDeriv (hyC 2) (show 0 < 2 by norm_num) s
    rwa [iteratedDeriv_zero] at h
  obtain ⟨D1, hD1, h1⟩ := rel_pulse_one_of_interior' d hm hmA hf hlow hupp
    hdecay hM hYd
  obtain ⟨D2, hD2, h2⟩ := rel_pulse_two_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj hYd
  obtain ⟨D3, hD3, h3⟩ := rel_pulse_three_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj
  obtain ⟨D4, hD4, h4⟩ := rel_pulse_four_of_interior d hm hmA hf hlow hupp
    hdecay hM hsurj
  refine ⟨fun j => if j = 0 then 1 else if j = 1 then D1 else
    if j = 2 then D2 else if j = 3 then D3 else D4, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · norm_num
    · exact hD1
    · exact hD2
    · exact hD3
    · exact hD4
  · refine rel_pulse_le_four_of_orders
      (fun s => pulseField_nonneg_interior hfpos (d.angle_mem (x s)))
      (by norm_num) (by simpa using h1) (by simpa using h2) (by simpa using h3)
      (by simpa using h4)
