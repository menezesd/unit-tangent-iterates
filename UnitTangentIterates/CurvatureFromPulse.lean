import UnitTangentIterates.PulseRelativeFromIdentity

/-!
# Curvature-side derivatives from pulse-side ones

§29 found that the order-`j` relative *pulse* bound consumes the order-`(j−1)`
relative *curvature* bound, and that only order one of the curvature induction
was proved (§24).  This file supplies the order-two ingredients.

The route is the one §29 identified: `curvField f = h ∘ pulseField f` with
`h z = z/√(1−z²)`, and `h z / z = 1/√(1−z²)` is bounded (`curvField_le_pulse_div`).
Writing `p = pulseField f` and `S = √(1−p²)`,

```
  G'  = p'/S³ ,
  G'' = (p''S³ + 3p(p')²S)/S⁶ ,
  (G')² + G G'' = (p')²/S⁶ + p p''/S⁴ + 3p²(p')²/S⁶ .
```

The middle term is the only place a bare second derivative of the pulse appears,
and it appears as `p·p''` — which is exactly what the order-two relative pulse
bound controls, since `coeff (pulseField f) 2 = (p')² + p p''`.  That is why the
unboundedness of `p''` alone is not an obstruction.

Main results:

* `hasDerivAt_curvField_of_pulse`, `hasDerivAt_curvField_two_of_pulse`;
* `abs_coeff_curv_two_le` : the bound on `(G')² + G G''`.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Real HairpinRelative

namespace HairpinRelative

/-- `G' = G₂'/(1−G₂²)^{3/2}` : the curvature field's derivative in terms of the
pulse field's. -/
theorem hasDerivAt_curvField_of_pulse {f : ℝ → ℝ} {pd : ℝ → ℝ} {t : ℝ}
    (hp : ∀ r, HasDerivAt (pulseField f) (pd r) r)
    (hsq : ∀ r, (0:ℝ) < 1 - pulseField f r ^ 2) :
    HasDerivAt (curvField f)
      (pd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 3) t := by
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr (hsq t)
  have hs2 : Real.sqrt (1 - pulseField f t ^ 2) ^ 2 = 1 - pulseField f t ^ 2 :=
    Real.sq_sqrt (hsq t).le
  have hin : HasDerivAt (fun r => 1 - pulseField f r ^ 2)
      (-(2 * pulseField f t * pd t)) t := by
    simpa using (((hp t).pow 2).const_sub 1)
  have hsqrt : HasDerivAt (fun r => Real.sqrt (1 - pulseField f r ^ 2))
      (-(2 * pulseField f t * pd t)
        / (2 * Real.sqrt (1 - pulseField f t ^ 2))) t := hin.sqrt (hsq t).ne'
  have hdiv : HasDerivAt
      (fun r => pulseField f r / Real.sqrt (1 - pulseField f r ^ 2))
      ((pd t * Real.sqrt (1 - pulseField f t ^ 2)
        - pulseField f t * (-(2 * pulseField f t * pd t)
          / (2 * Real.sqrt (1 - pulseField f t ^ 2))))
        / Real.sqrt (1 - pulseField f t ^ 2) ^ 2) t :=
    (hp t).div hsqrt hs.ne'
  rw [curvField_eq_pulse_div f]
  convert hdiv using 1
  have hnum : pd t * Real.sqrt (1 - pulseField f t ^ 2)
      - pulseField f t * (-(2 * pulseField f t * pd t)
        / (2 * Real.sqrt (1 - pulseField f t ^ 2)))
      = pd t / Real.sqrt (1 - pulseField f t ^ 2) := by
    field_simp
    linear_combination pd t * hs2
  rw [hnum, div_div]
  congr 1
  ring

/-- The second derivative of the curvature field, from the pulse field. -/
theorem hasDerivAt_curvField_two_of_pulse {f : ℝ → ℝ} {pd pdd : ℝ → ℝ} {t : ℝ}
    (hp : ∀ r, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r, HasDerivAt pd (pdd r) r)
    (hsq : ∀ r, (0:ℝ) < 1 - pulseField f r ^ 2) :
    HasDerivAt (fun r => pd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 3)
      ((pdd t * Real.sqrt (1 - pulseField f t ^ 2) ^ 3
        - pd t * (3 * Real.sqrt (1 - pulseField f t ^ 2) ^ 2
          * (-(pulseField f t * pd t)
            / Real.sqrt (1 - pulseField f t ^ 2))))
        / (Real.sqrt (1 - pulseField f t ^ 2) ^ 3) ^ 2) t := by
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr (hsq t)
  have hc : ∀ r, HasDerivAt (fun u => Real.sqrt (1 - pulseField f u ^ 2))
      (-(pulseField f r * pd r) / Real.sqrt (1 - pulseField f r ^ 2)) r := by
    intro r
    have hsr : 0 < Real.sqrt (1 - pulseField f r ^ 2) := Real.sqrt_pos.mpr (hsq r)
    have hin : HasDerivAt (fun u => 1 - pulseField f u ^ 2)
        (-(2 * pulseField f r * pd r)) r := by
      simpa using (((hp r).pow 2).const_sub 1)
    have h := hin.sqrt (hsq r).ne'
    have heq : -(2 * pulseField f r * pd r)
        / (2 * Real.sqrt (1 - pulseField f r ^ 2))
        = -(pulseField f r * pd r) / Real.sqrt (1 - pulseField f r ^ 2) := by
      field_simp
    rwa [heq] at h
  have hc3 : HasDerivAt (fun r => Real.sqrt (1 - pulseField f r ^ 2) ^ 3)
      (3 * Real.sqrt (1 - pulseField f t ^ 2) ^ 2
        * (-(pulseField f t * pd t)
          / Real.sqrt (1 - pulseField f t ^ 2))) t := by
    simpa [mul_comm] using (hc t).pow 3
  exact (hpd t).div hc3 (by positivity)

/-- The order-two curvature coefficient `(G')² + G G''`, written in pulse
quantities and bounded.  `G G'' + (G')² = pd²/S⁶ + p·pdd/S⁴ + 3p²pd²/S⁶`, and
`p·pdd = C₂ − pd²` is what the order-two relative pulse bound controls. -/
theorem abs_coeff_curv_two_le {p pd pdd S Sb b D1 D2 : ℝ}
    (hSb : 0 < Sb) (hSbS : Sb ≤ S)
    (hp0 : 0 ≤ p) (hpb : p ≤ b) (hb0 : 0 ≤ b)
    (hpd : |pd| ≤ D1) (hC2 : |p * pdd + pd ^ 2| ≤ D2) :
    |pd ^ 2 / S ^ 6 + p * pdd / S ^ 4 + 3 * p ^ 2 * pd ^ 2 / S ^ 6|
      ≤ D1 ^ 2 / Sb ^ 6 + (D2 + D1 ^ 2) / Sb ^ 4
        + 3 * b ^ 2 * D1 ^ 2 / Sb ^ 6 := by
  have hS : 0 < S := lt_of_lt_of_le hSb hSbS
  have hD2 : 0 ≤ D2 := le_trans (abs_nonneg _) hC2
  have hS6 : Sb ^ 6 ≤ S ^ 6 := pow_le_pow_left₀ hSb.le hSbS 6
  have hS4 : Sb ^ 4 ≤ S ^ 4 := pow_le_pow_left₀ hSb.le hSbS 4
  have hpd2 : pd ^ 2 ≤ D1 ^ 2 := by
    have h : |pd| ^ 2 ≤ D1 ^ 2 := pow_le_pow_left₀ (abs_nonneg pd) hpd 2
    rwa [sq_abs] at h
  have hppdd : |p * pdd| ≤ D2 + D1 ^ 2 := by
    have h : |p * pdd| ≤ |p * pdd + pd ^ 2| + |pd ^ 2| := by
      have := abs_sub (p * pdd + pd ^ 2) (pd ^ 2)
      simpa using this
    rw [abs_of_nonneg (sq_nonneg pd)] at h
    linarith [hC2, hpd2]
  have hT1 : |pd ^ 2 / S ^ 6| ≤ D1 ^ 2 / Sb ^ 6 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg pd),
      abs_of_pos (by positivity : (0:ℝ) < S ^ 6)]
    exact div_le_div₀ (by positivity) hpd2 (by positivity) hS6
  have hT2 : |p * pdd / S ^ 4| ≤ (D2 + D1 ^ 2) / Sb ^ 4 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < S ^ 4)]
    exact div_le_div₀ (by nlinarith [hD2, sq_nonneg D1]) hppdd (by positivity) hS4
  have hT3 : |3 * p ^ 2 * pd ^ 2 / S ^ 6| ≤ 3 * b ^ 2 * D1 ^ 2 / Sb ^ 6 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < S ^ 6)]
    refine div_le_div₀ (by positivity) ?_ (by positivity) hS6
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * p ^ 2 * pd ^ 2)]
    have hpb2 : p ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith [hpd2, sq_nonneg pd, sq_nonneg p]
  calc |pd ^ 2 / S ^ 6 + p * pdd / S ^ 4 + 3 * p ^ 2 * pd ^ 2 / S ^ 6|
      ≤ |pd ^ 2 / S ^ 6 + p * pdd / S ^ 4| + |3 * p ^ 2 * pd ^ 2 / S ^ 6| :=
        abs_add_le _ _
    _ ≤ (|pd ^ 2 / S ^ 6| + |p * pdd / S ^ 4|) + |3 * p ^ 2 * pd ^ 2 / S ^ 6| :=
        add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ _ := add_le_add (add_le_add hT1 hT2) hT3

/-- The pulse field is strictly inside `(−1,1)`, unconditionally. -/
theorem pulseField_sq_lt_one (f : ℝ → ℝ) (t : ℝ) : pulseField f t ^ 2 < 1 := by
  rw [pulseField, div_pow]
  have hpos : (0:ℝ) < 1 + curvField f t ^ 2 := by positivity
  have hs : Real.sqrt (1 + curvField f t ^ 2) ^ 2 = 1 + curvField f t ^ 2 :=
    Real.sq_sqrt hpos.le
  rw [hs, div_lt_one hpos]
  nlinarith

theorem one_sub_pulseField_sq_pos (f : ℝ → ℝ) (t : ℝ) :
    (0:ℝ) < 1 - pulseField f t ^ 2 := by
  have := pulseField_sq_lt_one f t; linarith

theorem coeff_one (G : ℝ → ℝ) : RelativeDerivatives.coeff G 1 = deriv G := by
  rw [RelativeDerivatives.coeff_succ]
  simp

theorem coeff_two (G : ℝ → ℝ) :
    RelativeDerivatives.coeff G 2 = deriv (fun t => G t * deriv G t) := by
  rw [show (2:ℕ) = 1 + 1 from rfl, RelativeDerivatives.coeff_succ, coeff_one]

theorem hasDerivAt_curvField_of_pulse' {f : ℝ → ℝ} {c : ℝ} {t : ℝ}
    (hp : HasDerivAt (pulseField f) c t) :
    HasDerivAt (curvField f)
      (c / Real.sqrt (1 - pulseField f t ^ 2) ^ 3) t := by
  have hsq := one_sub_pulseField_sq_pos f t
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr hsq
  have hs2 : Real.sqrt (1 - pulseField f t ^ 2) ^ 2 = 1 - pulseField f t ^ 2 :=
    Real.sq_sqrt hsq.le
  have hin : HasDerivAt (fun r => 1 - pulseField f r ^ 2)
      (-(2 * pulseField f t * c)) t := by
    simpa using ((hp.pow 2).const_sub 1)
  have hsqrt : HasDerivAt (fun r => Real.sqrt (1 - pulseField f r ^ 2))
      (-(2 * pulseField f t * c) / (2 * Real.sqrt (1 - pulseField f t ^ 2))) t :=
    hin.sqrt hsq.ne'
  have hdiv : HasDerivAt
      (fun r => pulseField f r / Real.sqrt (1 - pulseField f r ^ 2))
      ((c * Real.sqrt (1 - pulseField f t ^ 2)
        - pulseField f t * (-(2 * pulseField f t * c)
          / (2 * Real.sqrt (1 - pulseField f t ^ 2))))
        / Real.sqrt (1 - pulseField f t ^ 2) ^ 2) t := hp.div hsqrt hs.ne'
  rw [curvField_eq_pulse_div f]
  convert hdiv using 1
  have hnum : c * Real.sqrt (1 - pulseField f t ^ 2)
      - pulseField f t * (-(2 * pulseField f t * c)
        / (2 * Real.sqrt (1 - pulseField f t ^ 2)))
      = c / Real.sqrt (1 - pulseField f t ^ 2) := by
    field_simp
    linear_combination c * hs2
  rw [hnum, div_div]
  congr 1
  ring

theorem hasDerivAt_curvField_two_of_pulse' {f : ℝ → ℝ} {pd : ℝ → ℝ} {d : ℝ}
    {t : ℝ} (hp : HasDerivAt (pulseField f) (pd t) t)
    (hpd : HasDerivAt pd d t) :
    HasDerivAt (fun r => pd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 3)
      ((d * Real.sqrt (1 - pulseField f t ^ 2) ^ 3
        - pd t * (3 * Real.sqrt (1 - pulseField f t ^ 2) ^ 2
          * (-(pulseField f t * pd t)
            / Real.sqrt (1 - pulseField f t ^ 2))))
        / (Real.sqrt (1 - pulseField f t ^ 2) ^ 3) ^ 2) t := by
  have hsq := one_sub_pulseField_sq_pos f t
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr hsq
  have hc : HasDerivAt (fun u => Real.sqrt (1 - pulseField f u ^ 2))
      (-(pulseField f t * pd t) / Real.sqrt (1 - pulseField f t ^ 2)) t := by
    have hin : HasDerivAt (fun u => 1 - pulseField f u ^ 2)
        (-(2 * pulseField f t * pd t)) t := by
      simpa using ((hp.pow 2).const_sub 1)
    have h := hin.sqrt hsq.ne'
    have heq : -(2 * pulseField f t * pd t)
        / (2 * Real.sqrt (1 - pulseField f t ^ 2))
        = -(pulseField f t * pd t) / Real.sqrt (1 - pulseField f t ^ 2) := by
      field_simp
    rwa [heq] at h
  have hc3 : HasDerivAt (fun r => Real.sqrt (1 - pulseField f r ^ 2) ^ 3)
      (3 * Real.sqrt (1 - pulseField f t ^ 2) ^ 2
        * (-(pulseField f t * pd t)
          / Real.sqrt (1 - pulseField f t ^ 2))) t := by
    simpa [mul_comm] using hc.pow 3
  exact hpd.div hc3 (by positivity)

/-- `coeff (curvField f) 2` in pulse quantities, on the open interval. -/
theorem coeff_curvField_two_eq {f : ℝ → ℝ} {pd pdd : ℝ → ℝ}
    (hp : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pd (pdd r) r)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) π) :
    RelativeDerivatives.coeff (curvField f) 2 t
      = pd t ^ 2 / Real.sqrt (1 - pulseField f t ^ 2) ^ 6
        + pulseField f t * pdd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 4
        + 3 * pulseField f t ^ 2 * pd t ^ 2
          / Real.sqrt (1 - pulseField f t ^ 2) ^ 6 := by
  rw [coeff_two]
  have hev : (fun r => curvField f r * deriv (curvField f) r)
      =ᶠ[nhds t] fun r => curvField f r
        * (pd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 3) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    rw [(hasDerivAt_curvField_of_pulse' (hp r hr)).deriv]
  rw [hev.deriv_eq]
  have h1 := hasDerivAt_curvField_of_pulse' (hp t ht)
  have h2 := hasDerivAt_curvField_two_of_pulse' (hp t ht) (hpd t ht)
  have hmul : HasDerivAt (fun r => curvField f r
      * (pd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 3))
      (pd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 3
          * (pd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 3)
        + curvField f t
          * ((pdd t * Real.sqrt (1 - pulseField f t ^ 2) ^ 3
            - pd t * (3 * Real.sqrt (1 - pulseField f t ^ 2) ^ 2
              * (-(pulseField f t * pd t)
                / Real.sqrt (1 - pulseField f t ^ 2))))
            / (Real.sqrt (1 - pulseField f t ^ 2) ^ 3) ^ 2)) t := h1.mul h2
  rw [hmul.deriv]
  have hsq := one_sub_pulseField_sq_pos f t
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr hsq
  have hG : curvField f t
      = pulseField f t / Real.sqrt (1 - pulseField f t ^ 2) := by
    rw [curvField_eq_pulse_div f]
  rw [hG]
  field_simp
  ring

theorem abs_coeff_curvField_two_le {f : ℝ → ℝ} {pd pdd : ℝ → ℝ} {b D1 D2 : ℝ}
    (hp : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pd (pdd r) r)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy0 : ∀ r ∈ Ioo (0:ℝ) π, 0 ≤ pulseField f r)
    (hyb : ∀ r ∈ Ioo (0:ℝ) π, pulseField f r ≤ b)
    (hpdb : ∀ r ∈ Ioo (0:ℝ) π, |pd r| ≤ D1)
    (hC2 : ∀ r ∈ Ioo (0:ℝ) π, |pulseField f r * pdd r + pd r ^ 2| ≤ D2)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) π) :
    |RelativeDerivatives.coeff (curvField f) 2 t|
      ≤ D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6
        + (D2 + D1 ^ 2) / Real.sqrt (1 - b ^ 2) ^ 4
        + 3 * b ^ 2 * D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6 := by
  rw [coeff_curvField_two_eq hp hpd ht]
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith [hy0 t ht, hyb t ht]
  have hSb : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr hsb
  have hSbS : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - pulseField f t ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [hy0 t ht, hyb t ht])
  exact abs_coeff_curv_two_le hSb hSbS (hy0 t ht) (hyb t ht) hb0
    (hpdb t ht) (hC2 t ht)

open scoped ContDiff in
/-- **The order-two relative curvature bound**, from pulse-side data only. -/
theorem abs_iteratedDeriv_two_curv_le {f theta : ℝ → ℝ} {pd pdd : ℝ → ℝ}
    {b D1 D2 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hp : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pd (pdd r) r)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy0 : ∀ r ∈ Ioo (0:ℝ) π, 0 ≤ pulseField f r)
    (hyb : ∀ r ∈ Ioo (0:ℝ) π, pulseField f r ≤ b)
    (hpdb : ∀ r ∈ Ioo (0:ℝ) π, |pd r| ≤ D1)
    (hC2 : ∀ r ∈ Ioo (0:ℝ) π, |pulseField f r * pdd r + pd r ^ 2| ≤ D2) :
    ∀ u, |iteratedDeriv 2 (fun u => curvField f (theta u)) u|
      ≤ (D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6
          + (D2 + D1 ^ 2) / Real.sqrt (1 - b ^ 2) ^ 4
          + 3 * b ^ 2 * D1 ^ 2 / Real.sqrt (1 - b ^ 2) ^ 6)
        * curvField f (theta u) :=
  RelativeDerivatives.abs_iteratedDeriv_le_of_coeff_bound isOpen_Ioo
    (HairpinInteriorRegularity.contDiffOn_curvField hf hfpos) hmem hderiv
    (fun u => (curvField_pos_interior hfpos (hmem u)).le)
    (fun t ht => abs_coeff_curvField_two_le hp hpd hb0 hb1 hy0 hyb hpdb hC2 ht)

/-- Derivative of `N/S^{k+1}` where `S = √(1−y²)`. -/
theorem hasDerivAt_div_sqrtPow {f N : ℝ → ℝ} {pd : ℝ → ℝ} {n : ℝ} {k : ℕ}
    {t : ℝ} (hp : HasDerivAt (pulseField f) (pd t) t) (hN : HasDerivAt N n t) :
    HasDerivAt (fun r => N r / Real.sqrt (1 - pulseField f r ^ 2) ^ (k + 1))
      ((n * Real.sqrt (1 - pulseField f t ^ 2) ^ (k + 1)
        - N t * ((k + 1 : ℕ) * Real.sqrt (1 - pulseField f t ^ 2) ^ k
          * (-(pulseField f t * pd t)
            / Real.sqrt (1 - pulseField f t ^ 2))))
        / (Real.sqrt (1 - pulseField f t ^ 2) ^ (k + 1)) ^ 2) t := by
  have hsq := one_sub_pulseField_sq_pos f t
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr hsq
  have hc : HasDerivAt (fun u => Real.sqrt (1 - pulseField f u ^ 2))
      (-(pulseField f t * pd t) / Real.sqrt (1 - pulseField f t ^ 2)) t := by
    have hin : HasDerivAt (fun u => 1 - pulseField f u ^ 2)
        (-(2 * pulseField f t * pd t)) t := by
      simpa using ((hp.pow 2).const_sub 1)
    have h := hin.sqrt hsq.ne'
    have heq : -(2 * pulseField f t * pd t)
        / (2 * Real.sqrt (1 - pulseField f t ^ 2))
        = -(pulseField f t * pd t) / Real.sqrt (1 - pulseField f t ^ 2) := by
      field_simp
    rwa [heq] at h
  have hck : HasDerivAt (fun r => Real.sqrt (1 - pulseField f r ^ 2) ^ (k + 1))
      ((k + 1 : ℕ) * Real.sqrt (1 - pulseField f t ^ 2) ^ k
        * (-(pulseField f t * pd t)
          / Real.sqrt (1 - pulseField f t ^ 2))) t := by
    simpa [mul_comm] using hc.pow (k + 1)
  exact hN.div hck (by positivity)

theorem hasDerivAt_coeffTwoExpr {f pd pdd pddd : ℝ → ℝ} {t : ℝ}
    (hp : HasDerivAt (pulseField f) (pd t) t)
    (hpd : HasDerivAt pd (pdd t) t)
    (hpdd : HasDerivAt pdd (pddd t) t) :
    HasDerivAt (fun r => pd r ^ 2 / Real.sqrt (1 - pulseField f r ^ 2) ^ 6
        + pulseField f r * pdd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 4
        + 3 * pulseField f r ^ 2 * pd r ^ 2
          / Real.sqrt (1 - pulseField f r ^ 2) ^ 6)
      (2 * pd t * pdd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 6
        + 6 * pulseField f t * pd t ^ 3
          / Real.sqrt (1 - pulseField f t ^ 2) ^ 8
        + ((pd t * pdd t + pulseField f t * pddd t)
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 4
          + 4 * pulseField f t ^ 2 * pd t * pdd t
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 6)
        + ((6 * pulseField f t * pd t ^ 3
              + 6 * pulseField f t ^ 2 * pd t * pdd t)
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 6
          + 18 * pulseField f t ^ 3 * pd t ^ 3
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 8)) t := by
  have hsq := one_sub_pulseField_sq_pos f t
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr hsq
  have hN1 : HasDerivAt (fun r => pd r ^ 2) (2 * pd t * pdd t) t := by
    simpa [mul_comm] using hpd.pow 2
  have hN2 : HasDerivAt (fun r => pulseField f r * pdd r)
      (pd t * pdd t + pulseField f t * pddd t) t := hp.mul hpdd
  have hN3 : HasDerivAt (fun r => 3 * pulseField f r ^ 2 * pd r ^ 2)
      (6 * pulseField f t * pd t ^ 3
        + 6 * pulseField f t ^ 2 * pd t * pdd t) t := by
    have h1 : HasDerivAt (fun r => 3 * pulseField f r ^ 2)
        (3 * (2 * pulseField f t * pd t)) t := by
      have := (hp.pow 2).const_mul (3:ℝ)
      convert this using 1
      ring
    have h2 : HasDerivAt (fun r => pd r ^ 2) (2 * pd t * pdd t) t := hN1
    have := h1.mul h2
    convert this using 1
    ring
  have h1 := hasDerivAt_div_sqrtPow (k := 5) hp hN1
  have h2 := hasDerivAt_div_sqrtPow (k := 3) hp hN2
  have h3 := hasDerivAt_div_sqrtPow (k := 5) hp hN3
  have hsum := (h1.add h2).add h3
  convert hsum using 1
  push_cast
  field_simp
  ring

theorem coeff_three (G : ℝ → ℝ) :
    RelativeDerivatives.coeff G 3
      = deriv (fun t => G t * RelativeDerivatives.coeff G 2 t) := by
  rw [show (3:ℕ) = 2 + 1 from rfl, RelativeDerivatives.coeff_succ]

theorem coeff_curvField_three_eq {f pd pdd pddd : ℝ → ℝ}
    (hp : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pd (pdd r) r)
    (hpdd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pdd (pddd r) r)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) π) :
    RelativeDerivatives.coeff (curvField f) 3 t
      = pd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 3
          * (pd t ^ 2 / Real.sqrt (1 - pulseField f t ^ 2) ^ 6
            + pulseField f t * pdd t
              / Real.sqrt (1 - pulseField f t ^ 2) ^ 4
            + 3 * pulseField f t ^ 2 * pd t ^ 2
              / Real.sqrt (1 - pulseField f t ^ 2) ^ 6)
        + (2 * pd t * (pulseField f t * pdd t)
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 7
          + 6 * pulseField f t ^ 2 * pd t ^ 3
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 9
          + (pd t * (pulseField f t * pdd t)
              + pulseField f t ^ 2 * pddd t)
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 5
          + 4 * pulseField f t ^ 2 * pd t * (pulseField f t * pdd t)
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 7
          + (6 * pulseField f t ^ 2 * pd t ^ 3
              + 6 * pulseField f t ^ 2 * pd t * (pulseField f t * pdd t))
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 7
          + 18 * pulseField f t ^ 4 * pd t ^ 3
            / Real.sqrt (1 - pulseField f t ^ 2) ^ 9) := by
  have hsq := one_sub_pulseField_sq_pos f t
  have hs : 0 < Real.sqrt (1 - pulseField f t ^ 2) := Real.sqrt_pos.mpr hsq
  rw [coeff_three]
  have hev : (fun r => curvField f r * RelativeDerivatives.coeff (curvField f) 2 r)
      =ᶠ[nhds t] fun r => curvField f r
        * (pd r ^ 2 / Real.sqrt (1 - pulseField f r ^ 2) ^ 6
          + pulseField f r * pdd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 4
          + 3 * pulseField f r ^ 2 * pd r ^ 2
            / Real.sqrt (1 - pulseField f r ^ 2) ^ 6) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    rw [coeff_curvField_two_eq hp hpd hr]
  rw [hev.deriv_eq]
  have hG := hasDerivAt_curvField_of_pulse' (hp t ht)
  have hW := hasDerivAt_coeffTwoExpr (hp t ht) (hpd t ht) (hpdd t ht)
  have hmul : HasDerivAt (fun r => curvField f r
      * (pd r ^ 2 / Real.sqrt (1 - pulseField f r ^ 2) ^ 6
        + pulseField f r * pdd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 4
        + 3 * pulseField f r ^ 2 * pd r ^ 2
          / Real.sqrt (1 - pulseField f r ^ 2) ^ 6))
      (pd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 3
          * (pd t ^ 2 / Real.sqrt (1 - pulseField f t ^ 2) ^ 6
            + pulseField f t * pdd t
              / Real.sqrt (1 - pulseField f t ^ 2) ^ 4
            + 3 * pulseField f t ^ 2 * pd t ^ 2
              / Real.sqrt (1 - pulseField f t ^ 2) ^ 6)
        + curvField f t
          * (2 * pd t * pdd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 6
            + 6 * pulseField f t * pd t ^ 3
              / Real.sqrt (1 - pulseField f t ^ 2) ^ 8
            + ((pd t * pdd t + pulseField f t * pddd t)
                / Real.sqrt (1 - pulseField f t ^ 2) ^ 4
              + 4 * pulseField f t ^ 2 * pd t * pdd t
                / Real.sqrt (1 - pulseField f t ^ 2) ^ 6)
            + ((6 * pulseField f t * pd t ^ 3
                  + 6 * pulseField f t ^ 2 * pd t * pdd t)
                / Real.sqrt (1 - pulseField f t ^ 2) ^ 6
              + 18 * pulseField f t ^ 3 * pd t ^ 3
                / Real.sqrt (1 - pulseField f t ^ 2) ^ 8))) t := hG.mul hW
  rw [hmul.deriv, curvField_eq_pulse_div f]
  field_simp
  ring

theorem abs_div_sqrtPow_le {N S Sb M : ℝ} {k : ℕ} (hSb : 0 < Sb) (hSbS : Sb ≤ S)
    (hN : |N| ≤ M) : |N / S ^ k| ≤ M / Sb ^ k := by
  have hS : 0 < S := lt_of_lt_of_le hSb hSbS
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < S ^ k)]
  exact div_le_div₀ (le_trans (abs_nonneg _) hN) hN (by positivity)
    (pow_le_pow_left₀ hSb.le hSbS k)

/-- **The order-three curvature coefficient is bounded.**  Every term of
`coeff_curvField_three_eq` carries the pulse factors that the relative pulse
bounds control: `y'`, `y y''`, and `y² y'''`. -/
theorem abs_coeff_curvField_three_le {f pd pdd pddd : ℝ → ℝ}
    {b D1 E2 Q0 R0 : ℝ}
    (hp : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pd (pdd r) r)
    (hpdd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pdd (pddd r) r)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy0 : ∀ r ∈ Ioo (0:ℝ) π, 0 ≤ pulseField f r)
    (hyb : ∀ r ∈ Ioo (0:ℝ) π, pulseField f r ≤ b)
    (hpdb : ∀ r ∈ Ioo (0:ℝ) π, |pd r| ≤ D1)
    (hQ : ∀ r ∈ Ioo (0:ℝ) π, |pulseField f r * pdd r| ≤ Q0)
    (hR : ∀ r ∈ Ioo (0:ℝ) π, |pulseField f r ^ 2 * pddd r| ≤ R0)
    (hW : ∀ r ∈ Ioo (0:ℝ) π,
      |pd r ^ 2 / Real.sqrt (1 - pulseField f r ^ 2) ^ 6
        + pulseField f r * pdd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 4
        + 3 * pulseField f r ^ 2 * pd r ^ 2
          / Real.sqrt (1 - pulseField f r ^ 2) ^ 6| ≤ E2)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) π) :
    |RelativeDerivatives.coeff (curvField f) 3 t|
      ≤ D1 / Real.sqrt (1 - b ^ 2) ^ 3 * E2
        + (2 * D1 * Q0 / Real.sqrt (1 - b ^ 2) ^ 7
          + 6 * b ^ 2 * D1 ^ 3 / Real.sqrt (1 - b ^ 2) ^ 9
          + (D1 * Q0 + R0) / Real.sqrt (1 - b ^ 2) ^ 5
          + 4 * b ^ 2 * D1 * Q0 / Real.sqrt (1 - b ^ 2) ^ 7
          + (6 * b ^ 2 * D1 ^ 3 + 6 * b ^ 2 * D1 * Q0)
            / Real.sqrt (1 - b ^ 2) ^ 7
          + 18 * b ^ 4 * D1 ^ 3 / Real.sqrt (1 - b ^ 2) ^ 9) := by
  have hy0t := hy0 t ht
  have hybt := hyb t ht
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hSb : 0 < Real.sqrt (1 - b ^ 2) := Real.sqrt_pos.mpr hsb
  have hSbS : Real.sqrt (1 - b ^ 2) ≤ Real.sqrt (1 - pulseField f t ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hD1 : 0 ≤ D1 := le_trans (abs_nonneg _) (hpdb t ht)
  have hQ0 : 0 ≤ Q0 := le_trans (abs_nonneg _) (hQ t ht)
  have hR0 : 0 ≤ R0 := le_trans (abs_nonneg _) (hR t ht)
  have hE2 : 0 ≤ E2 := le_trans (abs_nonneg _) (hW t ht)
  have hp2 : pulseField f t ^ 2 ≤ b ^ 2 := by nlinarith
  have hp4 : pulseField f t ^ 4 ≤ b ^ 4 := by nlinarith
  have hpd3 : |pd t ^ 3| ≤ D1 ^ 3 := by
    have h := hpdb t ht
    calc |pd t ^ 3| = |pd t| ^ 3 := by rw [abs_pow]
      _ ≤ D1 ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h 3
  rw [coeff_curvField_three_eq hp hpd hpdd ht]
  have hA : |pd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 3
      * (pd t ^ 2 / Real.sqrt (1 - pulseField f t ^ 2) ^ 6
        + pulseField f t * pdd t / Real.sqrt (1 - pulseField f t ^ 2) ^ 4
        + 3 * pulseField f t ^ 2 * pd t ^ 2
          / Real.sqrt (1 - pulseField f t ^ 2) ^ 6)|
      ≤ D1 / Real.sqrt (1 - b ^ 2) ^ 3 * E2 := by
    rw [abs_mul]
    exact mul_le_mul (abs_div_sqrtPow_le hSb hSbS (hpdb t ht)) (hW t ht)
      (abs_nonneg _) (div_nonneg hD1 (by positivity))
  have hb1' : |2 * pd t * (pulseField f t * pdd t)| ≤ 2 * D1 * Q0 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    have := mul_le_mul (hpdb t ht) (hQ t ht) (abs_nonneg _) hD1
    nlinarith [abs_nonneg (pd t), abs_nonneg (pulseField f t * pdd t)]
  have hb2' : |6 * pulseField f t ^ 2 * pd t ^ 3| ≤ 6 * b ^ 2 * D1 ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (6:ℝ)),
      abs_of_nonneg (sq_nonneg _)]
    nlinarith [hpd3, hp2, abs_nonneg (pd t ^ 3), sq_nonneg (pulseField f t)]
  have hb3' : |pd t * (pulseField f t * pdd t) + pulseField f t ^ 2 * pddd t|
      ≤ D1 * Q0 + R0 := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ (hR t ht))
    rw [abs_mul]
    exact mul_le_mul (hpdb t ht) (hQ t ht) (abs_nonneg _) hD1
  have hb4' : |4 * pulseField f t ^ 2 * pd t * (pulseField f t * pdd t)|
      ≤ 4 * b ^ 2 * D1 * Q0 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (4:ℝ)),
      abs_of_nonneg (sq_nonneg _)]
    have hprod : |pd t| * |pulseField f t * pdd t| ≤ D1 * Q0 :=
      mul_le_mul (hpdb t ht) (hQ t ht) (abs_nonneg _) hD1
    have hA0 : (0:ℝ) ≤ |pd t| * |pulseField f t * pdd t| := by positivity
    nlinarith [hprod, hp2, hA0, sq_nonneg b]
  have hb5' : |6 * pulseField f t ^ 2 * pd t ^ 3
      + 6 * pulseField f t ^ 2 * pd t * (pulseField f t * pdd t)|
      ≤ 6 * b ^ 2 * D1 ^ 3 + 6 * b ^ 2 * D1 * Q0 := by
    refine le_trans (abs_add_le _ _) (add_le_add hb2' ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (6:ℝ)),
      abs_of_nonneg (sq_nonneg _)]
    have hprod : |pd t| * |pulseField f t * pdd t| ≤ D1 * Q0 :=
      mul_le_mul (hpdb t ht) (hQ t ht) (abs_nonneg _) hD1
    have hA0 : (0:ℝ) ≤ |pd t| * |pulseField f t * pdd t| := by positivity
    nlinarith [hprod, hp2, hA0, sq_nonneg b]
  have hb6' : |18 * pulseField f t ^ 4 * pd t ^ 3| ≤ 18 * b ^ 4 * D1 ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (18:ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ pulseField f t ^ 4)]
    nlinarith [hpd3, hp4, abs_nonneg (pd t ^ 3), pow_nonneg hy0t 4]
  refine le_trans (abs_add_le _ _) (add_le_add hA ?_)
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (abs_div_sqrtPow_le hSb hSbS hb6'))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (abs_div_sqrtPow_le hSb hSbS hb5'))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (abs_div_sqrtPow_le hSb hSbS hb4'))
  refine le_trans (abs_add_le _ _) (add_le_add ?_ (abs_div_sqrtPow_le hSb hSbS hb3'))
  refine le_trans (abs_add_le _ _) (add_le_add
    (abs_div_sqrtPow_le hSb hSbS hb1') (abs_div_sqrtPow_le hSb hSbS hb2'))

open scoped ContDiff in
/-- **The order-three relative curvature bound**, from pulse-side data only. -/
theorem abs_iteratedDeriv_three_curv_le {f theta : ℝ → ℝ} {pd pdd pddd : ℝ → ℝ}
    {b D1 E2 Q0 R0 : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 π)) (hfpos : ∀ t ∈ Ioo (0:ℝ) π, 0 < f t)
    (hmem : ∀ u, theta u ∈ Ioo 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u)
    (hp : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt (pulseField f) (pd r) r)
    (hpd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pd (pdd r) r)
    (hpdd : ∀ r ∈ Ioo (0:ℝ) π, HasDerivAt pdd (pddd r) r)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy0 : ∀ r ∈ Ioo (0:ℝ) π, 0 ≤ pulseField f r)
    (hyb : ∀ r ∈ Ioo (0:ℝ) π, pulseField f r ≤ b)
    (hpdb : ∀ r ∈ Ioo (0:ℝ) π, |pd r| ≤ D1)
    (hQ : ∀ r ∈ Ioo (0:ℝ) π, |pulseField f r * pdd r| ≤ Q0)
    (hR : ∀ r ∈ Ioo (0:ℝ) π, |pulseField f r ^ 2 * pddd r| ≤ R0)
    (hW : ∀ r ∈ Ioo (0:ℝ) π,
      |pd r ^ 2 / Real.sqrt (1 - pulseField f r ^ 2) ^ 6
        + pulseField f r * pdd r / Real.sqrt (1 - pulseField f r ^ 2) ^ 4
        + 3 * pulseField f r ^ 2 * pd r ^ 2
          / Real.sqrt (1 - pulseField f r ^ 2) ^ 6| ≤ E2) :
    ∀ u, |iteratedDeriv 3 (fun u => curvField f (theta u)) u|
      ≤ (D1 / Real.sqrt (1 - b ^ 2) ^ 3 * E2
          + (2 * D1 * Q0 / Real.sqrt (1 - b ^ 2) ^ 7
            + 6 * b ^ 2 * D1 ^ 3 / Real.sqrt (1 - b ^ 2) ^ 9
            + (D1 * Q0 + R0) / Real.sqrt (1 - b ^ 2) ^ 5
            + 4 * b ^ 2 * D1 * Q0 / Real.sqrt (1 - b ^ 2) ^ 7
            + (6 * b ^ 2 * D1 ^ 3 + 6 * b ^ 2 * D1 * Q0)
              / Real.sqrt (1 - b ^ 2) ^ 7
            + 18 * b ^ 4 * D1 ^ 3 / Real.sqrt (1 - b ^ 2) ^ 9))
        * curvField f (theta u) :=
  RelativeDerivatives.abs_iteratedDeriv_le_of_coeff_bound isOpen_Ioo
    (HairpinInteriorRegularity.contDiffOn_curvField hf hfpos) hmem hderiv
    (fun u => (curvField_pos_interior hfpos (hmem u)).le)
    (fun t ht => abs_coeff_curvField_three_le hp hpd hpdd hb0 hb1 hy0 hyb hpdb
      hQ hR hW ht)

end HairpinRelative
