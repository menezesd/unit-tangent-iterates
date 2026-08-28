import UnitTangentIterates.PulseRelativeOrderTwo

/-!
# The order-three relative pulse bound

The third step of the induction of `lem:pulse`, by the same method as
`PulseRelativeOrderTwo`.  Differentiating

```
  y'' = (−y y'/c)(K_* − y) + c(K_*' − y'),      c = √(1−y²),
```

once more gives

```
  y''' = −[(y')² + y y'']/c − y²(y')²/c³)(K_* − y)
         + 2(−y y'/c)(K_*' − y') + c(K_*'' − y''),
```

and every term is `O(y)` under the order-`≤2` pulse bounds, the order-`≤2`
curvature bounds, and `sup y ≤ b < 1`.  The surplus powers of `y` produced by
the extra differentiations are absorbed by `y ≤ b`, exactly as at order two.

**No derivative of the profile appears at this order either.**
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Real HairpinRelative

namespace HairpinRelative

theorem rel_three_expr_bound {Y yp ypp K Kd Kdd b Ch D1 D2 E1 E2 : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hY0 : 0 ≤ Y) (hYb : Y ≤ b) (hKnn : 0 ≤ K)
    (hypb : |yp| ≤ D1 * Y) (hyppb : |ypp| ≤ D2 * Y)
    (hKdb : |Kd| ≤ E1 * K) (hKddb : |Kdd| ≤ E2 * K)
    (hharn : K ≤ Ch * (Y / Real.sqrt (1 - b ^ 2))) :
    |(-((yp ^ 2 + Y * ypp) / Real.sqrt (1 - Y ^ 2)
        + Y ^ 2 * yp ^ 2 / Real.sqrt (1 - Y ^ 2) ^ 3)) * (K - Y)
      + 2 * (-(Y * yp) / Real.sqrt (1 - Y ^ 2)) * (Kd - yp)
      + Real.sqrt (1 - Y ^ 2) * (Kdd - ypp)|
    ≤ (b ^ 2 * (D1 ^ 2 + D2) * (Ch / Real.sqrt (1 - b ^ 2) + 1)
          / Real.sqrt (1 - b ^ 2)
        + b ^ 4 * D1 ^ 2 * (Ch / Real.sqrt (1 - b ^ 2) + 1)
          / Real.sqrt (1 - b ^ 2) ^ 3
        + 2 * b ^ 2 * D1 * (E1 * Ch / Real.sqrt (1 - b ^ 2) + D1)
          / Real.sqrt (1 - b ^ 2)
        + E2 * Ch / Real.sqrt (1 - b ^ 2) + D2) * Y := by
  set S := Real.sqrt (1 - b ^ 2) with hSdef
  set c := Real.sqrt (1 - Y ^ 2) with hcdef
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hS : 0 < S := Real.sqrt_pos.mpr hsb
  have hsq : (0:ℝ) < 1 - Y ^ 2 := by nlinarith
  have hc : 0 < c := Real.sqrt_pos.mpr hsq
  have hSc : S ≤ c := Real.sqrt_le_sqrt (by nlinarith)
  have hc1 : c ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - Y ^ 2 ≤ 1 by nlinarith)
    simpa [hcdef] using h
  have hCS : (0:ℝ) ≤ Ch / S := div_nonneg hCh hS.le
  have hypn : 0 ≤ D1 * Y := le_trans (abs_nonneg _) hypb
  have hyppn : 0 ≤ D2 * Y := le_trans (abs_nonneg _) hyppb
  -- `K - Y` and `Kd - yp`, `Kdd - ypp`
  have hKY : |K - Y| ≤ (Ch / S + 1) * Y := by
    have h : Ch * (Y / S) = Ch / S * Y := by ring
    rw [abs_le]; constructor <;> nlinarith [hharn, hY0, hKnn]
  have hKdyp : |Kd - yp| ≤ (E1 * Ch / S + D1) * Y := by
    have h1 : |Kd - yp| ≤ E1 * K + D1 * Y :=
      le_trans (abs_sub _ _) (add_le_add hKdb hypb)
    have h2 : E1 * K ≤ E1 * (Ch / S * Y) := by
      have h : Ch * (Y / S) = Ch / S * Y := by ring
      nlinarith [hharn, hE1]
    have h3 : E1 * (Ch / S * Y) = E1 * Ch / S * Y := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hKddypp : |Kdd - ypp| ≤ (E2 * Ch / S + D2) * Y := by
    have h1 : |Kdd - ypp| ≤ E2 * K + D2 * Y :=
      le_trans (abs_sub _ _) (add_le_add hKddb hyppb)
    have h2 : E2 * K ≤ E2 * (Ch / S * Y) := by
      have h : Ch * (Y / S) = Ch / S * Y := by ring
      nlinarith [hharn, hE2]
    have h3 : E2 * (Ch / S * Y) = E2 * Ch / S * Y := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hY2 : Y ^ 2 ≤ b ^ 2 := by nlinarith
  have hyp2 : yp ^ 2 ≤ D1 ^ 2 * Y ^ 2 := by
    have h : |yp| ^ 2 ≤ (D1 * Y) ^ 2 := pow_le_pow_left₀ (abs_nonneg yp) hypb 2
    rw [sq_abs] at h
    have he : (D1 * Y) ^ 2 = D1 ^ 2 * Y ^ 2 := by ring
    linarith [h, he.le, he.ge]
  have hYypp : |Y * ypp| ≤ D2 * Y ^ 2 := by
    rw [abs_mul, abs_of_nonneg hY0]
    nlinarith [hyppb, abs_nonneg ypp, hY0]
  have hSc3 : S ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hS.le hSc 3
  have hKYn : (0:ℝ) ≤ (Ch / S + 1) * Y := by nlinarith [hCS, hY0]
  have hY3 : Y ^ 2 * Y ≤ b ^ 2 * Y := by nlinarith [hY2, hY0]
  -- first term
  have hA : |(yp ^ 2 + Y * ypp) / c + Y ^ 2 * yp ^ 2 / c ^ 3|
      ≤ (D1 ^ 2 + D2) * Y ^ 2 / S + b ^ 2 * D1 ^ 2 * Y ^ 2 / S ^ 3 := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos hc]
      refine div_le_div₀ (by positivity) ?_ hS hSc
      calc |yp ^ 2 + Y * ypp| ≤ |yp ^ 2| + |Y * ypp| := abs_add_le _ _
        _ ≤ (D1 ^ 2 + D2) * Y ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg yp)]
            nlinarith [hyp2, hYypp]
    · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < c ^ 3)]
      refine div_le_div₀ (by positivity) ?_ (by positivity) hSc3
      rw [abs_mul, abs_of_nonneg (sq_nonneg Y), abs_of_nonneg (sq_nonneg yp)]
      nlinarith [hyp2, hY2, sq_nonneg Y, sq_nonneg yp, hD1]
  have hT1 : |(-((yp ^ 2 + Y * ypp) / c + Y ^ 2 * yp ^ 2 / c ^ 3)) * (K - Y)|
      ≤ (b ^ 2 * (D1 ^ 2 + D2) * (Ch / S + 1) / S
          + b ^ 4 * D1 ^ 2 * (Ch / S + 1) / S ^ 3) * Y := by
    rw [abs_mul, abs_neg]
    refine le_trans (mul_le_mul hA hKY (abs_nonneg _) (by positivity)) ?_
    have hexp : ((D1 ^ 2 + D2) * Y ^ 2 / S + b ^ 2 * D1 ^ 2 * Y ^ 2 / S ^ 3)
        * ((Ch / S + 1) * Y)
        = ((D1 ^ 2 + D2) * (Ch / S + 1) / S + b ^ 2 * D1 ^ 2 * (Ch / S + 1) / S ^ 3)
          * (Y ^ 2 * Y) := by field_simp
    rw [hexp]
    have hk : (0:ℝ) ≤ (D1 ^ 2 + D2) * (Ch / S + 1) / S
        + b ^ 2 * D1 ^ 2 * (Ch / S + 1) / S ^ 3 := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hY3 hk) ?_
    have : ((D1 ^ 2 + D2) * (Ch / S + 1) / S + b ^ 2 * D1 ^ 2 * (Ch / S + 1) / S ^ 3)
        * (b ^ 2 * Y)
        = (b ^ 2 * (D1 ^ 2 + D2) * (Ch / S + 1) / S
          + b ^ 4 * D1 ^ 2 * (Ch / S + 1) / S ^ 3) * Y := by field_simp
    exact this.le
  -- second term
  have hT2 : |2 * (-(Y * yp) / c) * (Kd - yp)|
      ≤ 2 * b ^ 2 * D1 * (E1 * Ch / S + D1) / S * Y := by
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_mul, abs_of_nonneg hY0, abs_of_pos hc]
    have h1 : Y * |yp| / c ≤ b * (D1 * Y) / S := by
      refine div_le_div₀ (by positivity) ?_ hS hSc
      nlinarith [hypb, abs_nonneg yp, hY0, hYb]
    have h2 : (0:ℝ) ≤ (E1 * Ch / S + D1) * Y := by
      have : (0:ℝ) ≤ E1 * Ch / S := by positivity
      nlinarith [hY0, hD1]
    have h3 : |(2:ℝ)| * (Y * |yp| / c) * |Kd - yp|
        ≤ 2 * (b * (D1 * Y) / S) * ((E1 * Ch / S + D1) * Y) := by
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hKdyp
        (abs_nonneg _) (by positivity)
    refine le_trans h3 ?_
    have hexp : 2 * (b * (D1 * Y) / S) * ((E1 * Ch / S + D1) * Y)
        = 2 * b * D1 * (E1 * Ch / S + D1) / S * (Y * Y) := by field_simp
    rw [hexp]
    have hk : (0:ℝ) ≤ 2 * b * D1 * (E1 * Ch / S + D1) / S := by positivity
    have hYY : Y * Y ≤ b * Y := by nlinarith
    refine le_trans (mul_le_mul_of_nonneg_left hYY hk) ?_
    have : 2 * b * D1 * (E1 * Ch / S + D1) / S * (b * Y)
        = 2 * b ^ 2 * D1 * (E1 * Ch / S + D1) / S * Y := by ring
    exact this.le
  -- third term
  have hT3 : |c * (Kdd - ypp)| ≤ (E2 * Ch / S + D2) * Y := by
    rw [abs_mul, abs_of_pos hc]
    calc c * |Kdd - ypp| ≤ 1 * |Kdd - ypp| :=
          mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
      _ = |Kdd - ypp| := one_mul _
      _ ≤ (E2 * Ch / S + D2) * Y := hKddypp
  calc |(-((yp ^ 2 + Y * ypp) / c + Y ^ 2 * yp ^ 2 / c ^ 3)) * (K - Y)
        + 2 * (-(Y * yp) / c) * (Kd - yp) + c * (Kdd - ypp)|
      ≤ |(-((yp ^ 2 + Y * ypp) / c + Y ^ 2 * yp ^ 2 / c ^ 3)) * (K - Y)
          + 2 * (-(Y * yp) / c) * (Kd - yp)| + |c * (Kdd - ypp)| := abs_add_le _ _
    _ ≤ (|(-((yp ^ 2 + Y * ypp) / c + Y ^ 2 * yp ^ 2 / c ^ 3)) * (K - Y)|
          + |2 * (-(Y * yp) / c) * (Kd - yp)|) + |c * (Kdd - ypp)| :=
        add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ _ := by
        refine le_trans (add_le_add (add_le_add hT1 hT2) hT3) ?_
        apply le_of_eq; ring

theorem hasDerivAt_ypp_of_solved {Y yp ypp K Kd Kdd : ℝ → ℝ} {s : ℝ}
    (hY : ∀ r, HasDerivAt Y (yp r) r)
    (hyp : ∀ r, HasDerivAt yp (ypp r) r)
    (hK : ∀ r, HasDerivAt K (Kd r) r)
    (hKd : ∀ r, HasDerivAt Kd (Kdd r) r)
    (hsq : ∀ r, (0:ℝ) < 1 - Y r ^ 2)
    (hform : ∀ r, ypp r
      = (-(Y r * yp r) / Real.sqrt (1 - Y r ^ 2)) * (K r - Y r)
        + Real.sqrt (1 - Y r ^ 2) * (Kd r - yp r)) :
    HasDerivAt ypp
      ((-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
          + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3)) * (K s - Y s)
        + 2 * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kd s - yp s)
        + Real.sqrt (1 - Y s ^ 2) * (Kdd s - ypp s)) s := by
  have hc : ∀ r, HasDerivAt (fun t => Real.sqrt (1 - Y t ^ 2))
      (-(Y r * yp r) / Real.sqrt (1 - Y r ^ 2)) r := by
    intro r
    have hin : HasDerivAt (fun t => 1 - Y t ^ 2) (-(2 * Y r * yp r)) r := by
      simpa using (((hY r).pow 2).const_sub 1)
    have h := hin.sqrt (hsq r).ne'
    have heq : -(2 * Y r * yp r) / (2 * Real.sqrt (1 - Y r ^ 2))
        = -(Y r * yp r) / Real.sqrt (1 - Y r ^ 2) := by
      have hs : 0 < Real.sqrt (1 - Y r ^ 2) := Real.sqrt_pos.mpr (hsq r)
      field_simp
    rwa [heq] at h
  -- the coefficient `u = -(Y yp)/c`
  have hnum : HasDerivAt (fun t => -(Y t * yp t))
      (-(yp s * yp s + Y s * ypp s)) s := by
    simpa using (((hY s).mul (hyp s)).neg)
  have hu : HasDerivAt (fun t => -(Y t * yp t) / Real.sqrt (1 - Y t ^ 2))
      ((-(yp s * yp s + Y s * ypp s) * Real.sqrt (1 - Y s ^ 2)
        - -(Y s * yp s) * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)))
        / Real.sqrt (1 - Y s ^ 2) ^ 2) s :=
    hnum.div (hc s) (Real.sqrt_pos.mpr (hsq s)).ne'
  have hu' : HasDerivAt (fun t => -(Y t * yp t) / Real.sqrt (1 - Y t ^ 2))
      (-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
        + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3)) s := by
    convert hu using 1
    have hs : 0 < Real.sqrt (1 - Y s ^ 2) := Real.sqrt_pos.mpr (hsq s)
    field_simp
    ring
  have hKY : HasDerivAt (fun t => K t - Y t) (Kd s - yp s) s := (hK s).sub (hY s)
  have hKdyp : HasDerivAt (fun t => Kd t - yp t) (Kdd s - ypp s) s :=
    (hKd s).sub (hyp s)
  have hprod1 : HasDerivAt
      (fun t => (-(Y t * yp t) / Real.sqrt (1 - Y t ^ 2)) * (K t - Y t))
      ((-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
          + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3)) * (K s - Y s)
        + (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kd s - yp s)) s :=
    hu'.mul hKY
  have hprod2 : HasDerivAt
      (fun t => Real.sqrt (1 - Y t ^ 2) * (Kd t - yp t))
      ((-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kd s - yp s)
        + Real.sqrt (1 - Y s ^ 2) * (Kdd s - ypp s)) s :=
    (hc s).mul hKdyp
  have hsum : HasDerivAt
      (fun t => (-(Y t * yp t) / Real.sqrt (1 - Y t ^ 2)) * (K t - Y t)
        + Real.sqrt (1 - Y t ^ 2) * (Kd t - yp t))
      (((-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
            + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3)) * (K s - Y s)
          + (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kd s - yp s))
        + ((-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kd s - yp s)
          + Real.sqrt (1 - Y s ^ 2) * (Kdd s - ypp s))) s := hprod1.add hprod2
  have hcongr : (fun t => (-(Y t * yp t) / Real.sqrt (1 - Y t ^ 2)) * (K t - Y t)
      + Real.sqrt (1 - Y t ^ 2) * (Kd t - yp t)) = ypp := by
    funext r; exact (hform r).symm
  rw [hcongr] at hsum
  convert hsum using 1
  ring

/-- `iteratedDeriv 3` in terms of first- and second-derivative witnesses. -/
theorem iteratedDeriv_three_eq {g yp ypp : ℝ → ℝ}
    (h1 : ∀ s, HasDerivAt g (yp s) s) (h2 : ∀ s, HasDerivAt yp (ypp s) s)
    (s : ℝ) : iteratedDeriv 3 g s = deriv ypp s := by
  have hd1 : deriv g = yp := funext fun r => (h1 r).deriv
  have hd2 : deriv yp = ypp := funext fun r => (h2 r).deriv
  have h2g : iteratedDeriv 2 g = ypp := by
    funext r
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd1,
      hd2]
  rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, h2g]

/-- **The order-three relative pulse bound**, in the form the hypothesis
`hrelj` of `data_of_interior` takes. -/
theorem rel_pulse_three_of_identity {f theta x yp ypp Kd Kdd : ℝ → ℝ}
    {s0 b Ch D1 D2 E1 E2 : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)))
    (hsup : ∀ s, pulseField f (theta (x s)) ≤ b)
    (hKnn : ∀ s, 0 ≤ curvField f (theta (s + s0)))
    (hform : ∀ r, ypp r
      = (-(pulseField f (theta (x r)) * yp r)
          / Real.sqrt (1 - pulseField f (theta (x r)) ^ 2))
        * (curvField f (theta (r + s0)) - pulseField f (theta (x r)))
        + Real.sqrt (1 - pulseField f (theta (x r)) ^ 2) * (Kd r - yp r))
    (hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s)
    (hypd : ∀ s, HasDerivAt yp (ypp s) s)
    (hKd1 : ∀ s, HasDerivAt (fun r => curvField f (theta (r + s0))) (Kd s) s)
    (hKd2 : ∀ s, HasDerivAt Kd (Kdd s) s)
    (hypb : ∀ s, |yp s| ≤ D1 * pulseField f (theta (x s)))
    (hyppb : ∀ s, |ypp s| ≤ D2 * pulseField f (theta (x s)))
    (hKdb : ∀ s, |Kd s| ≤ E1 * curvField f (theta (s + s0)))
    (hKddb : ∀ s, |Kdd s| ≤ E2 * curvField f (theta (s + s0)))
    (hharn : ∀ s, curvField f (theta (s + s0))
      ≤ Ch * (pulseField f (theta (x s)) / Real.sqrt (1 - b ^ 2))) :
    ∀ s, |iteratedDeriv 3 (fun r => pulseField f (theta (x r))) s|
      ≤ (b ^ 2 * (D1 ^ 2 + D2) * (Ch / Real.sqrt (1 - b ^ 2) + 1)
            / Real.sqrt (1 - b ^ 2)
          + b ^ 4 * D1 ^ 2 * (Ch / Real.sqrt (1 - b ^ 2) + 1)
            / Real.sqrt (1 - b ^ 2) ^ 3
          + 2 * b ^ 2 * D1 * (E1 * Ch / Real.sqrt (1 - b ^ 2) + D1)
            / Real.sqrt (1 - b ^ 2)
          + E2 * Ch / Real.sqrt (1 - b ^ 2) + D2)
        * pulseField f (theta (x s)) := by
  intro s
  have hsq : ∀ r, (0:ℝ) < 1 - pulseField f (theta (x r)) ^ 2 := by
    intro r
    have h1 := hy0 r
    have h2 := hsup r
    nlinarith
  rw [iteratedDeriv_three_eq hYd hypd s]
  have hd := hasDerivAt_ypp_of_solved (Y := fun r => pulseField f (theta (x r)))
    (yp := yp) (ypp := ypp) (K := fun r => curvField f (theta (r + s0)))
    (Kd := Kd) (Kdd := Kdd) hYd hypd hKd1 hKd2 hsq hform (s := s)
  rw [hd.deriv]
  exact rel_three_expr_bound hb0 hb1 hCh hD1 hD2 hE1 hE2 (hy0 s) (hsup s)
    (hKnn s) (hypb s) (hyppb s) (hKdb s) (hKddb s) (hharn s)

end HairpinRelative
