import UnitTangentIterates.PulseRelativeOrderThree

/-!
# The order-four relative pulse bound

The last step of the induction of `lem:pulse` that the development consumes
(`Data.relative` is bounded at `j ≤ 4`).  Differentiating the order-three
expression once more gives the Leibniz pattern

```
  y'''' = u''(K_* − y) + 3u'(K_*' − y') + 3u(K_*'' − y'') + c(K_*''' − y'''),
```

where `c = √(1−y²)`, `u = c'`, `u' = −((y')² + y y'')/c − y²(y')²/c³`.  The
binomial coefficients `1, 3, 3, 1` appear because `u = c'`, `u' = c''` and
`u'' = c'''`.

Pieces:

* `hasDerivAt_u1` — the derivative `u''` of the order-three coefficient;
* `hasDerivAt_yppp_of_solved` — the assembly above;
* `abs_u1_le`, `abs_u2_le` — the bounds `|u'| ≤ G₁ y`, `|u''| ≤ G₂ y`;
* `rel_four_expr_bound` — the resulting bound `|y''''| ≤ D₄ y`;
* `iteratedDeriv_four_eq` — the bridge to `iteratedDeriv 4`.

**No derivative of the profile appears at this order either**, exactly as at
orders one to three.  What is consumed is the order-`≤3` pulse bounds, the
order-`≤3` curvature bounds, the bounded-shift Harnack comparison, and
`sup y ≤ b < 1`.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Set Real HairpinRelative

namespace HairpinRelative

/-- The derivative of the order-three coefficient
`u' = −((y'² + y y'')/c + y²y'²/c³)`. -/
theorem hasDerivAt_u1 {Y yp ypp yppp : ℝ → ℝ} {s : ℝ}
    (hY : ∀ r, HasDerivAt Y (yp r) r)
    (hyp : ∀ r, HasDerivAt yp (ypp r) r)
    (hypp : ∀ r, HasDerivAt ypp (yppp r) r)
    (hsq : ∀ r, (0:ℝ) < 1 - Y r ^ 2) :
    HasDerivAt
      (fun t => -((yp t ^ 2 + Y t * ypp t) / Real.sqrt (1 - Y t ^ 2)
        + Y t ^ 2 * yp t ^ 2 / Real.sqrt (1 - Y t ^ 2) ^ 3))
      (-(((3 * yp s * ypp s + Y s * yppp s) * Real.sqrt (1 - Y s ^ 2)
            - (yp s ^ 2 + Y s * ypp s)
              * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)))
          / Real.sqrt (1 - Y s ^ 2) ^ 2
        + ((2 * Y s * yp s ^ 3 + 2 * Y s ^ 2 * (yp s * ypp s))
              * Real.sqrt (1 - Y s ^ 2) ^ 3
            - Y s ^ 2 * yp s ^ 2
              * (3 * Real.sqrt (1 - Y s ^ 2) ^ 2
                * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2))))
          / (Real.sqrt (1 - Y s ^ 2) ^ 3) ^ 2)) s := by
  have hc : ∀ r, HasDerivAt (fun t => Real.sqrt (1 - Y t ^ 2))
      (-(Y r * yp r) / Real.sqrt (1 - Y r ^ 2)) r := by
    intro r
    have hin : HasDerivAt (fun t => 1 - Y t ^ 2) (-(2 * Y r * yp r)) r := by
      simpa using (((hY r).pow 2).const_sub 1)
    have h := hin.sqrt (hsq r).ne'
    have hs : 0 < Real.sqrt (1 - Y r ^ 2) := Real.sqrt_pos.mpr (hsq r)
    have heq : -(2 * Y r * yp r) / (2 * Real.sqrt (1 - Y r ^ 2))
        = -(Y r * yp r) / Real.sqrt (1 - Y r ^ 2) := by field_simp
    rwa [heq] at h
  have hs : 0 < Real.sqrt (1 - Y s ^ 2) := Real.sqrt_pos.mpr (hsq s)
  have hP : HasDerivAt (fun t => yp t ^ 2 + Y t * ypp t)
      (3 * yp s * ypp s + Y s * yppp s) s := by
    have h1 : HasDerivAt (fun t => yp t ^ 2) (2 * yp s * ypp s) s := by
      simpa [mul_comm] using (hyp s).pow 2
    have h2 : HasDerivAt (fun t => Y t * ypp t)
        (yp s * ypp s + Y s * yppp s) s := (hY s).mul (hypp s)
    have := h1.add h2
    convert this using 1
    ring
  have hQ : HasDerivAt (fun t => Y t ^ 2 * yp t ^ 2)
      (2 * Y s * yp s ^ 3 + 2 * Y s ^ 2 * (yp s * ypp s)) s := by
    have h1 : HasDerivAt (fun t => Y t ^ 2) (2 * Y s * yp s) s := by
      simpa [mul_comm] using (hY s).pow 2
    have h2 : HasDerivAt (fun t => yp t ^ 2) (2 * yp s * ypp s) s := by
      simpa [mul_comm] using (hyp s).pow 2
    have := h1.mul h2
    convert this using 1
    ring
  have hc3 : HasDerivAt (fun t => Real.sqrt (1 - Y t ^ 2) ^ 3)
      (3 * Real.sqrt (1 - Y s ^ 2) ^ 2
        * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2))) s := by
    simpa [mul_comm] using (hc s).pow 3
  have h1 : HasDerivAt (fun t => (yp t ^ 2 + Y t * ypp t)
      / Real.sqrt (1 - Y t ^ 2))
      (((3 * yp s * ypp s + Y s * yppp s) * Real.sqrt (1 - Y s ^ 2)
        - (yp s ^ 2 + Y s * ypp s) * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)))
        / Real.sqrt (1 - Y s ^ 2) ^ 2) s := hP.div (hc s) hs.ne'
  have h2 : HasDerivAt (fun t => Y t ^ 2 * yp t ^ 2
      / Real.sqrt (1 - Y t ^ 2) ^ 3)
      (((2 * Y s * yp s ^ 3 + 2 * Y s ^ 2 * (yp s * ypp s))
          * Real.sqrt (1 - Y s ^ 2) ^ 3
        - Y s ^ 2 * yp s ^ 2 * (3 * Real.sqrt (1 - Y s ^ 2) ^ 2
          * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2))))
        / (Real.sqrt (1 - Y s ^ 2) ^ 3) ^ 2) s :=
    hQ.div hc3 (by positivity)
  exact (h1.add h2).neg

theorem hasDerivAt_yppp_of_solved
    {Y yp ypp yppp K Kd Kdd Kddd u2 : ℝ → ℝ} {s : ℝ}
    (hY : ∀ r, HasDerivAt Y (yp r) r)
    (hyp : ∀ r, HasDerivAt yp (ypp r) r)
    (hypp : ∀ r, HasDerivAt ypp (yppp r) r)
    (hK : ∀ r, HasDerivAt K (Kd r) r)
    (hKd : ∀ r, HasDerivAt Kd (Kdd r) r)
    (hKdd : ∀ r, HasDerivAt Kdd (Kddd r) r)
    (hsq : ∀ r, (0:ℝ) < 1 - Y r ^ 2)
    (hu2 : ∀ r, HasDerivAt
      (fun t => -((yp t ^ 2 + Y t * ypp t) / Real.sqrt (1 - Y t ^ 2)
        + Y t ^ 2 * yp t ^ 2 / Real.sqrt (1 - Y t ^ 2) ^ 3)) (u2 r) r)
    (hform : ∀ r, yppp r
      = (-((yp r ^ 2 + Y r * ypp r) / Real.sqrt (1 - Y r ^ 2)
          + Y r ^ 2 * yp r ^ 2 / Real.sqrt (1 - Y r ^ 2) ^ 3)) * (K r - Y r)
        + 2 * (-(Y r * yp r) / Real.sqrt (1 - Y r ^ 2)) * (Kd r - yp r)
        + Real.sqrt (1 - Y r ^ 2) * (Kdd r - ypp r)) :
    HasDerivAt yppp
      (u2 s * (K s - Y s)
        + 3 * (-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
            + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3))
          * (Kd s - yp s)
        + 3 * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kdd s - ypp s)
        + Real.sqrt (1 - Y s ^ 2) * (Kddd s - yppp s)) s := by
  have hc : ∀ r, HasDerivAt (fun t => Real.sqrt (1 - Y t ^ 2))
      (-(Y r * yp r) / Real.sqrt (1 - Y r ^ 2)) r := by
    intro r
    have hin : HasDerivAt (fun t => 1 - Y t ^ 2) (-(2 * Y r * yp r)) r := by
      simpa using (((hY r).pow 2).const_sub 1)
    have h := hin.sqrt (hsq r).ne'
    have hs : 0 < Real.sqrt (1 - Y r ^ 2) := Real.sqrt_pos.mpr (hsq r)
    have heq : -(2 * Y r * yp r) / (2 * Real.sqrt (1 - Y r ^ 2))
        = -(Y r * yp r) / Real.sqrt (1 - Y r ^ 2) := by field_simp
    rwa [heq] at h
  -- the derivative of `w = c'`
  have hw : ∀ r, HasDerivAt (fun t => -(Y t * yp t) / Real.sqrt (1 - Y t ^ 2))
      (-((yp r ^ 2 + Y r * ypp r) / Real.sqrt (1 - Y r ^ 2)
        + Y r ^ 2 * yp r ^ 2 / Real.sqrt (1 - Y r ^ 2) ^ 3)) r := by
    intro r
    have hs : 0 < Real.sqrt (1 - Y r ^ 2) := Real.sqrt_pos.mpr (hsq r)
    have hnum : HasDerivAt (fun t => -(Y t * yp t))
        (-(yp r * yp r + Y r * ypp r)) r := by
      simpa using (((hY r).mul (hyp r)).neg)
    have hd := hnum.div (hc r) hs.ne'
    convert hd using 1
    field_simp
    try ring
  have hA : HasDerivAt (fun t => (-((yp t ^ 2 + Y t * ypp t)
        / Real.sqrt (1 - Y t ^ 2)
        + Y t ^ 2 * yp t ^ 2 / Real.sqrt (1 - Y t ^ 2) ^ 3)) * (K t - Y t))
      (u2 s * (K s - Y s)
        + (-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
            + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3))
          * (Kd s - yp s)) s :=
    (hu2 s).mul ((hK s).sub (hY s))
  have hB : HasDerivAt (fun t => 2 * (-(Y t * yp t) / Real.sqrt (1 - Y t ^ 2))
        * (Kd t - yp t))
      (2 * (-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
            + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3))
          * (Kd s - yp s)
        + 2 * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kdd s - ypp s)) s := by
    have h := ((hw s).const_mul (2:ℝ)).mul ((hKd s).sub (hyp s))
    convert h using 1
    try ring
  have hC : HasDerivAt (fun t => Real.sqrt (1 - Y t ^ 2) * (Kdd t - ypp t))
      ((-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kdd s - ypp s)
        + Real.sqrt (1 - Y s ^ 2) * (Kddd s - yppp s)) s :=
    (hc s).mul ((hKdd s).sub (hypp s))
  have hsum : HasDerivAt
      (fun t => (-((yp t ^ 2 + Y t * ypp t) / Real.sqrt (1 - Y t ^ 2)
          + Y t ^ 2 * yp t ^ 2 / Real.sqrt (1 - Y t ^ 2) ^ 3)) * (K t - Y t)
        + 2 * (-(Y t * yp t) / Real.sqrt (1 - Y t ^ 2)) * (Kd t - yp t)
        + Real.sqrt (1 - Y t ^ 2) * (Kdd t - ypp t))
      ((u2 s * (K s - Y s)
          + (-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
              + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3))
            * (Kd s - yp s))
        + (2 * (-((yp s ^ 2 + Y s * ypp s) / Real.sqrt (1 - Y s ^ 2)
              + Y s ^ 2 * yp s ^ 2 / Real.sqrt (1 - Y s ^ 2) ^ 3))
            * (Kd s - yp s)
          + 2 * (-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kdd s - ypp s))
        + ((-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (Kdd s - ypp s)
          + Real.sqrt (1 - Y s ^ 2) * (Kddd s - yppp s))) s := (hA.add hB).add hC
  have hcongr : (fun t => (-((yp t ^ 2 + Y t * ypp t) / Real.sqrt (1 - Y t ^ 2)
        + Y t ^ 2 * yp t ^ 2 / Real.sqrt (1 - Y t ^ 2) ^ 3)) * (K t - Y t)
      + 2 * (-(Y t * yp t) / Real.sqrt (1 - Y t ^ 2)) * (Kd t - yp t)
      + Real.sqrt (1 - Y t ^ 2) * (Kdd t - ypp t)) = yppp := by
    funext r; exact (hform r).symm
  rw [hcongr] at hsum
  convert hsum using 1
  try ring

theorem rel_four_expr_bound
    {Y yp ypp yppp K Kd Kdd Kddd u1 u2 b Ch D1 D2 D3 E1 E2 E3 G1 G2 : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3)
    (hG1n : 0 ≤ G1) (hG2n : 0 ≤ G2)
    (hY0 : 0 ≤ Y) (hYb : Y ≤ b) (hKnn : 0 ≤ K)
    (hypb : |yp| ≤ D1 * Y) (hyppb : |ypp| ≤ D2 * Y) (hypppb : |yppp| ≤ D3 * Y)
    (hKdb : |Kd| ≤ E1 * K) (hKddb : |Kdd| ≤ E2 * K) (hKdddb : |Kddd| ≤ E3 * K)
    (hu1b : |u1| ≤ G1 * Y) (hu2b : |u2| ≤ G2 * Y)
    (hharn : K ≤ Ch * (Y / Real.sqrt (1 - b ^ 2))) :
    |u2 * (K - Y) + 3 * u1 * (Kd - yp)
      + 3 * (-(Y * yp) / Real.sqrt (1 - Y ^ 2)) * (Kdd - ypp)
      + Real.sqrt (1 - Y ^ 2) * (Kddd - yppp)|
    ≤ (b * G2 * (Ch / Real.sqrt (1 - b ^ 2) + 1)
        + 3 * b * G1 * (E1 * Ch / Real.sqrt (1 - b ^ 2) + D1)
        + 3 * b ^ 2 * D1 * (E2 * Ch / Real.sqrt (1 - b ^ 2) + D2)
          / Real.sqrt (1 - b ^ 2)
        + E3 * Ch / Real.sqrt (1 - b ^ 2) + D3) * Y := by
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
  -- the three difference bounds
  have hKY : |K - Y| ≤ (Ch / S + 1) * Y := by
    have h : Ch * (Y / S) = Ch / S * Y := by ring
    rw [abs_le]; constructor <;> nlinarith [hharn, hY0, hKnn]
  have hd1 : |Kd - yp| ≤ (E1 * Ch / S + D1) * Y := by
    have h1 : |Kd - yp| ≤ E1 * K + D1 * Y :=
      le_trans (abs_sub _ _) (add_le_add hKdb hypb)
    have h2 : E1 * K ≤ E1 * (Ch / S * Y) := by
      have h : Ch * (Y / S) = Ch / S * Y := by ring
      nlinarith [hharn, hE1]
    have h3 : E1 * (Ch / S * Y) = E1 * Ch / S * Y := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hd2 : |Kdd - ypp| ≤ (E2 * Ch / S + D2) * Y := by
    have h1 : |Kdd - ypp| ≤ E2 * K + D2 * Y :=
      le_trans (abs_sub _ _) (add_le_add hKddb hyppb)
    have h2 : E2 * K ≤ E2 * (Ch / S * Y) := by
      have h : Ch * (Y / S) = Ch / S * Y := by ring
      nlinarith [hharn, hE2]
    have h3 : E2 * (Ch / S * Y) = E2 * Ch / S * Y := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hd3 : |Kddd - yppp| ≤ (E3 * Ch / S + D3) * Y := by
    have h1 : |Kddd - yppp| ≤ E3 * K + D3 * Y :=
      le_trans (abs_sub _ _) (add_le_add hKdddb hypppb)
    have h2 : E3 * K ≤ E3 * (Ch / S * Y) := by
      have h : Ch * (Y / S) = Ch / S * Y := by ring
      nlinarith [hharn, hE3]
    have h3 : E3 * (Ch / S * Y) = E3 * Ch / S * Y := by ring
    linarith [h1, h2, h3.le, h3.ge]
  have hG1 : 0 ≤ G1 * Y := le_trans (abs_nonneg _) hu1b
  have hG2 : 0 ≤ G2 * Y := le_trans (abs_nonneg _) hu2b
  have hYY : Y * Y ≤ b * Y := by nlinarith
  -- term 1
  have hT1 : |u2 * (K - Y)| ≤ b * G2 * (Ch / S + 1) * Y := by
    rw [abs_mul]
    refine le_trans (mul_le_mul hu2b hKY (abs_nonneg _) hG2) ?_
    have he : G2 * Y * ((Ch / S + 1) * Y) = G2 * (Ch / S + 1) * (Y * Y) := by ring
    rw [he]
    have hk : (0:ℝ) ≤ G2 * (Ch / S + 1) := by nlinarith [hCS, hG2n]
    refine le_trans (mul_le_mul_of_nonneg_left hYY hk) ?_
    apply le_of_eq; ring
  -- term 2
  have hT2 : |3 * u1 * (Kd - yp)| ≤ 3 * b * G1 * (E1 * Ch / S + D1) * Y := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (3:ℝ))]
    have hk : (0:ℝ) ≤ G1 * (E1 * Ch / S + D1) := by
      have hE : (0:ℝ) ≤ E1 * Ch / S := by positivity
      nlinarith [hG1n, hD1]
    have hstep : 3 * |u1| * |Kd - yp|
        ≤ 3 * (G1 * Y) * ((E1 * Ch / S + D1) * Y) := by
      refine mul_le_mul ?_ hd1 (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hu1b (by norm_num)
    refine le_trans hstep ?_
    have he : (3:ℝ) * (G1 * Y) * ((E1 * Ch / S + D1) * Y)
        = 3 * (G1 * (E1 * Ch / S + D1)) * (Y * Y) := by ring
    rw [he]
    refine le_trans (mul_le_mul_of_nonneg_left hYY (by positivity)) ?_
    apply le_of_eq; ring
  -- term 3
  have hT3 : |3 * (-(Y * yp) / c) * (Kdd - ypp)|
      ≤ 3 * b ^ 2 * D1 * (E2 * Ch / S + D2) / S * Y := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (3:ℝ)),
      abs_div, abs_neg, abs_mul, abs_of_nonneg hY0, abs_of_pos hc]
    have h1 : Y * |yp| / c ≤ b * (D1 * Y) / S := by
      refine div_le_div₀ (by positivity) ?_ hS hSc
      nlinarith [hypb, abs_nonneg yp, hY0, hYb]
    have h2 : (0:ℝ) ≤ (E2 * Ch / S + D2) * Y := by
      have : (0:ℝ) ≤ E2 * Ch / S := by positivity
      nlinarith [hY0, hD2]
    have hstep : 3 * (Y * |yp| / c) * |Kdd - ypp|
        ≤ 3 * (b * (D1 * Y) / S) * ((E2 * Ch / S + D2) * Y) := by
      refine mul_le_mul ?_ hd2 (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    refine le_trans hstep ?_
    have he : (3:ℝ) * (b * (D1 * Y) / S) * ((E2 * Ch / S + D2) * Y)
        = 3 * b * D1 * (E2 * Ch / S + D2) / S * (Y * Y) := by field_simp
    rw [he]
    refine le_trans (mul_le_mul_of_nonneg_left hYY (by positivity)) ?_
    apply le_of_eq; field_simp
  -- term 4
  have hT4 : |c * (Kddd - yppp)| ≤ (E3 * Ch / S + D3) * Y := by
    rw [abs_mul, abs_of_pos hc]
    calc c * |Kddd - yppp| ≤ 1 * |Kddd - yppp| :=
          mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
      _ = |Kddd - yppp| := one_mul _
      _ ≤ (E3 * Ch / S + D3) * Y := hd3
  calc |u2 * (K - Y) + 3 * u1 * (Kd - yp)
        + 3 * (-(Y * yp) / c) * (Kdd - ypp) + c * (Kddd - yppp)|
      ≤ |u2 * (K - Y) + 3 * u1 * (Kd - yp)
          + 3 * (-(Y * yp) / c) * (Kdd - ypp)| + |c * (Kddd - yppp)| :=
        abs_add_le _ _
    _ ≤ (|u2 * (K - Y) + 3 * u1 * (Kd - yp)|
          + |3 * (-(Y * yp) / c) * (Kdd - ypp)|) + |c * (Kddd - yppp)| :=
        add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ ((|u2 * (K - Y)| + |3 * u1 * (Kd - yp)|)
          + |3 * (-(Y * yp) / c) * (Kdd - ypp)|) + |c * (Kddd - yppp)| :=
        add_le_add (add_le_add (abs_add_le _ _) (le_refl _)) (le_refl _)
    _ ≤ _ := by
        refine le_trans (add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4) ?_
        apply le_of_eq; ring

theorem abs_u2_le {Y yp ypp yppp b S p0 p1 q0 q1 w0 : ℝ}
    (hS : 0 < S) (hSc : S ≤ Real.sqrt (1 - Y ^ 2))
    (hc1 : Real.sqrt (1 - Y ^ 2) ≤ 1) (hcpos : 0 < Real.sqrt (1 - Y ^ 2))
    (hY0 : 0 ≤ Y) (hYb : Y ≤ b) (hb0 : 0 ≤ b)
    (hp0 : 0 ≤ p0) (hq0 : 0 ≤ q0) (hw0 : 0 ≤ w0)
    (hP : |yp ^ 2 + Y * ypp| ≤ p0 * Y)
    (hPd : |3 * yp * ypp + Y * yppp| ≤ p1 * Y)
    (hQ : |Y ^ 2 * yp ^ 2| ≤ q0 * Y)
    (hQd : |2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)| ≤ q1 * Y)
    (hw : |(-(Y * yp) / Real.sqrt (1 - Y ^ 2))| ≤ w0 * Y) :
    |(-(((3 * yp * ypp + Y * yppp) * Real.sqrt (1 - Y ^ 2)
          - (yp ^ 2 + Y * ypp) * (-(Y * yp) / Real.sqrt (1 - Y ^ 2)))
        / Real.sqrt (1 - Y ^ 2) ^ 2
      + ((2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)) * Real.sqrt (1 - Y ^ 2) ^ 3
          - Y ^ 2 * yp ^ 2 * (3 * Real.sqrt (1 - Y ^ 2) ^ 2
            * (-(Y * yp) / Real.sqrt (1 - Y ^ 2))))
        / (Real.sqrt (1 - Y ^ 2) ^ 3) ^ 2))|
    ≤ ((p1 + p0 * w0 * b) / S ^ 2 + (q1 + 3 * q0 * w0 * b) / S ^ 6) * Y := by
  set c := Real.sqrt (1 - Y ^ 2) with hcdef
  have hc0 : 0 < c := hcpos
  have hS2 : S ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hS.le hSc 2
  have hS6 : S ^ 6 ≤ (c ^ 3) ^ 2 := by
    have h : S ^ 6 ≤ c ^ 6 := pow_le_pow_left₀ hS.le hSc 6
    calc S ^ 6 ≤ c ^ 6 := h
      _ = (c ^ 3) ^ 2 := by ring
  have hwY : (0:ℝ) ≤ w0 * Y := le_trans (abs_nonneg _) hw
  have hYY : Y * Y ≤ b * Y := by nlinarith
  -- numerator of the first quotient
  have hN1 : |(3 * yp * ypp + Y * yppp) * c - (yp ^ 2 + Y * ypp)
      * (-(Y * yp) / c)| ≤ (p1 + p0 * w0 * b) * Y := by
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul, abs_mul, abs_of_pos hc0]
    have h1 : |3 * yp * ypp + Y * yppp| * c ≤ p1 * Y := by
      calc |3 * yp * ypp + Y * yppp| * c ≤ |3 * yp * ypp + Y * yppp| * 1 :=
            mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
        _ = |3 * yp * ypp + Y * yppp| := mul_one _
        _ ≤ p1 * Y := hPd
    have h2 : |yp ^ 2 + Y * ypp| * |(-(Y * yp) / c)| ≤ p0 * w0 * b * Y := by
      refine le_trans (mul_le_mul hP hw (abs_nonneg _) (by positivity)) ?_
      have he : p0 * Y * (w0 * Y) = p0 * w0 * (Y * Y) := by ring
      rw [he]
      refine le_trans (mul_le_mul_of_nonneg_left hYY (by positivity)) ?_
      apply le_of_eq; ring
    linarith
  -- numerator of the second quotient
  have hN2 : |(2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)) * c ^ 3
      - Y ^ 2 * yp ^ 2 * (3 * c ^ 2 * (-(Y * yp) / c))|
      ≤ (q1 + 3 * q0 * w0 * b) * Y := by
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < c ^ 3)]
    have hc3 : c ^ 3 ≤ 1 := by nlinarith [hc0.le, hc1]
    have h1 : |2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)| * c ^ 3 ≤ q1 * Y := by
      calc |2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)| * c ^ 3
          ≤ |2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)| * 1 :=
            mul_le_mul_of_nonneg_left hc3 (abs_nonneg _)
        _ = |2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)| := mul_one _
        _ ≤ q1 * Y := hQd
    have h2 : |Y ^ 2 * yp ^ 2| * |3 * c ^ 2 * (-(Y * yp) / c)|
        ≤ 3 * q0 * w0 * b * Y := by
      have hin : |3 * c ^ 2 * (-(Y * yp) / c)| ≤ 3 * (w0 * Y) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (3:ℝ)),
          abs_of_nonneg (sq_nonneg c)]
        have hc2 : c ^ 2 ≤ 1 := by nlinarith [hc0.le, hc1]
        calc 3 * c ^ 2 * |(-(Y * yp) / c)| ≤ 3 * 1 * |(-(Y * yp) / c)| := by
              nlinarith [abs_nonneg ((-(Y * yp) / c)), hc2, sq_nonneg c]
          _ = 3 * |(-(Y * yp) / c)| := by ring
          _ ≤ 3 * (w0 * Y) := by linarith [hw]
      refine le_trans (mul_le_mul hQ hin (abs_nonneg _) (by positivity)) ?_
      have he : q0 * Y * (3 * (w0 * Y)) = 3 * q0 * w0 * (Y * Y) := by ring
      rw [he]
      refine le_trans (mul_le_mul_of_nonneg_left hYY (by positivity)) ?_
      apply le_of_eq; ring
    linarith
  rw [abs_neg]
  refine le_trans (abs_add_le _ _) ?_
  have hT1 : |((3 * yp * ypp + Y * yppp) * c - (yp ^ 2 + Y * ypp)
      * (-(Y * yp) / c)) / c ^ 2| ≤ (p1 + p0 * w0 * b) / S ^ 2 * Y := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < c ^ 2)]
    have hnn : (0:ℝ) ≤ (p1 + p0 * w0 * b) * Y := le_trans (abs_nonneg _) hN1
    refine le_trans (div_le_div₀ hnn hN1 (by positivity) hS2) ?_
    apply le_of_eq; field_simp
  have hT2 : |((2 * Y * yp ^ 3 + 2 * Y ^ 2 * (yp * ypp)) * c ^ 3
      - Y ^ 2 * yp ^ 2 * (3 * c ^ 2 * (-(Y * yp) / c))) / (c ^ 3) ^ 2|
      ≤ (q1 + 3 * q0 * w0 * b) / S ^ 6 * Y := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (c ^ 3) ^ 2)]
    have hnn : (0:ℝ) ≤ (q1 + 3 * q0 * w0 * b) * Y := le_trans (abs_nonneg _) hN2
    refine le_trans (div_le_div₀ hnn hN2 (by positivity) hS6) ?_
    apply le_of_eq; field_simp
  refine le_trans (add_le_add hT1 hT2) ?_
  apply le_of_eq; ring

theorem abs_u1_le {Y yp ypp b S D1 D2 : ℝ}
    (hS : 0 < S) (hSc : S ≤ Real.sqrt (1 - Y ^ 2))
    (hcpos : 0 < Real.sqrt (1 - Y ^ 2))
    (hY0 : 0 ≤ Y) (hYb : Y ≤ b) (hb0 : 0 ≤ b) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) :
    |yp| ≤ D1 * Y → |ypp| ≤ D2 * Y →
    |(-((yp ^ 2 + Y * ypp) / Real.sqrt (1 - Y ^ 2)
      + Y ^ 2 * yp ^ 2 / Real.sqrt (1 - Y ^ 2) ^ 3))|
      ≤ ((D1 ^ 2 + D2) / S + b ^ 2 * D1 ^ 2 / S ^ 3) * b * Y := by
  intro hypb hyppb
  set c := Real.sqrt (1 - Y ^ 2) with hcdef
  have hc0 : 0 < c := hcpos
  have hS3 : S ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hS.le hSc 3
  have hY2 : Y ^ 2 ≤ b ^ 2 := by nlinarith
  have hyp2 : yp ^ 2 ≤ D1 ^ 2 * Y ^ 2 := by
    have h : |yp| ^ 2 ≤ (D1 * Y) ^ 2 := pow_le_pow_left₀ (abs_nonneg yp) hypb 2
    rw [sq_abs] at h
    have he : (D1 * Y) ^ 2 = D1 ^ 2 * Y ^ 2 := by ring
    linarith [h, he.le, he.ge]
  have hYypp : |Y * ypp| ≤ D2 * Y ^ 2 := by
    rw [abs_mul, abs_of_nonneg hY0]
    nlinarith [hyppb, abs_nonneg ypp, hY0]
  have hY3 : Y ^ 2 * Y ≤ b ^ 2 * Y := by nlinarith [hY2, hY0]
  rw [abs_neg]
  have hA : |(yp ^ 2 + Y * ypp) / c + Y ^ 2 * yp ^ 2 / c ^ 3|
      ≤ (D1 ^ 2 + D2) * Y ^ 2 / S + b ^ 2 * D1 ^ 2 * Y ^ 2 / S ^ 3 := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos hc0]
      refine div_le_div₀ (by positivity) ?_ hS hSc
      calc |yp ^ 2 + Y * ypp| ≤ |yp ^ 2| + |Y * ypp| := abs_add_le _ _
        _ ≤ (D1 ^ 2 + D2) * Y ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg yp)]
            nlinarith [hyp2, hYypp]
    · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < c ^ 3)]
      refine div_le_div₀ (by positivity) ?_ (by positivity) hS3
      rw [abs_mul, abs_of_nonneg (sq_nonneg Y), abs_of_nonneg (sq_nonneg yp)]
      nlinarith [hyp2, hY2, sq_nonneg Y, sq_nonneg yp, hD1]
  refine le_trans hA ?_
  have he : (D1 ^ 2 + D2) * Y ^ 2 / S + b ^ 2 * D1 ^ 2 * Y ^ 2 / S ^ 3
      = ((D1 ^ 2 + D2) / S + b ^ 2 * D1 ^ 2 / S ^ 3) * (Y ^ 2 * 1) := by
    field_simp
  rw [he]
  have hk : (0:ℝ) ≤ (D1 ^ 2 + D2) / S + b ^ 2 * D1 ^ 2 / S ^ 3 := by positivity
  have hstep : Y ^ 2 * 1 ≤ b * Y := by nlinarith [hY0, hYb, sq_nonneg Y]
  refine le_trans (mul_le_mul_of_nonneg_left hstep hk) ?_
  apply le_of_eq; ring

theorem iteratedDeriv_four_eq {g yp ypp yppp : ℝ → ℝ}
    (h1 : ∀ s, HasDerivAt g (yp s) s) (h2 : ∀ s, HasDerivAt yp (ypp s) s)
    (h3 : ∀ s, HasDerivAt ypp (yppp s) s) (s : ℝ) :
    iteratedDeriv 4 g s = deriv yppp s := by
  have hd1 : deriv g = yp := funext fun r => (h1 r).deriv
  have hd2 : deriv yp = ypp := funext fun r => (h2 r).deriv
  have hd3 : deriv ypp = yppp := funext fun r => (h3 r).deriv
  have h3g : iteratedDeriv 3 g = yppp := by
    funext r
    rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd1,
      hd2, hd3]
  rw [show (4:ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, h3g]

/-- **The order-four relative pulse bound**, in the form the hypothesis `hrelj`
of `data_of_interior` takes.  The coefficient bounds `G₁`, `G₂` are supplied by
`abs_u1_le` and `abs_u2_le`, and the derivative witness for `u''` by
`hasDerivAt_u1`. -/
theorem rel_pulse_four_of_identity
    {f theta x yp ypp yppp Kd Kdd Kddd u2 : ℝ → ℝ}
    {s0 b Ch D1 D2 D3 E1 E2 E3 G1 G2 : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3)
    (hG1n : 0 ≤ G1) (hG2n : 0 ≤ G2)
    (hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)))
    (hsup : ∀ s, pulseField f (theta (x s)) ≤ b)
    (hKnn : ∀ s, 0 ≤ curvField f (theta (s + s0)))
    (hform : ∀ r, yppp r
      = (-((yp r ^ 2 + pulseField f (theta (x r)) * ypp r)
            / Real.sqrt (1 - pulseField f (theta (x r)) ^ 2)
          + pulseField f (theta (x r)) ^ 2 * yp r ^ 2
            / Real.sqrt (1 - pulseField f (theta (x r)) ^ 2) ^ 3))
        * (curvField f (theta (r + s0)) - pulseField f (theta (x r)))
        + 2 * (-(pulseField f (theta (x r)) * yp r)
            / Real.sqrt (1 - pulseField f (theta (x r)) ^ 2)) * (Kd r - yp r)
        + Real.sqrt (1 - pulseField f (theta (x r)) ^ 2) * (Kdd r - ypp r))
    (hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s)
    (hypd : ∀ s, HasDerivAt yp (ypp s) s)
    (hyppd : ∀ s, HasDerivAt ypp (yppp s) s)
    (hKd1 : ∀ s, HasDerivAt (fun r => curvField f (theta (r + s0))) (Kd s) s)
    (hKd2 : ∀ s, HasDerivAt Kd (Kdd s) s)
    (hKd3 : ∀ s, HasDerivAt Kdd (Kddd s) s)
    (hu2d : ∀ r, HasDerivAt
      (fun t => -((yp t ^ 2 + pulseField f (theta (x t)) * ypp t)
          / Real.sqrt (1 - pulseField f (theta (x t)) ^ 2)
        + pulseField f (theta (x t)) ^ 2 * yp t ^ 2
          / Real.sqrt (1 - pulseField f (theta (x t)) ^ 2) ^ 3)) (u2 r) r)
    (hypb : ∀ s, |yp s| ≤ D1 * pulseField f (theta (x s)))
    (hyppb : ∀ s, |ypp s| ≤ D2 * pulseField f (theta (x s)))
    (hypppb : ∀ s, |yppp s| ≤ D3 * pulseField f (theta (x s)))
    (hKdb : ∀ s, |Kd s| ≤ E1 * curvField f (theta (s + s0)))
    (hKddb : ∀ s, |Kdd s| ≤ E2 * curvField f (theta (s + s0)))
    (hKdddb : ∀ s, |Kddd s| ≤ E3 * curvField f (theta (s + s0)))
    (hG1 : ∀ s, |(-((yp s ^ 2 + pulseField f (theta (x s)) * ypp s)
          / Real.sqrt (1 - pulseField f (theta (x s)) ^ 2)
        + pulseField f (theta (x s)) ^ 2 * yp s ^ 2
          / Real.sqrt (1 - pulseField f (theta (x s)) ^ 2) ^ 3))|
      ≤ G1 * pulseField f (theta (x s)))
    (hG2 : ∀ s, |u2 s| ≤ G2 * pulseField f (theta (x s)))
    (hharn : ∀ s, curvField f (theta (s + s0))
      ≤ Ch * (pulseField f (theta (x s)) / Real.sqrt (1 - b ^ 2))) :
    ∀ s, |iteratedDeriv 4 (fun r => pulseField f (theta (x r))) s|
      ≤ (b * G2 * (Ch / Real.sqrt (1 - b ^ 2) + 1)
          + 3 * b * G1 * (E1 * Ch / Real.sqrt (1 - b ^ 2) + D1)
          + 3 * b ^ 2 * D1 * (E2 * Ch / Real.sqrt (1 - b ^ 2) + D2)
            / Real.sqrt (1 - b ^ 2)
          + E3 * Ch / Real.sqrt (1 - b ^ 2) + D3)
        * pulseField f (theta (x s)) := by
  intro s
  have hsq : ∀ r, (0:ℝ) < 1 - pulseField f (theta (x r)) ^ 2 := by
    intro r
    have h1 := hy0 r
    have h2 := hsup r
    nlinarith
  rw [iteratedDeriv_four_eq hYd hypd hyppd s]
  have hd := hasDerivAt_yppp_of_solved
    (Y := fun r => pulseField f (theta (x r))) (yp := yp) (ypp := ypp)
    (yppp := yppp) (K := fun r => curvField f (theta (r + s0)))
    (Kd := Kd) (Kdd := Kdd) (Kddd := Kddd) (u2 := u2)
    hYd hypd hyppd hKd1 hKd2 hKd3 hsq hu2d hform (s := s)
  rw [hd.deriv]
  exact rel_four_expr_bound hb0 hb1 hCh hD1 hD2 hD3 hE1 hE2 hE3 hG1n hG2n
    (hy0 s) (hsup s) (hKnn s) (hypb s) (hyppb s) (hypppb s) (hKdb s) (hKddb s)
    (hKdddb s) (hG1 s) (hG2 s) (hharn s)

end HairpinRelative
