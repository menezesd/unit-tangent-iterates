import UnitTangentIterates.PulseRelativeFromIdentity

/-!
# The order-two relative pulse bound

Continuing the paper's route (`PulseRelativeFromIdentity`), this file takes the
next step of the induction of `lem:pulse`.  Solving the translator curvature
identity gave

```
  y' = √(1−y²)·(K_*(s+s₀) − y).
```

Differentiating once more and using the order-one bounds together with the
bounded-shift Harnack comparison gives `|y''| ≤ D₂ y`, with `D₂` explicit.

As at order one, **no derivative of the profile appears**.  What the step
consumes is: the order-one pulse bound `|y'| ≤ D₁ y`, the order-one curvature
bound `|K_*'| ≤ E₁ K_*` (which `relK_of_pulse_deriv_bound` supplies from the
order-one pulse bound), the Harnack comparison, and `sup y ≤ b < 1`.

That is the shape of every later step too: order `j` pulse and curvature bounds
feed order `j+1`.  Orders three and four are the same computation carried
further.
-/

noncomputable section

open Set Real HairpinRelative

namespace HairpinRelative

/-- Differentiating the solved identity `y' = √(1−y²)(K−y)`. -/
theorem hasDerivAt_yp_of_solved {Y K yp Kd : ℝ → ℝ} {s : ℝ}
    (hY : HasDerivAt Y (yp s) s) (hK : HasDerivAt K (Kd s) s)
    (hsq : (0:ℝ) < 1 - Y s ^ 2)
    (hyp : ∀ r, yp r = Real.sqrt (1 - Y r ^ 2) * (K r - Y r)) :
    HasDerivAt yp
      ((-(Y s * yp s) / Real.sqrt (1 - Y s ^ 2)) * (K s - Y s)
        + Real.sqrt (1 - Y s ^ 2) * (Kd s - yp s)) s := by
  have hs : 0 < Real.sqrt (1 - Y s ^ 2) := Real.sqrt_pos.mpr hsq
  have hin : HasDerivAt (fun r => 1 - Y r ^ 2) (-(2 * Y s * yp s)) s := by
    simpa using ((hY.pow 2).const_sub 1)
  have hsqrt : HasDerivAt (fun r => Real.sqrt (1 - Y r ^ 2))
      (-(2 * Y s * yp s) / (2 * Real.sqrt (1 - Y s ^ 2))) s := hin.sqrt hsq.ne'
  have hdiff : HasDerivAt (fun r => K r - Y r) (Kd s - yp s) s := hK.sub hY
  have hmul : HasDerivAt (fun r => Real.sqrt (1 - Y r ^ 2) * (K r - Y r))
      ((-(2 * Y s * yp s) / (2 * Real.sqrt (1 - Y s ^ 2))) * (K s - Y s)
        + Real.sqrt (1 - Y s ^ 2) * (Kd s - yp s)) s := hsqrt.mul hdiff
  have hcongr : (fun r => Real.sqrt (1 - Y r ^ 2) * (K r - Y r)) = yp := by
    funext r; exact (hyp r).symm
  rw [hcongr] at hmul
  have heq : -(2 * Y s * yp s) / (2 * Real.sqrt (1 - Y s ^ 2))
      = -(Y s * yp s) / Real.sqrt (1 - Y s ^ 2) := by
    field_simp
  rwa [heq] at hmul

/-- The order-two bound, as pure algebra on the differentiated identity. -/
theorem rel_two_expr_bound {y yp K Kd b Ch D1 E1 : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch) (hD1 : 0 ≤ D1) (hE1 : 0 ≤ E1)
    (hy0 : 0 ≤ y) (hyb : y ≤ b) (hKnn : 0 ≤ K)
    (hypb : |yp| ≤ D1 * y) (hKdb : |Kd| ≤ E1 * K)
    (hharn : K ≤ Ch * (y / Real.sqrt (1 - b ^ 2))) :
    |(-(y * yp) / Real.sqrt (1 - y ^ 2)) * (K - y)
        + Real.sqrt (1 - y ^ 2) * (Kd - yp)|
      ≤ (b ^ 2 * D1 * (Ch / Real.sqrt (1 - b ^ 2) + 1) / Real.sqrt (1 - b ^ 2)
          + E1 * Ch / Real.sqrt (1 - b ^ 2) + D1) * y := by
  set S := Real.sqrt (1 - b ^ 2) with hSdef
  have hsb : (0:ℝ) < 1 - b ^ 2 := by nlinarith
  have hS : 0 < S := Real.sqrt_pos.mpr hsb
  have hsq : (0:ℝ) < 1 - y ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.mpr hsq
  have hmono : S ≤ Real.sqrt (1 - y ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have hs1 : Real.sqrt (1 - y ^ 2) ≤ 1 := by
    have h := Real.sqrt_le_sqrt (show 1 - y ^ 2 ≤ 1 by nlinarith)
    simpa using h
  have hypn : 0 ≤ D1 * y := le_trans (abs_nonneg _) hypb
  have hKn : 0 ≤ E1 * K := le_trans (abs_nonneg _) hKdb
  -- bound `K + y`
  have hKy : K - y ≤ (Ch / S + 1) * y := by
    have : Ch * (y / S) = Ch / S * y := by ring
    nlinarith [hharn, hy0]
  have hKy' : -(K - y) ≤ (Ch / S + 1) * y := by
    have hCS : 0 ≤ Ch / S := div_nonneg hCh hS.le
    nlinarith [hKnn, hy0]
  have habsKy : |K - y| ≤ (Ch / S + 1) * y := abs_le.mpr ⟨by linarith, by linarith⟩
  -- first term
  have hT1 : |(-(y * yp) / Real.sqrt (1 - y ^ 2)) * (K - y)|
      ≤ b ^ 2 * D1 * (Ch / S + 1) / S * y := by
    rw [abs_mul, abs_div, abs_neg, abs_mul, abs_of_nonneg hy0,
      abs_of_pos hs]
    have h1 : y * |yp| ≤ b * (D1 * y) := by nlinarith [abs_nonneg yp, hypb, hy0, hyb]
    have h2 : y * |yp| / Real.sqrt (1 - y ^ 2) ≤ b * (D1 * y) / S := by
      apply div_le_div₀ (by positivity) h1 hS hmono
    have h3 : (0:ℝ) ≤ y * |yp| / Real.sqrt (1 - y ^ 2) := by positivity
    have h4 : (0:ℝ) ≤ (Ch / S + 1) * y := by
      have : 0 ≤ Ch / S := div_nonneg hCh hS.le
      nlinarith
    calc y * |yp| / Real.sqrt (1 - y ^ 2) * |K - y|
        ≤ (b * (D1 * y) / S) * ((Ch / S + 1) * y) :=
          mul_le_mul h2 habsKy (abs_nonneg _)
            (div_nonneg (mul_nonneg hb0 (mul_nonneg hD1 hy0)) hS.le)
      _ ≤ b ^ 2 * D1 * (Ch / S + 1) / S * y := by
          have hC : (0:ℝ) ≤ Ch / S := div_nonneg hCh hS.le
          have hk : (0:ℝ) ≤ b * D1 * (Ch / S + 1) / S := by positivity
          have hyy : y * y ≤ b * y := by nlinarith
          have hL : (b * (D1 * y) / S) * ((Ch / S + 1) * y)
              = (b * D1 * (Ch / S + 1) / S) * (y * y) := by field_simp
          have hR : b ^ 2 * D1 * (Ch / S + 1) / S * y
              = (b * D1 * (Ch / S + 1) / S) * (b * y) := by field_simp
          rw [hL, hR]
          exact mul_le_mul_of_nonneg_left hyy hk
  -- second term
  have hT2 : |Real.sqrt (1 - y ^ 2) * (Kd - yp)| ≤ (E1 * Ch / S + D1) * y := by
    rw [abs_mul, abs_of_pos hs]
    have h1 : |Kd - yp| ≤ E1 * K + D1 * y :=
      le_trans (abs_sub _ _) (add_le_add hKdb hypb)
    have h2 : E1 * K ≤ E1 * (Ch / S * y) := by
      have : Ch * (y / S) = Ch / S * y := by ring
      nlinarith [hharn, hE1]
    have h3 : |Kd - yp| ≤ (E1 * Ch / S + D1) * y := by
      have : E1 * (Ch / S * y) = E1 * Ch / S * y := by ring
      nlinarith [h1, h2]
    calc Real.sqrt (1 - y ^ 2) * |Kd - yp| ≤ 1 * |Kd - yp| :=
          mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
      _ = |Kd - yp| := one_mul _
      _ ≤ (E1 * Ch / S + D1) * y := h3
  calc |(-(y * yp) / Real.sqrt (1 - y ^ 2)) * (K - y)
          + Real.sqrt (1 - y ^ 2) * (Kd - yp)|
      ≤ _ + _ := abs_add_le _ _
    _ ≤ b ^ 2 * D1 * (Ch / S + 1) / S * y + (E1 * Ch / S + D1) * y :=
        add_le_add hT1 hT2
    _ = _ := by ring

/-- **The order-two relative pulse bound.**  `D₂` is explicit in the order-one
constants, the Harnack constant, and the uniform bound `b`. -/
theorem rel_pulse_two_of_identity {f theta x yp Kd : ℝ → ℝ} {s0 b Ch D1 E1 : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch) (hD1 : 0 ≤ D1) (hE1 : 0 ≤ E1)
    (hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)))
    (hsup : ∀ s, pulseField f (theta (x s)) ≤ b)
    (hKnn : ∀ s, 0 ≤ curvField f (theta (s + s0)))
    (hyp : ∀ r, yp r = Real.sqrt (1 - pulseField f (theta (x r)) ^ 2)
      * (curvField f (theta (r + s0)) - pulseField f (theta (x r))))
    (hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s)
    (hKdd : ∀ s, HasDerivAt (fun r => curvField f (theta (r + s0))) (Kd s) s)
    (hypb : ∀ s, |yp s| ≤ D1 * pulseField f (theta (x s)))
    (hKdb : ∀ s, |Kd s| ≤ E1 * curvField f (theta (s + s0)))
    (hharn : ∀ s, curvField f (theta (s + s0))
      ≤ Ch * (pulseField f (theta (x s)) / Real.sqrt (1 - b ^ 2))) :
    ∀ s, |deriv yp s| ≤
      (b ^ 2 * D1 * (Ch / Real.sqrt (1 - b ^ 2) + 1) / Real.sqrt (1 - b ^ 2)
        + E1 * Ch / Real.sqrt (1 - b ^ 2) + D1) * pulseField f (theta (x s)) := by
  intro s
  have hsq : (0:ℝ) < 1 - pulseField f (theta (x s)) ^ 2 := by
    have h1 := hy0 s
    have h2 := hsup s
    nlinarith
  have hd := hasDerivAt_yp_of_solved (hYd s) (hKdd s) hsq hyp
  rw [hd.deriv]
  exact rel_two_expr_bound hb0 hb1 hCh hD1 hE1 (hy0 s) (hsup s) (hKnn s)
    (hypb s) (hKdb s) (hharn s)

/-- `iteratedDeriv 2` in terms of a first-derivative witness. -/
theorem iteratedDeriv_two_eq {g yp : ℝ → ℝ}
    (h : ∀ s, HasDerivAt g (yp s) s) (s : ℝ) :
    iteratedDeriv 2 g s = deriv yp s := by
  have hd : deriv g = yp := funext fun r => (h r).deriv
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]

/-- **The relative pulse bounds at every order `j ≤ 2`, on the paper's route.**
This is the `j ≤ 2` fragment of the hypothesis `hrelj` that `data_of_interior`
consumes, established with no bound on any derivative of the profile. -/
theorem rel_pulse_le_two {f theta x yp Kd : ℝ → ℝ} {s0 b Ch D1 E1 : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1) (hCh : 0 ≤ Ch) (hD1 : 0 ≤ D1) (hE1 : 0 ≤ E1)
    (hy0 : ∀ s, 0 ≤ pulseField f (theta (x s)))
    (hsup : ∀ s, pulseField f (theta (x s)) ≤ b)
    (hKnn : ∀ s, 0 ≤ curvField f (theta (s + s0)))
    (hyp : ∀ r, yp r = Real.sqrt (1 - pulseField f (theta (x r)) ^ 2)
      * (curvField f (theta (r + s0)) - pulseField f (theta (x r))))
    (hYd : ∀ s, HasDerivAt (fun r => pulseField f (theta (x r))) (yp s) s)
    (hKdd : ∀ s, HasDerivAt (fun r => curvField f (theta (r + s0))) (Kd s) s)
    (hypb : ∀ s, |yp s| ≤ D1 * pulseField f (theta (x s)))
    (hKdb : ∀ s, |Kd s| ≤ E1 * curvField f (theta (s + s0)))
    (hharn : ∀ s, curvField f (theta (s + s0))
      ≤ Ch * (pulseField f (theta (x s)) / Real.sqrt (1 - b ^ 2))) :
    ∀ j ≤ 2, ∀ s,
      |iteratedDeriv j (fun r => pulseField f (theta (x r))) s|
        ≤ (if j = 0 then 1 else if j = 1 then D1 else
            b ^ 2 * D1 * (Ch / Real.sqrt (1 - b ^ 2) + 1) / Real.sqrt (1 - b ^ 2)
              + E1 * Ch / Real.sqrt (1 - b ^ 2) + D1)
          * pulseField f (theta (x s)) := by
  intro j hj s
  interval_cases j
  · simpa [iteratedDeriv_zero, abs_of_nonneg (hy0 s)] using le_refl _
  · have hd : deriv (fun r => pulseField f (theta (x r))) = yp :=
      funext fun r => (hYd r).deriv
    simpa [iteratedDeriv_one, hd] using hypb s
  · rw [iteratedDeriv_two_eq hYd s]
    simpa using rel_pulse_two_of_identity hb0 hb1 hCh hD1 hE1 hy0 hsup hKnn hyp
      hYd hKdd hypb hKdb hharn s

end HairpinRelative
