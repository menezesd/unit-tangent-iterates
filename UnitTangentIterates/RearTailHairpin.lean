import Mathlib
import UnitTangentIterates.PerimeterHairpinPulse
import UnitTangentIterates.MatchingExponential
import UnitTangentIterates.OverlapIntegral
import UnitTangentIterates.HairpinPulseMass
import UnitTangentIterates.FrontPeriodizationHairpin

/-!
# The omitted mass of the matching estimate, in the configuration of a pulse

`MatchingExponential.rear_tail_exp` bounds the *omitted mass* of the theorem
*Curvature-measure matching* of *A Noncircular Oval with Convex Unit-Tangent
Iterates*,

```
  ∫_{-H/2}^{H/2} |c_H ∑_{j≠0} K_*(x_H - jP)| ≤ (2Ce^{αB}/α) e^{-αH/2},
```

once the endpoints of the fundamental interval `[x_H(-H/2), x_H(-H/2) + P]`
are within `B` of `∓H/2`.  Those positional hypotheses are supplied here, for
the rear arclength of the periodized profile of a pulse: with
`Y_H = ∑_m y(· - mH)`, `c_H = √(1 - Y_H²)` and `x_H(t) = ∫₀^t c_H`, the defect

```
  ∫_{-H/2}^{H/2} (1 - c_H) ≤ a ∫_{-H/2}^{H/2} Y_H = a ∫_ℝ y
```

is bounded independently of the period — the first inequality because
`1 - √(1-z²) ≤ z² ≤ a z` for `0 ≤ z ≤ a`, the identity because the translates
of the cell tile the line (`OverlapIntegral.integral_tsum_translates_all`).
Hence `|x_H(t) - t| ≤ B := a ∫_ℝ y` on the cell, which is exactly what the
omitted-mass bound consumes.

For the hairpin of the paper the total mass is `∫_ℝ y = π`
(`HairpinRelative.hairpin_pulse_mass`), so `B = aπ ≤ π`.

Main results:

* `hasDerivAt_rearArclength`, `speed_pos`, `speed_le_one` : the rear arclength
  of the periodized profile;
* `defect_integral_le` : `∫_{-H/2}^{H/2}(1 - c_H) ≤ a ∫_ℝ y`;
* `rear_tail_of_pulse` : the omitted mass for the configuration of a pulse;
* `hairpin_rear_tail` : the omitted mass in the paper's own configuration, the
  pulse and the curvature profile being those of the hairpin.
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

open scoped ContDiff

namespace RearTailPulse

open PerimeterHairpinPulse

/-! ### The periodized profile, its speed and its rear arclength -/

/-- The periodization `Y_H(u) = ∑_m y(u - mH)` of the pulse. -/
def periodize (y : ℝ → ℝ) (H : ℝ) (u : ℝ) : ℝ := ∑' m : ℤ, y (u - m * H)

/-- The speed `c_H = √(1 - Y_H²)` of the rear track. -/
def speed (y : ℝ → ℝ) (H : ℝ) (u : ℝ) : ℝ := Real.sqrt (1 - periodize y H u ^ 2)

/-- The rear arclength `x_H(t) = ∫₀^t c_H`. -/
def rearArclength (y : ℝ → ℝ) (H : ℝ) (t : ℝ) : ℝ := ∫ u in (0:ℝ)..t, speed y H u

variable {y : ℝ → ℝ} {C alpha b H : ℝ}

theorem periodize_nonneg (hy0 : ∀ s, 0 ≤ y s) (u : ℝ) : 0 ≤ periodize y H u :=
  tsum_nonneg fun _ => hy0 _

theorem periodize_le (halpha : 0 < alpha) (hb1 : b < 1)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) (u : ℝ) :
    periodize y H u ≤ (1 + b) / 2 :=
  periodization_le_mid halpha hb1 hy0 hyb hsup hH u

theorem continuous_periodize (halpha : 0 < alpha) (hHpos : 0 < H) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) :
    Continuous (periodize y H) := by
  have habs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  exact FrontPeriodizationIntegral.continuous_tsum_translates (C := C) halpha hHpos hy habs

theorem continuous_speed (halpha : 0 < alpha) (hHpos : 0 < H) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) :
    Continuous (speed y H) := by
  have h := continuous_periodize halpha hHpos hy hy0 hyb
  unfold speed
  fun_prop

theorem speed_pos (halpha : 0 < alpha) (hb1 : b < 1)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) (u : ℝ) :
    0 < speed y H u := by
  have h0 : 0 ≤ periodize y H u := periodize_nonneg hy0 u
  have h1 : periodize y H u ≤ (1 + b) / 2 := periodize_le halpha hb1 hy0 hyb hsup hH u
  have h2 : (1 + b) / 2 < 1 := by linarith
  have : 0 < 1 - periodize y H u ^ 2 := by nlinarith
  exact Real.sqrt_pos.mpr this

theorem speed_le_one (u : ℝ) : speed y H u ≤ 1 := by
  have h : 1 - periodize y H u ^ 2 ≤ 1 := by nlinarith [sq_nonneg (periodize y H u)]
  calc speed y H u ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
    _ = 1 := Real.sqrt_one

theorem hasDerivAt_rearArclength (halpha : 0 < alpha) (hHpos : 0 < H) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) (t : ℝ) :
    HasDerivAt (rearArclength y H) (speed y H t) t :=
  ((continuous_speed halpha hHpos hy hy0 hyb).integral_hasStrictDerivAt (0:ℝ) t).hasDerivAt

/-! ### The defect of the rear arclength over one cell -/

/-- The mass of the periodized profile over one cell is the total mass of the
pulse: the translates of the cell tile the line. -/
theorem integral_periodize_cell (halpha : 0 < alpha) (hHpos : 0 < H) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)) :
    (∫ u in (-(H / 2))..(H / 2), periodize y H u) = ∫ s : ℝ, y s := by
  have hyint : Integrable y := OverlapIntegral.integrable_of_exp_bound halpha hy hy0 hyb
  have h := OverlapIntegral.integral_tsum_translates_all (p := -(H / 2)) (P := H)
    (f := y) hHpos hyint hy0
  have hrw : -(H / 2) + H = H / 2 := by ring
  rw [hrw] at h
  have hle : -(H / 2) ≤ H / 2 := by linarith
  rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo]
  exact h

/-- **The defect of the rear arclength over one cell is bounded by `a ∫_ℝ y`.** -/
theorem defect_integral_le (halpha : 0 < alpha) (hb1 : b < 1) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    (∫ u in (-(H / 2))..(H / 2), (1 - speed y H u))
      ≤ (1 + b) / 2 * ∫ s : ℝ, y s := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hle : -(H / 2) ≤ H / 2 := by linarith
  have hcY := continuous_periodize halpha hHpos hy hy0 hyb
  have hcs := continuous_speed halpha hHpos hy hy0 hyb
  have hpt : ∀ u ∈ uIcc (-(H / 2)) (H / 2),
      1 - speed y H u ≤ (1 + b) / 2 * periodize y H u := by
    intro u _
    have h0 : 0 ≤ periodize y H u := periodize_nonneg hy0 u
    have h1 : periodize y H u ≤ (1 + b) / 2 := periodize_le halpha hb1 hy0 hyb hsup hH u
    have h2 : (1 + b) / 2 < 1 := by linarith
    have hsq : 1 - periodize y H u ^ 2 ≥ 0 := by nlinarith
    have hs : speed y H u ^ 2 = 1 - periodize y H u ^ 2 := Real.sq_sqrt hsq
    have hs0 : 0 ≤ speed y H u := Real.sqrt_nonneg _
    have hs1 : speed y H u ≤ 1 := speed_le_one u
    have hstep : 1 - speed y H u ≤ periodize y H u ^ 2 := by nlinarith
    nlinarith
  have hmono : (∫ u in (-(H / 2))..(H / 2), (1 - speed y H u))
      ≤ ∫ u in (-(H / 2))..(H / 2), (1 + b) / 2 * periodize y H u := by
    refine intervalIntegral.integral_mono_on hle ?_ ?_ (fun u hu => hpt u (by
      rw [uIcc_of_le hle]; exact hu))
    · exact (continuous_const.sub hcs).intervalIntegrable _ _
    · exact (continuous_const.mul hcY).intervalIntegrable _ _
  have hconst : (∫ u in (-(H / 2))..(H / 2), (1 + b) / 2 * periodize y H u)
      = (1 + b) / 2 * ∫ s : ℝ, y s := by
    rw [intervalIntegral.integral_const_mul,
      integral_periodize_cell halpha hHpos hy hy0 hyb]
  linarith [hmono, hconst.le, hconst.ge]

/-! ### The position of the fundamental interval -/

/-- The rear arclength stays below the identity and within the defect of it. -/
theorem rearArclength_le_self (halpha : 0 < alpha) (hb1 : b < 1) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hH : threshold alpha C b ≤ H)
    {t : ℝ} (ht0 : 0 ≤ t) : rearArclength y H t ≤ t := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hcs := continuous_speed halpha hHpos hy hy0 hyb
  have hmono : (∫ u in (0:ℝ)..t, speed y H u) ≤ ∫ u in (0:ℝ)..t, (1:ℝ) := by
    refine intervalIntegral.integral_mono_on ht0 (hcs.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun u _ => speed_le_one u)
  simpa [rearArclength] using hmono

/-- The rear arclength at the right endpoint of the cell is at least `H/2 - B`,
`B` being the defect bound. -/
theorem le_rearArclength_right (halpha : 0 < alpha) (hb1 : b < 1) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    H / 2 - (1 + b) / 2 * (∫ s : ℝ, y s) ≤ rearArclength y H (H / 2) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hcs := continuous_speed halpha hHpos hy hy0 hyb
  have hdef := defect_integral_le halpha hb1 hy hy0 hyb hsup hH
  have hsub : (∫ u in (0:ℝ)..(H / 2), (1 - speed y H u))
      ≤ ∫ u in (-(H / 2))..(H / 2), (1 - speed y H u) := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl ?_
      ((continuous_const.sub hcs).intervalIntegrable _ _)
    filter_upwards with u
    have := speed_le_one (y := y) (H := H) u
    simp only [Pi.zero_apply]
    linarith
  have hsplit : (∫ u in (0:ℝ)..(H / 2), (1 - speed y H u))
      = H / 2 - rearArclength y H (H / 2) := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hcs.intervalIntegrable _ _)]
    simp [rearArclength]
  linarith [hsplit.symm.trans_le (hsub.trans hdef)]

/-- The rear arclength at the left endpoint of the cell is at most `-H/2 + B`. -/
theorem rearArclength_left_le (halpha : 0 < alpha) (hb1 : b < 1) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    rearArclength y H (-(H / 2)) ≤ -(H / 2) + (1 + b) / 2 * (∫ s : ℝ, y s) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hcs := continuous_speed halpha hHpos hy hy0 hyb
  have hdef := defect_integral_le halpha hb1 hy hy0 hyb hsup hH
  have hsub : (∫ u in (-(H / 2))..(0:ℝ), (1 - speed y H u))
      ≤ ∫ u in (-(H / 2))..(H / 2), (1 - speed y H u) := by
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith) ?_
      ((continuous_const.sub hcs).intervalIntegrable _ _)
    filter_upwards with u
    have := speed_le_one (y := y) (H := H) u
    simp only [Pi.zero_apply]
    linarith
  have hsplit : (∫ u in (-(H / 2))..(0:ℝ), (1 - speed y H u))
      = H / 2 + rearArclength y H (-(H / 2)) := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hcs.intervalIntegrable _ _)]
    have hswap : (∫ u in (-(H / 2))..(0:ℝ), speed y H u) = -rearArclength y H (-(H / 2)) := by
      rw [rearArclength, ← intervalIntegral.integral_symm]
    rw [hswap]
    simp
  linarith [hsplit.symm.trans_le (hsub.trans hdef)]

theorem rearArclength_left_nonpos (halpha : 0 < alpha) (hb1 : b < 1) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    rearArclength y H (-(H / 2)) ≤ 0 := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hcs := continuous_speed halpha hHpos hy hy0 hyb
  have hnn : 0 ≤ ∫ u in (-(H / 2))..(0:ℝ), speed y H u := by
    refine intervalIntegral.integral_nonneg (by linarith) (fun u _ => ?_)
    exact (speed_pos halpha hb1 hy0 hyb hsup hH u).le
  have hswap : (∫ u in (-(H / 2))..(0:ℝ), speed y H u) = -rearArclength y H (-(H / 2)) := by
    rw [rearArclength, ← intervalIntegral.integral_symm]
  linarith [hswap ▸ hnn]

theorem rearArclength_right_nonneg (halpha : 0 < alpha) (hb1 : b < 1)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    0 ≤ rearArclength y H (H / 2) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  refine intervalIntegral.integral_nonneg (by linarith) (fun u _ => ?_)
  exact (speed_pos halpha hb1 hy0 hyb hsup hH u).le

/-! ### The omitted mass for the configuration of a pulse -/

/-- **The omitted mass is exponentially small, in the configuration of a
pulse.**  With `Y_H` the periodization of the pulse, `c_H = √(1 - Y_H²)` its
speed, `x_H` its rear arclength and `P` the length of the fundamental interval,

`∫_{-H/2}^{H/2} |c_H ∑_{j≠0} K_*(x_H - jP)| ≤ rearTailConst CK α B · e^{-αH/2}`,
`B = a ∫_ℝ y`,

for any nonnegative integrable curvature profile `K_*` with
`|K_*| ≤ CK e^{-α|·|}`. -/
theorem rear_tail_of_pulse {Kstar : ℝ → ℝ} {CK : ℝ}
    (halpha : 0 < alpha) (hb1 : b < 1) (hy : Continuous y)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|)) :
    (∫ s in (-(H / 2))..(H / 2),
        |speed y H s * ∑' j : {j : ℤ // j ≠ 0},
          Kstar (rearArclength y H s
            - (j : ℤ) * (rearArclength y H (H / 2) - rearArclength y H (-(H / 2))))|)
      ≤ MatchingExponential.rearTailConst CK alpha ((1 + b) / 2 * ∫ s : ℝ, y s)
        * Real.exp (-(alpha / 2 * H)) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  set P : ℝ := rearArclength y H (H / 2) - rearArclength y H (-(H / 2)) with hPdef
  have hleft := rearArclength_left_le halpha hb1 hy hy0 hyb hsup hH
  have hright := le_rearArclength_right halpha hb1 hy hy0 hyb hsup hH
  have hl0 := rearArclength_left_nonpos halpha hb1 hy hy0 hyb hsup hH
  have hr0 := rearArclength_right_nonneg halpha hb1 hy0 hyb hsup hH
  have hcs := continuous_speed halpha hHpos hy hy0 hyb
  have hPpos : 0 < P := by
    have hsplit : (∫ u in (-(H / 2))..(H / 2), speed y H u)
        = rearArclength y H (H / 2) - rearArclength y H (-(H / 2)) := by
      rw [rearArclength, rearArclength,
        ← intervalIntegral.integral_interval_sub_left
          (hcs.intervalIntegrable _ _) (hcs.intervalIntegrable _ _)]
    have hpos : 0 < ∫ u in (-(H / 2))..(H / 2), speed y H u :=
      intervalIntegral.intervalIntegral_pos_of_pos_on
        (hcs.intervalIntegrable _ _) (fun u _ => speed_pos halpha hb1 hy0 hyb hsup hH u)
        (by linarith)
    rw [hsplit] at hpos
    rw [hPdef]
    linarith
  exact MatchingExponential.rear_tail_exp (xH := rearArclength y H) (cH := speed y H)
    (Kstar := Kstar) (H := H) (P := P) (C := CK) (alpha := alpha)
    (B := (1 + b) / 2 * ∫ s : ℝ, y s)
    hHpos.le (hasDerivAt_rearArclength halpha hHpos hy hy0 hyb)
    (fun t => speed_pos halpha hb1 hy0 hyb hsup hH t)
    (by rw [hPdef]; ring) hPpos halpha hKint hK0 hKbd hl0
    (by rw [hPdef]; linarith) hleft (by rw [hPdef]; linarith)

end RearTailPulse

/-! ### The omitted mass for the hairpin of the paper -/

namespace RearTailHairpin

open HairpinRelative PerimeterHairpinPulse RearTailPulse

/-- **The omitted mass of the matching estimate, in the paper's own
configuration.**  For a profile `f` smooth and positive on the line, let `y` be
the steering pulse of its hairpin and `K_*` the curvature of the hairpin in its
own arclength.  With the rear arclength `x_H` of the periodized pulse and the
fundamental interval of length `P = x_H(H/2) - x_H(-H/2)`, the omitted mass
obeys

`∫_{-H/2}^{H/2}|c_H ∑_{j≠0} K_*(x_H - jP)| ≤ rearTailConst CK α B · e^{-αH/2}`

for every period `H` beyond the explicit threshold, with `B = a ∫_ℝ y = aπ`. -/
theorem hairpin_rear_tail {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (alpha C CK b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ CK ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      (∀ s, pulseField f (theta (x s)) ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ u, |curvField f (theta u)| ≤ CK * Real.exp (-alpha * |u|)) ∧
      ∀ H, threshold alpha C b ≤ H →
        (∫ s in (-(H / 2))..(H / 2),
            |speed (fun s => pulseField f (theta (x s))) H s
              * ∑' j : {j : ℤ // j ≠ 0},
                curvField f (theta (rearArclength (fun s => pulseField f (theta (x s))) H s
                  - (j : ℤ) * (rearArclength (fun s => pulseField f (theta (x s))) H (H / 2)
                    - rearArclength (fun s => pulseField f (theta (x s))) H (-(H / 2)))))|)
          ≤ MatchingExponential.rearTailConst CK alpha
              ((1 + b) / 2 * ∫ s : ℝ, pulseField f (theta (x s)))
            * Real.exp (-(alpha / 2 * H)) := by
  obtain ⟨theta, x, -, alpha, C, -, b, halpha, hC0, -, hb0, hb1, hK0, hKint, hKb,
    hmem, hval, hderiv, hxinv, hxderiv, hycont, hy0, hyb, hsup, -, -, -, -⟩ :=
    FrontPeriodizationHairpin.exists_hairpin_pulse_data hf hfpos
  refine ⟨theta, x, alpha, C, C, b, halpha, hC0, hC0, hb0, hb1, hmem, hval, hderiv,
    hxinv, hxderiv, hyb, hKb, ?_⟩
  intro H hH
  exact rear_tail_of_pulse (y := fun s => pulseField f (theta (x s)))
    (Kstar := fun u => curvField f (theta u)) (C := C) (CK := C) (alpha := alpha) (b := b)
    halpha hb1 hycont hy0 hyb hsup hH hKint hK0 hKb

end RearTailHairpin
