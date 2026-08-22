import Mathlib
import UnitTangentIterates.RearTailHairpin
import UnitTangentIterates.HairpinPulseIdentity
import UnitTangentIterates.MatchingExponential

/-!
# Curvature-measure matching in the configuration of a pulse

`MatchingExponential.curvature_measure_matching_exp_of_pulse` proves the rear
half of the theorem *Curvature-measure matching* of *A Noncircular Oval with
Convex Unit-Tangent Iterates*: with the front periodization error assumed, the
matching integral over the fundamental interval is at most

```
  (pulseConst + rearTailConst + C₄) e^{-βH}.
```

Its hypotheses describe a configuration built from a single pulse: the
periodization `Y_H`, the rear arclength `x_H = ∫₀^· √(1-Y_H²)`, the closed
curvature `k_H` read in the rear arclength, the fundamental interval
`[x_H(-H/2), x_H(H/2)]` and the sum `K̄` of the translates of the isolated
profile.  This file **constructs** all of them from the pulse and discharges
every hypothesis that does not involve the periodized front `K_P`:

* `rearInverse` : the inverse of the rear arclength, defined for any pulse
  below `(1+b)/2 < 1`;
* `cellCurv` : the closed curvature `k_H = Y_H/c_H`, read in the rear
  arclength, so that `k_H(x_H(t))·c_H(t) = Y_H(t)` (`cellCurv_spec`);
* `matching_of_pulse_config` : the matching estimate for an arbitrary such
  pulse, given the front periodization error;
* `MatchingHairpin.hairpin_matching_of_front_error` : the same for the paper's
  own hairpin, whose steering identity comes from `HairpinPulseIdentity.lean`.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace MatchingPulseConfig

open PerimeterHairpinPulse RearTailPulse

variable {y Kstar Kstar' KP x : ℝ → ℝ} {C CK alpha beta b H Km Kd C4 : ℝ}

/-! ### The inverse of the rear arclength -/

/-- The length of the fundamental interval. -/
def cellPeriod (y : ℝ → ℝ) (H : ℝ) : ℝ :=
  rearArclength y H (H / 2) - rearArclength y H (-(H / 2))

/-- The inverse of the rear arclength. -/
def rearInverse (y : ℝ → ℝ) (H : ℝ) : ℝ → ℝ := Function.invFun (rearArclength y H)

/-- The closed curvature `k_H = Y_H/c_H`, read in the rear arclength. -/
def cellCurv (y : ℝ → ℝ) (H : ℝ) (u : ℝ) : ℝ :=
  periodize y H (rearInverse y H u) / speed y H (rearInverse y H u)

/-- The speed of the closed rear track is bounded below. -/
theorem speed_ge (halpha : 0 < alpha) (hb1 : b < 1)
    (hy0 : ∀ s, 0 ≤ y s) (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) (u : ℝ) :
    Real.sqrt (1 - ((1 + b) / 2) ^ 2) ≤ speed y H u := by
  have h0 : 0 ≤ periodize y H u := periodize_nonneg hy0 u
  have h1 : periodize y H u ≤ (1 + b) / 2 := periodize_le halpha hb1 hy0 hyb hsup hH u
  refine Real.sqrt_le_sqrt ?_
  nlinarith

theorem sqrt_one_sub_mid_pos (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 < Real.sqrt (1 - ((1 + b) / 2) ^ 2) := by
  refine Real.sqrt_pos.mpr ?_
  nlinarith

theorem rearArclength_rearInverse (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) (u : ℝ) :
    rearArclength y H (rearInverse y H u) = u := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hsurj : Function.Surjective (rearArclength y H) :=
    ArclengthInverse.surjective_of_deriv_ge (sqrt_one_sub_mid_pos hb0 hb1)
      (hasDerivAt_rearArclength halpha hHpos hy hy0 hyb)
      (speed_ge halpha hb1 hy0 hyb hsup hH)
  exact Function.invFun_eq (hsurj u)

theorem rearArclength_injective (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    Function.Injective (rearArclength y H) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  exact (ArclengthInverse.strictMono_of_deriv_ge (sqrt_one_sub_mid_pos hb0 hb1)
    (hasDerivAt_rearArclength halpha hHpos hy hy0 hyb)
    (speed_ge halpha hb1 hy0 hyb hsup hH)).injective

theorem rearInverse_rearArclength (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) (t : ℝ) :
    rearInverse y H (rearArclength y H t) = t :=
  ArclengthInverse.leftInverse_of_rightInverse
    (rearArclength_injective halpha hb0 hb1 hy hy0 hyb hsup hH)
    (rearArclength_rearInverse halpha hb0 hb1 hy hy0 hyb hsup hH) t

theorem continuous_rearInverse (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    Continuous (rearInverse y H) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  exact ArclengthInverse.continuous_of_rightInverse (sqrt_one_sub_mid_pos hb0 hb1)
    (hasDerivAt_rearArclength halpha hHpos hy hy0 hyb)
    (speed_ge halpha hb1 hy0 hyb hsup hH)
    (rearArclength_rearInverse halpha hb0 hb1 hy hy0 hyb hsup hH)

/-! ### The closed curvature -/

/-- The closed curvature is the curvature of the periodized configuration:
`k_H(x_H(t))·c_H(t) = Y_H(t)`. -/
theorem cellCurv_spec (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) (t : ℝ) :
    cellCurv y H (rearArclength y H t) * speed y H t = periodize y H t := by
  have hne : speed y H t ≠ 0 := (speed_pos halpha hb1 hy0 hyb hsup hH t).ne'
  rw [cellCurv, rearInverse_rearArclength halpha hb0 hb1 hy hy0 hyb hsup hH t,
    div_mul_cancel₀ _ hne]

theorem continuous_cellCurv (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    Continuous (cellCurv y H) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hinv := continuous_rearInverse halpha hb0 hb1 hy hy0 hyb hsup hH
  have hP := continuous_periodize halpha hHpos hy hy0 hyb
  have hs := continuous_speed halpha hHpos hy hy0 hyb
  refine (hP.comp hinv).div (hs.comp hinv) fun u => ?_
  exact (speed_pos halpha hb1 hy0 hyb hsup hH _).ne'

/-! ### The sum of the translates of the isolated profile -/

/-- The sum of all the translates splits off the central one. -/
theorem periodize_split (halpha : 0 < alpha) {P : ℝ} (hP : 0 < P)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|)) (u : ℝ) :
    periodize Kstar P u = Kstar u + ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P) := by
  have hs : Summable (fun m : ℤ => Kstar (u - m * P)) :=
    FrontPeriodizationIntegral.summable_translates halpha hP hKbd u
  rw [periodize, FrontPeriodizationIntegral.tsum_split_zero hs]
  norm_num

/-- The fundamental interval has positive length. -/
theorem cellPeriod_pos (halpha : 0 < alpha) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H) :
    0 < cellPeriod y H := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hcs := continuous_speed halpha hHpos hy hy0 hyb
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
  exact hpos

/-! ### The matching estimate for the configuration of a pulse -/

/-- **Curvature-measure matching in the configuration of a pulse.**  For a
pulse `y` that is continuous, nonnegative, bounded by `b < 1` and by
`Ce^{-α|·|}`, whose isolated profile `K_*` obeys the steering identity
`y = √(1-y²)K_*(x)` with `x' = √(1-y²)`, `x(0) = 0`, and is nonnegative,
integrable, bounded together with its derivative and exponentially localized,
the closed curvature `k_H` of the periodized configuration satisfies

`∫_{J_H}|k_H - K_P| ≤ (pulseConst + rearTailConst + C₄)e^{-βH}`

for every periodized front `K_P` whose periodization error over the cell is at
most `C₄e^{-βH}`. -/
theorem matching_of_pulse_config
    (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t) (hx0 : x 0 = 0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKderiv : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hbeta : beta < alpha / 2)
    (hi0 : IntervalIntegrable (fun u => |cellCurv y H u - KP u|) volume
      (rearArclength y H (-(H / 2))) (rearArclength y H (H / 2)))
    (hi2 : IntervalIntegrable
      (fun u => |periodize Kstar (cellPeriod y H) u - KP u|) volume
      (rearArclength y H (-(H / 2))) (rearArclength y H (H / 2)))
    (h4 : (∫ u in (rearArclength y H (-(H / 2)))..(rearArclength y H (H / 2)),
        |periodize Kstar (cellPeriod y H) u - KP u|)
      ≤ C4 * Real.exp (-(beta * H))) :
    (∫ u in (rearArclength y H (-(H / 2)))..(rearArclength y H (H / 2)),
        |cellCurv y H u - KP u|)
      ≤ (MatchingExponential.pulseConst C Km Kd
            ((1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2)) alpha beta
          + MatchingExponential.rearTailConst CK alpha ((1 + b) / 2 * ∫ s : ℝ, y s)
          + C4) * Real.exp (-(beta * H)) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  have hK0' : ∀ s, Kstar s ≤ CK * Real.exp (-alpha * |s|) := fun s =>
    le_trans (le_abs_self _) (hKbd s)
  set P : ℝ := cellPeriod y H with hPdef
  have hPpos : 0 < P := cellPeriod_pos halpha hb1 hy hy0 hyb hsup hH
  have hcs := continuous_speed halpha hHpos hy hy0 hyb
  have hcper := continuous_periodize halpha hHpos hy hy0 hyb
  have hcK : Continuous (periodize Kstar P) :=
    continuous_periodize halpha hPpos hKcont hK0 hK0'
  have hxHd : ∀ t, HasDerivAt (rearArclength y H)
      (Real.sqrt (1 - periodize y H t ^ 2)) t := fun t => by
    simpa [speed] using hasDerivAt_rearArclength halpha hHpos hy hy0 hyb t
  have hcxH : Continuous (rearArclength y H) :=
    continuous_iff_continuousAt.2 fun t => (hxHd t).continuousAt
  have hsplit : ∀ u, ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P)
      = periodize Kstar P u - Kstar u := fun u => by
    rw [periodize_split halpha hPpos hKbd u]; ring
  refine MatchingExponential.curvature_measure_matching_exp_of_pulse
    (Y := periodize y H) (y := y) (xH := rearArclength y H) (x := x)
    (Kstar := Kstar) (Kstar' := Kstar') (kH := cellCurv y H)
    (Kbar := periodize Kstar P) (KP := KP)
    (a := (1 + b) / 2) (C := C) (CK := CK) (alpha := alpha) (beta := beta)
    (H := H) (P := P) (B := (1 + b) / 2 * ∫ s : ℝ, y s) (Km := Km) (Kd := Kd) (C4 := C4)
    halpha hy0 hyb hHpos (exp_le_half_of_threshold halpha hC hb1 hH)
    (fun s => rfl) (by linarith) (by linarith) hcper hy
    (fun s => by
      rw [abs_of_nonneg (periodize_nonneg hy0 s)]
      exact periodize_le halpha hb1 hy0 hyb hsup hH s)
    (fun s => by
      rw [abs_of_nonneg (hy0 s)]
      linarith [hsup s])
    hxHd hx ?_ hid hK hKderiv hKd' hKcont hbeta ?_ ?_
    (fun u => periodize_split halpha hPpos hKbd u) ?_ hi0 hi2 ?_ hPpos
    hKint hK0 hKbd
    (rearArclength_left_nonpos halpha hb1 hy hy0 hyb hsup hH)
    ?_ (rearArclength_left_le halpha hb1 hy hy0 hyb hsup hH) ?_ h4
  · rw [hx0, rearArclength]; simp
  · intro t
    simpa [speed] using cellCurv_spec halpha hb0 hb1 hy hy0 hyb hsup hH t
  · exact ((continuous_cellCurv halpha hb0 hb1 hy hy0 hyb hsup hH).sub hcK).abs
  · have heq : (fun s => Real.sqrt (1 - periodize y H s ^ 2) *
        ∑' j : {j : ℤ // j ≠ 0}, Kstar (rearArclength y H s - (j : ℤ) * P))
        = fun s => speed y H s *
          (periodize Kstar P (rearArclength y H s) - Kstar (rearArclength y H s)) := by
      funext s
      rw [hsplit]
      rfl
    rw [heq]
    exact (hcs.mul ((hcK.comp hcxH).sub (hKcont.comp hcxH))).intervalIntegrable _ _
  · rw [hPdef, cellPeriod]; ring
  · have h := rearArclength_right_nonneg halpha hb1 hy0 hyb hsup hH (C := C)
    have hP' : rearArclength y H (-(H / 2)) + P = rearArclength y H (H / 2) := by
      rw [hPdef, cellPeriod]; ring
    rw [hP']
    exact h
  · have hP' : rearArclength y H (-(H / 2)) + P = rearArclength y H (H / 2) := by
      rw [hPdef, cellPeriod]; ring
    rw [hP']
    exact le_rearArclength_right halpha hb1 hy hy0 hyb hsup hH

/-- The hypotheses carried on the periodized front `K_P` are satisfiable: the
choice `K_P = K̄` makes both integrability clauses hold and the front
periodization error vanish. -/
theorem matching_hypotheses_satisfiable
    (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H)
    (hKcont : Continuous Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|)) (beta : ℝ) :
    IntervalIntegrable
        (fun u => |cellCurv y H u - periodize Kstar (cellPeriod y H) u|) volume
        (rearArclength y H (-(H / 2))) (rearArclength y H (H / 2)) ∧
      IntervalIntegrable
        (fun u => |periodize Kstar (cellPeriod y H) u
          - periodize Kstar (cellPeriod y H) u|) volume
        (rearArclength y H (-(H / 2))) (rearArclength y H (H / 2)) ∧
      (∫ u in (rearArclength y H (-(H / 2)))..(rearArclength y H (H / 2)),
          |periodize Kstar (cellPeriod y H) u - periodize Kstar (cellPeriod y H) u|)
        ≤ 0 * Real.exp (-(beta * H)) := by
  have hPpos : 0 < cellPeriod y H := cellPeriod_pos halpha hb1 hy hy0 hyb hsup hH
  have hK0' : ∀ s, Kstar s ≤ CK * Real.exp (-alpha * |s|) := fun s =>
    le_trans (le_abs_self _) (hKbd s)
  have hcK : Continuous (periodize Kstar (cellPeriod y H)) :=
    continuous_periodize halpha hPpos hKcont hK0 hK0'
  refine ⟨(((continuous_cellCurv halpha hb0 hb1 hy hy0 hyb hsup hH).sub hcK).abs).intervalIntegrable
    _ _, ?_, ?_⟩
  · simp
  · simp

end MatchingPulseConfig

/-! ### The matching estimate for the hairpin of the paper -/

namespace MatchingHairpin

open HairpinRelative PerimeterHairpinPulse RearTailPulse MatchingPulseConfig

/-- The curvature of the hairpin, read in its own arclength, is differentiable
with a bounded derivative. -/
theorem exists_curv_derivative_bounds {f theta : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t) (hmem : ∀ u, theta u ∈ Icc 0 π)
    (hderiv : ∀ u, HasDerivAt theta (curvField f (theta u)) u) {Km : ℝ}
    (hbd : ∀ u, curvField f (theta u) ≤ Km) :
    ∃ Kstar' : ℝ → ℝ, ∃ Kd : ℝ,
      (∀ u, HasDerivAt (fun u => curvField f (theta u)) (Kstar' u) u) ∧
        ∀ u, |Kstar' u| ≤ Kd := by
  obtain ⟨C₁, hC₁0, hC₁b⟩ := abs_iteratedDeriv_curv_le hf hfpos hmem hderiv 1
  have hdiff : Differentiable ℝ fun u => curvField f (theta u) := by
    intro u
    exact (((contDiff_curvField hf hfpos).differentiable (by simp)) (theta u)).comp u
      (hderiv u).differentiableAt
  refine ⟨deriv fun u => curvField f (theta u), C₁ * Km,
    fun u => (hdiff u).hasDerivAt, fun u => ?_⟩
  have h := hC₁b u
  rw [iteratedDeriv_one] at h
  have h0 : 0 ≤ curvField f (theta u) := curvField_nonneg hfpos (hmem u)
  calc |deriv (fun u => curvField f (theta u)) u| ≤ C₁ * curvField f (theta u) := h
    _ ≤ C₁ * Km := by nlinarith [hbd u]

/-- **Curvature-measure matching for the hairpin of the paper, given the front
periodization error.**  For a profile `f` smooth and positive on the line, the
hairpin has an arclength parametrization `θ`, a front-arclength
parametrization `x` and a steering pulse `y = G₂(θ(x(·)))`; for every period
`H` beyond the explicit threshold, the closed curvature `k_H` of the periodized
configuration and any periodized front `K_P` whose periodization error over the
fundamental interval is at most `C₄e^{−βH}` satisfy

`∫_{J_H}|k_H − K_P| ≤ (pulseConst + rearTailConst + C₄)e^{−βH}`

for every `0 < β < α/2`. -/
theorem hairpin_matching_of_front_error {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfpos : ∀ t, 0 < f t) :
    ∃ (theta x : ℝ → ℝ) (alpha C Km Kd b : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ b ∧ b < 1 ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, HasDerivAt (fun s => theta (x s)) (pulseField f (theta (x s))) s) ∧
      ∀ (H beta C4 : ℝ) (KP : ℝ → ℝ),
        threshold alpha C b ≤ H → beta < alpha / 2 →
        IntervalIntegrable
          (fun u => |cellCurv (fun s => pulseField f (theta (x s))) H u - KP u|) volume
          (rearArclength (fun s => pulseField f (theta (x s))) H (-(H / 2)))
          (rearArclength (fun s => pulseField f (theta (x s))) H (H / 2)) →
        IntervalIntegrable
          (fun u => |periodize (fun u => curvField f (theta u))
            (cellPeriod (fun s => pulseField f (theta (x s))) H) u - KP u|) volume
          (rearArclength (fun s => pulseField f (theta (x s))) H (-(H / 2)))
          (rearArclength (fun s => pulseField f (theta (x s))) H (H / 2)) →
        (∫ u in (rearArclength (fun s => pulseField f (theta (x s))) H (-(H / 2)))..
            (rearArclength (fun s => pulseField f (theta (x s))) H (H / 2)),
            |periodize (fun u => curvField f (theta u))
              (cellPeriod (fun s => pulseField f (theta (x s))) H) u - KP u|)
          ≤ C4 * Real.exp (-(beta * H)) →
        (∫ u in (rearArclength (fun s => pulseField f (theta (x s))) H (-(H / 2)))..
            (rearArclength (fun s => pulseField f (theta (x s))) H (H / 2)),
            |cellCurv (fun s => pulseField f (theta (x s))) H u - KP u|)
          ≤ (MatchingExponential.pulseConst C Km Kd
                ((1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2)) alpha beta
              + MatchingExponential.rearTailConst C alpha
                  ((1 + b) / 2 * ∫ s : ℝ, pulseField f (theta (x s)))
              + C4) * Real.exp (-(beta * H)) := by
  obtain ⟨theta, x, -, alpha, C, -, b, halpha, hC0, -, hb0, hb1, hK0, hKint, hKb,
    hmem, hval, hderiv, hxinv, hxderiv, hycont, hy0, hyb, hsup, -, -, -, -⟩ :=
    FrontPeriodizationHairpin.exists_hairpin_pulse_data hf hfpos
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hKcont : Continuous fun u => curvField f (theta u) := by
    have hthetac : Continuous theta :=
      Differentiable.continuous fun u => (hderiv u).differentiableAt
    exact ((contDiff_curvField hf hfpos).continuous).comp hthetac
  have hbd : ∀ u, curvField f (theta u) ≤ C := by
    intro u
    have h1 := hKb u
    have h2 : Real.exp (-alpha * |u|) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have h3 : 0 ≤ |u| := abs_nonneg u
      nlinarith
    have h3 : curvField f (theta u) ≤ |curvField f (theta u)| := le_abs_self _
    nlinarith [hK0 u]
  obtain ⟨Kstar', Kd, hKderiv, hKd'⟩ :=
    exists_curv_derivative_bounds hf hfpos hmem' hderiv hbd
  refine ⟨theta, x, alpha, C, C, Kd, b, halpha, hC0, hb0, hb1, hmem, hval, hderiv,
    hxinv, hxderiv, ?_⟩
  intro H beta C4 KP hH hbeta hi0 hi2 h4
  exact MatchingPulseConfig.matching_of_pulse_config
    (y := fun s => pulseField f (theta (x s))) (x := x)
    (Kstar := fun u => curvField f (theta u)) (Kstar' := Kstar') (KP := KP)
    (C := C) (CK := C) (alpha := alpha) (beta := beta) (b := b) (H := H)
    (Km := C) (Kd := Kd) (C4 := C4)
    halpha hb0 hb1 hycont hy0 hyb hsup hH
    (fun t => HairpinPulseIdentity.hasDerivAt_pulseInverse hf hfpos hderiv hxinv t)
    (HairpinPulseIdentity.pulseInverse_zero hf hfpos hderiv hxinv)
    (fun t => HairpinPulseIdentity.pulseField_eq_speed_mul_curvField f (theta (x t)))
    (fun u => by
      rw [abs_of_nonneg (hK0 u)]
      exact hbd u)
    hKderiv hKd' hKcont hKint hK0 hKb hbeta hi0 hi2 h4

end MatchingHairpin
