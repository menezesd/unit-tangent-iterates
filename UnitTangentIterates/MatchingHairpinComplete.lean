import Mathlib
import UnitTangentIterates.MatchingHairpin
import UnitTangentIterates.HairpinFrontCurvature

/-!
# Curvature-measure matching for the hairpin, with every error produced

`MatchingHairpin.matching_of_pulse_config` proves the theorem
*Curvature-measure matching* of *A Noncircular Oval with Convex Unit-Tangent
Iterates* in the configuration of a pulse, with the front periodization error
carried as a hypothesis, and with the rear arclength normalized by `x(0) = 0`.

For the hairpin the two intrinsic origins — that of the rear track and that of
the front — differ by the constant phase `s₀ = S(g(π/2))` of
`HairpinFrontCurvature.lean`, and it is the pulse phased by the *front* origin
that satisfies the front relation `K_* = y + G(y)y'`.  This file therefore

* generalizes the pulse configuration to a rear arclength with an arbitrary
  origin `x(0) = x₀` (`matching_of_pulse_config_shift`), the only cost being
  that the endpoints of the fundamental interval are now within
  `B + |x₀|` of `∓H/2`; and
* assembles the matching estimate for the paper's own hairpin with **all four
  error terms produced** (`hairpin_matching_complete`): the two pulse errors,
  the omitted mass and the front periodization error, the last of these coming
  from `HairpinFrontCurvature.hairpin_front_periodization_error_curv`, so that
  no error term is assumed and the periodized front `K_P = Y_P + G(Y_P)Y_P'`
  is the explicit one of the paper.
-/

noncomputable section

open Real Set MeasureTheory

open scoped ContDiff

namespace MatchingPulseConfig

open PerimeterHairpinPulse RearTailPulse

variable {y Kstar Kstar' KP x : ℝ → ℝ} {C CK alpha beta b H Km Kd C4 x0 : ℝ}

/-! ### The pulse configuration with a shifted rear origin -/

/-- The rear arclength with origin `x₀`. -/
def rearArclengthShift (y : ℝ → ℝ) (H x0 : ℝ) (t : ℝ) : ℝ := rearArclength y H t + x0

/-- The closed curvature read in the shifted rear arclength. -/
def cellCurvShift (y : ℝ → ℝ) (H x0 : ℝ) (u : ℝ) : ℝ := cellCurv y H (u - x0)

/-- **Curvature-measure matching in the configuration of a pulse, with a
shifted rear origin.**  Exactly `matching_of_pulse_config`, except that the
rear arclength has origin `x(0) = x₀`; the endpoints of the fundamental
interval are then within `B + |x₀|` of `∓H/2`. -/
theorem matching_of_pulse_config_shift
    (halpha : 0 < alpha) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hy : Continuous y) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|))
    (hsup : ∀ s, y s ≤ b) (hH : threshold alpha C b ≤ H)
    (hHshift : (1 + b) / 2 * (∫ s : ℝ, y s) + |x0| ≤ H / 2)
    (hx : ∀ t, HasDerivAt x (Real.sqrt (1 - (y t) ^ 2)) t) (hx0 : x 0 = x0)
    (hid : ∀ t, y t = Real.sqrt (1 - (y t) ^ 2) * Kstar (x t))
    (hK : ∀ u, |Kstar u| ≤ Km) (hKderiv : ∀ u, HasDerivAt Kstar (Kstar' u) u)
    (hKd' : ∀ u, |Kstar' u| ≤ Kd) (hKcont : Continuous Kstar)
    (hKint : Integrable Kstar) (hK0 : ∀ u, 0 ≤ Kstar u)
    (hKbd : ∀ s, |Kstar s| ≤ CK * Real.exp (-alpha * |s|))
    (hbeta : beta < alpha / 2)
    (hi0 : IntervalIntegrable (fun u => |cellCurvShift y H x0 u - KP u|) volume
      (rearArclengthShift y H x0 (-(H / 2))) (rearArclengthShift y H x0 (H / 2)))
    (hi2 : IntervalIntegrable
      (fun u => |periodize Kstar (cellPeriod y H) u - KP u|) volume
      (rearArclengthShift y H x0 (-(H / 2))) (rearArclengthShift y H x0 (H / 2)))
    (h4 : (∫ u in (rearArclengthShift y H x0 (-(H / 2)))..(rearArclengthShift y H x0 (H / 2)),
        |periodize Kstar (cellPeriod y H) u - KP u|)
      ≤ C4 * Real.exp (-(beta * H))) :
    (∫ u in (rearArclengthShift y H x0 (-(H / 2)))..(rearArclengthShift y H x0 (H / 2)),
        |cellCurvShift y H x0 u - KP u|)
      ≤ (MatchingExponential.pulseConst C Km Kd
            ((1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2)) alpha beta
          + MatchingExponential.rearTailConst CK alpha
              ((1 + b) / 2 * (∫ s : ℝ, y s) + |x0|)
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
  have hxHd : ∀ t, HasDerivAt (rearArclengthShift y H x0)
      (Real.sqrt (1 - periodize y H t ^ 2)) t := fun t => by
    exact (hasDerivAt_rearArclength halpha hHpos hy hy0 hyb t).add_const x0
  have hcxH : Continuous (rearArclengthShift y H x0) :=
    continuous_iff_continuousAt.2 fun t => (hxHd t).continuousAt
  -- the endpoints of the fundamental interval
  have hleft := rearArclength_left_le halpha hb1 hy hy0 hyb hsup hH
  have hright := le_rearArclength_right halpha hb1 hy hy0 hyb hsup hH
  have habs : x0 ≤ |x0| := le_abs_self x0
  have habs' : -|x0| ≤ x0 := neg_abs_le x0
  have hPeq : rearArclengthShift y H x0 (-(H / 2)) + P
      = rearArclengthShift y H x0 (H / 2) := by
    rw [hPdef, cellPeriod, rearArclengthShift, rearArclengthShift]; ring
  refine MatchingExponential.curvature_measure_matching_exp_of_pulse
    (Y := periodize y H) (y := y) (xH := rearArclengthShift y H x0) (x := x)
    (Kstar := Kstar) (Kstar' := Kstar') (kH := cellCurvShift y H x0)
    (Kbar := periodize Kstar P) (KP := KP)
    (a := (1 + b) / 2) (C := C) (CK := CK) (alpha := alpha) (beta := beta)
    (H := H) (P := P) (B := (1 + b) / 2 * (∫ s : ℝ, y s) + |x0|)
    (Km := Km) (Kd := Kd) (C4 := C4)
    halpha hy0 hyb hHpos (exp_le_half_of_threshold halpha hC hb1 hH)
    (fun s => rfl) (by linarith) (by linarith) hcper hy
    (fun s => by
      rw [abs_of_nonneg (periodize_nonneg hy0 s)]
      exact periodize_le halpha hb1 hy0 hyb hsup hH s)
    (fun s => by
      rw [abs_of_nonneg (hy0 s)]
      linarith [hsup s])
    hxHd hx ?_ hid hK hKderiv hKd' hKcont hbeta ?_ ?_
    (fun u => periodize_split halpha hPpos hKbd u) ?_ hi0 hi2 hPeq.symm hPpos
    hKint hK0 hKbd ?_ ?_ ?_ ?_ h4
  · rw [hx0, rearArclengthShift, rearArclength]; simp
  · intro t
    have h := cellCurv_spec halpha hb0 hb1 hy hy0 hyb hsup hH t
    simpa [cellCurvShift, rearArclengthShift, speed] using h
  · have hshift : Continuous (cellCurvShift y H x0) :=
      (continuous_cellCurv halpha hb0 hb1 hy hy0 hyb hsup hH).comp
        (continuous_id.sub continuous_const)
    exact (hshift.sub hcK).abs
  · have hsplit : ∀ u, ∑' j : {j : ℤ // j ≠ 0}, Kstar (u - (j : ℤ) * P)
        = periodize Kstar P u - Kstar u := fun u => by
      rw [periodize_split halpha hPpos hKbd u]; ring
    have heq : (fun s => Real.sqrt (1 - periodize y H s ^ 2) *
        ∑' j : {j : ℤ // j ≠ 0}, Kstar (rearArclengthShift y H x0 s - (j : ℤ) * P))
        = fun s => speed y H s *
          (periodize Kstar P (rearArclengthShift y H x0 s)
            - Kstar (rearArclengthShift y H x0 s)) := by
      funext s
      rw [hsplit]
      rfl
    rw [heq]
    exact (hcs.mul ((hcK.comp hcxH).sub (hKcont.comp hcxH))).intervalIntegrable _ _
  · rw [rearArclengthShift]
    linarith
  · rw [hPeq, rearArclengthShift]
    linarith
  · rw [rearArclengthShift]
    linarith
  · rw [hPeq, rearArclengthShift]
    linarith

end MatchingPulseConfig

/-! ### The matching estimate for the hairpin, with nothing assumed -/

namespace MatchingHairpin

open HairpinRelative PerimeterHairpinPulse RearTailPulse MatchingPulseConfig
  FrontPeriodization FrontPeriodizationIntegral HairpinFrontCurvature

variable {f g gp : ℝ → ℝ}

/-- **Curvature-measure matching for the hairpin of the paper, with all four
error terms produced.**  For a profile `f` smooth and positive on the line and
satisfying the translator relations, let `θ` be the arclength parametrization
of the hairpin, `x` the inverse of its front arclength, `s₀ = S(g(π/2))` the
phase between the two intrinsic origins, `ỹ(s) = y(s − s₀)` the steering pulse
phased by the front origin and `x₀ = x(−s₀)` the corresponding rear origin.
Then, beyond an explicit threshold in the period `H` and for every
`0 < β < α/2`, the closed curvature `k_H` of the periodized configuration and
the periodized front `K_P = Y_P + G(Y_P)Y_P'` of the same period satisfy

`∫_{J_H}|k_H − K_P| ≤ (pulseConst + rearTailConst + C₄)e^{−βH}`,

with `C₄ = Lip(a)·D·(8C²/(α−β))e^{2βB}` the front periodization error.  No
error term is assumed. -/
theorem hairpin_matching_complete (hf : ContDiff ℝ ∞ f) (hfpos : ∀ t, 0 < f t)
    (hdelta : ∀ θ ∈ Ioo (0:ℝ) π, g θ - θ = Real.arctan (curvField f θ))
    (hgmem : ∀ θ ∈ Ioo (0:ℝ) π, g θ ∈ Ioo (0:ℝ) π)
    (hnextd : ∀ θ ∈ Ioo (0:ℝ) π, f (g θ) * gp θ = f θ + Real.cos θ)
    (hg : ∀ θ ∈ Ioo (0:ℝ) π, HasDerivAt g (gp θ) θ) :
    ∃ (theta x ytil ypt : ℝ → ℝ) (alpha C D b Kd s0 x0 : ℝ),
      0 < alpha ∧ 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ b ∧ b < 1 ∧
      s0 = Hairpin.hairpinArclength f (π / 2) (g (π / 2)) ∧ x0 = x (-s0) ∧
      (∀ u, theta u ∈ Ioo 0 π) ∧
      (∀ u, Hairpin.hairpinArclength f (π / 2) (theta u) = u) ∧
      (∀ u, HasDerivAt theta (curvField f (theta u)) u) ∧
      (∀ s, frontArclength f theta (x s) = s) ∧
      (∀ s, ytil s = pulseField f (theta (x (s - s0)))) ∧
      (∀ s, curvField f (theta s) = ytil s + G (ytil s) * ypt s) ∧
      ∀ H beta : ℝ, 0 < beta → beta < alpha / 2 →
        threshold alpha C b + 2 * ((1 + b) / 2 * (∫ s : ℝ, ytil s)) ≤ H →
        (1 + b) / 2 * (∫ s : ℝ, ytil s) + |x0| ≤ H / 2 →
        2 ≤ beta * (H - 2 * ((1 + b) / 2 * (∫ s : ℝ, ytil s))) →
        (∫ u in (rearArclengthShift ytil H x0 (-(H / 2)))..
            (rearArclengthShift ytil H x0 (H / 2)),
            |cellCurvShift ytil H x0 u
              - ((∑' m : ℤ, ytil (u - m * cellPeriod ytil H))
                  + G (∑' m : ℤ, ytil (u - m * cellPeriod ytil H))
                    * (∑' m : ℤ, ypt (u - m * cellPeriod ytil H)))|)
          ≤ (MatchingExponential.pulseConst C C Kd
                ((1 + b) / 2 / Real.sqrt (1 - ((1 + b) / 2) ^ 2)) alpha beta
              + MatchingExponential.rearTailConst C alpha
                  ((1 + b) / 2 * (∫ s : ℝ, ytil s) + |x0|)
              + lipConst ((1 + b) / 2) * D * (8 * C ^ 2 / (alpha - beta))
                  * Real.exp (2 * beta * ((1 + b) / 2 * (∫ s : ℝ, ytil s))))
            * Real.exp (-(beta * H)) := by
  obtain ⟨theta, x, yp, alpha, C0, D, b, halpha, hC0, hD0, hb0, hb1, hK0, hKint, hKbd0,
    hmem, hvalθ, hderiv, hxinv, hxderiv, hycont, hy0, hyb, hsup, hy, hypc, hypexp, hrel⟩ :=
    FrontPeriodizationHairpin.exists_hairpin_pulse_data hf hfpos
  set s0 : ℝ := Hairpin.hairpinArclength f (π / 2) (g (π / 2)) with hs0
  set C : ℝ := C0 * Real.exp (alpha * |s0|) with hCdef
  have hexp1 : (1:ℝ) ≤ Real.exp (alpha * |s0|) :=
    Real.one_le_exp (by positivity)
  have hC : 0 ≤ C := by positivity
  have hC0C : C0 ≤ C := by
    rw [hCdef]
    nlinarith
  set ytil : ℝ → ℝ := fun s => pulseField f (theta (x (s - s0))) with hyt
  set ypt : ℝ → ℝ := fun s => yp (s - s0) with hypt
  set xt : ℝ → ℝ := fun s => x (s - s0) with hxt
  set x0 : ℝ := x (-s0) with hx0def
  have hshift : Continuous fun s : ℝ => s - s0 := continuous_id.sub continuous_const
  have hytc : Continuous ytil := hycont.comp hshift
  have hyptc : Continuous ypt := hypc.comp hshift
  have hyt0 : ∀ s, 0 ≤ ytil s := fun s => hy0 _
  have hytsup : ∀ s, ytil s ≤ b := fun s => hsup _
  have hshiftbd : ∀ (K : ℝ) (F : ℝ → ℝ), 0 ≤ K →
      (∀ s, |F s| ≤ K * Real.exp (-alpha * |s|)) →
      ∀ s, |F (s - s0)| ≤ (K * Real.exp (alpha * |s0|)) * Real.exp (-alpha * |s|) := by
    intro K F hK hFb s
    refine (hFb (s - s0)).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
    have h : |s| - |s0| ≤ |s - s0| := abs_sub_abs_le_abs_sub s s0
    nlinarith [halpha]
  have hytb : ∀ s, ytil s ≤ C * Real.exp (-alpha * |s|) := by
    intro s
    have h := hshiftbd C0 (fun s => pulseField f (theta (x s))) hC0
      (fun s => by rw [abs_of_nonneg (hy0 s)]; exact hyb s) s
    rw [abs_of_nonneg (hy0 _)] at h
    exact h
  have hytabs : ∀ s, |ytil s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hyt0 s)]; exact hytb s
  have hyptb : ∀ s, |ypt s| ≤ C * Real.exp (-alpha * |s|) :=
    hshiftbd C0 yp hC0 hypexp
  have hytrel : ∀ s, |ypt s| ≤ D * ytil s := fun s => hrel _
  -- the isolated curvature and its bounds
  have hmem' : ∀ u, theta u ∈ Icc (0:ℝ) π := fun u => ⟨(hmem u).1.le, (hmem u).2.le⟩
  have hKcont : Continuous fun u => curvField f (theta u) := by
    have hthetac : Continuous theta :=
      Differentiable.continuous fun u => (hderiv u).differentiableAt
    exact ((contDiff_curvField hf hfpos).continuous).comp hthetac
  have hKbd : ∀ s, |curvField f (theta s)| ≤ C * Real.exp (-alpha * |s|) := by
    intro s
    refine (hKbd0 s).trans ?_
    exact mul_le_mul_of_nonneg_right hC0C (Real.exp_pos _).le
  have hbd : ∀ u, curvField f (theta u) ≤ C := by
    intro u
    have h1 := hKbd u
    have h2 : Real.exp (-alpha * |u|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg u, halpha])
    have h3 : curvField f (theta u) ≤ |curvField f (theta u)| := le_abs_self _
    nlinarith [hK0 u]
  obtain ⟨Kstar', Kd, hKderiv, hKd'⟩ :=
    MatchingHairpin.exists_curv_derivative_bounds hf hfpos hmem' hderiv hbd
  -- the front relation
  have hident : ∀ s, curvField f (theta s) = ytil s + G (ytil s) * ypt s := fun s =>
    front_curvature_identity_shifted hf hfpos hdelta hgmem hnextd hg hmem hvalθ hderiv
      hxinv hxderiv hy s
  refine ⟨theta, x, ytil, ypt, alpha, C, D, b, Kd, s0, x0, halpha, hC, hD0, hb0, hb1,
    rfl, rfl, hmem, hvalθ, hderiv, hxinv, fun s => rfl, hident, ?_⟩
  intro H beta hbeta0 hbeta hHthr hHshift hHbeta
  set B : ℝ := (1 + b) / 2 * (∫ s : ℝ, ytil s) with hB
  have hB0 : 0 ≤ B := by
    have hint : 0 ≤ ∫ s : ℝ, ytil s := integral_nonneg fun s => hyt0 s
    have : (0:ℝ) ≤ (1 + b) / 2 := by linarith
    exact mul_nonneg this hint
  have hH : threshold alpha C b ≤ H := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le (threshold_pos halpha hC hb1) hH
  set P : ℝ := cellPeriod ytil H with hPdef
  have hPpos : 0 < P := cellPeriod_pos halpha hb1 hytc hyt0 hytb hytsup hH
  -- the fundamental interval is long
  have hleft := rearArclength_left_le halpha hb1 hytc hyt0 hytb hytsup hH
  have hright := le_rearArclength_right halpha hb1 hytc hyt0 hytb hytsup hH
  have hPge : H - 2 * B ≤ P := by
    rw [hPdef, cellPeriod]
    linarith
  have hPthr : threshold alpha C b ≤ P := by linarith
  have hbP : 2 ≤ beta * P := by
    have : beta * (H - 2 * B) ≤ beta * P := by nlinarith
    linarith
  -- the periodized front is continuous
  have hYc : Continuous fun u => ∑' m : ℤ, ytil (u - m * P) :=
    continuous_tsum_translates halpha hPpos hytc hytabs
  have hYpc : Continuous fun u => ∑' m : ℤ, ypt (u - m * P) :=
    continuous_tsum_translates halpha hPpos hyptc hyptb
  have hY0 : ∀ u, 0 ≤ ∑' m : ℤ, ytil (u - m * P) := fun u =>
    periodize_nonneg (H := P) hyt0 u
  have hYa : ∀ u : ℝ, (∑' m : ℤ, ytil (u - m * P)) ≤ (1 + b) / 2 :=
    periodization_le_mid halpha hb1 hyt0 hytb hytsup hPthr
  have hKPc : Continuous fun u => (∑' m : ℤ, ytil (u - m * P))
      + G (∑' m : ℤ, ytil (u - m * P)) * (∑' m : ℤ, ypt (u - m * P)) :=
    hYc.add ((continuous_G_comp (by linarith) (by linarith) hYc hY0 hYa).mul hYpc)
  have hcellc : Continuous (cellCurvShift ytil H x0) :=
    (continuous_cellCurv halpha hb0 hb1 hytc hyt0 hytb hytsup hH).comp
      (continuous_id.sub continuous_const)
  have hKbarc : Continuous (periodize (fun u => curvField f (theta u)) P) :=
    continuous_periodize halpha hPpos hKcont hK0
      (fun s => le_trans (le_abs_self _) (hKbd s))
  -- the front periodization error
  have hsplit : ∀ u, periodize (fun u => curvField f (theta u)) P u
      = curvField f (theta u)
        + ∑' j : {j : ℤ // j ≠ 0}, curvField f (theta (u - (j : ℤ) * P)) :=
    fun u => periodize_split halpha hPpos hKbd u
  have hhalf : Real.exp (-(beta * P)) ≤ 1 / 2 := by
    have h := exp_neg_le_inv (t := beta * P) (by positivity)
    have hinv : (1:ℝ) / (beta * P) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hbP
    linarith
  have h4 := FrontPeriodizationIntegral.front_periodization_error_exp
    (y := ytil) (yp := ypt) (C := C) (alpha := alpha) (beta := beta)
    (a := (1 + b) / 2) (D := D) (P := P)
    (Kstar := fun u => curvField f (theta u))
    (Kbar := periodize (fun u => curvField f (theta u)) P)
    (KP := fun u => (∑' m : ℤ, ytil (u - m * P))
      + G (∑' m : ℤ, ytil (u - m * P)) * (∑' m : ℤ, ypt (u - m * P)))
    (H := H) (B := B) (q := rearArclengthShift ytil H x0 (-(H / 2)))
    halpha hPpos hbeta0 (by linarith) hhalf hytc hyptc hyt0 hytb hD0 hytrel
    (by linarith) (by linarith) hYa hident hsplit (fun _ => rfl) hPge
  have hPeq : rearArclengthShift ytil H x0 (-(H / 2)) + P
      = rearArclengthShift ytil H x0 (H / 2) := by
    rw [hPdef, cellPeriod, rearArclengthShift, rearArclengthShift]; ring
  rw [hPeq] at h4
  -- the matching estimate
  exact matching_of_pulse_config_shift
    (y := ytil) (x := xt) (Kstar := fun u => curvField f (theta u)) (Kstar' := Kstar')
    (KP := fun u => (∑' m : ℤ, ytil (u - m * P))
      + G (∑' m : ℤ, ytil (u - m * P)) * (∑' m : ℤ, ypt (u - m * P)))
    (C := C) (CK := C) (alpha := alpha) (beta := beta) (b := b) (H := H)
    (Km := C) (Kd := Kd) (C4 := lipConst ((1 + b) / 2) * D * (8 * C ^ 2 / (alpha - beta))
      * Real.exp (2 * beta * B)) (x0 := x0)
    halpha hb0 hb1 hytc hyt0 hytb hytsup hH hHshift
    (fun t => by
      have h := HairpinPulseIdentity.hasDerivAt_pulseInverse hf hfpos hderiv hxinv (t - s0)
      simpa [hxt, hyt] using h.comp t ((hasDerivAt_id t).sub_const s0))
    (by rw [hxt, hx0def]; norm_num)
    (fun t => HairpinPulseIdentity.pulseField_eq_speed_mul_curvField f (theta (x (t - s0))))
    (fun u => by rw [abs_of_nonneg (hK0 u)]; exact hbd u)
    hKderiv hKd' hKcont hKint hK0 hKbd hbeta
    ((hcellc.sub hKPc).abs.intervalIntegrable _ _)
    ((hKbarc.sub hKPc).abs.intervalIntegrable _ _)
    h4

end MatchingHairpin
