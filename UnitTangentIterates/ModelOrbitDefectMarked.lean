import Mathlib
import UnitTangentIterates.ModelOrbitDefect
import UnitTangentIterates.MatchingMarkedDistance

/-!
# The defect estimate of the model pseudo-orbit in the marked metric

`ModelOrbitDefect.Config.pathDistRigid_le` states the defect estimate of the
model pseudo-orbit in the *path* pseudodistance, modulo a rigid motion.  The
shadowing scheme of `MarkedSchemeTheorem.lean`, however, asks for the defect in
the **metric of the space of marked curves**, `dist (Q n) (A n) ≤ e n`.

`MatchingMarkedDistance.dist_le_of_matching` is the passage between the two: it
feeds the `L¹` matching estimate into the stability bound
`CurvatureStabilityL1.dist_le_of_L1_curvature_close`.  Its first block of
hypotheses is exactly the block a `ModelOrbitDefect.Config` produces, so the
whole of it is discharged here from the configuration; what remains is the
second block, which says that the two curves compared *carry* the two
curvatures of the configuration — the rear curvature `k_H` of the pair of
separation `H` and the model curvature `K_P` of period `P` — are members of one
tube, have the same perimeter and are aligned at the marked point.

Main results:

* `ModelOrbitDefect.Config.dist_le` — the defect estimate of one matching
  configuration in the marked metric, with the constants of the configuration:
  the two curves are at distance at most
  `l1Modulus (2kd) (matchConst … · e^{−βH}) P · L²(1 + kstar·L)`;
* `dist_selInv_model_orbit` — its reading along the recursion
  `P(H_{n+1}) = H_n` of the pseudo-orbit;
* `tendsto_markedDefect_zero` — the bound tends to `0` as the separations grow,
  so the sequence really is a pseudo-orbit of the marked space;
* `l1Modulus_le_exp` and `summable_markedDefect` — the defect of one step is
  dominated by `exp(−(β/2)H)`, so that along separations growing at least
  linearly the whole sequence of defects is **summable**, which is the form the
  shadowing scheme of `MarkedSchemeTheorem.lean` asks of it.
-/

noncomputable section

open Real Set Function MeasureTheory MarkedSpace PathMetric

namespace ModelOrbitDefectMarked

open ModelOrbitDefect MatchingMarkedDistance CurvatureStabilityL1 RearTrack

variable {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P : ℝ}

/-- **The defect estimate of a matching configuration in the marked metric.**

`pt` and `qt` are two members of one tube, of the same perimeter `L`, aligned in
position and direction at the marked point, whose curvatures are the rear
curvature `k_H` of the configuration and the model curvature `K_P` of period
`P`.  Then they are at marked distance at most
`l1Modulus (2kd) (matchConst … · e^{−βH}) P · L² (1 + kstar·L)`.

Every hypothesis of the matching estimate itself is produced by the
configuration. -/
theorem dist_le
    (c : Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P)
    {cc kmin delta L : ℝ} {pt qt : Data} {Θp Θq : ℝ → ℝ}
    (hkd : 0 < kd) (hcc : 0 < cc)
    (hpt : IsTubeMember cc kmin delta pt) (hqt : IsTubeMember cc kmin delta qt)
    (hLp : perim pt = L) (hLq : perim qt = L)
    (hevp : ∀ s, HasDerivAt (ev pt) (Complex.exp (Complex.I * (Θp s : ℂ))) s)
    (hevq : ∀ s, HasDerivAt (ev qt) (Complex.exp (Complex.I * (Θq s : ℂ))) s)
    (hΘp : ∀ s, HasDerivAt Θp (c.kH s) s)
    (hΘq : ∀ s, HasDerivAt Θq (modelCurvature c.yu c.yu' P s) s)
    (hF0 : ev pt 0 = ev qt 0) (hΘ0 : Θp 0 = Θq 0) :
    dist pt qt
      ≤ l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * H))) P
        * L ^ 2 * (1 + kstar * L) := by
  have hkb : ∀ u, |modelCurvature c.yu c.yu' P u| ≤ kstar := fun u => by
    rw [abs_of_nonneg (c.KP_nonneg u)]
    exact c.KP_le u
  have hbp : ∀ u, |kHderiv c.Y (modelCurvature c.y c.yd H) c.sf u| ≤ 2 * kd / 2 := fun u => by
    simpa using c.abs_kHderiv_le u
  have hbq : ∀ u, |c.KP' u| ≤ 2 * kd / 2 := fun u => by
    simpa using c.abs_KP'_le u
  have h := dist_le_of_matching
    (Y := c.Y) (y := c.y) (xH := modelRearArclength c.Y) (x := c.x)
    (Kstar := c.Kstar) (Kstar' := c.Kstar') (kH := c.kH) (Kbar := c.Kbar)
    (KP := modelCurvature c.yu c.yu' P) (yu := c.yu) (yu' := c.yu')
    (kH' := kHderiv c.Y (modelCurvature c.y c.yd H) c.sf) (KP' := c.KP')
    (M := 2 * kd) (kb := kstar)
    c.ha c.hy0 c.hyb c.hH c.hq2 c.hYdef c.ha0 c.ha1 c.continuous_Y c.continuous_y
    c.hYa c.abs_y_le_strip
    (fun t => by
      rw [show Real.sqrt (1 - (c.Y t) ^ 2) = Real.cos (modelSteering c.Y t) from
        (cos_modelSteering (Y := c.Y) (s := t)).symm]
      exact hasDerivAt_rearArclength c.continuous_dl t)
    c.hx
    (by rw [c.hx0]; simp [modelRearArclength, rearArclength])
    c.hid c.abs_Kstar_le c.hKderiv c.abs_Kstar'_le c.continuous_Kstar c.hbeta0 c.hbeta
    c.hk c.continuous_kH_sub_Kbar c.hKbar c.intervalIntegrable_puncturedSum
    c.intervalIntegrable_kH_sub c.intervalIntegrable_Kbar_sub
    c.rearArclength_period c.Ppos c.integrable_Kstar c.Kstar_nonneg c.abs_Kstar_le_exp
    c.rearArclength_left_nonpos c.rearArclength_right_nonneg c.hpB c.hqB c.hhalf
    c.continuous_yu c.hyu'c c.hyu0 c.hyub c.hDU c.hyu'b c.hau0 c.hau1 c.hYau
    c.hKstaru (fun _ => rfl) c.hPH
    hcc hpt hqt hLp hLq hevp hevq hΘp hΘq hF0 hΘ0 (by linarith)
    c.periodic_kH c.periodic_KP c.hasDerivAt_kH c.hd1 hbp hbq hkb
  simpa [matchConst] using h

/-! ### The estimate along the recursion of the pseudo-orbit -/

/-- **The defect estimate of the model pseudo-orbit in the marked metric.**  With
the separations fixed by the recursion `P(H_{n+1}) = H_n`, the `n`-th model and
the marked selected inverse of the `(n+1)`-st — whenever they are carried by two
aligned members of one tube — are at marked distance at most
`l1Modulus (2kd) (matchConst … · e^{−βH_{n+1}}) (H n) · L²(1 + kstar·L)`. -/
theorem dist_selInv_model_orbit {eps0 : ℕ → ℝ} {Hs : ℕ → ℝ}
    (cfg : ∀ n, Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd (eps0 n)
      (Hs (n + 1)) (Hs n))
    (hkd : 0 < kd) (n : ℕ)
    {cc kmin delta L : ℝ} {pt qt : Data} {Θp Θq : ℝ → ℝ}
    (hcc : 0 < cc)
    (hpt : IsTubeMember cc kmin delta pt) (hqt : IsTubeMember cc kmin delta qt)
    (hLp : perim pt = L) (hLq : perim qt = L)
    (hevp : ∀ s, HasDerivAt (ev pt) (Complex.exp (Complex.I * (Θp s : ℂ))) s)
    (hevq : ∀ s, HasDerivAt (ev qt) (Complex.exp (Complex.I * (Θq s : ℂ))) s)
    (hΘp : ∀ s, HasDerivAt Θp ((cfg n).kH s) s)
    (hΘq : ∀ s, HasDerivAt Θq (modelCurvature (cfg n).yu (cfg n).yu' (Hs n) s) s)
    (hF0 : ev pt 0 = ev qt 0) (hΘ0 : Θp 0 = Θq 0) :
    dist pt qt
      ≤ l1Modulus (2 * kd)
          (matchConst a C CK CU DU Km Kd au alpha beta B
            * Real.exp (-(beta * Hs (n + 1)))) (Hs n)
        * L ^ 2 * (1 + kstar * L) :=
  dist_le (cfg n) hkd hcc hpt hqt hLp hLq hevp hevq hΘp hΘq hF0 hΘ0

/-- **The marked defect tends to zero along the pseudo-orbit.**  As the
separations grow, the bound of `dist_selInv_model_orbit` tends to `0`, the
period `P` and the perimeter `L` being fixed. -/
theorem tendsto_markedDefect_zero {Cm L kstar kd Pp beta : ℝ} {Hs : ℕ → ℝ}
    (hbeta : 0 < beta)
    (hHs : Filter.Tendsto Hs Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n : ℕ => l1Modulus (2 * kd) (Cm * Real.exp (-(beta * Hs n))) Pp
        * L ^ 2 * (1 + kstar * L)) Filter.atTop (nhds 0) := by
  have hmul : Filter.Tendsto (fun x : ℝ => beta * x) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hbeta Filter.tendsto_id
  have hneg : Filter.Tendsto (fun x : ℝ => -(beta * x)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atBot_iff.mpr hmul
  have hline : Filter.Tendsto (fun x : ℝ => Real.exp (-(beta * x)))
      Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
  have hexp : Filter.Tendsto (fun n : ℕ => Cm * Real.exp (-(beta * Hs n)))
      Filter.atTop (nhds 0) := by
    have h := (hline.comp hHs).const_mul Cm
    simpa [Function.comp] using h
  have hmod : Filter.Tendsto
      (fun n : ℕ => l1Modulus (2 * kd) (Cm * Real.exp (-(beta * Hs n))) Pp)
      Filter.atTop (nhds 0) := by
    have hscale : Filter.Tendsto
        (fun n : ℕ => 2 * (2 * kd) * (Cm * Real.exp (-(beta * Hs n))))
        Filter.atTop (nhds 0) := by
      simpa using hexp.const_mul (2 * (2 * kd))
    have h1 : Filter.Tendsto
        (fun n : ℕ => Real.sqrt (2 * (2 * kd) * (Cm * Real.exp (-(beta * Hs n)))))
        Filter.atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hscale
      simpa [Function.comp] using h
    have h2 : Filter.Tendsto
        (fun n : ℕ => 4 * (Cm * Real.exp (-(beta * Hs n))) / Pp)
        Filter.atTop (nhds 0) := by
      have h := (hexp.const_mul 4).div_const Pp
      simpa using h
    have h := h1.max h2
    simpa [l1Modulus] using h
  simpa using (hmod.mul_const (L ^ 2)).mul_const (1 + kstar * L)

/-! ### Summability of the marked defects -/

/-- `√(exp (−βH)) = exp (−(β/2)H)`. -/
theorem sqrt_exp_neg (beta H : ℝ) :
    Real.sqrt (Real.exp (-(beta * H))) = Real.exp (-(beta / 2) * H) := by
  have hsq : (Real.exp (-(beta / 2) * H)) ^ 2 = Real.exp (-(beta * H)) := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]

/-- **The marked defect of one step, bounded by a single exponential.**  Both
branches of `l1Modulus` are dominated by `exp(−(β/2)H)`, the square root branch
exactly and the `L¹` branch because the period is bounded below. -/
theorem l1Modulus_le_exp {Cm kd P0 beta Pp H : ℝ} (hbeta : 0 ≤ beta)
    (hCm : 0 ≤ Cm) (hkd : 0 ≤ kd) (hP0 : 0 < P0) (hPp : P0 ≤ Pp) (hH : 0 ≤ H) :
    l1Modulus (2 * kd) (Cm * Real.exp (-(beta * H))) Pp
      ≤ (Real.sqrt (4 * kd * Cm) + 4 * Cm / P0) * Real.exp (-(beta / 2) * H) := by
  have hE : (0:ℝ) < Real.exp (-(beta * H)) := Real.exp_pos _
  have hE2 : (0:ℝ) < Real.exp (-(beta / 2) * H) := Real.exp_pos _
  have hsqrtc : 0 ≤ Real.sqrt (4 * kd * Cm) := Real.sqrt_nonneg _
  have hA : Real.sqrt (2 * (2 * kd) * (Cm * Real.exp (-(beta * H))))
      = Real.sqrt (4 * kd * Cm) * Real.exp (-(beta / 2) * H) := by
    have hrw : 2 * (2 * kd) * (Cm * Real.exp (-(beta * H)))
        = (4 * kd * Cm) * Real.exp (-(beta * H)) := by ring
    rw [hrw, Real.sqrt_mul (by positivity), sqrt_exp_neg]
  have hB : 4 * (Cm * Real.exp (-(beta * H))) / Pp
      ≤ (4 * Cm / P0) * Real.exp (-(beta / 2) * H) := by
    have h1 : Real.exp (-(beta * H)) ≤ Real.exp (-(beta / 2) * H) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : 4 * (Cm * Real.exp (-(beta * H))) / Pp
        ≤ 4 * (Cm * Real.exp (-(beta / 2) * H)) / P0 := by
      gcongr
    calc 4 * (Cm * Real.exp (-(beta * H))) / Pp
        ≤ 4 * (Cm * Real.exp (-(beta / 2) * H)) / P0 := h2
      _ = (4 * Cm / P0) * Real.exp (-(beta / 2) * H) := by ring
  refine max_le ?_ ?_
  · rw [hA]
    nlinarith [hE2.le, hsqrtc, div_nonneg (by positivity : (0:ℝ) ≤ 4 * Cm) hP0.le]
  · refine le_trans hB ?_
    nlinarith [hE2.le, hsqrtc]

/-- **The marked defects are summable along the pseudo-orbit.**  If the
separations grow at least linearly — as they do for the family of configurations
produced by the recursion — and stay above a positive threshold, then the
sequence of marked defect bounds is summable, which is exactly what the
shadowing scheme asks of its defect sequence. -/
theorem summable_markedDefect {Cm L kstar kd P0 H0 Delta beta : ℝ} {Hs : ℕ → ℝ}
    (hbeta : 0 < beta) (hDelta : 0 < Delta) (hCm : 0 ≤ Cm) (hkd : 0 ≤ kd)
    (hP0 : 0 < P0) (hPle : ∀ n, P0 ≤ Hs n)
    (hgrow : ∀ n : ℕ, H0 + n * Delta ≤ Hs n) :
    Summable (fun n : ℕ =>
      l1Modulus (2 * kd) (Cm * Real.exp (-(beta * Hs (n + 1)))) (Hs n)
        * L ^ 2 * (1 + kstar * L)) := by
  set q : ℝ := Real.exp (-(beta / 2) * Delta) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hqdef]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  set c0 : ℝ := Real.exp (-(beta / 2) * H0) with hc0def
  have hc0 : 0 < c0 := Real.exp_pos _
  set A : ℝ := Real.sqrt (4 * kd * Cm) + 4 * Cm / P0 with hAdef
  have hA0 : 0 ≤ A := by
    have : (0:ℝ) ≤ 4 * Cm / P0 := by positivity
    exact add_nonneg (Real.sqrt_nonneg _) this
  -- the exponential of the growing separations is dominated by a geometric series
  have hexp : ∀ n : ℕ, Real.exp (-(beta / 2) * Hs (n + 1)) ≤ c0 * q ^ n := by
    intro n
    have hstep : Real.exp (-(beta / 2) * Hs (n + 1))
        ≤ Real.exp (-(beta / 2) * (H0 + ((n : ℝ) + 1) * Delta)) := by
      refine Real.exp_le_exp.mpr ?_
      have := hgrow (n + 1)
      push_cast at this
      nlinarith
    have hval : Real.exp (-(beta / 2) * (H0 + ((n : ℝ) + 1) * Delta))
        = c0 * q ^ (n + 1) := by
      rw [hc0def, hqdef, ← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      ring_nf
    have hmono : c0 * q ^ (n + 1) ≤ c0 * q ^ n := by
      have : q ^ (n + 1) ≤ q ^ n := by
        rw [pow_succ]
        nlinarith [pow_nonneg hq0.le n, pow_pos hq0 n]
      exact mul_le_mul_of_nonneg_left this hc0.le
    exact le_trans hstep (le_trans (le_of_eq hval) hmono)
  -- the comparison series
  have hgeo : Summable (fun n : ℕ => A * (c0 * q ^ n)) :=
    ((summable_geometric_of_lt_one hq0.le hq1).mul_left c0).mul_left A
  have hmain : Summable (fun n : ℕ =>
      l1Modulus (2 * kd) (Cm * Real.exp (-(beta * Hs (n + 1)))) (Hs n)) := by
    refine hgeo.of_nonneg_of_le (fun n => l1Modulus_nonneg _ _ _) (fun n => ?_)
    have hH : (0:ℝ) ≤ Hs (n + 1) := le_trans hP0.le (hPle (n + 1))
    have h1 := l1Modulus_le_exp (Cm := Cm) (kd := kd) (P0 := P0) (beta := beta)
      (Pp := Hs n) (H := Hs (n + 1)) hbeta.le hCm hkd hP0 (hPle n) hH
    exact le_trans h1 (mul_le_mul_of_nonneg_left (hexp n) hA0)
  exact (hmain.mul_right (L ^ 2)).mul_right (1 + kstar * L)

end ModelOrbitDefectMarked
