import Mathlib
import UnitTangentIterates.ModelOrbitDefect
import UnitTangentIterates.PeriodizedPulseSmooth
import UnitTangentIterates.RearOwnHigherRegularity

/-!
# Smooth endpoint curvatures from a model-orbit configuration

`ModelOrbitDefect.Config` stores the first derivative of its current pulse and
the first two derivatives of its preceding-model pulse.  The shadowing
interpolation needs the corresponding two model curvatures to be `C³`.
This file supplies the missing bridge: callers provide only the remaining
finite derivative-chain tails and exponential majorants.  The strict steering
strip hypotheses are discharged from the bounds already carried by `Config`.
-/

noncomputable section

open Real
open scoped ContDiff

namespace ModelOrbitDefect.Config

open ModelOrbitDefect PeriodizedPulseSmooth

/-- A `C²` periodized steering pulse gives a `C²` rear curvature.  The only
nonlinear change of variable is the inverse rear arclength, whose derivative
is uniformly positive on the strict steering strip already stored by `c`. -/
theorem contDiff_two_kH_of_contDiff_Y
    (c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0
      kstar kd eps0 H P)
    (hY : ContDiff ℝ (2 : ℕ) c.Y) :
    ContDiff ℝ (2 : ℕ) c.kH := by
  have hdelta : ContDiff ℝ (2 : ℕ) (modelSteering c.Y) := by
    rw [contDiff_iff_contDiffAt]
    intro s
    have hne_neg : c.Y s ≠ -1 := by
      have hs := c.hYa s
      have ha := c.ha1
      intro heq
      rw [heq, abs_neg, abs_one] at hs
      linarith
    have hne_pos : c.Y s ≠ 1 := by
      have hs := c.hYa s
      have ha := c.ha1
      intro heq
      rw [heq, abs_one] at hs
      linarith
    exact (Real.contDiffAt_arcsin hne_neg hne_pos).comp s hY.contDiffAt
  let delta : ℝ → ℝ → ℝ := fun _ s => modelSteering c.Y s
  let sf : ℝ → ℝ → ℝ := fun _ z => c.sf z
  have hdelta_family : ContDiff ℝ (2 : ℕ) (Function.uncurry delta) := by
    simpa [delta, Function.uncurry] using hdelta.comp contDiff_snd
  have hsf_family : ContDiff ℝ (2 : ℕ) (Function.uncurry sf) := by
    exact RearOwnHigherRegularity.contDiff_sf (n := 1) (kh := a)
      c.ha0 c.ha1 hdelta_family
      (fun _ s => Real.arcsin_nonneg.mpr (c.Y_nonneg s))
      (fun _ s => Real.arcsin_le_arcsin
        ((le_abs_self (c.Y s)).trans (c.hYa s)))
      (fun _ z => c.sf_rightInverse z)
  have hsf : ContDiff ℝ (2 : ℕ) c.sf := by
    have hin : ContDiff ℝ (2 : ℕ) (fun z : ℝ => ((0 : ℝ), z)) :=
      contDiff_const.prodMk contDiff_id
    have h := hsf_family.comp hin
    simpa [sf, Function.uncurry] using h
  have hcomp : ContDiff ℝ (2 : ℕ) (fun z => c.Y (c.sf z)) := hY.comp hsf
  have heq : c.kH = fun z =>
      c.Y (c.sf z) / Real.sqrt (1 - c.Y (c.sf z) ^ 2) :=
    funext fun z => by rw [c.kH_eq, c.tan_dl]
  rw [heq]
  have hpos : ∀ z, 0 < 1 - c.Y (c.sf z) ^ 2 := by
    intro z
    have hs := c.hYa (c.sf z)
    have ha := c.ha1
    have habs : |c.Y (c.sf z)| < 1 := hs.trans_lt ha
    nlinarith [sq_abs (c.Y (c.sf z)), abs_nonneg (c.Y (c.sf z))]
  have hsqrt : ContDiff ℝ (2 : ℕ)
      (fun z => Real.sqrt (1 - c.Y (c.sf z) ^ 2)) :=
    (contDiff_const.sub (hcomp.pow 2)).sqrt (fun z => (hpos z).ne')
  exact hcomp.div hsqrt (fun z => (Real.sqrt_pos.mpr (hpos z)).ne')

/-- The same inverse-arclength argument at the order needed by the smooth
selected-rear construction. -/
theorem contDiff_three_kH_of_contDiff_Y
    (c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0
      kstar kd eps0 H P)
    (hY : ContDiff ℝ (3 : ℕ) c.Y) :
    ContDiff ℝ (3 : ℕ) c.kH := by
  have hdelta : ContDiff ℝ (3 : ℕ) (modelSteering c.Y) := by
    rw [contDiff_iff_contDiffAt]
    intro s
    have hne_neg : c.Y s ≠ -1 := by
      have hs := c.hYa s
      have ha := c.ha1
      intro heq
      rw [heq, abs_neg, abs_one] at hs
      linarith
    have hne_pos : c.Y s ≠ 1 := by
      have hs := c.hYa s
      have ha := c.ha1
      intro heq
      rw [heq, abs_one] at hs
      linarith
    exact (Real.contDiffAt_arcsin hne_neg hne_pos).comp s hY.contDiffAt
  let delta : ℝ → ℝ → ℝ := fun _ s => modelSteering c.Y s
  let sf : ℝ → ℝ → ℝ := fun _ z => c.sf z
  have hdelta_family : ContDiff ℝ (3 : ℕ) (Function.uncurry delta) := by
    simpa [delta, Function.uncurry] using hdelta.comp contDiff_snd
  have hsf_family : ContDiff ℝ (3 : ℕ) (Function.uncurry sf) := by
    exact RearOwnHigherRegularity.contDiff_sf (n := 2) (kh := a)
      c.ha0 c.ha1 hdelta_family
      (fun _ s => Real.arcsin_nonneg.mpr (c.Y_nonneg s))
      (fun _ s => Real.arcsin_le_arcsin
        ((le_abs_self (c.Y s)).trans (c.hYa s)))
      (fun _ z => c.sf_rightInverse z)
  have hsf : ContDiff ℝ (3 : ℕ) c.sf := by
    have hin : ContDiff ℝ (3 : ℕ) (fun z : ℝ => ((0 : ℝ), z)) :=
      contDiff_const.prodMk contDiff_id
    have h := hsf_family.comp hin
    simpa [sf, Function.uncurry] using h
  have hcomp : ContDiff ℝ (3 : ℕ) (fun z => c.Y (c.sf z)) := hY.comp hsf
  have heq : c.kH = fun z =>
      c.Y (c.sf z) / Real.sqrt (1 - c.Y (c.sf z) ^ 2) :=
    funext fun z => by rw [c.kH_eq, c.tan_dl]
  rw [heq]
  have hpos : ∀ z, 0 < 1 - c.Y (c.sf z) ^ 2 := by
    intro z
    have hs := c.hYa (c.sf z)
    have ha := c.ha1
    have habs : |c.Y (c.sf z)| < 1 := hs.trans_lt ha
    nlinarith [sq_abs (c.Y (c.sf z)), abs_nonneg (c.Y (c.sf z))]
  have hsqrt : ContDiff ℝ (3 : ℕ)
      (fun z => Real.sqrt (1 - c.Y (c.sf z) ^ 2)) :=
    (contDiff_const.sub (hcomp.pow 2)).sqrt (fun z => (hpos z).ne')
  exact hcomp.div hsqrt (fun z => (Real.sqrt_pos.mpr (hpos z)).ne')

/-- The two `C²` endpoint certificates for a configuration whose current pulse
and prior pulse are translates of one common three-step derivative chain. -/
theorem contDiff_two_endpoints_of_common_pulse
    (c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0
      kstar kd eps0 H P)
    {y y1 y2 y3 : ℝ → ℝ} {q gamma Cjet : ℝ}
    (hgamma : 0 < gamma) (hCjet : 0 ≤ Cjet)
    (hy01 : ∀ s, HasDerivAt y (y1 s) s)
    (hy12 : ∀ s, HasDerivAt y1 (y2 s) s)
    (hy23 : ∀ s, HasDerivAt y2 (y3 s) s)
    (hy3c : Continuous y3)
    (hyb0 : ∀ s, |y s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hyb1 : ∀ s, |y1 s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hyb2 : ∀ s, |y2 s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hyb3 : ∀ s, |y3 s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hcy : c.y = y)
    (hcyu : c.yu = fun s => y (s - q))
    (hcyu1 : c.yu' = fun s => y1 (s - q)) :
    ContDiff ℝ (2 : ℕ) (modelCurvature c.yu c.yu' P) ∧
      ContDiff ℝ (2 : ℕ) c.kH := by
  have periodized_two
      {z0 z1 z2 : ℝ → ℝ} {L C0 : ℝ}
      (hL : 0 < L)
      (hz01 : ∀ s, HasDerivAt z0 (z1 s) s)
      (hz12 : ∀ s, HasDerivAt z1 (z2 s) s)
      (hz2c : Continuous z2)
      (hzb0 : ∀ s, |z0 s| ≤ C0 * Real.exp (-gamma * |s|))
      (hzb1 : ∀ s, |z1 s| ≤ C0 * Real.exp (-gamma * |s|))
      (hzb2 : ∀ s, |z2 s| ≤ C0 * Real.exp (-gamma * |s|)) :
      ContDiff ℝ (2 : ℕ) (periodizedPulse z0 L) := by
    have hZ2 : ContDiff ℝ (0 : ℕ) (periodizedPulse z2 L) :=
      contDiff_zero_periodizedPulse hgamma hL hz2c hzb2
    have hZ1 : ContDiff ℝ (1 : ℕ) (periodizedPulse z1 L) := by
      simpa using contDiff_succ_periodizedPulse hgamma hL hz12 hzb1 hzb2 hZ2
    simpa using contDiff_succ_periodizedPulse hgamma hL hz01 hzb0 hzb1 hZ1
  have hY : ContDiff ℝ (2 : ℕ) (periodizedPulse y H) :=
    periodized_two c.hH hy01 hy12
      (Differentiable.continuous fun s => (hy23 s).differentiableAt)
      hyb0 hyb1 hyb2
  let u0 : ℝ → ℝ := fun s => y (s - q)
  let u1 : ℝ → ℝ := fun s => y1 (s - q)
  let u2 : ℝ → ℝ := fun s => y2 (s - q)
  let u3 : ℝ → ℝ := fun s => y3 (s - q)
  have hu01 : ∀ s, HasDerivAt u0 (u1 s) s := fun s => by
    simpa [u0, u1] using
      (hy01 (s - q)).comp s ((hasDerivAt_id s).sub_const q)
  have hu12 : ∀ s, HasDerivAt u1 (u2 s) s := fun s => by
    simpa [u1, u2] using
      (hy12 (s - q)).comp s ((hasDerivAt_id s).sub_const q)
  have hu23 : ∀ s, HasDerivAt u2 (u3 s) s := fun s => by
    simpa [u2, u3] using
      (hy23 (s - q)).comp s ((hasDerivAt_id s).sub_const q)
  have hexp : ∀ s, Real.exp (-gamma * |s - q|) ≤
      Real.exp (gamma * |q|) * Real.exp (-gamma * |s|) := by
    intro s
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have habs : |s| ≤ |s - q| + |q| := by
      calc
        |s| = |(s - q) + q| := by ring_nf
        _ ≤ |s - q| + |q| := abs_add_le _ _
    nlinarith [mul_nonneg hgamma.le (abs_nonneg (s - q)),
      mul_nonneg hgamma.le (abs_nonneg s), mul_nonneg hgamma.le (abs_nonneg q)]
  have shifted_bound (j : ℝ → ℝ)
      (hj : ∀ s, |j s| ≤ Cjet * Real.exp (-gamma * |s|)) :
      ∀ s, |j (s - q)| ≤
        (Cjet * Real.exp (gamma * |q|)) * Real.exp (-gamma * |s|) := by
    intro s
    exact (hj (s - q)).trans (by
      calc
        Cjet * Real.exp (-gamma * |s - q|) ≤
            Cjet * (Real.exp (gamma * |q|) * Real.exp (-gamma * |s|)) :=
          mul_le_mul_of_nonneg_left (hexp s) hCjet
        _ = (Cjet * Real.exp (gamma * |q|)) * Real.exp (-gamma * |s|) := by ring)
  have hu0b := shifted_bound y hyb0
  have hu1b := shifted_bound y1 hyb1
  have hu2b := shifted_bound y2 hyb2
  have hu3b := shifted_bound y3 hyb3
  have hU0 : ContDiff ℝ (2 : ℕ) (periodizedPulse u0 P) :=
    periodized_two (C0 := Cjet * Real.exp (gamma * |q|)) c.Ppos hu01 hu12
      (Differentiable.continuous fun s => (hu23 s).differentiableAt) hu0b hu1b hu2b
  have hU1 : ContDiff ℝ (2 : ℕ) (periodizedPulse u1 P) :=
    periodized_two (C0 := Cjet * Real.exp (gamma * |q|)) c.Ppos hu12 hu23
      (hy3c.comp (continuous_id.sub continuous_const)) hu1b hu2b hu3b
  have hstripu : ∀ s, |periodizedPulse u0 P s| < 1 := by
    intro s
    have hnonneg : 0 ≤ periodizedPulse c.yu P s := by
      exact tsum_nonneg fun m => c.hyu0 (s - m * P)
    have hle : periodizedPulse c.yu P s ≤ au := c.hYau s
    rw [hcyu] at hnonneg hle
    rw [abs_of_nonneg hnonneg] at *
    simpa [u0] using lt_of_le_of_lt hle c.hau1
  constructor
  · rw [hcyu, hcyu1]
    exact ModelCurvatureSmooth.contDiff_modelCurvature_of_periodized hU0 hU1 hstripu
  · apply contDiff_two_kH_of_contDiff_Y c
    simpa [ModelOrbitDefect.Config.Y, hcy] using hY

/-- A five-member exponentially decaying derivative chain gives the `C³`
prior model curvature and the `C³` selected rear curvature of the current
model.  Translation of the common pulse is handled internally. -/
theorem contDiff_three_endpoints_of_common_pulse
    (c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0
      kstar kd eps0 H P)
    {y y1 y2 y3 y4 : ℝ → ℝ} {q gamma Cjet : ℝ}
    (hgamma : 0 < gamma) (hCjet : 0 ≤ Cjet)
    (hy01 : ∀ s, HasDerivAt y (y1 s) s)
    (hy12 : ∀ s, HasDerivAt y1 (y2 s) s)
    (hy23 : ∀ s, HasDerivAt y2 (y3 s) s)
    (hy34 : ∀ s, HasDerivAt y3 (y4 s) s)
    (hy3c : Continuous y3) (hy4c : Continuous y4)
    (hyb0 : ∀ s, |y s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hyb1 : ∀ s, |y1 s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hyb2 : ∀ s, |y2 s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hyb3 : ∀ s, |y3 s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hyb4 : ∀ s, |y4 s| ≤ Cjet * Real.exp (-gamma * |s|))
    (hcy : c.y = y)
    (hcyu : c.yu = fun s => y (s - q))
    (hcyu1 : c.yu' = fun s => y1 (s - q)) :
    ContDiff ℝ (3 : ℕ) (modelCurvature c.yu c.yu' P) ∧
      ContDiff ℝ (3 : ℕ) c.kH := by
  have hY : ContDiff ℝ (3 : ℕ) (periodizedPulse y H) :=
    PeriodizedPulseSmooth.contDiff_three_periodizedPulse hgamma c.hH
      hy01 hy12 hy23 hy3c hyb0 hyb1 hyb2 hyb3
  have hkH : ContDiff ℝ (3 : ℕ) c.kH := by
    apply contDiff_three_kH_of_contDiff_Y c
    simpa [ModelOrbitDefect.Config.Y, hcy] using hY
  let u0 : ℝ → ℝ := fun s => y (s - q)
  let u1 : ℝ → ℝ := fun s => y1 (s - q)
  let u2 : ℝ → ℝ := fun s => y2 (s - q)
  let u3 : ℝ → ℝ := fun s => y3 (s - q)
  let u4 : ℝ → ℝ := fun s => y4 (s - q)
  have hu01 : ∀ s, HasDerivAt u0 (u1 s) s := fun s => by
    simpa [u0, u1] using
      (hy01 (s - q)).comp s ((hasDerivAt_id s).sub_const q)
  have hu12 : ∀ s, HasDerivAt u1 (u2 s) s := fun s => by
    simpa [u1, u2] using
      (hy12 (s - q)).comp s ((hasDerivAt_id s).sub_const q)
  have hu23 : ∀ s, HasDerivAt u2 (u3 s) s := fun s => by
    simpa [u2, u3] using
      (hy23 (s - q)).comp s ((hasDerivAt_id s).sub_const q)
  have hu34 : ∀ s, HasDerivAt u3 (u4 s) s := fun s => by
    simpa [u3, u4] using
      (hy34 (s - q)).comp s ((hasDerivAt_id s).sub_const q)
  have hu3c : Continuous u3 := hy3c.comp (continuous_id.sub continuous_const)
  have hu4c : Continuous u4 := hy4c.comp (continuous_id.sub continuous_const)
  have hexp : ∀ s, Real.exp (-gamma * |s - q|) ≤
      Real.exp (gamma * |q|) * Real.exp (-gamma * |s|) := by
    intro s
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have habs : |s| ≤ |s - q| + |q| := by
      calc
        |s| = |(s - q) + q| := by ring_nf
        _ ≤ |s - q| + |q| := abs_add_le _ _
    nlinarith [mul_nonneg hgamma.le (abs_nonneg (s - q)),
      mul_nonneg hgamma.le (abs_nonneg s), mul_nonneg hgamma.le (abs_nonneg q)]
  have shifted_bound (j : ℝ → ℝ)
      (hj : ∀ s, |j s| ≤ Cjet * Real.exp (-gamma * |s|)) :
      ∀ s, |j (s - q)| ≤
        (Cjet * Real.exp (gamma * |q|)) * Real.exp (-gamma * |s|) := by
    intro s
    exact (hj (s - q)).trans (by
      calc
        Cjet * Real.exp (-gamma * |s - q|) ≤
            Cjet * (Real.exp (gamma * |q|) * Real.exp (-gamma * |s|)) :=
          mul_le_mul_of_nonneg_left (hexp s) hCjet
        _ = (Cjet * Real.exp (gamma * |q|)) * Real.exp (-gamma * |s|) := by ring)
  have hu0b := shifted_bound y hyb0
  have hu1b := shifted_bound y1 hyb1
  have hu2b := shifted_bound y2 hyb2
  have hu3b := shifted_bound y3 hyb3
  have hu4b := shifted_bound y4 hyb4
  have hstripu : ∀ s, |periodizedPulse u0 P s| < 1 := by
    intro s
    have hnonneg : 0 ≤ periodizedPulse c.yu P s := by
      exact tsum_nonneg fun m => c.hyu0 (s - m * P)
    have hle : periodizedPulse c.yu P s ≤ au := c.hYau s
    rw [hcyu] at hnonneg hle
    rw [abs_of_nonneg hnonneg] at *
    simpa [u0] using lt_of_le_of_lt hle c.hau1
  have hprior : ContDiff ℝ (3 : ℕ) (modelCurvature u0 u1 P) :=
    PeriodizedPulseSmooth.contDiff_three_modelCurvature_of_derivative_chain
      hgamma c.Ppos hu01 hu12 hu23 hu34 hu3c hu4c
      hu0b hu1b hu2b hu3b hu4b hstripu
  constructor
  · simpa [hcyu, hcyu1, u0, u1] using hprior
  · exact hkH

variable {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P : ℝ}

/-- The two endpoint model curvatures in a configured model-orbit step are
`C³` once the stored pulse derivatives are extended to finite five-member
exponentially decaying derivative chains. -/
theorem contDiff_three_modelCurvatures_of_derivative_chains
    (c : ModelOrbitDefect.Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0
      kstar kd eps0 H P)
    {ydd y3 y4 yu3 yu4 : ℝ → ℝ} {Cy Cu : ℝ}
    (hy12 : ∀ x, HasDerivAt c.yd (ydd x) x)
    (hy23 : ∀ x, HasDerivAt ydd (y3 x) x)
    (hy34 : ∀ x, HasDerivAt y3 (y4 x) x)
    (hy4c : Continuous y4)
    (hyb0 : ∀ x, |c.y x| ≤ Cy * Real.exp (-alpha * |x|))
    (hyb1 : ∀ x, |c.yd x| ≤ Cy * Real.exp (-alpha * |x|))
    (hyb2 : ∀ x, |ydd x| ≤ Cy * Real.exp (-alpha * |x|))
    (hyb3 : ∀ x, |y3 x| ≤ Cy * Real.exp (-alpha * |x|))
    (hyb4 : ∀ x, |y4 x| ≤ Cy * Real.exp (-alpha * |x|))
    (hyu23 : ∀ x, HasDerivAt c.yu'' (yu3 x) x)
    (hyu34 : ∀ x, HasDerivAt yu3 (yu4 x) x)
    (hyu4c : Continuous yu4)
    (hyub0 : ∀ x, |c.yu x| ≤ Cu * Real.exp (-alpha * |x|))
    (hyub1 : ∀ x, |c.yu' x| ≤ Cu * Real.exp (-alpha * |x|))
    (hyub2 : ∀ x, |c.yu'' x| ≤ Cu * Real.exp (-alpha * |x|))
    (hyub3 : ∀ x, |yu3 x| ≤ Cu * Real.exp (-alpha * |x|))
    (hyub4 : ∀ x, |yu4 x| ≤ Cu * Real.exp (-alpha * |x|)) :
    ContDiff ℝ (3 : ℕ) (modelCurvature c.y c.yd H) ∧
      ContDiff ℝ (3 : ℕ) (modelCurvature c.yu c.yu' P) := by
  have hstrip : ∀ s, |periodizedPulse c.y H s| < 1 := fun s =>
    lt_of_le_of_lt (c.hYa s) c.ha1
  have hstripu : ∀ s, |periodizedPulse c.yu P s| < 1 := by
    intro s
    have hnonneg : 0 ≤ periodizedPulse c.yu P s := by
      exact tsum_nonneg fun m => c.hyu0 (s - m * P)
    rw [abs_of_nonneg hnonneg]
    exact lt_of_le_of_lt (c.hYau s) c.hau1
  constructor
  · exact contDiff_three_modelCurvature_of_derivative_chain c.ha c.hH
      c.hyderiv hy12 hy23 hy34
      (Differentiable.continuous fun x => (hy34 x).differentiableAt) hy4c
      hyb0 hyb1 hyb2 hyb3 hyb4 hstrip
  · exact contDiff_three_modelCurvature_of_derivative_chain c.ha c.Ppos
      c.hyuderiv c.hyu''deriv hyu23 hyu34
      (Differentiable.continuous fun x => (hyu34 x).differentiableAt) hyu4c
      hyub0 hyub1 hyub2 hyub3 hyub4 hstripu

end ModelOrbitDefect.Config
