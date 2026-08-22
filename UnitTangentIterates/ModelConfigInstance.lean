import Mathlib
import UnitTangentIterates.ModelOrbitDefect
import UnitTangentIterates.SechHairpinCurvature
import UnitTangentIterates.PulseFromCurvature
import UnitTangentIterates.PeriodizationSup

/-!
# A matching configuration exists

`ModelOrbitDefect.Config` packages the whole hypothesis block of the defect
estimate of the model pseudo-orbit of *A Noncircular Oval with Convex
Unit-Tangent Iterates*: the steering pulse `y` of the isolated pair and the
steering pulse `y_u` of the previous model, with their decay, their relative
derivative bounds, their masses `π`, the strip bounds for their periodizations,
the matching identity `y = √(1-y²)·K_*(x)` of the isolated pair, the rear period
of the configuration and the inequalities fixing the constants of the estimate.

Nothing so far checked that this block is **jointly satisfiable**.  This file
does: the explicit pulse `y_u = A·sech²(λ·)` with `A = πλ/2` (so that
`∫ y_u = π`) has an isolated curvature `K_* = y_u + G(y_u)y_u'`
(`SechHairpinCurvature.lean`), and the steering pulse of the isolated pair with
that rear curvature is produced by `PulseFromCurvature.lean`; the two together
satisfy every field of `Config`, for every separation `H` beyond an explicit
threshold.

Main results:

* `exists_config` — a configuration exists for every `0 < λ ≤ 1/100` and every
  separation `H` with `e^{-λH/8} ≤ 1/8`;
* `nonempty_config` — a concrete one, with `λ = 1/100` and `H = 3200`;
* `exists_config_pathDistRigid_le` — hence the defect estimate of
  `ModelOrbitDefect` is not vacuous.

The configuration built here is *not* the one of the paper: its isolated pair is
the explicit pulse above, not the hairpin translator.  It shows that the
hypothesis block is consistent, not that the paper's hairpin satisfies it.
-/

noncomputable section

open Real MeasureTheory Filter Topology Set

namespace ModelConfigInstance

open ModelOrbitDefect FrontPeriodization SechHairpin MarkedSpace PathMetric
open CurvatureInterpolation RearTrack TwoCapPairsAssembly
open InterpolationPathDistSummable MarkedRigid

variable {lam H : ℝ}

/-- The decay rate of the constructed pulse of the isolated pair. -/
def rate (lam : ℝ) : ℝ := 2 * lam / Real.sqrt (1 + (2 * amp lam) ^ 2)

theorem sqrt_le_two (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) :
    Real.sqrt (1 + (2 * amp lam) ^ 2) ≤ 2 := by
  have hA := amp_le hlam hlam'
  have hA0 := amp_nonneg hlam
  have h : 1 + (2 * amp lam) ^ 2 ≤ 4 := by nlinarith
  calc Real.sqrt (1 + (2 * amp lam) ^ 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h
    _ = 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem one_le_sqrt' : (1:ℝ) ≤ Real.sqrt (1 + (2 * amp lam) ^ 2) := by
  have h : (1:ℝ) ≤ 1 + (2 * amp lam) ^ 2 := by nlinarith [sq_nonneg (2 * amp lam)]
  calc (1:ℝ) = Real.sqrt 1 := by simp
    _ ≤ _ := Real.sqrt_le_sqrt h

theorem rate_ge (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) : lam ≤ rate lam := by
  have h2 := sqrt_le_two hlam hlam'
  have h1 : (0:ℝ) < Real.sqrt (1 + (2 * amp lam) ^ 2) :=
    lt_of_lt_of_le one_pos one_le_sqrt'
  rw [rate, le_div_iff₀ h1]
  nlinarith [hlam.le]

theorem rate_le (hlam : 0 < lam) : rate lam ≤ 2 * lam := by
  have h1 : (1:ℝ) ≤ Real.sqrt (1 + (2 * amp lam) ^ 2) := one_le_sqrt'
  have h0 : (0:ℝ) < Real.sqrt (1 + (2 * amp lam) ^ 2) := lt_of_lt_of_le one_pos h1
  rw [rate, div_le_iff₀ h0]
  nlinarith [hlam.le]

theorem rate_pos (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) : 0 < rate lam :=
  lt_of_lt_of_le hlam (rate_ge hlam hlam')

/-- `1 - √(1-z²) ≤ z²`. -/
theorem one_sub_sqrt_le_sq {z : ℝ} (hz : z ^ 2 ≤ 1) :
    1 - Real.sqrt (1 - z ^ 2) ≤ z ^ 2 := by
  have h0 : (0:ℝ) ≤ 1 - z ^ 2 := by linarith
  have hsq : Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt h0
  have hle1 : Real.sqrt (1 - z ^ 2) ≤ 1 := by
    nlinarith [Real.sqrt_nonneg (1 - z ^ 2)]
  nlinarith [Real.sqrt_nonneg (1 - z ^ 2)]

set_option maxHeartbeats 6400000 in
/-- **Every separation gives a matching configuration, from one pulse of the
isolated pair.**  The constants are produced once and for all — they depend on
`λ` alone — and the configuration of separation `H` has for rear period the rear
arclength of one front period of the periodized pulse. -/
theorem exists_config_of_pulse (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (theta0 : ℝ)
    (y yd x : ℝ → ℝ)
    (hy0 : ∀ s, 0 ≤ y s) (hyKm : ∀ s, y s ≤ 2 * amp lam)
    (hyc : Continuous y) (hydc : Continuous yd)
    (hyderiv : ∀ s, HasDerivAt y (yd s) s)
    (hyb : ∀ s, y s ≤ 8 * amp lam * Real.exp (-rate lam * |s|))
    (hydb : ∀ s, |yd s| ≤ 12 * lam * amp lam * Real.exp (-rate lam * |s|))
    (hrelD : ∀ s, |yd s| ≤ 6 * lam * y s)
    (hxint : ∀ t, (∫ u in (0:ℝ)..t, Real.sqrt (1 - y u ^ 2)) = x t)
    (hidx : ∀ t, y t = Real.sqrt (1 - y t ^ 2) * curv lam (x t))
    (hyint : Integrable y) (hymass : (∫ s, y s) = ∫ u, curv lam u) :
    ∃ alpha beta a au C CU CK DU DU2 D Km Kd B kstar kd : ℝ,
      ∀ H : ℝ, 0 < H → Real.exp (-(lam / 8) * H) ≤ 1 / 8 →
        (∀ s, |periodizedPulse y H s| ≤ 1 / 2) ∧
        H / 2 ≤ modelRearArclength (periodizedPulse y H) H ∧
        Nonempty (Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd
          (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * H)))
          H (modelRearArclength (periodizedPulse y H) H)) := by
  -- the explicit amplitude and the constants of the estimate
  set A : ℝ := amp lam with hAdef
  have hA0 : 0 < A := amp_pos hlam
  have hA50 : A ≤ 1 / 50 := amp_le hlam hlam'
  set alpha : ℝ := rate lam with halphadef
  have halpha0 : 0 < alpha := rate_pos hlam hlam'
  have halphage : lam ≤ alpha := rate_ge hlam hlam'
  have halphale : alpha ≤ 2 * lam := rate_le hlam
  set a : ℝ := 1 / 2 with hadef
  set au : ℝ := 1 / 4 with haudef
  set DU : ℝ := 2 * lam with hDUdef
  set DU2 : ℝ := 8 * lam ^ 2 with hDU2def
  set D : ℝ := 6 * lam with hDdef
  set C : ℝ := 8 * A with hCdef
  set CU : ℝ := 4 * A with hCUdef
  set beta : ℝ := alpha / 4 with hbetadef
  set B : ℝ := 2 with hBdef
  have hGau : G au ≤ 2 := G_le_two (by norm_num) (by norm_num)
  have hGau0 : 0 ≤ G au := by rw [G]; positivity
  have hGa0 : 0 ≤ G a := by rw [G]; positivity
  have hlip0 : 0 ≤ lipConst au := by
    rw [lipConst]
    have h1 : (0:ℝ) < 1 - au ^ 2 := by rw [haudef]; norm_num
    have h2 : (0:ℝ) < Real.sqrt (1 - au ^ 2) := Real.sqrt_pos.mpr h1
    positivity
  set Km : ℝ := (1 + G au * DU) * au with hKmdef
  set CK : ℝ := (1 + G au * DU) * CU with hCKdef
  set Kd : ℝ := DU * au + lipConst au * (DU ^ 2 * au ^ 2) + G au * (DU2 * au) with hKddef
  have hKd0 : 0 ≤ Kd := by
    have : (0:ℝ) ≤ DU := by rw [hDUdef]; positivity
    have h2 : (0:ℝ) ≤ DU2 := by rw [hDU2def]; positivity
    rw [hKddef]
    have : (0:ℝ) ≤ au := by norm_num
    positivity
  set kstar : ℝ := (1 + G au * DU) * au + a / Real.sqrt (1 - a ^ 2) with hkstardef
  set kd : ℝ := Kd + ((1 + G a * D) * a + a) / Real.sqrt (1 - a ^ 2) ^ 3 + 1 with hkddef
  have hsqrt_a : (0:ℝ) < Real.sqrt (1 - a ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    rw [hadef]; norm_num
  have hkstar_split : 0 ≤ a / Real.sqrt (1 - a ^ 2) := by
    apply div_nonneg (by norm_num) hsqrt_a.le
  have hkd_split : 0 ≤ ((1 + G a * D) * a + a) / Real.sqrt (1 - a ^ 2) ^ 3 := by
    have hnum : (0:ℝ) ≤ (1 + G a * D) * a + a := by
      have : (0:ℝ) ≤ G a * D := by
        have : (0:ℝ) ≤ D := by rw [hDdef]; positivity
        positivity
      rw [hadef]; nlinarith
    positivity
  -- the pulse of the isolated pair sees the isolated curvature at its rear arclength
  have hxeq : ∀ t, modelRearArclength y t = x t := by
    intro t
    have : modelRearArclength y t = ∫ u in (0:ℝ)..t, Real.sqrt (1 - y u ^ 2) := by
      rw [modelRearArclength, RearTrack.rearArclength]
      refine intervalIntegral.integral_congr fun u _ => ?_
      exact cos_modelSteering (Y := y) (s := u)
    rw [this, hxint t]
  refine ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, ?_⟩
  intro H hH hHbig
  -- the exponential thresholds
  have hexp_mono : ∀ c : ℝ, lam / 8 ≤ c → Real.exp (-c * H) ≤ 1 / 8 := by
    intro c hc
    refine le_trans (Real.exp_le_exp.mpr ?_) hHbig
    nlinarith [hH.le]
  have hq2 : Real.exp (-alpha * H) ≤ 1 / 2 := by
    have := hexp_mono alpha (by linarith)
    linarith
  -- the strip bound for the periodization of the pulse of the isolated pair
  have hyabs : ∀ s, |y s| ≤ C * Real.exp (-alpha * |s|) := fun s => by
    rw [abs_of_nonneg (hy0 s)]; exact hyb s
  have hYa : ∀ s : ℝ, (∑' m : ℤ, y (s - m * H)) ≤ 2 * A + 4 * C *
      Real.exp (-(alpha / 2) * H) :=
    fun s => PeriodizationSup.periodization_le_of_sup halpha0 hH hq2 hy0 hyb hyKm s
  have hhalfexp : Real.exp (-(alpha / 2) * H) ≤ 1 / 8 := hexp_mono (alpha / 2) (by linarith)
  have hYa' : ∀ s : ℝ, |(∑' m : ℤ, y (s - m * H))| ≤ 1 / 2 := by
    intro s
    have hnn : 0 ≤ ∑' m : ℤ, y (s - m * H) := tsum_nonneg fun m => hy0 _
    rw [abs_of_nonneg hnn]
    have h1 := hYa s
    have h2 : 4 * C * Real.exp (-(alpha / 2) * H) ≤ 4 * C * (1 / 8) := by
      have : (0:ℝ) ≤ 4 * C := by rw [hCdef]; positivity
      nlinarith
    rw [hCdef] at h1 h2
    linarith [hA50]
  -- the rear speed of the configuration
  set Y : ℝ → ℝ := periodizedPulse y H with hYdef
  have hYcont : Continuous Y :=
    PeriodizedTurning.continuous_periodization (alpha := alpha) (P := H) (C := C)
      halpha0 hH hyc hyabs
  have hYle : ∀ s, |Y s| ≤ 1 / 2 := hYa'
  have hcos_ge : ∀ s, (1:ℝ) / 2 ≤ Real.cos (modelSteering Y s) := by
    intro s
    rw [cos_modelSteering]
    have h := abs_le.mp (hYle s)
    have h1 : (1:ℝ) / 4 ≤ 1 - Y s ^ 2 := by nlinarith
    calc (1:ℝ) / 2 = Real.sqrt (1 / 4) := by
          rw [show (1:ℝ)/4 = (1/2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hsteercont : Continuous (modelSteering Y) := continuous_modelSteering hYcont
  have hrear : ∀ t, HasDerivAt (modelRearArclength Y) (Real.cos (modelSteering Y t)) t :=
    fun t => RearTrack.hasDerivAt_rearArclength hsteercont t
  have hrear0 : modelRearArclength Y 0 = 0 := by
    simp [modelRearArclength, RearTrack.rearArclength]
  -- the rear period
  set P : ℝ := modelRearArclength Y H with hPdef
  have hPge : H / 2 ≤ P := by
    have := ArclengthInverse.rearArclength_ge (δ := modelSteering Y) (c := 1/2)
      hsteercont hcos_ge (P := H) hH.le
    rw [hPdef]
    simpa [modelRearArclength] using by linarith [this]
  have hPle : P ≤ H := by
    have := ArclengthInverse.rearArclength_le_of_period (δ := modelSteering Y) hsteercont hH.le
    rw [hPdef]
    exact this
  have hPpos : 0 < P := lt_of_lt_of_le (by linarith) hPge
  -- the perimeter defect over any interval shorter than one period is at most `π/2`
  have hY0' : ∀ s, 0 ≤ Y s := fun s => tsum_nonneg fun m => hy0 _
  have hmassy : (∫ s, y s) = Real.pi := by rw [hymass]; exact integral_curv hlam hlam'
  have hYmass : ∀ c : ℝ, (∫ u in c..(c + H), Y u) = Real.pi := fun c => by
    have h := PeriodizedTurning.integral_periodization_eq_integral (y := y) (P := H)
      hH hyint hy0 c
    rw [hmassy] at h
    exact h
  have hcosc : Continuous fun s => Real.cos (modelSteering Y s) :=
    Real.continuous_cos.comp hsteercont
  have hdefect : ∀ c d : ℝ, c ≤ d → d ≤ c + H →
      (∫ s in c..d, (1 - Real.cos (modelSteering Y s))) ≤ Real.pi / 2 := by
    intro c d hcd hdc
    have hcont : Continuous fun s => 1 - Real.cos (modelSteering Y s) :=
      continuous_const.sub hcosc
    have hnn : ∀ s, 0 ≤ 1 - Real.cos (modelSteering Y s) := fun s => by
      have := Real.cos_le_one (modelSteering Y s); linarith
    have hsplit : ((∫ s in c..d, (1 - Real.cos (modelSteering Y s)))
        + ∫ s in d..(c + H), (1 - Real.cos (modelSteering Y s)))
        = ∫ s in c..(c + H), (1 - Real.cos (modelSteering Y s)) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) c d)
        (hcont.intervalIntegrable (μ := volume) d (c + H))
    have hpos : 0 ≤ ∫ s in d..(c + H), (1 - Real.cos (modelSteering Y s)) :=
      intervalIntegral.integral_nonneg hdc (fun s _ => hnn s)
    have hstep2 : (∫ s in c..(c + H), (1 - Real.cos (modelSteering Y s)))
        ≤ ∫ s in c..(c + H), (1 / 2) * Y s := by
      refine intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
        ((continuous_const.mul hYcont).intervalIntegrable _ _) (fun s _ => ?_)
      rw [cos_modelSteering]
      have h1 := hY0' s
      have h2 := abs_le.mp (hYle s)
      have h3 : 1 - Real.sqrt (1 - Y s ^ 2) ≤ Y s ^ 2 := one_sub_sqrt_le_sq (by nlinarith)
      nlinarith
    have hstep3 : (∫ s in c..(c + H), (1 / 2) * Y s) = Real.pi / 2 := by
      rw [intervalIntegral.integral_const_mul, hYmass c]; ring
    linarith
  -- hence the rear period is within `π/2` of the front period
  have hPlow : H - Real.pi / 2 ≤ P := by
    have h1 := hdefect 0 H hH.le (by linarith)
    have h2 : (∫ s in (0:ℝ)..H, (1 - Real.cos (modelSteering Y s))) = H - P := by
      rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
        (hcosc.intervalIntegrable _ _), intervalIntegral.integral_const]
      simp [hPdef, modelRearArclength, RearTrack.rearArclength]
    linarith
  -- the endpoint of the cell
  have hmid_ge : -(H / 2) ≤ modelRearArclength Y (-(H / 2)) := by
    have := PulseFromCurvature.ge_of_deriv_le (f := modelRearArclength Y)
      (g := fun t => Real.cos (modelSteering Y t)) (c := 1) hrear
      (fun s => Real.cos_le_one _) (s := -(H/2)) (by linarith)
    rw [hrear0] at this
    linarith
  have hmid_hi : modelRearArclength Y (-(H / 2)) ≤ -(H / 2) + Real.pi / 2 := by
    have h1 := hdefect (-(H / 2)) 0 (by linarith) (by linarith)
    have h2 : (∫ s in (-(H / 2))..(0:ℝ), (1 - Real.cos (modelSteering Y s)))
        = H / 2 + modelRearArclength Y (-(H / 2)) := by
      have hsym : modelRearArclength Y (-(H / 2))
          = -∫ x in (-(H / 2))..(0:ℝ), Real.cos (modelSteering Y x) := by
        simp only [modelRearArclength, RearTrack.rearArclength]
        exact intervalIntegral.integral_symm _ _
      rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
        (hcosc.intervalIntegrable _ _), intervalIntegral.integral_const, hsym]
      simp only [smul_eq_mul, mul_one]
      ring
    linarith
  -- the strip bound for the periodization of the pulse of the previous model
  have hqP : Real.exp (-(2 * lam) * P) ≤ 1 / 2 := by
    have h1 : Real.exp (-(2 * lam) * P) ≤ Real.exp (-(lam / 8) * H) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hlam.le, hPge, hH.le]
    linarith
  have hYau : ∀ u : ℝ, (∑' m : ℤ, pul lam (u - m * P)) ≤ 1 / 4 := by
    intro u
    have hsup := PeriodizationSup.periodization_le_of_sup (alpha := 2 * lam) (P := P)
      (C := 4 * A) (b := A) (by positivity) hPpos hqP (fun s => pul_nonneg hlam s)
      (fun s => pul_le_exp hlam s) (fun s => pul_le_amp hlam s) u
    have hexpP : Real.exp (-(2 * lam / 2) * P) ≤ 1 / 8 := by
      have h1 : Real.exp (-(2 * lam / 2) * P) ≤ Real.exp (-(lam / 8) * H) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hlam.le, hPge, hH.le]
      linarith
    have h2 : 4 * (4 * A) * Real.exp (-(2 * lam / 2) * P) ≤ 4 * (4 * A) * (1 / 8) := by
      have hnn : (0:ℝ) ≤ 4 * (4 * A) := by positivity
      nlinarith
    linarith
  refine ⟨hYle, hPge, ⟨?_⟩⟩
  refine
    { y := y
      yd := yd
      yu := pul lam
      yu' := pulD lam
      yu'' := pulD2 lam
      ha := halpha0
      hy0 := hy0
      hyb := hyb
      hH := hH
      hq2 := hq2
      hyderiv := hyderiv
      hydc := hydc
      hydb := ?_
      hD0 := by rw [hDdef]; positivity
      hrelD := hrelD
      ha0 := by rw [hadef]; norm_num
      ha1 := by rw [hadef]; norm_num
      hYa' := fun s => by rw [hadef]; exact hYa' s
      hid := ?_
      hbeta0 := by rw [hbetadef]; positivity
      hbeta := by rw [hbetadef]; linarith
      hPdef' := rfl
      hpB' := by rw [hBdef]; linarith [hmid_hi, Real.pi_le_four]
      hqB' := by rw [hBdef]; linarith [hmid_ge, hPlow, Real.pi_le_four]
      hhalf := ?_
      hyu'c := continuous_pulD
      hyu0 := fun s => pul_nonneg hlam s
      hyub := ?_
      hDU := by rw [hDUdef]; positivity
      hyu'b := fun s => by rw [hDUdef]; exact abs_pulD_le hlam s
      hau0 := by rw [haudef]; norm_num
      hau1 := by rw [haudef]; norm_num
      hYau := fun u => by rw [haudef]; exact hYau u
      hyuderiv := fun s => hasDerivAt_pul s
      hyu''deriv := fun s => hasDerivAt_pulD s
      hyu''c := continuous_pulD2
      hDU2 := by rw [hDU2def]; positivity
      hyu''b := fun s => by rw [hDU2def]; exact abs_pulD2_le hlam s
      hyuint := integrable_pul hlam
      hmassu := integral_pul hlam
      hsmallU := ?_
      hkstarU := by rw [hkstardef]; linarith [hkstar_split]
      hKmU := le_rfl
      hCKU := le_rfl
      hPH := by rw [hBdef]; linarith [hPlow, Real.pi_le_four]
      hyint := hyint
      hmass := hmassy
      hkd := by rw [hkddef]; linarith [hKd0, hkd_split]
      hkstar := by rw [hkstardef]; nlinarith [hGau0, hGau, hlam.le]
      hkdge := by rw [hkddef]; linarith [hKd0, hkd_split]
      hkdU := by rw [hkddef, ← hKddef]; linarith [hKd0, hkd_split]
      hKdU := le_rfl
      heps0 := le_rfl }
  · -- `hydb`
    intro s
    have h1 := hydb s
    have h2 : 12 * lam * A ≤ C := by rw [hCdef]; nlinarith [hA0]
    have h3 : (0:ℝ) < Real.exp (-alpha * |s|) := Real.exp_pos _
    nlinarith
  · -- `hid`
    intro t
    rw [hxeq t]
    exact hidx t
  · -- `hhalf`
    have h1 : Real.exp (-(beta * P)) ≤ Real.exp (-(lam / 8) * H) := by
      refine Real.exp_le_exp.mpr ?_
      rw [hbetadef]
      nlinarith [hlam.le, hPge, hH.le, halphage]
    linarith
  · -- `hyub`
    intro s
    have h1 := pul_le_exp hlam s
    have h2 : Real.exp (-(2 * lam) * |s|) ≤ Real.exp (-alpha * |s|) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [abs_nonneg s]
    have h3 : (0:ℝ) ≤ 4 * A := by positivity
    calc pul lam s ≤ 4 * A * Real.exp (-(2 * lam) * |s|) := h1
      _ ≤ 4 * A * Real.exp (-alpha * |s|) := by nlinarith
      _ = CU * Real.exp (-alpha * |s|) := by rw [hCUdef]
  · -- `hsmallU`
    have : DU ≤ 2 / 100 := by rw [hDUdef]; linarith
    nlinarith [hGau0, hGau]

/-- **A matching configuration of `ModelOrbitDefect` exists**, for every small
`λ` and every separation `H` beyond the threshold `e^{-λH/8} ≤ 1/8`. -/
theorem exists_config (hlam : 0 < lam) (hlam' : lam ≤ 1 / 100) (hH : 0 < H)
    (hHbig : Real.exp (-(lam / 8) * H) ≤ 1 / 8) (theta0 : ℝ) :
    ∃ alpha beta a au C CU CK DU DU2 D Km Kd B kstar kd eps0 P : ℝ, H / 2 ≤ P ∧
      Nonempty (Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P) := by
  have hA0 : 0 < amp lam := amp_pos hlam
  obtain ⟨y, yd, x, -, hy0, hyKm, hyc, hydc, hyderiv, hyb, hydb, hrelD, hxint, hidx,
      hyint, hymass⟩ :=
    PulseFromCurvature.exists_pulse_of_curvature (K := curv lam) (K' := curvD lam)
      (Km := 2 * amp lam) (alpha := 2 * lam) (CK := 8 * amp lam)
      (CK1 := 12 * lam * amp lam) (DK := 6 * lam)
      (continuous_curv hlam hlam') (continuous_curvD hlam hlam')
      (fun u => hasDerivAt_curv hlam hlam' u) (fun u => curv_nonneg hlam hlam' u)
      (fun u => curv_le hlam hlam' u) (by positivity) (by positivity)
      (fun u => curv_le_exp hlam hlam' u) (by positivity)
      (fun u => abs_curvD_le_exp hlam hlam' u) (by positivity)
      (fun u => abs_curvD_le_curv hlam hlam' u) (integrable_curv hlam hlam')
  have hratedef : 2 * lam / Real.sqrt (1 + (2 * amp lam) ^ 2) = rate lam := rfl
  rw [hratedef] at hyb hydb
  obtain ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, h⟩ :=
    exists_config_of_pulse hlam hlam' theta0 y yd x hy0 hyKm hyc hydc hyderiv hyb hydb
      hrelD hxint hidx hyint hymass
  obtain ⟨-, hP, hc⟩ := h H hH hHbig
  exact ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, _, _, hP, hc⟩

theorem exp_neg_four_le : Real.exp (-4) ≤ 1 / 8 := by
  have h1 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h27 : (2.7:ℝ) ≤ Real.exp 1 := by linarith
  have hpow : (2.7:ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := by gcongr
  have h8 : (8:ℝ) ≤ Real.exp 4 := by rw [h4]; nlinarith
  have hle : 1 / Real.exp 4 ≤ 1 / 8 := by
    apply one_div_le_one_div_of_le (by norm_num) h8
  calc Real.exp (-4) = 1 / Real.exp 4 := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / 8 := hle

/-- **A concrete matching configuration**: `λ = 1/100` and separation `H = 3200`. -/
theorem nonempty_config (theta0 : ℝ) :
    ∃ alpha beta a au C CU CK DU DU2 D Km Kd B kstar kd eps0 P : ℝ, 1600 ≤ P ∧
      Nonempty (Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0
        3200 P) := by
  obtain ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, eps0, P, hP, hc⟩ :=
    exists_config (lam := 1 / 100) (H := 3200) (by norm_num) (by norm_num) (by norm_num)
      (by
        have h : Real.exp (-(1 / 100 / 8) * 3200) = Real.exp (-4) := by norm_num
        rw [h]; exact exp_neg_four_le) theta0
  exact ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, eps0, P,
    by linarith, hc⟩

/-- **The defect estimate of the model pseudo-orbit is not vacuous**: there is a
matching configuration, and for it the marked selected inverse of the model
front and the previous model are within the interpolation cost of the matching
bound. -/
theorem exists_config_pathDistRigid_le (theta0 : ℝ) :
    ∃ (alpha beta a au C CU CK DU DU2 D Km Kd B kstar kd eps0 H P : ℝ)
      (c : Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P),
      0 < H ∧ 0 < P ∧
      ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * P) ∧
        ∀ p' q' : Data,
          (∀ u, p'.1 u = rearTrack (c.frontCurve (theta0 := theta0))
            (c.frontTangentAngle (theta0 := theta0)) (modelSteering c.Y) (c.sf (2 * P * u))) →
          (∀ u, q'.1 u = interpCurve (modelCurvature c.yu c.yu' P) theta0 P (psi u)) →
          pathDistRigid p' q' ≤ interpCostL1 kstar kd P eps0
            (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * H))) := by
  obtain ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, eps0, P, hP1600, ⟨c⟩⟩ :=
    nonempty_config theta0
  have hP : 0 < P := by linarith
  exact ⟨alpha, beta, a, au, C, CU, CK, DU, DU2, D, Km, Kd, B, kstar, kd, eps0, 3200, P, c,
    by norm_num, hP, c.pathDistRigid_le⟩

end ModelConfigInstance
