import Mathlib
import UnitTangentIterates.SelectedInverseCarrier
import UnitTangentIterates.SelectedInverseCarrierModel
import UnitTangentIterates.PeriodizedTurning
import UnitTangentIterates.PeriodizedCurvatureDeriv

/-!
# The defect estimate of the model pseudo-orbit

The last section of *A Noncircular Oval with Convex Unit-Tangent Iterates*
shadows the sequence of exact two-cap pairs at the separations
`H₀ < H₁ < ⋯` fixed by the recursion `P(H_{n+1}) = H_n`.  Its defect estimate
compares the `n`-th model `Q_n = F_{H_n}` with the rear `A_n = R_{H_{n+1}}` of
the `(n+1)`-st pair, that is, with the **marked selected inverse** of the
`(n+1)`-st model.

`SelectedInverseCarrier.pathDistRigid_rearOwn_front_le_of_matching` bounds the
path pseudodistance, modulo a rigid motion, between the rear track of a front
written in its own arclength and a marked oval carrying a model curvature `K_P`.
Both curves of that statement are identified here with the two models of the
paper:

* **The front of the configuration is the model front of separation `H`.**  The
  exact front curvature of the model of separation `L` is
  `K_L = Y_L + G(Y_L)·Y_L'` in the periodized steering pulse `Y_L`
  (`modelCurvature`), and the front is the curve reconstructed from it
  (`TwoCapPairsAssembly.front`).
* **Its steering angle is explicit**: the relation `sin δ = Y_H` of the exact
  pair says `δ = arcsin Y_H` (`modelSteering`), and this *solves* the steering
  equation `δ_s = K_H − sin δ` of the bicycle relations
  (`hasDerivAt_modelSteering`), stays on the closed strip and has speed
  `cos δ = √(1 − Y_H²)` bounded below (`cos_modelSteering_ge`).  So the whole
  rear geometry of the configuration — the steering angle, the rear arclength
  and the rear track — is produced by the pulse, and nothing about it needs to
  be assumed.
* **The comparison curvature is the model curvature of period `P`**: `K_P` is
  `modelCurvature` at the period `P`, which the recursion identifies with the
  separation `H_n` of the previous model.
* **The rear curvature is produced with it**: it is `tan δ` read in the rear
  arclength (`Config.kH_eq`), hence continuous, nonnegative, bounded by
  `a/√(1−a²)`, periodic with the rear period, of total turning `π` over that
  period — the change of variables `dx = cos δ ds` turning it into the steering
  mass `∫_ℝ y = π` of the pulse (`Config.integral_kH_eq_pi`) — and
  differentiable with `k_H' = (K − Y)/cos³δ` (`kHderiv`), bounded by an explicit
  constant in the pulse data.  The same holds of the model curvature itself,
  through the theory of `PeriodizedTurning.lean`.

`Config` bundles the resulting configuration.  Its data are only the two
pulses: the steering pulse `y` of the isolated pair with its derivative, and
the pulse `yu` of the previous model with its first two derivatives.
Everything else the matching theorem consumes is produced from them inside the
namespace: the periodized pulse `Y` (`Config.Y`), the rear arclength of the
isolated pair (`Config.x`), the inverse `sf` of the rear arclength of the
configuration (`Config.sf`, from the lower bound `cos δ ≥ √(1−a²) > 0`), the
rear curvature `k_H = tan δ ∘ sf` (`Config.kH`) with its matching relation
(`Config.hk`), the curvature `K_* = yu + G(yu)yu'` of the isolated hairpin
(`Config.Kstar`) with its derivative (`Config.Kstar'`), the sum `K̄` of its
translates (`Config.Kbar`), and the derivative `K_P'` of the model curvature of
period `P` (`Config.KP'`).  Their regularity — continuity, integrability,
positivity, periodicity, total turning `π`, and the sup bounds — is derived,
not assumed; what the hypothesis block still carries is the decay and the
relative derivative bounds of the two pulses, the strip bounds, the matching
identity of the isolated pair, and the inequalities fixing the constants.
`Config.pathDistRigid_le` is the defect estimate: the marked selected inverse of
the model front of separation `H` and the model front of separation `P` are at
path pseudodistance, modulo a rigid motion, at most
`interpCostL1 … (C·e^{−βH})`.  `pathDistRigid_selInv_model_orbit` reads it along
the recursion `P = H_n`, `H = H_{n+1}`: the `n`-th model and the marked selected
inverse of the `(n+1)`-st are that close, which is the defect estimate of the
model pseudo-orbit.

What is still not supplied is the *joint satisfiability* of the hypothesis block
of `Config` — the paper's hairpin is not fed into it here — and the
non-expansiveness of the selected inverse; so nothing here should be read as a
verification of the paper's main theorem.
-/

noncomputable section

open Real Set Function MeasureTheory MarkedSpace PathMetric

namespace ModelOrbitDefect

open CurvatureInterpolation RearTrack FrontPeriodization TwoCapPairsAssembly
  MarkedRigid SelectedInverseCarrier MatchingComplete MatchingExponential
  InterpolationPathDistSummable

/-! ### The model curvature and the steering angle it selects -/

/-- **The exact front curvature of the model of separation `L`**:
`K_L = Y_L + G(Y_L)·Y_L'`, where `Y_L = ∑_m y(· − mL)` is the periodized
steering pulse and `Y_L' = ∑_m y'(· − mL)` its derivative. -/
def modelCurvature (y yd : ℝ → ℝ) (L : ℝ) : ℝ → ℝ := fun s =>
  (∑' m : ℤ, y (s - m * L)) + G (∑' m : ℤ, y (s - m * L)) * (∑' m : ℤ, yd (s - m * L))

/-- **The periodized steering pulse** of the model of separation `L`. -/
def periodizedPulse (y : ℝ → ℝ) (L : ℝ) : ℝ → ℝ := fun s => ∑' m : ℤ, y (s - m * L)

/-- **The intrinsic curvature of the isolated hairpin**: `K_* = yu + G(yu)·yu'`
in its own steering pulse. -/
def hairpinCurvature (yu yu' : ℝ → ℝ) : ℝ → ℝ := fun s => yu s + G (yu s) * yu' s

/-- **The derivative of the intrinsic curvature of the isolated hairpin**:
`K_*' = yu' + G'(yu)(yu')² + G(yu)·yu''`. -/
def hairpinCurvatureDeriv (yu yu' yu'' : ℝ → ℝ) : ℝ → ℝ := fun s =>
  yu' s + (lipConst (yu s) * (yu' s) ^ 2 + G (yu s) * yu'' s)

/-- **The sum of the translates of a curvature** at the period `P`. -/
def translatesSum (K : ℝ → ℝ) (P : ℝ) : ℝ → ℝ := fun u =>
  K u + ∑' j : {j : ℤ // j ≠ 0}, K (u - (j : ℤ) * P)

/-- **The derivative of the exact front curvature of the model of separation
`L`**: `K_L' = Y_L' + G'(Y_L)(Y_L')² + G(Y_L)·Y_L''`. -/
def modelCurvatureDeriv (y yd ydd : ℝ → ℝ) (L : ℝ) : ℝ → ℝ := fun u =>
  (∑' m : ℤ, yd (u - m * L))
    + (lipConst (∑' m : ℤ, y (u - m * L)) * (∑' m : ℤ, yd (u - m * L)) ^ 2
      + G (∑' m : ℤ, y (u - m * L)) * ∑' m : ℤ, ydd (u - m * L))

/-- **The steering angle of the model configuration**: the exact pair has
`sin δ = Y_H`, so `δ = arcsin Y_H`. -/
def modelSteering (Y : ℝ → ℝ) : ℝ → ℝ := fun s => Real.arcsin (Y s)

/-- The rear arclength of the model configuration, `x_H = ∫ cos δ`. -/
def modelRearArclength (Y : ℝ → ℝ) : ℝ → ℝ := rearArclength (modelSteering Y)

/-- **The derivative of the rear curvature** of the configuration, in closed
form: differentiating `k_H = tan δ ∘ sf` with `δ_s = K − sin δ` and
`sf' = sec δ` gives `k_H' = (K − Y)/cos³δ`, read in the rear arclength. -/
def kHderiv (Y K sf : ℝ → ℝ) : ℝ → ℝ := fun z =>
  (K (sf z) - Y (sf z)) / Real.cos (modelSteering Y (sf z)) ^ 3

section PulseLemmas

variable {Y Yd : ℝ → ℝ} {a s : ℝ}

/-- The steering pulse is the sine of the steering angle. -/
theorem sin_modelSteering (ha : a ≤ 1) (hYa : |Y s| ≤ a) :
    Real.sin (modelSteering Y s) = Y s := by
  have h := abs_le.mp hYa
  exact Real.sin_arcsin (by linarith [h.1]) (by linarith [h.2])

/-- The rear speed of the model configuration is `√(1 − Y²)`. -/
theorem cos_modelSteering : Real.cos (modelSteering Y s) = Real.sqrt (1 - Y s ^ 2) :=
  Real.cos_arcsin _

/-- The rear speed is bounded below by `√(1 − a²)` on the strip `|Y| ≤ a`. -/
theorem cos_modelSteering_ge (hYa : |Y s| ≤ a) :
    Real.sqrt (1 - a ^ 2) ≤ Real.cos (modelSteering Y s) := by
  rw [cos_modelSteering]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [abs_le.mp hYa, abs_nonneg (Y s), sq_abs (Y s), sq_nonneg (|Y s| - a),
    sq_nonneg (|Y s| + a)]

/-- The rear speed of a configuration on the strip `|Y| ≤ a < 1` is positive. -/
theorem sqrt_one_sub_sq_pos (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 < Real.sqrt (1 - a ^ 2) :=
  Real.sqrt_pos.mpr (by nlinarith)

/-- The steering angle of the model configuration is continuous. -/
theorem continuous_modelSteering (hY : Continuous Y) : Continuous (modelSteering Y) :=
  Real.continuous_arcsin.comp hY

/-- **`δ = arcsin Y` solves the steering equation** `δ_s = K − sin δ` of the
bicycle relations, for the exact front curvature `K = Y + G(Y)·Y'`. -/
theorem hasDerivAt_modelSteering (hY : HasDerivAt Y (Yd s) s) (ha1 : a < 1)
    (hYa : |Y s| ≤ a) :
    HasDerivAt (modelSteering Y)
      ((Y s + G (Y s) * Yd s) - Real.sin (modelSteering Y s)) s := by
  have h := abs_le.mp hYa
  have hne1 : Y s ≠ 1 := by intro h1; rw [h1] at h; linarith [h.2]
  have hne2 : Y s ≠ -1 := by intro h1; rw [h1] at h; linarith [h.1]
  have harc := (Real.hasDerivAt_arcsin hne2 hne1).comp s hY
  rw [sin_modelSteering ha1.le hYa,
    show (Y s + G (Y s) * Yd s) - Y s = 1 / Real.sqrt (1 - Y s ^ 2) * Yd s by rw [G]; ring]
  exact harc

/-! ### The model curvature is produced by the pulse

The theory of `PeriodizedTurning.lean` gives, from the pulse alone, everything
the two curvature sides of a configuration ask of the model curvature: it is
continuous, `L`-periodic, nonnegative, bounded, of total turning `π` over one
period, and the periodized pulse may be differentiated termwise. -/

section FromPulse

variable {y yd : ℝ → ℝ} {Cp alphap L ap : ℝ}

/-- **The periodized pulse may be differentiated termwise**, in the form the
configuration asks for. -/
theorem hasDerivAt_periodized (halpha : 0 < alphap) (hL : 0 < L)
    (hy : ∀ x, HasDerivAt y (yd x) x)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hYdef : ∀ s, Y s = ∑' m : ℤ, y (s - m * L)) (s : ℝ) :
    HasDerivAt Y (∑' m : ℤ, yd (s - m * L)) s := by
  have h := PeriodizedTurning.hasDerivAt_periodization halpha hL hy hyb hydb s
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => hYdef z)

/-- The model curvature is continuous. -/
theorem continuous_modelCurvature (halpha : 0 < alphap) (hL : 0 < L)
    (hyc : Continuous y) (hydc : Continuous yd)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hy0 : ∀ u, 0 ≤ y u) (ha0 : 0 ≤ ap) (ha1 : ap < 1)
    (hYa : ∀ v, (∑' m : ℤ, y (v - m * L)) ≤ ap) :
    Continuous (modelCurvature y yd L) := by
  have hYcont : Continuous fun u => ∑' m : ℤ, y (u - m * L) :=
    PeriodizedTurning.continuous_periodization halpha hL hyc hyb
  have hY'cont : Continuous fun u => ∑' m : ℤ, yd (u - m * L) :=
    FrontPeriodizationIntegral.continuous_tsum_translates halpha hL hydc hydb
  have hY0 : ∀ u, 0 ≤ ∑' m : ℤ, y (u - m * L) := fun u => tsum_nonneg fun m => hy0 _
  have hGcont : Continuous fun u => G (∑' m : ℤ, y (u - m * L)) :=
    FrontPeriodizationIntegral.continuous_G_comp ha0 ha1 hYcont hY0 hYa
  exact hYcont.add (hGcont.mul hY'cont)

/-- The model curvature of period `L` is `L`-periodic. -/
theorem periodic_modelCurvature (y yd : ℝ → ℝ) (L : ℝ) :
    Periodic (modelCurvature y yd L) L :=
  PeriodizedTurning.periodic_frontCurv y yd L

/-- **The model curvature has total turning `π` over one period**, the pulse
having the steering mass `∫_ℝ y = π` of the paper's hairpin. -/
theorem integral_modelCurvature_eq_pi (halpha : 0 < alphap) (hL : 0 < L)
    (hyc : Continuous y) (hydc : Continuous yd)
    (hy : ∀ x, HasDerivAt y (yd x) x)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hy0 : ∀ u, 0 ≤ y u) (hyint : Integrable y)
    (ha0 : 0 ≤ ap) (ha1 : ap < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * L)| ≤ ap)
    (hmass : (∫ u : ℝ, y u) = Real.pi) :
    (∫ r in (0:ℝ)..L, modelCurvature y yd L r) = Real.pi := by
  have h := PeriodizedTurning.integral_frontCurv_eq_pi halpha hL hyc hydc hy hyb hydb hy0
    hyint ha0 ha1 hYa hmass 0
  rw [zero_add] at h
  exact h

/-- The model curvature is nonnegative when the relative derivative bound of the
pulse is small for the periodization bound. -/
theorem modelCurvature_nonneg (halpha : 0 < alphap) (hL : 0 < L) {D : ℝ} (hD : 0 ≤ D)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hrel : ∀ s, |yd s| ≤ D * y s) (ha1 : ap < 1)
    (hYa : ∀ v, (∑' m : ℤ, y (v - m * L)) ≤ ap) (hsmall : G ap * D ≤ 1) (u : ℝ) :
    0 ≤ modelCurvature y yd L u :=
  PeriodizedTurning.frontCurv_nonneg halpha hL hD hy0 hyb hydb hrel ha1 hYa hsmall u

/-- A sup bound for the absolute value of the model curvature. -/
theorem abs_modelCurvature_le (halpha : 0 < alphap) (hL : 0 < L) {D : ℝ} (hD : 0 ≤ D)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hrel : ∀ s, |yd s| ≤ D * y s) (ha1 : ap < 1)
    (hYa : ∀ v, (∑' m : ℤ, y (v - m * L)) ≤ ap) (u : ℝ) :
    |modelCurvature y yd L u| ≤ (1 + G ap * D) * ap :=
  PeriodizedTurning.abs_frontCurv_le halpha hL hD hy0 hyb hydb hrel ha1 hYa u

/-- A sup bound for the model curvature. -/
theorem modelCurvature_le (halpha : 0 < alphap) (hL : 0 < L) {D : ℝ} (hD : 0 ≤ D)
    (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hrel : ∀ s, |yd s| ≤ D * y s) (ha1 : ap < 1)
    (hYa : ∀ v, (∑' m : ℤ, y (v - m * L)) ≤ ap) (u : ℝ) :
    modelCurvature y yd L u ≤ (1 + G ap * D) * ap :=
  le_trans (le_abs_self _)
    (PeriodizedTurning.abs_frontCurv_le halpha hL hD hy0 hyb hydb hrel ha1 hYa u)

/-- **The model curvature is differentiable**, with the derivative produced by
the pulse. -/
theorem hasDerivAt_modelCurvature {ydd : ℝ → ℝ} (halpha : 0 < alphap) (hL : 0 < L)
    (hy : ∀ x, HasDerivAt y (yd x) x) (hyd : ∀ x, HasDerivAt yd (ydd x) x)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hyddb : ∀ x, |ydd x| ≤ Cp * Real.exp (-alphap * |x|))
    (ha1 : ap < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * L)| ≤ ap) (u : ℝ) :
    HasDerivAt (modelCurvature y yd L) (modelCurvatureDeriv y yd ydd L u) u :=
  PeriodizedCurvatureDeriv.hasDerivAt_frontCurv halpha hL hy hyd hyb hydb hyddb ha1 hYa u

/-- The derivative of the model curvature is continuous. -/
theorem continuous_modelCurvatureDeriv {ydd : ℝ → ℝ} (halpha : 0 < alphap) (hL : 0 < L)
    (hyc : Continuous y) (hydc : Continuous yd) (hyddc : Continuous ydd)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hyddb : ∀ x, |ydd x| ≤ Cp * Real.exp (-alphap * |x|))
    (ha1 : ap < 1) (hYa : ∀ v, |∑' m : ℤ, y (v - m * L)| ≤ ap) :
    Continuous (modelCurvatureDeriv y yd ydd L) :=
  PeriodizedCurvatureDeriv.continuous_deriv_frontCurv halpha hL hydc hyddc hyc hyb hydb
    hyddb ha1 hYa

/-- **A uniform bound for the derivative of the model curvature**, in the pulse
data. -/
theorem abs_modelCurvatureDeriv_le {ydd : ℝ → ℝ} {D D2 : ℝ} (halpha : 0 < alphap)
    (hL : 0 < L) (hD : 0 ≤ D) (hD2 : 0 ≤ D2) (hy0 : ∀ s, 0 ≤ y s)
    (hyb : ∀ x, |y x| ≤ Cp * Real.exp (-alphap * |x|))
    (hydb : ∀ x, |yd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hyddb : ∀ x, |ydd x| ≤ Cp * Real.exp (-alphap * |x|))
    (hrel : ∀ s, |yd s| ≤ D * y s) (hrel2 : ∀ s, |ydd s| ≤ D2 * y s)
    (ha1 : ap < 1) (hYa : ∀ v, (∑' m : ℤ, y (v - m * L)) ≤ ap) (u : ℝ) :
    |modelCurvatureDeriv y yd ydd L u|
      ≤ D * ap + lipConst ap * (D ^ 2 * ap ^ 2) + G ap * (D2 * ap) :=
  PeriodizedCurvatureDeriv.abs_deriv_frontCurv_le halpha hL hD hD2 hy0 hyb hydb hyddb
    hrel hrel2 ha1 hYa u

end FromPulse

end PulseLemmas

/-! ### The configuration -/

/-- The constant of the matching estimate: the two pulse errors, the omitted
mass and the front periodization error. -/
def matchConst (a C CK CU DU Km Kd au alpha beta B : ℝ) : ℝ :=
  pulseConst C Km Kd (a / Real.sqrt (1 - a ^ 2)) alpha beta
    + rearTailConst CK alpha B + frontConst au CU DU alpha beta B

/-- **A matching configuration over a model front of separation `H` whose rear
has period `P`.**

The fields are those of `SelectedInverseCarrier.pathDistRigid_rearOwn_front_le_of_matching`,
with the whole rear geometry of the configuration produced from the pulse: the
front is the model front of separation `H`, its steering angle is `arcsin Y`,
its rear arclength is `∫ cos δ`, and the curvature it is compared with is the
model curvature of period `P`. -/
structure Config (alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P : ℝ) where
  /-- the steering pulse of the isolated pair, in the front arclength -/
  y : ℝ → ℝ
  /-- its derivative -/
  yd : ℝ → ℝ
  /-- the steering pulse of the previous model, in the front arclength -/
  yu : ℝ → ℝ
  /-- its derivative -/
  yu' : ℝ → ℝ
  /-- the second derivative of the pulse of the previous model -/
  yu'' : ℝ → ℝ
  ha : 0 < alpha
  hy0 : ∀ s, 0 ≤ y s
  hyb : ∀ s, y s ≤ C * Real.exp (-alpha * |s|)
  hH : 0 < H
  hq2 : Real.exp (-alpha * H) ≤ 1 / 2
  hyderiv : ∀ s, HasDerivAt y (yd s) s
  /-- the derivative of the pulse is continuous -/
  hydc : Continuous yd
  hydb : ∀ s, |yd s| ≤ C * Real.exp (-alpha * |s|)
  hD0 : 0 ≤ D
  hrelD : ∀ s, |yd s| ≤ D * y s
  ha0 : 0 ≤ a
  ha1 : a < 1
  hYa' : ∀ s, |periodizedPulse y H s| ≤ a
  hid : ∀ t, y t
    = Real.sqrt (1 - (y t) ^ 2) * hairpinCurvature yu yu' (modelRearArclength y t)
  hbeta0 : 0 < beta
  hbeta : beta < alpha / 2
  /-- the period of the rear is the rear arclength of one front period -/
  hPdef' : modelRearArclength (periodizedPulse y H) H = P
  hpB' : modelRearArclength (periodizedPulse y H) (-(H / 2)) ≤ -(H / 2) + B
  hqB' : H / 2 - B ≤ modelRearArclength (periodizedPulse y H) (-(H / 2)) + P
  hhalf : Real.exp (-(beta * P)) ≤ 1 / 2
  hyu'c : Continuous yu'
  hyu0 : ∀ s, 0 ≤ yu s
  hyub : ∀ s, yu s ≤ CU * Real.exp (-alpha * |s|)
  hDU : 0 ≤ DU
  hyu'b : ∀ s, |yu' s| ≤ DU * yu s
  hau0 : 0 ≤ au
  hau1 : au < 1
  hYau : ∀ u, (∑' m : ℤ, yu (u - m * P)) ≤ au
  /-- the derivative of the pulse of the previous model -/
  hyuderiv : ∀ x, HasDerivAt yu (yu' x) x
  /-- its second derivative -/
  hyu''deriv : ∀ x, HasDerivAt yu' (yu'' x) x
  hyu''c : Continuous yu''
  hDU2 : 0 ≤ DU2
  hyu''b : ∀ s, |yu'' s| ≤ DU2 * yu s
  /-- the pulse of the previous model is integrable, of steering mass `π` -/
  hyuint : Integrable yu
  hmassu : (∫ u : ℝ, yu u) = Real.pi
  /-- Positivity of the isolated and periodized model curvatures.  The first
  branch is the convenient relative-derivative criterion used by explicit
  pulse instances.  The second branch is the paper's geometric route, where
  positivity follows from comparison with the translating hairpin and the
  exponentially small periodization overlap. -/
  hcurvNonnegU : G au * DU ≤ 1 ∨
    ((∀ s, 0 ≤ hairpinCurvature yu yu' s) ∧
      ∀ r, 0 ≤ modelCurvature yu yu' P r)
  /-- the sup bound of the model curvature of the previous model -/
  hkstarU : (1 + G au * DU) * au ≤ kstar
  /-- the sup bound of the curvature of the isolated hairpin -/
  hKmU : (1 + G au * DU) * au ≤ Km
  /-- the exponential majorant of the curvature of the isolated hairpin -/
  hCKU : (1 + G au * DU) * CU ≤ CK
  hPH : H - 2 * B ≤ P
  /-- the pulse is integrable, of the steering mass of the hairpin -/
  hyint : Integrable y
  hmass : (∫ u : ℝ, y u) = Real.pi
  hkd : 0 < kd
  hkstar : a / Real.sqrt (1 - a ^ 2) ≤ kstar
  hkdge : ((1 + G a * D) * a + a) / Real.sqrt (1 - a ^ 2) ^ 3 ≤ kd
  /-- the sup bound of the derivative of the model curvature of the previous
  model -/
  hkdU : DU * au + lipConst au * (DU ^ 2 * au ^ 2) + G au * (DU2 * au) ≤ kd
  /-- the sup bound of the derivative of the curvature of the isolated
  hairpin -/
  hKdU : DU * au + lipConst au * (DU ^ 2 * au ^ 2) + G au * (DU2 * au) ≤ Kd
  heps0 : matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * H)) ≤ eps0

namespace Config

variable {alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P : ℝ}
  (c : Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd eps0 H P)

/-- The model front of separation `H` — the front of the configuration. -/
def frontCurve : ℝ → ℂ := front (modelCurvature c.y c.yd H) theta0 H

/-- Its tangent angle. -/
def frontTangentAngle : ℝ → ℝ := frontAngle (modelCurvature c.y c.yd H) theta0

/-! #### The rear side of the configuration is produced -/

/-- The periodized steering pulse of the configuration. -/
def Y : ℝ → ℝ := periodizedPulse c.y H

theorem hYdef (s : ℝ) : c.Y s = ∑' m : ℤ, c.y (s - m * H) := rfl

theorem hYa (s : ℝ) : |c.Y s| ≤ a := c.hYa' s

theorem hPdef : modelRearArclength c.Y H = P := c.hPdef'

theorem hpB : modelRearArclength c.Y (-(H / 2)) ≤ -(H / 2) + B := c.hpB'

theorem hqB : H / 2 - B ≤ modelRearArclength c.Y (-(H / 2)) + P := c.hqB'

/-- The intrinsic curvature of the isolated hairpin, `K_* = yu + G(yu)·yu'`. -/
def Kstar : ℝ → ℝ := hairpinCurvature c.yu c.yu'

/-- The sum of the translates of the hairpin curvature at the rear period. -/
def Kbar : ℝ → ℝ := translatesSum c.Kstar P

theorem hKstaru (s : ℝ) : c.Kstar s = c.yu s + G (c.yu s) * c.yu' s := rfl

theorem hKbar (u : ℝ) :
    c.Kbar u = c.Kstar u + ∑' j : {j : ℤ // j ≠ 0}, c.Kstar (u - (j : ℤ) * P) := rfl

/-- **The rear arclength of the isolated pair is produced**: it is the rear
arclength of the steering angle `arcsin y` of the isolated pair. -/
def x : ℝ → ℝ := modelRearArclength c.y

/-- The pulse is continuous, being differentiable. -/
theorem continuous_y : Continuous c.y :=
  continuous_iff_continuousAt.mpr fun s => (c.hyderiv s).continuousAt

/-- The pulse of the previous model is continuous, being differentiable. -/
theorem continuous_yu : Continuous c.yu :=
  continuous_iff_continuousAt.mpr fun s => (c.hyuderiv s).continuousAt

/-- The pulse is dominated by its exponential majorant in absolute value. -/
theorem abs_y_le (s : ℝ) : |c.y s| ≤ C * Real.exp (-alpha * |s|) := by
  rw [abs_of_nonneg (c.hy0 s)]
  exact c.hyb s

/-- The periodized pulse of the configuration stays below `a`. -/
theorem periodization_le (v : ℝ) : (∑' m : ℤ, c.y (v - m * H)) ≤ a := by
  rw [← c.hYdef v]
  exact le_trans (le_abs_self _) (c.hYa v)

/-- **The periodized pulse is continuous**, being a locally uniformly convergent
series of translates of the pulse. -/
theorem continuous_Y : Continuous c.Y := by
  have heq : c.Y = fun u => ∑' m : ℤ, c.y (u - m * H) := funext c.hYdef
  rw [heq]
  exact PeriodizedTurning.continuous_periodization c.ha c.hH c.continuous_y c.abs_y_le

/-- **The pulse itself stays below `a`**, being dominated by its
periodization. -/
theorem abs_y_le_strip (s : ℝ) : |c.y s| ≤ a := by
  have h := FrontPeriodizationIntegral.le_tsum_translates (y := c.y) (P := H) (C := C)
    c.ha c.hH c.hy0 c.hyb s 0
  simp only [Int.cast_zero, zero_mul, sub_zero] at h
  rw [abs_of_nonneg (c.hy0 s)]
  exact h.trans (c.periodization_le s)

/-- The rear arclength of the isolated pair has the speed of the pair. -/
theorem hx (t : ℝ) : HasDerivAt c.x (Real.sqrt (1 - (c.y t) ^ 2)) t := by
  have h := hasDerivAt_rearArclength (δ := modelSteering c.y)
    (continuous_modelSteering c.continuous_y) t
  rwa [cos_modelSteering (Y := c.y) (s := t)] at h

/-- It vanishes at the marked point. -/
theorem hx0 : c.x 0 = 0 := by
  simp [Config.x, modelRearArclength, rearArclength]

/-- **The model front of separation `H` is a regular curve**: its curvature is
continuous, being produced by the pulse. -/
theorem continuous_frontCurvature : Continuous (modelCurvature c.y c.yd H) :=
  continuous_modelCurvature (Cp := C) c.ha c.hH c.continuous_y c.hydc c.abs_y_le c.hydb
    c.hy0 c.ha0 c.ha1 c.periodization_le

/-- **The periodized pulse may be differentiated termwise.** -/
theorem hasDerivAt_Y (s : ℝ) : HasDerivAt c.Y (∑' m : ℤ, c.yd (s - m * H)) s :=
  hasDerivAt_periodized c.ha c.hH c.hyderiv c.abs_y_le c.hydb c.hYdef s

/-- **The steering angle of the configuration solves the steering equation** of
the model front of separation `H`. -/
theorem hasDerivAt_dl (s : ℝ) :
    HasDerivAt (modelSteering c.Y)
      (modelCurvature c.y c.yd H s - Real.sin (modelSteering c.Y s)) s := by
  have hKfront : modelCurvature c.y c.yd H s
      = c.Y s + G (c.Y s) * ∑' m : ℤ, c.yd (s - m * H) := by
    rw [modelCurvature, ← c.hYdef s]
  rw [hKfront]
  exact hasDerivAt_modelSteering (Yd := fun z => ∑' m : ℤ, c.yd (z - m * H))
    (c.hasDerivAt_Y s) c.ha1 (c.hYa s)

/-- The steering pulse of the configuration is nonnegative. -/
theorem Y_nonneg (t : ℝ) : 0 ≤ c.Y t := by
  rw [c.hYdef t]
  exact tsum_nonneg fun _ => c.hy0 _

theorem cos_dl_ge (s : ℝ) : Real.sqrt (1 - a ^ 2) ≤ Real.cos (modelSteering c.Y s) :=
  cos_modelSteering_ge (c.hYa s)

theorem continuous_dl : Continuous (modelSteering c.Y) := continuous_modelSteering c.continuous_Y

/-- **The inverse of the rear arclength is produced, not assumed**: the rear
speed `cos δ` is bounded below by `√(1 − a²) > 0`, so the rear arclength is a
bijection of the line, and `sf` is its inverse. -/
def sf : ℝ → ℝ :=
  Classical.choose (ArclengthInverse.exists_rightInverse (f := modelRearArclength c.Y)
    (g := fun s => Real.cos (modelSteering c.Y s)) (sqrt_one_sub_sq_pos c.ha0 c.ha1)
    (fun s => hasDerivAt_rearArclength c.continuous_dl s) c.cos_dl_ge)

/-- It is a right inverse of the rear arclength. -/
theorem sf_rightInverse (z : ℝ) : modelRearArclength c.Y (c.sf z) = z :=
  Classical.choose_spec (ArclengthInverse.exists_rightInverse (f := modelRearArclength c.Y)
    (g := fun s => Real.cos (modelSteering c.Y s)) (sqrt_one_sub_sq_pos c.ha0 c.ha1)
    (fun s => hasDerivAt_rearArclength c.continuous_dl s) c.cos_dl_ge) z

/-- **The rear curvature of the configuration is produced too**: it is `tan δ`
read in the rear arclength, `δ = arcsin Y` being the steering angle of the
configuration. -/
def kH : ℝ → ℝ := fun z => Real.tan (modelSteering c.Y (c.sf z))

theorem kH_eq (z : ℝ) : c.kH z = Real.tan (modelSteering c.Y (c.sf z)) := rfl

theorem continuous_sf : Continuous c.sf :=
  ArclengthInverse.continuous_of_rightInverse (sqrt_one_sub_sq_pos c.ha0 c.ha1)
    (fun s => hasDerivAt_rearArclength c.continuous_dl s) c.cos_dl_ge c.sf_rightInverse

/-- The rear arclength is strictly increasing, the rear speed being positive. -/
theorem strictMono_rearArclength : StrictMono (modelRearArclength c.Y) :=
  ArclengthInverse.strictMono_of_deriv_ge (sqrt_one_sub_sq_pos c.ha0 c.ha1)
    (fun s => hasDerivAt_rearArclength c.continuous_dl s) c.cos_dl_ge

/-- The rear arclength vanishes at the marked point. -/
theorem rearArclength_zero : modelRearArclength c.Y 0 = 0 := by
  simp [modelRearArclength, rearArclength]

include c in
/-- **The rear period is positive.** -/
theorem Ppos : 0 < P := by
  rw [← c.hPdef, ← c.rearArclength_zero]
  exact c.strictMono_rearArclength c.hH

/-- The rear arclength of the left endpoint of a front period is nonpositive. -/
theorem rearArclength_left_nonpos : modelRearArclength c.Y (-(H / 2)) ≤ 0 := by
  rw [← c.rearArclength_zero]
  exact (c.strictMono_rearArclength.le_iff_le).mpr (by linarith [c.hH])

/-- The right inverse of the rear arclength is a two-sided inverse. -/
theorem sf_leftInverse (t : ℝ) : c.sf (modelRearArclength c.Y t) = t :=
  ArclengthInverse.leftInverse_of_rightInverse
    (ArclengthInverse.strictMono_of_deriv_ge (sqrt_one_sub_sq_pos c.ha0 c.ha1)
      (fun s => hasDerivAt_rearArclength c.continuous_dl s) c.cos_dl_ge).injective
    c.sf_rightInverse t

/-- **The matching relation of the configuration**: the rear curvature, read in
the rear arclength, satisfies `k_H·cos δ = sin δ = Y`. -/
theorem hk (t : ℝ) :
    c.kH (modelRearArclength c.Y t) * Real.sqrt (1 - (c.Y t) ^ 2) = c.Y t := by
  have hcos : Real.cos (modelSteering c.Y t) = Real.sqrt (1 - c.Y t ^ 2) :=
    cos_modelSteering
  have hne : Real.cos (modelSteering c.Y t) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (sqrt_one_sub_sq_pos c.ha0 c.ha1) (c.cos_dl_ge t))
  rw [c.kH_eq, c.sf_leftInverse t, Real.tan_eq_sin_div_cos, ← hcos,
    div_mul_cancel₀ _ hne, sin_modelSteering c.ha1.le (c.hYa t)]

/-- The rear curvature of the configuration, in closed form. -/
theorem tan_dl (s : ℝ) :
    Real.tan (modelSteering c.Y s) = c.Y s / Real.sqrt (1 - c.Y s ^ 2) := by
  rw [Real.tan_eq_sin_div_cos, sin_modelSteering c.ha1.le (c.hYa s),
    cos_modelSteering (Y := c.Y) (s := s)]

/-- **The rear curvature is nonnegative**: the rear track is convex. -/
theorem kH_nonneg (r : ℝ) : 0 ≤ c.kH r := by
  rw [c.kH_eq, c.tan_dl]
  exact div_nonneg (c.Y_nonneg _) (Real.sqrt_nonneg _)

/-- **The rear curvature is bounded** by `a/√(1−a²)`. -/
theorem kH_le (r : ℝ) : c.kH r ≤ kstar := by
  refine le_trans ?_ c.hkstar
  rw [c.kH_eq, c.tan_dl]
  have h1 : c.Y (c.sf r) ≤ a := le_trans (le_abs_self _) (c.hYa _)
  have h2 : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - c.Y (c.sf r) ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [c.Y_nonneg (c.sf r)]
  have h3 : 0 < Real.sqrt (1 - a ^ 2) := sqrt_one_sub_sq_pos c.ha0 c.ha1
  gcongr
  exact c.ha0

/-- The rear curvature is continuous. -/
theorem continuous_kH : Continuous c.kH := by
  have heq : c.kH = fun r => c.Y (c.sf r) / Real.sqrt (1 - c.Y (c.sf r) ^ 2) :=
    funext fun r => by rw [c.kH_eq, c.tan_dl]
  rw [heq]
  have hcomp : Continuous fun r => c.Y (c.sf r) := c.continuous_Y.comp c.continuous_sf
  refine hcomp.div ((continuous_const.sub (hcomp.pow 2)).sqrt) fun r => ?_
  have h1 : c.Y (c.sf r) ≤ a := le_trans (le_abs_self _) (c.hYa _)
  refine ne_of_gt (Real.sqrt_pos.mpr ?_)
  nlinarith [c.Y_nonneg (c.sf r), c.ha1, c.ha0]

/-! #### The model curvature of the previous model is produced -/

include c in
/-- The majorant of the pulse of the previous model is nonnegative. -/
theorem CU_nonneg : 0 ≤ CU := by
  have h0 := c.hyu0 0
  have h1 := c.hyub 0
  simpa using h0.trans h1

/-- The pulse of the previous model and its derivative share an exponential
majorant. -/
theorem abs_yu_le (s : ℝ) :
    |c.yu s| ≤ (CU + DU * CU + DU2 * CU) * Real.exp (-alpha * |s|) := by
  rw [abs_of_nonneg (c.hyu0 s)]
  have hpos : (0:ℝ) < Real.exp (-alpha * |s|) := Real.exp_pos _
  have := c.hyub s
  nlinarith [mul_nonneg c.hDU c.CU_nonneg, mul_nonneg c.hDU2 c.CU_nonneg, hpos.le]

theorem abs_yu'_le (s : ℝ) :
    |c.yu' s| ≤ (CU + DU * CU + DU2 * CU) * Real.exp (-alpha * |s|) := by
  have hpos : (0:ℝ) < Real.exp (-alpha * |s|) := Real.exp_pos _
  refine (c.hyu'b s).trans ?_
  have h := c.hyub s
  nlinarith [c.CU_nonneg, hpos.le, c.hDU, mul_nonneg c.hDU2 c.CU_nonneg]

theorem abs_yu''_le (s : ℝ) :
    |c.yu'' s| ≤ (CU + DU * CU + DU2 * CU) * Real.exp (-alpha * |s|) := by
  have hpos : (0:ℝ) < Real.exp (-alpha * |s|) := Real.exp_pos _
  refine (c.hyu''b s).trans ?_
  have h := c.hyub s
  nlinarith [c.CU_nonneg, hpos.le, c.hDU2, mul_nonneg c.hDU c.CU_nonneg]

/-- **The model curvature of the previous model is continuous.** -/
theorem continuous_KP : Continuous (modelCurvature c.yu c.yu' P) :=
  continuous_modelCurvature (Cp := CU + DU * CU + DU2 * CU) c.ha c.Ppos c.continuous_yu c.hyu'c
    c.abs_yu_le c.abs_yu'_le c.hyu0 c.hau0 c.hau1 c.hYau

/-- The model curvature of the previous model is periodic with its period. -/
theorem periodic_KP : Periodic (modelCurvature c.yu c.yu' P) P :=
  periodic_modelCurvature c.yu c.yu' P

/-- The pulse of the previous model stays below `au`, being dominated by its
periodization. -/
theorem yu_le_strip (s : ℝ) : c.yu s ≤ au := by
  have h := FrontPeriodizationIntegral.le_tsum_translates (y := c.yu) (P := P) (C := CU)
    c.ha c.Ppos c.hyu0 c.hyub s 0
  simp only [Int.cast_zero, zero_mul, sub_zero] at h
  exact h.trans (c.hYau s)

/-- **The intrinsic curvature of the isolated hairpin is continuous**, being
`yu + G(yu)·yu'`. -/
theorem continuous_Kstar : Continuous c.Kstar := by
  have heq : c.Kstar = fun s => c.yu s + G (c.yu s) * c.yu' s := funext c.hKstaru
  rw [heq]
  exact c.continuous_yu.add ((FrontPeriodizationIntegral.continuous_G_comp c.hau0 c.hau1
    c.continuous_yu c.hyu0 c.yu_le_strip).mul c.hyu'c)

/-- **The curvature of the isolated hairpin is dominated by its pulse**:
`|K_*| ≤ (1 + G(au)·DU)·yu`. -/
theorem abs_Kstar_le_pulse (s : ℝ) : |c.Kstar s| ≤ (1 + G au * DU) * c.yu s := by
  have hyu0 := c.hyu0 s
  have hGle : G (c.yu s) ≤ G au := PeriodizedTurning.G_le_G_of_le hyu0 (c.yu_le_strip s) c.hau1
  have hG0 : 0 ≤ G (c.yu s) := by simp [G]
  have hGa0 : 0 ≤ G au := hG0.trans hGle
  have hyu' : |c.yu' s| ≤ DU * c.yu s := c.hyu'b s
  have hprod : |G (c.yu s) * c.yu' s| ≤ G au * (DU * c.yu s) := by
    rw [abs_mul, abs_of_nonneg hG0]
    exact mul_le_mul hGle hyu' (abs_nonneg _) hGa0
  calc |c.Kstar s| = |c.yu s + G (c.yu s) * c.yu' s| := by rw [c.hKstaru s]
    _ ≤ |c.yu s| + |G (c.yu s) * c.yu' s| := abs_add_le _ _
    _ ≤ c.yu s + G au * (DU * c.yu s) := by rw [abs_of_nonneg hyu0]; linarith
    _ = (1 + G au * DU) * c.yu s := by ring

/-- **The curvature of the isolated hairpin is nonnegative**, the relative
derivative bound of its pulse being small on the strip. -/
theorem Kstar_nonneg (s : ℝ) : 0 ≤ c.Kstar s := by
  rcases c.hcurvNonnegU with hsmall | hdirect
  ·
    have hyu0 := c.hyu0 s
    have hGle : G (c.yu s) ≤ G au := PeriodizedTurning.G_le_G_of_le hyu0 (c.yu_le_strip s) c.hau1
    have hG0 : 0 ≤ G (c.yu s) := by simp [G]
    have hGa0 : 0 ≤ G au := hG0.trans hGle
    have hyu' : |c.yu' s| ≤ DU * c.yu s := c.hyu'b s
    have hlow : -(DU * c.yu s) ≤ c.yu' s := neg_le_of_abs_le hyu'
    have hprod : -(G au * (DU * c.yu s)) ≤ G (c.yu s) * c.yu' s := by
      rcases le_or_gt 0 (c.yu' s) with h | h
      · have h1 : 0 ≤ G (c.yu s) * c.yu' s := mul_nonneg hG0 h
        have h2 : 0 ≤ G au * (DU * c.yu s) := mul_nonneg hGa0 (mul_nonneg c.hDU hyu0)
        linarith
      · have h1 : G au * c.yu' s ≤ G (c.yu s) * c.yu' s := by nlinarith
        have h2 : G au * (-(DU * c.yu s)) ≤ G au * c.yu' s :=
          mul_le_mul_of_nonneg_left hlow hGa0
        nlinarith
    have hsm : G au * (DU * c.yu s) ≤ c.yu s := by
      have := mul_le_mul_of_nonneg_right hsmall hyu0
      nlinarith
    rw [c.hKstaru s]
    linarith
  · exact hdirect.1 s

/-- The curvature of the isolated hairpin is bounded. -/
theorem abs_Kstar_le (s : ℝ) : |c.Kstar s| ≤ Km :=
  (c.abs_Kstar_le_pulse s).trans
    ((mul_le_mul_of_nonneg_left (c.yu_le_strip s)
      (by nlinarith [c.hDU, c.hau0, show (0:ℝ) ≤ G au by simp [G]])).trans c.hKmU)

/-- The curvature of the isolated hairpin decays exponentially. -/
theorem abs_Kstar_le_exp (s : ℝ) : |c.Kstar s| ≤ CK * Real.exp (-alpha * |s|) := by
  have hfac : (0:ℝ) ≤ 1 + G au * DU := by
    nlinarith [c.hDU, show (0:ℝ) ≤ G au by simp [G]]
  have hpos : (0:ℝ) < Real.exp (-alpha * |s|) := Real.exp_pos _
  have h := (c.abs_Kstar_le_pulse s).trans (mul_le_mul_of_nonneg_left (c.hyub s) hfac)
  refine h.trans ?_
  have := mul_le_mul_of_nonneg_right c.hCKU hpos.le
  nlinarith

/-- **The derivative of the curvature of the isolated hairpin is produced** by
its pulse. -/
def Kstar' : ℝ → ℝ := hairpinCurvatureDeriv c.yu c.yu' c.yu''

/-- The curvature of the isolated hairpin is differentiable. -/
theorem hKderiv (u : ℝ) : HasDerivAt c.Kstar (c.Kstar' u) u := by
  have habs : |c.yu u| < 1 := by
    rw [abs_of_nonneg (c.hyu0 u)]
    exact lt_of_le_of_lt (c.yu_le_strip u) c.hau1
  have hG : HasDerivAt (fun v => G (c.yu v)) (lipConst (c.yu u) * c.yu' u) u := by
    have h := (FrontPeriodization.hasDerivAt_G habs).comp u (c.hyuderiv u)
    simpa [lipConst] using h
  have h := (c.hyuderiv u).add (hG.mul (c.hyu''deriv u))
  exact h.congr_deriv (by simp [Config.Kstar', hairpinCurvatureDeriv]; ring)

/-- Its derivative is bounded. -/
theorem abs_Kstar'_le (u : ℝ) : |c.Kstar' u| ≤ Kd := by
  refine le_trans ?_ c.hKdU
  have hyu0 := c.hyu0 u
  have hyule := c.yu_le_strip u
  have hau0 : 0 ≤ au := hyu0.trans hyule
  have hGle : G (c.yu u) ≤ G au := PeriodizedTurning.G_le_G_of_le hyu0 hyule c.hau1
  have hG0 : 0 ≤ G (c.yu u) := by simp [G]
  have hGa0 : 0 ≤ G au := hG0.trans hGle
  have hLle : lipConst (c.yu u) ≤ lipConst au :=
    PeriodizedCurvatureDeriv.lipConst_le_lipConst hyu0 hyule c.hau1
  have hL0 : 0 ≤ lipConst (c.yu u) :=
    FrontPeriodization.lipConst_nonneg hyu0 (lt_of_le_of_lt hyule c.hau1)
  have hLa0 : 0 ≤ lipConst au := hL0.trans hLle
  have h1 : |c.yu' u| ≤ DU * au :=
    (c.hyu'b u).trans (mul_le_mul_of_nonneg_left hyule c.hDU)
  have hsq : (c.yu' u) ^ 2 ≤ DU ^ 2 * au ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (c.yu' u)) h1 2
    calc (c.yu' u) ^ 2 = |c.yu' u| ^ 2 := (sq_abs _).symm
      _ ≤ (DU * au) ^ 2 := h
      _ = DU ^ 2 * au ^ 2 := by ring
  have h2 : |lipConst (c.yu u) * (c.yu' u) ^ 2| ≤ lipConst au * (DU ^ 2 * au ^ 2) := by
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul hLle hsq (by positivity) hLa0
  have h3 : |G (c.yu u) * c.yu'' u| ≤ G au * (DU2 * au) := by
    rw [abs_mul, abs_of_nonneg hG0]
    exact mul_le_mul hGle ((c.hyu''b u).trans (mul_le_mul_of_nonneg_left hyule c.hDU2))
      (abs_nonneg _) hGa0
  have h4 := abs_add_le (lipConst (c.yu u) * (c.yu' u) ^ 2) (G (c.yu u) * c.yu'' u)
  have h5 := abs_add_le (c.yu' u)
    (lipConst (c.yu u) * (c.yu' u) ^ 2 + G (c.yu u) * c.yu'' u)
  simp only [Config.Kstar', hairpinCurvatureDeriv]
  linarith

/-- The intrinsic curvature of the isolated hairpin is integrable. -/
theorem integrable_Kstar : Integrable c.Kstar :=
  FrontPeriodizationIntegral.integrable_of_exp_bound' c.ha c.continuous_Kstar c.abs_Kstar_le_exp

/-- **The model curvature of the previous model is nonnegative**: its front is
convex. -/
theorem KP_nonneg (r : ℝ) : 0 ≤ modelCurvature c.yu c.yu' P r := by
  rcases c.hcurvNonnegU with hsmall | hdirect
  · exact modelCurvature_nonneg (Cp := CU + DU * CU + DU2 * CU) c.ha c.Ppos c.hDU
      c.hyu0 c.abs_yu_le c.abs_yu'_le c.hyu'b c.hau1 c.hYau hsmall r
  · exact hdirect.2 r

/-- **The model curvature of the previous model is bounded** by `kstar`. -/
theorem KP_le (r : ℝ) : modelCurvature c.yu c.yu' P r ≤ kstar :=
  (modelCurvature_le (Cp := CU + DU * CU + DU2 * CU) c.ha c.Ppos c.hDU c.hyu0 c.abs_yu_le
    c.abs_yu'_le c.hyu'b c.hau1 c.hYau r).trans c.hkstarU

/-- **The total turning of the previous model over one period is `π`**, the
pulse having the steering mass `∫_ℝ yu = π` of the hairpin. -/
theorem integral_KP_eq_pi : (∫ r in (0:ℝ)..P, modelCurvature c.yu c.yu' P r) = Real.pi :=
  integral_modelCurvature_eq_pi (Cp := CU + DU * CU + DU2 * CU) c.ha c.Ppos c.continuous_yu c.hyu'c
    c.hyuderiv c.abs_yu_le c.abs_yu'_le c.hyu0 c.hyuint c.hau0 c.hau1
    (fun v => by
      rw [abs_of_nonneg (tsum_nonneg fun m => c.hyu0 _)]
      exact c.hYau v)
    c.hmassu

/-- **The derivative of the model curvature of the previous model is
produced** by its pulse. -/
def KP' : ℝ → ℝ := modelCurvatureDeriv c.yu c.yu' c.yu'' P

/-- The periodization of the previous pulse stays on the strip. -/
theorem abs_periodization_yu_le (v : ℝ) : |∑' m : ℤ, c.yu (v - m * P)| ≤ au := by
  rw [abs_of_nonneg (tsum_nonneg fun m => c.hyu0 _)]
  exact c.hYau v

/-- The model curvature of the previous model is differentiable. -/
theorem hd1 (r : ℝ) : HasDerivAt (modelCurvature c.yu c.yu' P) (c.KP' r) r :=
  hasDerivAt_modelCurvature (Cp := CU + DU * CU + DU2 * CU) c.ha c.Ppos c.hyuderiv
    c.hyu''deriv c.abs_yu_le c.abs_yu'_le c.abs_yu''_le c.hau1 c.abs_periodization_yu_le r

/-- Its derivative is continuous. -/
theorem continuous_KP' : Continuous c.KP' :=
  continuous_modelCurvatureDeriv (Cp := CU + DU * CU + DU2 * CU) c.ha c.Ppos
    c.continuous_yu c.hyu'c c.hyu''c c.abs_yu_le c.abs_yu'_le c.abs_yu''_le c.hau1
    c.abs_periodization_yu_le

/-- And it is bounded by `kd`. -/
theorem abs_KP'_le (r : ℝ) : |c.KP' r| ≤ kd :=
  (abs_modelCurvatureDeriv_le (Cp := CU + DU * CU + DU2 * CU) c.ha c.Ppos c.hDU c.hDU2
    c.hyu0 c.abs_yu_le c.abs_yu'_le c.abs_yu''_le c.hyu'b c.hyu''b c.hau1 c.hYau r).trans
    c.hkdU

/-- The rear arclength of the configuration is continuous. -/
theorem continuous_rearArclength : Continuous (modelRearArclength c.Y) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_rearArclength c.continuous_dl t).continuousAt

/-- **The omitted translates of the hairpin curvature sum to a continuous
function**: the full periodization is continuous, and the central term is
split off from it. -/
theorem continuous_puncturedSum :
    Continuous fun u => ∑' j : {j : ℤ // j ≠ 0}, c.Kstar (u - (j : ℤ) * P) := by
  have hfull : Continuous fun u => ∑' m : ℤ, c.Kstar (u - m * P) :=
    FrontPeriodizationIntegral.continuous_tsum_translates c.ha c.Ppos c.continuous_Kstar
      c.abs_Kstar_le_exp
  have heq : ∀ u, (∑' j : {j : ℤ // j ≠ 0}, c.Kstar (u - (j : ℤ) * P))
      = (∑' m : ℤ, c.Kstar (u - m * P)) - c.Kstar u := by
    intro u
    have hs : Summable fun m : ℤ => c.Kstar (u - m * P) :=
      FrontPeriodizationIntegral.summable_translates c.ha c.Ppos c.abs_Kstar_le_exp u
    have hsplit := FrontPeriodizationIntegral.tsum_split_zero hs
    simp only [Int.cast_zero, zero_mul, sub_zero] at hsplit
    linarith
  simpa only [heq] using hfull.sub c.continuous_Kstar

/-- The sum of the translates of the hairpin curvature is continuous. -/
theorem continuous_Kbar : Continuous c.Kbar := by
  have heq : c.Kbar = fun u => c.Kstar u + ∑' j : {j : ℤ // j ≠ 0}, c.Kstar (u - (j : ℤ) * P) :=
    funext c.hKbar
  rw [heq]
  exact c.continuous_Kstar.add c.continuous_puncturedSum

/-- The gap between the rear curvature and the sum of the translates is
continuous. -/
theorem continuous_kH_sub_Kbar : Continuous fun u => |c.kH u - c.Kbar u| :=
  (c.continuous_kH.sub c.continuous_Kbar).abs

/-- The gap between the rear curvature and the model curvature of period `P` is
integrable over the rear period. -/
theorem intervalIntegrable_kH_sub :
    IntervalIntegrable (fun u => |c.kH u - modelCurvature c.yu c.yu' P u|) volume
      (modelRearArclength c.Y (-(H / 2))) (modelRearArclength c.Y (H / 2)) :=
  ((c.continuous_kH.sub c.continuous_KP).abs).intervalIntegrable _ _

/-- The gap between the sum of the translates and the model curvature of period
`P` is integrable over the rear period. -/
theorem intervalIntegrable_Kbar_sub :
    IntervalIntegrable (fun u => |c.Kbar u - modelCurvature c.yu c.yu' P u|) volume
      (modelRearArclength c.Y (-(H / 2))) (modelRearArclength c.Y (H / 2)) :=
  ((c.continuous_Kbar.sub c.continuous_KP).abs).intervalIntegrable _ _

/-- The omitted translates, read in the rear arclength and weighted by the rear
speed, are integrable over one front period. -/
theorem intervalIntegrable_puncturedSum :
    IntervalIntegrable
      (fun s => Real.sqrt (1 - (c.Y s) ^ 2) *
        ∑' j : {j : ℤ // j ≠ 0}, c.Kstar (modelRearArclength c.Y s - (j : ℤ) * P))
      volume (-(H / 2)) (H / 2) :=
  (((continuous_const.sub (c.continuous_Y.pow 2)).sqrt).mul
    (c.continuous_puncturedSum.comp c.continuous_rearArclength)).intervalIntegrable _ _

/-- The steering pulse is periodic with the separation. -/
theorem periodic_Y : Periodic c.Y H := by
  intro u
  rw [c.hYdef (u + H), c.hYdef u]
  exact PeriodizedTurning.periodic_periodization c.y H u

theorem periodic_dl : Periodic (modelSteering c.Y) H := by
  intro u
  simp only [modelSteering, c.periodic_Y u]

/-- **The rear period is the rear arclength of one front period.** -/
theorem rearPeriod_eq : modelRearArclength c.Y H = P := c.hPdef

/-- **One front period is one rear period.** -/
theorem rearArclength_period : modelRearArclength c.Y (H / 2)
    = modelRearArclength c.Y (-(H / 2)) + P := by
  have h := ArclengthInverse.rearArclength_add_period c.continuous_dl c.periodic_dl (-(H / 2))
  rw [show -(H / 2) + H = H / 2 by ring] at h
  have h2 := c.hPdef
  simp only [modelRearArclength] at h h2 ⊢
  linarith

/-- The right endpoint of a rear period is nonnegative. -/
theorem rearArclength_right_nonneg : 0 ≤ modelRearArclength c.Y (-(H / 2)) + P := by
  rw [← c.rearArclength_period, ← c.rearArclength_zero]
  exact (c.strictMono_rearArclength.le_iff_le).mpr (by linarith [c.hH])

/-- **The rear curvature is periodic with the rear period.** -/
theorem periodic_kH : Periodic c.kH P := by
  intro x
  have hstep : c.sf (x + P) = c.sf x + H := by
    have h := SelectedInverseRearOwn.sf_add_rearPeriod (P := H)
      (sqrt_one_sub_sq_pos c.ha0 c.ha1) c.continuous_dl c.cos_dl_ge c.periodic_dl
      c.sf_rightInverse x
    rw [show rearArclength (modelSteering c.Y) H = P from c.rearPeriod_eq] at h
    exact h
  rw [c.kH_eq, c.kH_eq, hstep]
  simp only [modelSteering, c.periodic_Y (c.sf x)]

/-- **The total turning of the rear over one period is `π`**: the change of
variables `dx = cos δ ds` turns it into the mass `∫_ℝ y = π` of the pulse. -/
theorem integral_kH_eq_pi : (∫ r in (0:ℝ)..P, c.kH r) = Real.pi := by
  have hxH0 : modelRearArclength c.Y 0 = 0 := by
    simp [modelRearArclength, rearArclength]
  have hsub := intervalIntegral.integral_comp_smul_deriv
    (f := modelRearArclength c.Y) (f' := fun s => Real.cos (modelSteering c.Y s))
    (g := c.kH) (a := 0) (b := H)
    (fun x _ => hasDerivAt_rearArclength c.continuous_dl x)
    ((Real.continuous_cos.comp c.continuous_dl).continuousOn) c.continuous_kH
  rw [hxH0, c.rearPeriod_eq] at hsub
  rw [← hsub]
  have hpoint : ∀ s : ℝ, Real.cos (modelSteering c.Y s) •
      (c.kH ∘ modelRearArclength c.Y) s = c.Y s := by
    intro s
    have hk : c.kH (modelRearArclength c.Y s) = Real.tan (modelSteering c.Y s) := by
      rw [c.kH_eq, c.sf_leftInverse s]
    simp only [Function.comp_apply, smul_eq_mul, hk, Real.tan_eq_sin_div_cos]
    have hcos : Real.cos (modelSteering c.Y s) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (sqrt_one_sub_sq_pos c.ha0 c.ha1) (c.cos_dl_ge s))
    field_simp
    exact sin_modelSteering c.ha1.le (c.hYa s)
  rw [intervalIntegral.integral_congr (fun s _ => hpoint s)]
  have hmassint := PeriodizedTurning.integral_periodization_eq_integral (y := c.y) (P := H)
    c.hH c.hyint c.hy0 0
  rw [zero_add] at hmassint
  rw [intervalIntegral.integral_congr (g := fun s => ∑' m : ℤ, c.y (s - m * H))
    (fun s _ => c.hYdef s), hmassint, c.hmass]

/-! #### The derivative of the rear curvature is produced -/

theorem cos_dl_pos (s : ℝ) : 0 < Real.cos (modelSteering c.Y s) :=
  lt_of_lt_of_le (sqrt_one_sub_sq_pos c.ha0 c.ha1) (c.cos_dl_ge s)

/-- **The rear curvature is differentiable**, of derivative `(K − Y)/cos³δ` read
in the rear arclength. -/
theorem hasDerivAt_kH (z : ℝ) :
    HasDerivAt c.kH (kHderiv c.Y (modelCurvature c.y c.yd H) c.sf z) z := by
  have hsf : HasDerivAt c.sf (1 / Real.cos (modelSteering c.Y (c.sf z))) z :=
    ArclengthInverse.hasDerivAt_of_rightInverse (sqrt_one_sub_sq_pos c.ha0 c.ha1)
      (fun s => hasDerivAt_rearArclength c.continuous_dl s) c.cos_dl_ge c.sf_rightInverse z
  have htan : HasDerivAt Real.tan (1 / Real.cos (modelSteering c.Y (c.sf z)) ^ 2)
      (modelSteering c.Y (c.sf z)) := Real.hasDerivAt_tan (c.cos_dl_pos _).ne'
  have hcomp := (htan.comp (c.sf z) (c.hasDerivAt_dl (c.sf z))).comp z hsf
  have hfun : c.kH = fun w => Real.tan (modelSteering c.Y (c.sf w)) := funext c.kH_eq
  rw [hfun]
  refine (hcomp.congr_deriv ?_ :)
  have hne : Real.cos (modelSteering c.Y (c.sf z)) ≠ 0 := (c.cos_dl_pos _).ne'
  rw [kHderiv, sin_modelSteering c.ha1.le (c.hYa (c.sf z))]
  field_simp

/-- The derivative of the rear curvature is continuous. -/
theorem continuous_kHderiv :
    Continuous (kHderiv c.Y (modelCurvature c.y c.yd H) c.sf) := by
  have hsf : Continuous c.sf := c.continuous_sf
  have hnum : Continuous fun z =>
      modelCurvature c.y c.yd H (c.sf z) - c.Y (c.sf z) :=
    (c.continuous_frontCurvature.comp hsf).sub (c.continuous_Y.comp hsf)
  have hden : Continuous fun z => Real.cos (modelSteering c.Y (c.sf z)) ^ 3 :=
    ((Real.continuous_cos.comp (c.continuous_dl.comp hsf))).pow 3
  exact hnum.div hden fun z => pow_ne_zero 3 (c.cos_dl_pos (c.sf z)).ne'

/-- **The derivative of the rear curvature is bounded**, by an explicit constant
in the pulse data. -/
theorem abs_kHderiv_le (z : ℝ) :
    |kHderiv c.Y (modelCurvature c.y c.yd H) c.sf z| ≤ kd := by
  refine le_trans ?_ c.hkdge
  have hK : |modelCurvature c.y c.yd H (c.sf z)| ≤ (1 + G a * D) * a :=
    abs_modelCurvature_le c.ha c.hH c.hD0 c.hy0 c.abs_y_le c.hydb c.hrelD c.ha1
      c.periodization_le _
  have hYb : |c.Y (c.sf z)| ≤ a := c.hYa _
  have hnum : |modelCurvature c.y c.yd H (c.sf z) - c.Y (c.sf z)| ≤ (1 + G a * D) * a + a :=
    le_trans (abs_sub _ _) (add_le_add hK hYb)
  have hc0 : 0 < Real.sqrt (1 - a ^ 2) := sqrt_one_sub_sq_pos c.ha0 c.ha1
  have hGa : 0 ≤ G a := by rw [G]; positivity
  have hGaD : 0 ≤ G a * D := mul_nonneg hGa c.hD0
  have hnn : 0 ≤ (1 + G a * D) * a + a := by nlinarith [c.ha0]
  have hcosge : Real.sqrt (1 - a ^ 2) ≤ Real.cos (modelSteering c.Y (c.sf z)) :=
    c.cos_dl_ge _
  have hdenpos : 0 < Real.cos (modelSteering c.Y (c.sf z)) ^ 3 :=
    pow_pos (c.cos_dl_pos _) 3
  rw [kHderiv, abs_div, abs_of_pos hdenpos]
  calc |modelCurvature c.y c.yd H (c.sf z) - c.Y (c.sf z)|
        / Real.cos (modelSteering c.Y (c.sf z)) ^ 3
      ≤ ((1 + G a * D) * a + a) / Real.cos (modelSteering c.Y (c.sf z)) ^ 3 := by
        gcongr
    _ ≤ ((1 + G a * D) * a + a) / Real.sqrt (1 - a ^ 2) ^ 3 := by
        gcongr

/-- **The defect estimate of the model pseudo-orbit.**

The marked selected inverse of the model front of separation `H` — the rear
track of that front, written in its own arclength and marked at `x = 0` — and
the model front of separation `P` are at path pseudodistance, modulo a rigid
motion, at most the interpolation cost of the matching bound `C·e^{−βH}`.

Every datum of the rear side is produced: the steering angle is `arcsin Y`, the
rear arclength is `∫ cos δ`, and the front is the reconstruction from the model
curvature of separation `H`. -/
theorem pathDistRigid_le :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * P) ∧
      ∀ p' q' : Data,
        (∀ u, p'.1 u = rearTrack (c.frontCurve (theta0 := theta0))
          (c.frontTangentAngle (theta0 := theta0)) (modelSteering c.Y) (c.sf (2 * P * u))) →
        (∀ u, q'.1 u = interpCurve (modelCurvature c.yu c.yu' P) theta0 P (psi u)) →
        pathDistRigid p' q' ≤ interpCostL1 kstar kd P eps0
          (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * H))) := by
  -- the produced rear geometry
  set dl := modelSteering c.Y with hdl
  have hdc : Continuous dl := continuous_modelSteering c.continuous_Y
  have hcpos : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr (by nlinarith [c.ha0, c.ha1])
  have hcos : ∀ s, Real.sqrt (1 - a ^ 2) ≤ Real.cos (dl s) := fun s =>
    cos_modelSteering_ge (c.hYa s)
  have hYsin : ∀ t, c.Y t = Real.sin (dl t) := fun t =>
    (sin_modelSteering c.ha1.le (c.hYa t)).symm
  have hsqY : ∀ t, Real.sqrt (1 - (c.Y t) ^ 2) = Real.cos (dl t) := fun t =>
    (cos_modelSteering (Y := c.Y) (s := t)).symm
  -- the steering equation for the model curvature of separation `H`
  have hode : ∀ s, HasDerivAt dl (modelCurvature c.y c.yd H s - Real.sin (dl s)) s :=
    c.hasDerivAt_dl
  -- the front data
  have hFd : ∀ s, HasDerivAt (c.frontCurve (theta0 := theta0))
      (Complex.exp (Complex.I * (c.frontTangentAngle (theta0 := theta0) s : ℂ))) s := fun s =>
    front_hasDerivAt (theta0 := theta0) (H := H) c.continuous_frontCurvature s
  have hTh : ∀ s, HasDerivAt (c.frontTangentAngle (theta0 := theta0))
      (modelCurvature c.y c.yd H s) s := fun s =>
    hasDerivAt_tangentAngle (θ₀ := theta0) c.continuous_frontCurvature s
  -- the rear arclength
  have hxH : ∀ t, HasDerivAt (modelRearArclength c.Y) (Real.sqrt (1 - (c.Y t) ^ 2)) t := by
    intro t
    rw [hsqY t]
    exact hasDerivAt_rearArclength hdc t
  have hx0 : modelRearArclength c.Y 0 = c.x 0 := by
    rw [c.hx0]
    simp [modelRearArclength, rearArclength]
  have hkstar0 : 0 ≤ kstar :=
    le_trans (div_nonneg c.ha0 (Real.sqrt_nonneg _)) c.hkstar
  exact pathDistRigid_rearOwn_front_le_of_matching
    (Θ := c.frontTangentAngle (theta0 := theta0)) (K := modelCurvature c.y c.yd H)
    (dl := dl) (sf := c.sf) (kH := c.kH) (F := c.frontCurve (theta0 := theta0))
    (Y := c.Y) (y := c.y) (xH := modelRearArclength c.Y) (x := c.x)
    (Kstar := c.Kstar) (Kstar' := c.Kstar') (Kbar := c.Kbar)
    (KP := modelCurvature c.yu c.yu' P) (yu := c.yu) (yu' := c.yu')
    (kH' := kHderiv c.Y (modelCurvature c.y c.yd H) c.sf) (KP' := c.KP')
    (theta0 := theta0) (kstar := kstar) (kd := kd)
    (eps0 := eps0) (c := Real.sqrt (1 - a ^ 2))
    c.ha c.hy0 c.hyb c.hH c.hq2 c.hYdef c.ha0 c.ha1 c.continuous_Y c.continuous_y c.hYa
    c.abs_y_le_strip hxH c.hx hx0
    c.hid c.abs_Kstar_le c.hKderiv c.abs_Kstar'_le c.continuous_Kstar c.hbeta0 c.hbeta c.hk
    c.continuous_kH_sub_Kbar c.hKbar c.intervalIntegrable_puncturedSum
    c.intervalIntegrable_kH_sub c.intervalIntegrable_Kbar_sub c.rearArclength_period c.Ppos
    c.integrable_Kstar c.Kstar_nonneg c.abs_Kstar_le_exp c.rearArclength_left_nonpos
    c.rearArclength_right_nonneg c.hpB c.hqB c.hhalf
    c.continuous_yu c.hyu'c c.hyu0 c.hyub c.hDU c.hyu'b c.hau0 c.hau1 c.hYau c.hKstaru
    (fun _ => rfl) c.hPH c.continuous_kH c.continuous_KP c.continuous_kHderiv c.continuous_KP'
    c.periodic_kH c.periodic_KP c.integral_kH_eq_pi c.integral_KP_eq_pi c.hkd hkstar0
    c.hasDerivAt_kH c.hd1
    c.abs_kHderiv_le c.abs_KP'_le c.kH_nonneg c.KP_nonneg c.kH_le c.KP_le c.heps0
    hcpos hdc hcos c.sf_rightInverse hFd hTh hode (fun _ => rfl) hYsin

end Config

/-! ### The estimate along the recursion of the pseudo-orbit -/

/-- **The defect estimate along the model pseudo-orbit.**  With the separations
fixed by the recursion `P(H_{n+1}) = H_n` — so that the rear of the `(n+1)`-st
pair has the period `H_n` of the `n`-th model — the marked selected inverse of
the `(n+1)`-st model front and the `n`-th model front are at path
pseudodistance, modulo a rigid motion, at most the interpolation cost of
`C·e^{−βH_{n+1}}`, which tends to zero as `n → ∞`. -/
theorem pathDistRigid_selInv_model_orbit {alpha beta a au C CU CK DU DU2 D Km Kd B theta0
    kstar kd : ℝ} {eps0 : ℕ → ℝ} {Hs : ℕ → ℝ}
    (cfg : ∀ n, Config alpha beta a au C CU CK DU DU2 D Km Kd B theta0 kstar kd (eps0 n)
      (Hs (n + 1)) (Hs n)) (n : ℕ) :
    ∃ psi : ℝ → ℝ, Continuous psi ∧ (∀ u, psi (u + 1) = psi u + 2 * Hs n) ∧
      ∀ p' q' : Data,
        (∀ u, p'.1 u = rearTrack ((cfg n).frontCurve (theta0 := theta0))
          ((cfg n).frontTangentAngle (theta0 := theta0)) (modelSteering (cfg n).Y)
          ((cfg n).sf (2 * Hs n * u))) →
        (∀ u, q'.1 u = interpCurve (modelCurvature (cfg n).yu (cfg n).yu' (Hs n))
          theta0 (Hs n) (psi u)) →
        pathDistRigid p' q' ≤ interpCostL1 kstar kd (Hs n) (eps0 n)
          (matchConst a C CK CU DU Km Kd au alpha beta B * Real.exp (-(beta * Hs (n + 1)))) :=
  (cfg n).pathDistRigid_le

/-- **The produced steering angle is not vacuous**: for the pulse `Y = ½cos`,
`δ = arcsin Y` solves the steering equation of the exact front curvature
`K = Y + G(Y)·Y'`. -/
theorem hasDerivAt_modelSteering_instance (s : ℝ) :
    HasDerivAt (modelSteering fun z => Real.cos z / 2)
      (((fun z => Real.cos z / 2) s + G ((fun z => Real.cos z / 2) s) * (-Real.sin s / 2))
        - Real.sin (modelSteering (fun z => Real.cos z / 2) s)) s := by
  refine hasDerivAt_modelSteering (a := 1 / 2) (Yd := fun z => -Real.sin z / 2) ?_
    (by norm_num) ?_
  · simpa using (Real.hasDerivAt_cos s).div_const 2
  · rw [abs_div, abs_two]
    have := Real.abs_cos_le_one s
    linarith

/-- The defect of the pseudo-orbit tends to zero along the recursion, as soon as
the separations tend to infinity. -/
theorem tendsto_defect_zero {kstar kd L eps0 Cm beta : ℝ} {Hs : ℕ → ℝ}
    (hL : 0 < L) (hbeta : 0 < beta) (hHs : Filter.Tendsto Hs Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n : ℕ => interpCostL1 kstar kd L eps0 (Cm * Real.exp (-(beta * Hs n))))
      Filter.atTop (nhds 0) :=
  (MatchingPathDist.tendsto_interpCostL1_exp (kstar := kstar) (kd := kd) (eps0 := eps0)
    (C := Cm) hL hbeta).comp hHs

end ModelOrbitDefect
