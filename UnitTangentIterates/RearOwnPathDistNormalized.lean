import Mathlib
import UnitTangentIterates.RearOwnPathDistSlices
import UnitTangentIterates.SteeringNormalizedPeriod
import UnitTangentIterates.SecondOrderBounds

/-!
# The path-distance bound with the front data in the normalized parameter

`RearOwnPathDistSlices.pathDist_le_of_front_slices` states the bound for the
selected rears of a normal path of fronts with every hypothesis on the front,
but it takes the curvature data in the **arclength** of each slice, and there it
asks the parameter derivative `K̇` of the curvature to be periodic with the
current period `P(t)`.  `SteeringPeriodRigidity.lean` shows that this is rigid:
it forces `P'(t) ∂_sK = 0`, so the period cannot move unless the fronts are
circles.

This file removes the restriction.  The curvature and the steering angle are
given in the **normalized** parameter `σ = s / P(t)`,

```
  δ(t, s) = δ̂(t, s / P t) ,     K(t, s) = K̂(t, s / P t) ,
```

with `δ̂(t, ·)`, `K̂(t, ·)` and `K̂̇(t, ·)` all `1`-periodic, the steering equation
reading `∂_σ δ̂ = P(t)(K̂ − sin δ̂)`.  Everything the assembly needs is derived
from that:

* `hasDerivAt_delta_arclength`, `periodic_delta_arclength` — the steering
  equation and the periodicity in the arclength;
* `contDiff_four_uncurry_delta_of_normalized` — the joint `C⁴` regularity of the
  steering angle, from `SteeringNormalizedPeriod.lean`, with **no** restriction
  on the motion of the period;
* `abs_delta_sub_le_of_normalized` — the Lipschitz bound in the path parameter,
  which in this parametrization only holds on a bounded range of the arclength
  (two slices are compared at the points `s/P(a)` and `s/P(b)` of the normalized
  circle, which drift apart as `|s|` grows) — enough for the endpoint term of
  the rear period, by the local Leibniz rule of `RearPeriodDeriv.lean`;
* `exists_hasDerivAt_rearPeriod_local` — the derivative of the rear period.

Main result: `pathDist_le_of_front_normalized`.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistNormalized

open UniformFrameBounds GaugePathDistVariable RearOwnPathDistSmooth
  RearOwnHigherRegularity SelectedInverseJacobiODE RearOwnPathDistIntrinsic
  RearOwnPathDistSlices

variable {F : ℝ → ℝ → ℂ} {Θ δ K dn Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-! ### The steering data in the arclength of each slice -/

/-- **The steering equation in the arclength.**  If the normalized steering
angle solves `∂_σ δ̂ = P(t)(K̂ − sin δ̂)`, then `δ(t, s) = δ̂(t, s/P t)` solves
`δ_s = K − sin δ` for `K(t, s) = K̂(t, s/P t)`. -/
theorem hasDerivAt_delta_arclength (hPpos : ∀ t, 0 < P t)
    (hdelta : ∀ t s, δ t s = dn t (s / P t)) (hK : ∀ t s, K t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) (t s : ℝ) :
    HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s := by
  have hne : P t ≠ 0 := (hPpos t).ne'
  have hdiv : HasDerivAt (fun x : ℝ => x / P t) (1 / P t) s := by
    simpa using (hasDerivAt_id s).div_const (P t)
  have hcomp : HasDerivAt (fun x : ℝ => dn t (x / P t))
      (P t * (Kn t (s / P t) - Real.sin (dn t (s / P t))) * (1 / P t)) s := by
    simpa [Function.comp] using (hsol t (s / P t)).comp s hdiv
  have hval : P t * (Kn t (s / P t) - Real.sin (dn t (s / P t))) * (1 / P t)
      = K t s - Real.sin (dn t (s / P t)) := by
    rw [hK t s]; field_simp
  rw [hval] at hcomp
  have hfun : δ t = fun x : ℝ => dn t (x / P t) := funext (hdelta t)
  rw [hfun]
  exact hcomp

/-- **The steering angle is periodic with the front period.** -/
theorem periodic_delta_arclength (hPpos : ∀ t, 0 < P t)
    (hdelta : ∀ t s, δ t s = dn t (s / P t)) (hdnper : ∀ t, Function.Periodic (dn t) 1)
    (t : ℝ) : Function.Periodic (δ t) (P t) := by
  intro s
  have hne : P t ≠ 0 := (hPpos t).ne'
  have harg : (s + P t) / P t = s / P t + 1 := by field_simp
  rw [hdelta t (s + P t), hdelta t s, harg]
  exact hdnper t (s / P t)

/-- The normalized steering angle is Lipschitz in the normalized parameter, with
constant `2 P₁ κ̂`. -/
theorem abs_dn_sub_arg_le (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1) (hP0 : 0 < P0)
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh) (t σ₁ σ₂ : ℝ) :
    |dn t σ₁ - dn t σ₂| ≤ 2 * P1 * kh * |σ₁ - σ₂| := by
  have hPtpos : 0 < P t := lt_of_lt_of_le hP0 (hPl t)
  have hbd : ∀ σ, |P t * (Kn t σ - Real.sin (dn t σ))| ≤ 2 * P1 * kh := by
    intro σ
    have hsin0 : 0 ≤ Real.sin (dn t σ) := by
      have h := hstrip t σ
      have hpi : Real.arcsin kh ≤ Real.pi := le_trans (Real.arcsin_le_pi_div_two kh)
        (by linarith [Real.pi_pos])
      exact Real.sin_nonneg_of_nonneg_of_le_pi h.1 (le_trans h.2 hpi)
    have hsin1 : Real.sin (dn t σ) ≤ kh := by
      have h := hstrip t σ
      have hkk : Real.sin (Real.arcsin kh) = kh :=
        Real.sin_arcsin (by linarith) (le_of_lt hkh1)
      have hlo : -(Real.pi / 2) ≤ dn t σ := by linarith [h.1, Real.pi_pos]
      have hle := Real.sin_le_sin_of_le_of_le_pi_div_two hlo
        (Real.arcsin_le_pi_div_two kh) h.2
      rwa [hkk] at hle
    have hKn := hKnbd t σ
    rw [abs_le] at hKn ⊢
    have hP1 : P t ≤ P1 := hPu t
    have hP1pos : 0 < P1 := lt_of_lt_of_le hPtpos hP1
    have hkh1 : 0 ≤ kh := hkh0
    constructor
    · nlinarith [hKn.1, hKn.2, hsin0, hsin1, hPtpos.le]
    · nlinarith [hKn.1, hKn.2, hsin0, hsin1, hPtpos.le]
  exact SecondOrderBounds.abs_sub_le_of_deriv_bound (g := dn t)
    (g' := fun σ => P t * (Kn t σ - Real.sin (dn t σ))) (hsol t) hbd σ₁ σ₂

/-- **The steering angle in the arclength is Lipschitz in the path parameter on
a bounded range of the arclength.**  The two slices are compared at the points
`s/P(a)` and `s/P(b)` of the normalized circle; the drift of those points is
proportional to `|s|`, so the constant grows with the range. -/
theorem abs_delta_sub_le_of_normalized {R : ℝ} (hP0 : 0 < P0)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hRnn : 0 ≤ R)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hdelta : ∀ t s, δ t s = dn t (s / P t))
    (hKncont : Continuous (uncurry Kn))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (a b s : ℝ) (hs : |s| ≤ R) :
    |δ a s - δ b s|
      ≤ (SteeringNormalizedPeriod.lipConst P0 P1 kh Klip Plip
          + 2 * P1 * kh * (R * Plip / P0 ^ 2)) * |a - b| := by
  have hPapos : 0 < P a := lt_of_lt_of_le hP0 (hPl a)
  have hPbpos : 0 < P b := lt_of_lt_of_le hP0 (hPl b)
  -- the two steps
  have h1 : |dn a (s / P a) - dn b (s / P a)|
      ≤ SteeringNormalizedPeriod.lipConst P0 P1 kh Klip Plip * |a - b| :=
    SteeringNormalizedPeriod.abs_delta_sub_le (P0 := P0) (P1 := P1) (kap := kh)
      (Klip := Klip) (Plip := Plip) hP0 hkh0 hkh1 hPl hPu hKncont hsol hstrip hKnbd
      hKnlip hPlip a b (s / P a)
  have harg : |s / P a - s / P b| ≤ R * Plip / P0 ^ 2 * |a - b| := by
    have hrw : s / P a - s / P b = s * (P b - P a) / (P a * P b) := by
      field_simp
    rw [hrw, abs_div, abs_mul]
    have hden : |P a * P b| = P a * P b := abs_of_pos (mul_pos hPapos hPbpos)
    have hdenge : P0 ^ 2 ≤ P a * P b := by
      have := hPl a; have := hPl b; nlinarith [hP0.le]
    have hnum : |s| * |P b - P a| ≤ R * (Plip * |a - b|) := by
      have hPab : |P b - P a| ≤ Plip * |a - b| := by
        have := hPlip b a
        rw [abs_sub_comm b a] at this
        exact this
      have hPlnn : 0 ≤ Plip * |a - b| := le_trans (abs_nonneg _) (hPlip a b)
      exact mul_le_mul hs hPab (abs_nonneg _) hRnn
    rw [hden]
    have hpos : (0 : ℝ) < P a * P b := mul_pos hPapos hPbpos
    rw [div_le_iff₀ hpos]
    have hP0sq : (0 : ℝ) < P0 ^ 2 := by positivity
    have hnn : 0 ≤ R * Plip * |a - b| := by
      have hPlnn : 0 ≤ Plip := by
        have h1 := hPlip 1 0
        have h2 : (0 : ℝ) ≤ Plip * |(1 : ℝ) - 0| := le_trans (abs_nonneg _) h1
        simpa using h2
      positivity
    have hgoal : R * (Plip * |a - b|) ≤ R * Plip / P0 ^ 2 * |a - b| * (P a * P b) := by
      have hkey : R * Plip / P0 ^ 2 * |a - b| * (P a * P b)
          = R * Plip * |a - b| * (P a * P b) / P0 ^ 2 := by
        field_simp
      rw [hkey, le_div_iff₀ hP0sq]
      calc R * (Plip * |a - b|) * P0 ^ 2 = R * Plip * |a - b| * P0 ^ 2 := by ring
        _ ≤ R * Plip * |a - b| * (P a * P b) := mul_le_mul_of_nonneg_left hdenge hnn
    exact le_trans hnum hgoal
  have h2 : |dn b (s / P a) - dn b (s / P b)| ≤ 2 * P1 * kh * (R * Plip / P0 ^ 2 * |a - b|) := by
    have hstep := abs_dn_sub_arg_le (P0 := P0) (P1 := P1) hkh0 hkh1 hPl hPu hP0 hsol hstrip
      hKnbd b (s / P a) (s / P b)
    have hcoef : 0 ≤ 2 * P1 * kh := by
      have hP1pos : 0 < P1 := lt_of_lt_of_le hPapos (hPu a)
      positivity
    exact le_trans hstep (mul_le_mul_of_nonneg_left harg hcoef)
  calc |δ a s - δ b s| = |dn a (s / P a) - dn b (s / P b)| := by rw [hdelta, hdelta]
    _ ≤ |dn a (s / P a) - dn b (s / P a)| + |dn b (s / P a) - dn b (s / P b)| := by
        have := abs_add_le (dn a (s / P a) - dn b (s / P a)) (dn b (s / P a) - dn b (s / P b))
        simpa using this
    _ ≤ SteeringNormalizedPeriod.lipConst P0 P1 kh Klip Plip * |a - b|
          + 2 * P1 * kh * (R * Plip / P0 ^ 2 * |a - b|) := add_le_add h1 h2
    _ = (SteeringNormalizedPeriod.lipConst P0 P1 kh Klip Plip
          + 2 * P1 * kh * (R * Plip / P0 ^ 2)) * |a - b| := by ring

/-! ### The derivative of the rear period, with a local Lipschitz bound -/

/-- **The rear arclength period is differentiable in the time**, with the
Lipschitz bound in the path parameter required only on a bounded range of the
arclength. -/
theorem exists_hasDerivAt_rearPeriod_local {L R : ℝ}
    (hδdiff : Differentiable ℝ (uncurry δ))
    (hdtc : Continuous (uncurry (partialTime δ)))
    (hPR : ∀ t, |P t| < R)
    (hlipδ : ∀ a b s, |s| ≤ R → |δ a s - δ b s| ≤ L * |a - b|)
    (hPdiff : Differentiable ℝ P) :
    ∃ Qf' : ℝ → ℝ, ∀ t, HasDerivAt (fun r => rearArclength (δ r) (P r)) (Qf' t) t := by
  have hδc : Continuous (uncurry δ) := hδdiff.continuous
  have hdt : ∀ t s, HasDerivAt (fun r => δ r s) (partialTime δ t s) t :=
    hasDerivAt_partialTime hδdiff
  refine ⟨fun t => Real.cos (δ t (P t)) * deriv P t
      + ∫ u in (0:ℝ)..(P t), SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t u, ?_⟩
  intro t
  have hlip : ∀ r s, |s| ≤ R → |Real.cos (δ r s) - Real.cos (δ t s)| ≤ L * |r - t| := by
    intro r s hs
    have h1 : |Real.cos (δ r s) - Real.cos (δ t s)| ≤ |δ r s - δ t s| := by
      have := Real.lipschitzWith_cos.dist_le_mul (δ r s) (δ t s)
      simpa [Real.dist_eq] using this
    exact le_trans h1 (hlipδ r t s hs)
  have hparam : HasDerivAt (fun r => ∫ s in (0:ℝ)..(P t), Real.cos (δ r s))
      (∫ s in (0:ℝ)..(P t), SelectedChangeOfVariable.cosTimeDeriv δ (partialTime δ) t s) t :=
    SelectedChangeOfVariable.hasDerivAt_rearArclength_time hδc hdt hdtc t (P t)
  exact RearPeriodDeriv.hasDerivAt_rearPeriod_local (L := L) (R := R)
    (fun r => hδc.comp (continuous_const.prodMk continuous_id)) (hPR t) hlip
    ((hPdiff t).hasDerivAt) hparam

/-! ### The path-metric bound -/

/-- **The path pseudodistance of the selected rears, with the front data in the
normalized parameter.**  The curvature `K̂`, its parameter derivative `K̂̇` and the
selected steering angle `δ̂` are given on the normalized circle, where they are
`1`-periodic for every time whatever the motion of the arclength period `P`; the
front data in the arclength are `δ(t,s) = δ̂(t, s/P t)` and `K(t,s) = K̂(t, s/P t)`.
Every remaining ingredient — the steering equation and the periodicity in the
arclength, the joint `C⁴` regularity of the steering angle, the periodicity of
the front normal velocity, its sup bound, the derivative of the rear period, and
the link between the normal path and the fronts — is derived.  Unlike
`RearOwnPathDistSlices.pathDist_le_of_front_slices`, no hypothesis here forces
`P'(t) ∂_sK = 0`. -/
theorem pathDist_le_of_front_normalized {p q : Data} (Γ : NormalPath p q) (p' : Data)
    {Md MP CK CP : ℝ} {sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hdelta : ∀ t s, δ t s = dn t (s / P t)) (hKeq : ∀ t s, K t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh) (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md)
    (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hsfinv : ∀ t x, rearArclength (δ t) (sf t x) = x)
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ)))
    (hstart : ∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) :
    ∃ EF : ℝ, 0 ≤ EF ∧
      (∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF) ∧
      ∃ Phi : ℝ → ℝ → ℝ,
        (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
        ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
        ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
          pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
              (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
              ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                  * (kh / Real.sqrt (1 - kh ^ 2))
                + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
            (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hle34 : ((3 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  have hPC3 : ContDiff ℝ (3 : ℕ) P := hPC4.of_le hle34
  -- the steering data in the arclength
  have hsteer : ∀ t s, HasDerivAt (δ t) (K t s - Real.sin (δ t s)) s :=
    hasDerivAt_delta_arclength hPpos hdelta hKeq hsol
  have hdper : ∀ t, Function.Periodic (δ t) (P t) :=
    periodic_delta_arclength hPpos hdelta hdnper
  have hstrip0 : ∀ t s, 0 ≤ δ t s := fun t s => by rw [hdelta]; exact (hstrip t _).1
  have hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh := fun t s => by
    rw [hdelta]; exact (hstrip t _).2
  have hKbd : ∀ t s, |K t s| ≤ kh := fun t s => by rw [hKeq]; exact hKnbd t _
  have hKc : ∀ t, Continuous (K t) := by
    intro t
    have hfun : K t = fun s => Kn t (s / P t) := funext (hKeq t)
    rw [hfun]
    exact (hKnC3.continuous.comp (continuous_const.prodMk
      (continuous_id.div_const (P t))))
  -- the joint regularity of the steering angle, with no restriction on the period
  have hdnC4 : ContDiff ℝ (4 : ℕ) (uncurry dn) :=
    SteeringNormalizedPeriod.contDiff_four_uncurry_delta (P0 := P0) (P1 := P1) (kap := kh)
      (Md := Md) (MP := MP) (Klip := Klip) (Plip := Plip) (CK := CK) (CP := CP)
      hP0 hkh0 hkh1 hPl hPu hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd
      hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC3 hPdC3 hKnC3 hKdnC3
  have hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ) := by
    have h := SteeringNormalizedPeriod.contDiff_arclength_of_normalized (n := 4)
      (delta := dn) (Pf := P) hdnC4 hPC4 hPpos
    have heq : (uncurry δ) = uncurry fun t s => dn t (s / P t) := by
      funext x; exact hdelta x.1 x.2
    rw [heq]; exact h
  have hδdiff : Differentiable ℝ (uncurry δ) := hδc4.differentiable (by norm_num)
  have hFdiff : Differentiable ℝ (uncurry F) := hFc4.differentiable (by norm_num)
  have hPdiff : Differentiable ℝ P := hPC4.differentiable (by norm_num)
  -- the link with the fronts and the rest condition
  have hlink : ∀ t u,
      Γ.eta t u = frontNormalVelocityAt (partialTime F) Θ δ t (P t * u) :=
    fun t u => eta_eq_frontNormalVelocity (δ := δ) Γ hFdiff hF hPdiff hX hnu t u
  have hFrest : ∀ t ∉ Ioo (0 : ℝ) Γ.T, ∀ s,
      frontNormalVelocityAt (partialTime F) Θ δ t s = 0 :=
    fun t ht s => frontNormalVelocity_eq_zero_of_rest Γ hPpos hlink ht s
  -- the periodicity of the front normal velocity and its sup bound
  have hetaFper : ∀ t,
      Function.Periodic (frontNormalVelocityAt (partialTime F) Θ δ t) (P t) :=
    periodic_frontNormalVelocityAt (δ := δ) hFdiff hF hFper hΘper hPdiff
  have hF4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry F) := by norm_num; exact_mod_cast hFc4
  have hΘ3 : ContDiff ℝ (3 : ℕ) (uncurry Θ) := hΘc4.of_le hle34
  have hFdot3 : ContDiff ℝ (3 : ℕ) (uncurry (partialTime F)) := contDiff_partialTime_self hF4
  have hetaC3 : ContDiff ℝ (3 : ℕ)
      (uncurry (frontNormalVelocityAt (partialTime F) Θ δ)) :=
    contDiff_frontNormalVelocityAt hFdot3 hΘ3
  obtain ⟨EF, hEF0, hEF⟩ := exists_bound_of_periodic_rest (P := P)
    (eta := frontNormalVelocityAt (partialTime F) Θ δ) hetaC3.continuous Γ.T_pos
    hPpos hPu hetaFper hFrest
  -- the derivative of the rear period, from the local Lipschitz bound
  have hδ4 : ContDiff ℝ ((3 + 1 : ℕ)) (uncurry δ) := by norm_num; exact_mod_cast hδc4
  have hdtc : Continuous (uncurry (partialTime δ)) :=
    (contDiff_partialTime_self hδ4).continuous
  have hPR : ∀ t, |P t| < P1 + 1 := by
    intro t
    rw [abs_of_pos (hPpos t)]
    linarith [hPu t]
  have hR : (0 : ℝ) ≤ P1 + 1 := by
    have : 0 < P1 := lt_of_lt_of_le (hPpos 0) (hPu 0)
    linarith
  have hlipδ : ∀ a b s, |s| ≤ P1 + 1 → |δ a s - δ b s|
      ≤ (SteeringNormalizedPeriod.lipConst P0 P1 kh Klip Plip
          + 2 * P1 * kh * ((P1 + 1) * Plip / P0 ^ 2)) * |a - b| :=
    fun a b s hs => abs_delta_sub_le_of_normalized (R := P1 + 1) hP0 hkh0 hkh1 hR hPl hPu
      hdelta hKnC3.continuous hsol hstrip hKnbd hKnlip hPlip a b s hs
  obtain ⟨Qf', hQd⟩ := exists_hasDerivAt_rearPeriod_local (δ := δ) (P := P)
    (R := P1 + 1) hδdiff hdtc hPR hlipδ hPdiff
  obtain ⟨Phi, hPhi0, hbase, hPhi⟩ :=
    RearOwnPathDistFrontOnly.pathDist_le_of_front_curve Γ p' (Qf' := Qf') (EF := EF)
      hP0 hkh0 hkh1 hPl hPu hF hΘ hsteer hstrip0 hstrip1 hdper hKbd hKc hFper hΘper hFc4
      hΘc4 hδc4 hsfinv hetaFper hlink hQd hEF hFrest hstart
  refine ⟨EF, hEF0, hEF, Phi, hPhi0, fun h => hbase fun t => ?_, hPhi⟩
  -- the front does not move at the marked point, so the base drift vanishes there
  have hXF : (fun r => Γ.X r 0) = fun r => F r 0 := by
    funext r
    rw [hX r 0, mul_zero]
  have hd := Γ.hasDerivAt_time t 0
  rw [hXF, h t] at hd
  simp only [Complex.ofReal_zero, zero_mul] at hd
  have hFdot : partialTime F t 0 = 0 :=
    (hasDerivAt_partialTime hFdiff t 0).unique hd
  exact RearBaseDrift.frontBaseDrift_eq_zero_of_velocity_zero hFdot

/-- **The same, with the change of variable from the rear to the front arclength
produced rather than assumed.**  The steering angle stays in the selected strip,
so the rear arclength of each slice is a bijection of the line; its family of
inverses is the change of variable the assembly uses. -/
theorem exists_sf_pathDist_le_of_front_normalized {p q : Data} (Γ : NormalPath p q)
    {Md MP CK CP : ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hdelta : ∀ t s, δ t s = dn t (s / P t)) (hKeq : ∀ t s, K t s = Kn t (s / P t))
    (hsol : ∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ)
    (hstrip : ∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh))
    (hdnper : ∀ t, Function.Periodic (dn t) 1) (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKnbd : ∀ t σ, |Kn t σ| ≤ kh) (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md)
    (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (K t s) s)
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ))) :
    ∃ sf : ℝ → ℝ → ℝ, (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∀ p' : Data, (∀ u, p'.1 u = rearOwn F Θ δ sf 0 (rearArclength (δ 0) (P 0) * u)) →
        ∃ EF : ℝ, 0 ≤ EF ∧
          (∀ t s, |frontNormalVelocityAt (partialTime F) Θ δ t s| ≤ EF) ∧
          ∃ Phi : ℝ → ℝ → ℝ,
            (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
            ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
            ∀ q' : Data, (∀ u, q'.1 u = rearOwn F Θ δ sf Γ.T (Phi Γ.T u)) →
              pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hle34 : ((3 : ℕ) : WithTop ℕ∞) ≤ ((4 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by norm_num : (3 : ℕ) ≤ 4)
  have hPC3 : ContDiff ℝ (3 : ℕ) P := hPC4.of_le hle34
  have hstrip0 : ∀ t s, 0 ≤ δ t s := fun t s => by rw [hdelta]; exact (hstrip t _).1
  have hstrip1 : ∀ t s, δ t s ≤ Real.arcsin kh := fun t s => by
    rw [hdelta]; exact (hstrip t _).2
  have hdnC4 : ContDiff ℝ (4 : ℕ) (uncurry dn) :=
    SteeringNormalizedPeriod.contDiff_four_uncurry_delta (P0 := P0) (P1 := P1) (kap := kh)
      (Md := Md) (MP := MP) (Klip := Klip) (Plip := Plip) (CK := CK) (CP := CP)
      hP0 hkh0 hkh1 hPl hPu hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd hPdbd
      hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC3 hPdC3 hKnC3 hKdnC3
  have hδc4 : ContDiff ℝ (4 : ℕ) (uncurry δ) := by
    have h := SteeringNormalizedPeriod.contDiff_arclength_of_normalized (n := 4)
      (delta := dn) (Pf := P) hdnC4 hPC4 hPpos
    have heq : (uncurry δ) = uncurry fun t s => dn t (s / P t) := by
      funext x; exact hdelta x.1 x.2
    rw [heq]; exact h
  obtain ⟨sf, hsf⟩ := SelectedChangeOfVariable.exists_sf_family (kap := kh) hkh0 hkh1
    (hδc4.continuous) hstrip0 hstrip1
  refine ⟨sf, hsf, ?_⟩
  intro p' hstart
  exact pathDist_le_of_front_normalized Γ p' (Md := Md) (MP := MP) (CK := CK) (CP := CP)
    hP0 hkh0 hkh1 hPl hPu hdelta hKeq hsol hstrip hdnper hKnper hKdnper hKnbd hKdnbd
    hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3 hF hΘ hFper
    hΘper hFc4 hΘc4 hsf hX hnu hstart

end RearOwnPathDistNormalized
