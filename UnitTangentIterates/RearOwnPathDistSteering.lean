import Mathlib
import UnitTangentIterates.RearOwnPathDistNormalized
import UnitTangentIterates.FrontFromPathNormalized
import UnitTangentIterates.SteeringExistence

/-!
# The path-distance bound with the steering angle produced from the front

`RearOwnPathDistNormalized.exists_sf_pathDist_le_of_front_normalized` bounds the
path pseudodistance between the selected rears of a normal path of fronts by a
uniform constant times the cost of the front path, with the change of variable
from the rear to the front arclength produced rather than assumed.  What it
still takes as data is the **selected steering angle** itself: a normalized
angle `δ̂(t, ·)`, `1`-periodic, confined to the selected strip and solving

```
  ∂_σ δ̂ = P(t) · (K̂(t, σ) − sin δ̂(t, σ)) .
```

This file produces it from the front curvature alone.  For each time the
arclength curvature `K(t, s) = K̂(t, s/P t)` is continuous, `P t`-periodic and
pinched by `0 ≤ K ≤ κ̂ < 1`, so `SteeringExistence.exists_periodic_steering`
gives a periodic solution `δ(t, ·)` of `δ_s = K − sin δ` in the selected strip;
rescaling, `δ̂(t, σ) = δ(t, P t · σ)` is the normalized steering angle.

Main results:

* `exists_normalized_steering` — the normalized selected steering angle of a
  family of fronts of moving period;
* `exists_steering_pathDist_le_of_front` — the path-distance bound with the
  steering angle, the arclength steering angle and the change of variable all
  produced: the hypotheses are now only the tube bounds and the regularity of
  the front data;
* `exists_steering_pathDist_le_of_path` — the same for the canonical front data
  of the path itself, so that the only hypotheses left are on the normal path of
  fronts: its slices are closed curves of constant speed and turning number one,
  their curvature in the normalized parameter is pinched by `0 ≤ K̂ ≤ κ̂ < 1` and
  is regular in the path parameter.
-/

noncomputable section

open Set Function Complex MeasureTheory MarkedSpace MarkedTopology PathMetric
  PathMetric.NormalPath RearTrack ArclengthInverse RearFamilyFrame RearOwnArclength
  RearOwnMotion

namespace RearOwnPathDistSteering

open RearOwnHigherRegularity GaugePathDistVariable

variable {F : ℝ → ℝ → ℂ} {Θ Kn Kdn : ℝ → ℝ → ℝ} {P Pd : ℝ → ℝ}
  {P0 P1 kh Klip Plip : ℝ}

/-- **The normalized selected steering angle of a path of fronts of moving
period.**  For a family of front curvatures given in the normalized parameter,
continuous, `1`-periodic and pinched by `0 ≤ K̂ ≤ κ̂ < 1`, there is a `1`-periodic
family `δ̂` in the selected strip solving `∂_σ δ̂ = P(t)(K̂ − sin δ̂)`. -/
theorem exists_normalized_steering (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPpos : ∀ t, 0 < P t) (hKnc : ∀ t, Continuous (Kn t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKn0 : ∀ t σ, 0 ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh) :
    ∃ dn : ℝ → ℝ → ℝ, (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) := by
  have hex : ∀ t, ∃ d : ℝ → ℝ, Function.Periodic d (P t) ∧
      (∀ s, d s ∈ Icc 0 (Real.arcsin kh)) ∧
      (∀ s, Real.sqrt (1 - kh ^ 2) ≤ Real.cos (d s)) ∧
      (∀ s, HasDerivAt d (Kn t (s / P t) - Real.sin (d s)) s) := by
    intro t
    have hne : P t ≠ 0 := (hPpos t).ne'
    have hKc : Continuous fun s => Kn t (s / P t) :=
      (hKnc t).comp (continuous_id.div_const (P t))
    have hKper : Function.Periodic (fun s => Kn t (s / P t)) (P t) := by
      intro s
      have h : (s + P t) / P t = s / P t + 1 := by field_simp
      simp only [h, hKnper t (s / P t)]
    exact SteeringExistence.exists_periodic_steering (hPpos t) hKc hKper hkh0 hkh1.le
      (fun s => hKn0 t _) (fun s => hKnk t _)
  choose d hper hrange _hcos hode using hex
  refine ⟨fun t σ => d t (P t * σ), ?_, fun t σ => hrange t _, ?_⟩
  · intro t σ
    have h : P t * (σ + 1) = P t * σ + P t := by ring
    simp only [h, hper t (P t * σ)]
  · intro t σ
    have hne : P t ≠ 0 := (hPpos t).ne'
    have hlin : HasDerivAt (fun x : ℝ => P t * x) (P t) σ := by
      simpa using (hasDerivAt_id σ).const_mul (P t)
    have hcomp := (hode t (P t * σ)).comp σ hlin
    refine hcomp.congr_deriv ?_
    have harg : P t * σ / P t = σ := by field_simp
    rw [harg]
    ring

/-- **The path-distance bound for the selected rears of a path of fronts, with
all the steering data produced.**  The hypotheses are the tube bounds
`0 ≤ K̂ ≤ κ̂ < 1` on the front curvatures in the normalized parameter, the
two-sided bounds and the regularity of the period and of the curvature family,
and the front curves themselves; the selected steering angle `δ̂`, its arclength
form `δ` and the change of variable `sf` from the rear to the front arclength
are all produced. -/
theorem exists_steering_pathDist_le_of_front {p q : Data} (Γ : NormalPath p q)
    {Md MP CK CP : ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKn0 : ∀ t σ, 0 ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md) (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hF : ∀ t s, HasDerivAt (F t) (Complex.exp (Complex.I * (Θ t s : ℂ))) s)
    (hΘ : ∀ t s, HasDerivAt (Θ t) (Kn t (s / P t)) s)
    (hFper : ∀ t s, F t (s + P t) = F t s)
    (hΘper : ∀ t s, Θ t (s + P t) = Θ t s + 2 * Real.pi)
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry F)) (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry Θ))
    (hX : ∀ t u, Γ.X t u = F t (P t * u))
    (hnu : ∀ t u, Γ.nu t u = Complex.I * Complex.exp (Complex.I * (Θ t (P t * u) : ℂ))) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
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
  have hKnc : ∀ t, Continuous (Kn t) := fun t =>
    hKnC3.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨dn, hdnper, hstrip, hsol⟩ :=
    exists_normalized_steering (P := P) hkh0 hkh1 hPpos hKnc hKnper hKn0 hKnk
  obtain ⟨sf, hsf, hrest⟩ :=
    RearOwnPathDistNormalized.exists_sf_pathDist_le_of_front_normalized Γ
      (δ := fun t s => dn t (s / P t)) (K := fun t s => Kn t (s / P t)) (dn := dn)
      (Kn := Kn) (Kdn := Kdn) (Md := Md) (MP := MP) (CK := CK) (CP := CP)
      hP0 hkh0 hkh1 hPl hPu (fun _ _ => rfl) (fun _ _ => rfl) hsol hstrip hdnper hKnper
      hKdnper (fun t σ => abs_le.mpr ⟨by linarith [hKn0 t σ, hKnk t σ], hKnk t σ⟩)
      hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
      hF hΘ hFper hΘper hFc4 hΘc4 hX hnu
  exact ⟨dn, fun t s => dn t (s / P t), sf, hdnper, hstrip, hsol, fun _ _ => rfl, hsf, hrest⟩

/-- **The path-distance bound for the selected rears of a normal path of fronts,
with the steering data produced.**  The front data are the canonical data of the
path itself (`FrontFromPath.frontOfPath`, `angleOfPath`, `curvOfPath`), so what
is assumed is only that the slices of the path are closed curves of constant
speed `P t` and turning number one moving along their standard unit normal, that
their curvature read on the normalized circle is pinched by `0 ≤ K̂ ≤ κ̂ < 1`, and
that the period and the curvature family are regular in the path parameter.  The
selected steering angle and the change of variable from the rear to the front
arclength are produced. -/
theorem exists_steering_pathDist_le_of_path {p q : Data} (Γ : NormalPath p q)
    {V A : ℝ → ℝ → ℂ} {Md MP CK CP : ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hV : ∀ t u, HasDerivAt (Γ.X t) (V t u) u)
    (hA : ∀ t u, HasDerivAt (V t) (A t u) u)
    (hAcont : ∀ t, Continuous (A t))
    (hspeed : ∀ t u, ‖V t u‖ = P t)
    (hXper : ∀ t, Periodic (Γ.X t) 1) (hVper : ∀ t, Periodic (V t) 1)
    (hAper : ∀ t, Periodic (A t) 1)
    (hturn : ∀ t, (∫ u in (0 : ℝ)..1, ((starRingEnd ℂ) (V t u) * A t u).im / P t ^ 2)
      = 2 * Real.pi)
    (hnuX : ∀ t u, Γ.nu t u = Complex.I * (V t u / (P t : ℂ)))
    (hKeq : ∀ t s, FrontFromPath.curvOfPath V A P t s = Kn t (s / P t))
    (hKnper : ∀ t, Function.Periodic (Kn t) 1)
    (hKdnper : ∀ t, Function.Periodic (Kdn t) 1)
    (hKn0 : ∀ t σ, 0 ≤ Kn t σ) (hKnk : ∀ t σ, Kn t σ ≤ kh)
    (hKdnbd : ∀ t σ, |Kdn t σ| ≤ Md) (hPdbd : ∀ t, |Pd t| ≤ MP)
    (hKnlip : ∀ a b σ, |Kn a σ - Kn b σ| ≤ Klip * |a - b|)
    (hPlip : ∀ a b, |P a - P b| ≤ Plip * |a - b|)
    (hKntaylor : ∀ a b σ, |Kn a σ - Kn b σ - (a - b) * Kdn b σ| ≤ CK * (a - b) ^ 2)
    (hPtaylor : ∀ a b, |P a - P b - (a - b) * Pd b| ≤ CP * (a - b) ^ 2)
    (hCK : 0 ≤ CK) (hCP : 0 ≤ CP)
    (hPC4 : ContDiff ℝ (4 : ℕ) P) (hPdC3 : ContDiff ℝ (3 : ℕ) Pd)
    (hKnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kn)) (hKdnC3 : ContDiff ℝ (3 : ℕ) (uncurry Kdn))
    (hFc4 : ContDiff ℝ (4 : ℕ) (uncurry (FrontFromPath.frontOfPath Γ.X P)))
    (hΘc4 : ContDiff ℝ (4 : ℕ) (uncurry (FrontFromPath.angleOfPath V A P))) :
    ∃ dn δ sf : ℝ → ℝ → ℝ,
      (∀ t, Function.Periodic (dn t) 1) ∧
      (∀ t σ, dn t σ ∈ Icc (0 : ℝ) (Real.arcsin kh)) ∧
      (∀ t σ, HasDerivAt (dn t) (P t * (Kn t σ - Real.sin (dn t σ))) σ) ∧
      (∀ t s, δ t s = dn t (s / P t)) ∧
      (∀ t x, rearArclength (δ t) (sf t x) = x) ∧
      ∀ p' : Data, (∀ u, p'.1 u = rearOwn (FrontFromPath.frontOfPath Γ.X P)
          (FrontFromPath.angleOfPath V A P) δ sf 0 (rearArclength (δ 0) (P 0) * u)) →
        ∃ EF : ℝ, 0 ≤ EF ∧
          (∀ t s, |frontNormalVelocityAt (partialTime (FrontFromPath.frontOfPath Γ.X P))
            (FrontFromPath.angleOfPath V A P) δ t s| ≤ EF) ∧
          ∃ Phi : ℝ → ℝ → ℝ,
            (∀ u, Phi 0 u = rearArclength (δ 0) (P 0) * u) ∧
            ((∀ t, Γ.eta t 0 = 0) → ∀ t, Phi t 0 = 0) ∧
            ∀ q' : Data, (∀ u, q'.1 u = rearOwn (FrontFromPath.frontOfPath Γ.X P)
                (FrontFromPath.angleOfPath V A P) δ sf Γ.T (Phi Γ.T u)) →
              pathDist p' q' ≤ gaugeJacobiConst P0 P1 kh
                  (EF / Real.sqrt (1 - kh ^ 2) * (kh / Real.sqrt (1 - kh ^ 2)))
                  ((EF / Real.sqrt (1 - kh ^ 2) + EF / Real.sqrt (1 - kh ^ 2))
                      * (kh / Real.sqrt (1 - kh ^ 2))
                    + EF / Real.sqrt (1 - kh ^ 2) * (2 * kh / Real.sqrt (1 - kh ^ 2) ^ 3)) Γ.T
                (rearArclength (δ 0) (P 0)) * cost Γ := by
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hKnc : ∀ t, Continuous (Kn t) := fun t =>
    hKnC3.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨dn, hdnper, hstrip, hsol⟩ :=
    exists_normalized_steering (P := P) hkh0 hkh1 hPpos hKnc hKnper hKn0 hKnk
  set δ : ℝ → ℝ → ℝ := fun t s => dn t (s / P t) with hδdef
  have hdnc : ∀ t, Continuous (dn t) := fun t =>
    Differentiable.continuous fun σ => (hsol t σ).differentiableAt
  have hδc : ∀ t, Continuous (δ t) := fun t =>
    (hdnc t).comp (continuous_id.div_const (P t))
  have hslice : ∀ t : ℝ, ∃ f : ℝ → ℝ, ∀ x, rearArclength (δ t) (f x) = x := fun t =>
    exists_inverse_rearArclength hkh0 hkh1 (hδc t) (fun s => (hstrip t _).1)
      (fun s => (hstrip t _).2)
  choose sf hsf using hslice
  refine ⟨dn, δ, sf, hdnper, hstrip, hsol, fun _ _ => rfl, hsf, ?_⟩
  intro p' hstart
  exact FrontFromPathNormalized.pathDist_le_of_path_normalized Γ p'
    (dn := dn) (Kn := Kn) (Kdn := Kdn) (Md := Md) (MP := MP) (CK := CK) (CP := CP)
    hP0 hkh0 hkh1 hPl hPu hV hA hAcont hspeed hXper hVper hAper hturn hnuX
    (fun _ _ => rfl) hKeq hsol hstrip hdnper hKnper hKdnper
    (fun t σ => abs_le.mpr ⟨by linarith [hKn0 t σ, hKnk t σ], hKnk t σ⟩)
    hKdnbd hPdbd hKnlip hPlip hKntaylor hPtaylor hCK hCP hPC4 hPdC3 hKnC3 hKdnC3
    hFc4 hΘc4 hsf hstart

end RearOwnPathDistSteering
