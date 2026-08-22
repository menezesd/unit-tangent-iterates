import Mathlib
import UnitTangentIterates.MarkedReparam
import UnitTangentIterates.UnitTangentSpeed

/-!
# The unit-tangent transform of an oval, up to reparametrization

`UnitTangentSpeed.lean` shows that the unit-tangent transform of an oval is
never itself parametrized by arclength: its speed is `√(1+k²) > 1`.  The right
statement is therefore that `𝒯γ`, **reparametrized by its own arclength**, is
an oval; this is what the paper's convexity criterion is about, and this file
proves it.

For an oval `γ` with tangent angle `θ` and curvature `k`, the transform has
velocity `V = (1+ik)e^{iθ}`, speed `√(1+k²) ≥ 1` and tangent angle
`θ + arctan k`.  Its arclength `σ(s) = ∫₀^s √(1+k²)` is a strictly increasing
bijection of the line with `σ(s+L) = σ(s) + Λ`, and the reparametrized curve
`Y = 𝒯γ ∘ σ⁻¹` has unit speed, period `Λ`, the same image as `𝒯γ`, and tangent
angle whose derivative is the curvature

`K = (k + k'/(1+k²))/√(1+k²)`

of the transform.  So `Y` is an oval as soon as `K > 0` and `𝒯γ` is injective on
one period.

Main results:

* `arcLength_add_period_gen`, `exists_inverse_arcLength_gen` : the arclength
  machinery of `MarkedReparam.lean` for an arbitrary period `p > 0`;
* `isOval_reparam_unitTangentMap` : **the unit-tangent transform of an oval
  with positive transform-curvature is an oval up to reparametrization**.
-/

noncomputable section

open Set Function Filter Topology MeasureTheory intervalIntegral

namespace UnitTangentOval

/-- The length of one period of a closed curve with velocity `V`. -/
def periodLength (V : ℝ → ℂ) (p : ℝ) : ℝ := ∫ x in (0 : ℝ)..p, ‖V x‖

theorem arcLength_add_period_gen {V : ℝ → ℂ} {p : ℝ} (hVc : Continuous V) (hper : Periodic V p)
    (u : ℝ) :
    MarkedReparam.arcLength V (u + p) = MarkedReparam.arcLength V u + periodLength V p := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x => ‖V x‖) volume a b := fun a b =>
    (hVc.norm).intervalIntegrable a b
  have hnormper : Periodic (fun x => ‖V x‖) p := fun x => by simp only [hper x]
  have hsplit : MarkedReparam.arcLength V (u + p)
      = MarkedReparam.arcLength V u + ∫ x in u..(u + p), ‖V x‖ := by
    rw [MarkedReparam.arcLength, MarkedReparam.arcLength,
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 u) (hint u (u + p))]
  rw [hsplit, hnormper.intervalIntegral_add_eq u 0, periodLength]
  norm_num

theorem periodLength_pos {V : ℝ → ℂ} {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (hVc : Continuous V)
    (hspeed : ∀ u, c ≤ ‖V u‖) : 0 < periodLength V p := by
  have h : (∫ _x in (0 : ℝ)..p, c) ≤ ∫ x in (0 : ℝ)..p, ‖V x‖ :=
    intervalIntegral.integral_mono_on hp.le (intervalIntegral.intervalIntegrable_const)
      ((hVc.norm).intervalIntegrable 0 p) (fun x _ => hspeed x)
  rw [intervalIntegral.integral_const] at h
  simp only [smul_eq_mul, sub_zero] at h
  exact lt_of_lt_of_le (by positivity) h

/-- **The inverse of the arclength function**, for a closed regular curve of an
arbitrary period `p > 0`: the arclength is a differentiable increasing
bijection of the line, its inverse is differentiable with derivative
`1/‖V∘φ‖`, and it shifts the length of one period to that period. -/
theorem exists_inverse_arcLength_gen {V : ℝ → ℂ} {c p : ℝ} (hc : 0 < c) (hVc : Continuous V)
    (hper : Periodic V p) (hspeed : ∀ u, c ≤ ‖V u‖) :
    ∃ phi : ℝ → ℝ, Continuous phi ∧ (∀ y, MarkedReparam.arcLength V (phi y) = y) ∧
      (∀ u, phi (MarkedReparam.arcLength V u) = u) ∧
      (∀ y, HasDerivAt phi (1 / ‖V (phi y)‖) y) ∧
      (∀ y, phi (y + periodLength V p) = phi y + p) := by
  have hpos : ∀ u, 0 < ‖V u‖ := fun u => lt_of_lt_of_le hc (hspeed u)
  have hmono : StrictMono (MarkedReparam.arcLength V) := MarkedReparam.strictMono_arcLength hVc hpos
  have hsurj : Surjective (MarkedReparam.arcLength V) :=
    MarkedReparam.surjective_arcLength hc hVc hspeed
  set iso : ℝ ≃o ℝ := hmono.orderIsoOfSurjective (MarkedReparam.arcLength V) hsurj with hiso
  have hisoapp : ∀ x, iso x = MarkedReparam.arcLength V x := fun x => rfl
  refine ⟨iso.symm, (iso.symm.toHomeomorph).continuous, ?_, ?_, ?_, ?_⟩
  · intro y
    have h := iso.apply_symm_apply y
    rw [hisoapp] at h
    exact h
  · intro u
    have h : iso.symm (iso u) = u := iso.symm_apply_apply u
    rw [hisoapp] at h
    exact h
  · intro y
    have hcont : ContinuousAt iso.symm y := (iso.symm.toHomeomorph).continuous.continuousAt
    have hderiv : HasDerivAt (MarkedReparam.arcLength V) ‖V (iso.symm y)‖ (iso.symm y) :=
      MarkedReparam.hasDerivAt_arcLength hVc _
    have hne : ‖V (iso.symm y)‖ ≠ 0 := ne_of_gt (hpos _)
    have heq : ∀ᶠ z in 𝓝 y, MarkedReparam.arcLength V (iso.symm z) = z := by
      filter_upwards with z
      have h := iso.apply_symm_apply z
      rw [hisoapp] at h
      exact h
    have h := HasDerivAt.of_local_left_inverse hcont hderiv hne heq
    simpa [one_div] using h
  · intro y
    have hy : MarkedReparam.arcLength V (iso.symm y) = y := by
      have h := iso.apply_symm_apply y
      rw [hisoapp] at h
      exact h
    have hb : MarkedReparam.arcLength V (iso.symm y + p) = y + periodLength V p := by
      rw [arcLength_add_period_gen hVc hper, hy]
    have h2 : iso.symm (MarkedReparam.arcLength V (iso.symm y + p)) = iso.symm y + p := by
      have h3 : iso.symm (iso (iso.symm y + p)) = iso.symm y + p := iso.symm_apply_apply _
      rw [hisoapp] at h3
      exact h3
    rw [hb] at h2
    exact h2

/-- **The unit-tangent transform of an oval, reparametrized by arclength, is an
oval** — provided its curvature `K = (k + k'/(1+k²))/√(1+k²)` is positive and it
is injective on one period.  The reparametrized curve `Y` has the same image as
`𝒯γ`, so the pair `(γ, Y)` satisfies the orbit condition
`range Y = range (𝒯γ)` of
`MarkedSpace.main_theorem_on_marked_space_range`. -/
theorem isOval_reparam_unitTangentMap {γ : ℝ → ℂ} {θ k k' : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hper : Periodic γ L) (hkper : Periodic k L)
    (hγ : ∀ s, HasDerivAt γ (Complex.exp (Complex.I * (θ s : ℂ))) s)
    (hθ : ∀ s, HasDerivAt θ (k s) s) (hk : ∀ s, HasDerivAt k (k' s) s)
    (hKpos : ∀ s, 0 < k s + k' s / (1 + k s ^ 2))
    (hinj : InjOn (UnitTangent.unitTangentMap γ) (Ico 0 L)) :
    ∃ Y : ℝ → ℂ, MainTheoremConditional.IsOval Y ∧
      range Y = range (UnitTangent.unitTangentMap γ) := by
  classical
  set T : ℝ → ℂ := UnitTangent.unitTangentMap γ with hT
  set V : ℝ → ℂ := fun s => (1 + Complex.I * (k s : ℂ)) * Complex.exp (Complex.I * (θ s : ℂ))
    with hV
  have hTd : ∀ s, HasDerivAt T (V s) s := fun s =>
    UnitTangentSpeed.hasDerivAt_unitTangentMap hγ hθ s
  -- the speed of the transform
  have hVnorm : ∀ s, ‖V s‖ = Real.sqrt (1 + k s ^ 2) := by
    intro s
    have h := UnitTangentSpeed.norm_deriv_unitTangentMap hγ hθ s
    rwa [(hTd s).deriv] at h
  have hspeed : ∀ s, (1 : ℝ) ≤ ‖V s‖ := by
    intro s
    rw [hVnorm s]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (1 + k s ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (k s)])
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun s => (hk s).continuousAt
  have hθc : Continuous θ := continuous_iff_continuousAt.2 fun s => (hθ s).continuousAt
  have hVc : Continuous V := by
    rw [hV]
    exact (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp hkc))).mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp hθc)).cexp)
  -- the tangent angle of the transform, and the polar form of its velocity
  have hpolar : ∀ s, V s
      = (Real.sqrt (1 + k s ^ 2) : ℂ) *
        Complex.exp (Complex.I * ((θ s + Real.arctan (k s) : ℝ) : ℂ)) := by
    intro s
    have h := UnitTangentSpeed.deriv_unitTangentMap_polar hγ hθ s
    rwa [(hTd s).deriv] at h
  -- the tangent field of `γ` is `L`-periodic, hence so are `T` and `V`
  have htanper : ∀ s, Complex.exp (Complex.I * (θ (s + L) : ℂ))
      = Complex.exp (Complex.I * (θ s : ℂ)) := by
    intro s
    have h1 : HasDerivAt (fun t => γ (t + L)) (Complex.exp (Complex.I * (θ (s + L) : ℂ))) s := by
      have h := (hγ (s + L)).scomp s ((hasDerivAt_id s).add_const L)
      simpa using h
    have h2 : (fun t => γ (t + L)) = γ := by funext t; exact hper t
    rw [h2] at h1
    exact h1.unique (hγ s)
  have hTper : Periodic T L := by
    intro s
    simp only [hT, UnitTangent.unitTangentMap, (hγ (s + L)).deriv, (hγ s).deriv, hper s,
      htanper s]
  have hVper : Periodic V L := by
    intro s
    simp only [hV, hkper s, htanper s]
  -- the arclength of the transform
  set Λ : ℝ := periodLength V L with hΛ
  have hΛpos : 0 < Λ := periodLength_pos one_pos hL hVc hspeed
  obtain ⟨phi, hphic, hphiright, hphileft, hphideriv, hphiper⟩ :=
    exists_inverse_arcLength_gen (c := 1) one_pos hVc hVper hspeed
  set Y : ℝ → ℂ := fun y => T (phi y) with hY
  have hphistrict : StrictMono phi := by
    have hmono : StrictMono (MarkedReparam.arcLength V) :=
      MarkedReparam.strictMono_arcLength hVc (fun u => lt_of_lt_of_le one_pos (hspeed u))
    intro a b hab
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with h | h
    · rw [← hphiright a, ← hphiright b, h] at hab
      exact lt_irrefl _ hab
    · have := hmono h
      rw [hphiright, hphiright] at this
      exact absurd this (not_lt.mpr hab.le)
  have hphi0 : phi 0 = 0 := by
    have h := hphileft 0
    rwa [MarkedReparam.arcLength, intervalIntegral.integral_same] at h
  have hphiΛ : phi Λ = L := by
    have h := hphiper 0
    rw [hphi0, zero_add, zero_add] at h
    exact h
  -- the reparametrized curve has unit speed and tangent angle `θ + arctan k`
  set Θ : ℝ → ℝ := fun y => θ (phi y) + Real.arctan (k (phi y)) with hΘ
  have hYderiv : ∀ y, HasDerivAt Y (Complex.exp (Complex.I * (Θ y : ℂ))) y := by
    intro y
    have h := (hTd (phi y)).scomp y (hphideriv y)
    have hnorm : ‖V (phi y)‖ = Real.sqrt (1 + k (phi y) ^ 2) := hVnorm _
    have hne : Real.sqrt (1 + k (phi y) ^ 2) ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt (1 + k (phi y) ^ 2) := Real.sqrt_pos.mpr (by positivity)
      exact ne_of_gt this
    have hval : (1 / ‖V (phi y)‖ : ℝ) • V (phi y) = Complex.exp (Complex.I * (Θ y : ℂ)) := by
      have hΘy : Θ y = θ (phi y) + Real.arctan (k (phi y)) := rfl
      have hcancel : ((1 / Real.sqrt (1 + k (phi y) ^ 2) : ℝ) : ℂ)
          * ((Real.sqrt (1 + k (phi y) ^ 2) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, one_div, inv_mul_cancel₀ hne]
        norm_num
      rw [hΘy, hnorm, hpolar (phi y), Complex.real_smul, ← mul_assoc, hcancel, one_mul]
    rw [hY]
    rw [← hval]
    exact h
  have hΘderiv : ∀ y, HasDerivAt Θ
      ((k (phi y) + k' (phi y) / (1 + k (phi y) ^ 2)) / Real.sqrt (1 + k (phi y) ^ 2)) y := by
    intro y
    have hangle := UnitTangentSpeed.hasDerivAt_transform_angle hθ hk (phi y)
    have h := hangle.comp y (hphideriv y)
    have hnorm : (1 : ℝ) / ‖V (phi y)‖ = 1 / Real.sqrt (1 + k (phi y) ^ 2) := by rw [hVnorm]
    rw [hnorm] at h
    have h2 : HasDerivAt Θ ((k (phi y) + k' (phi y) / (1 + k (phi y) ^ 2))
        * (1 / Real.sqrt (1 + k (phi y) ^ 2))) y := by
      simpa [hΘ, Function.comp_def] using h
    convert h2 using 1
    field_simp
  refine ⟨Y, ⟨Λ, hΛpos, ?_, ?_, Θ, hYderiv, _, hΘderiv, ?_⟩, ?_⟩
  · -- periodicity
    intro y
    have h : phi (y + Λ) = phi y + L := hphiper y
    rw [hY]
    simp only [h]
    exact hTper (phi y)
  · -- injectivity on one period
    intro a ha b hb hab
    have hmem : ∀ x ∈ Ico (0 : ℝ) Λ, phi x ∈ Ico (0 : ℝ) L := by
      intro x hx
      constructor
      · rw [← hphi0]
        exact (hphistrict.le_iff_le).mpr hx.1
      · rw [← hphiΛ]
        exact hphistrict hx.2
    have := hinj (hmem a ha) (hmem b hb) hab
    exact hphistrict.injective this
  · -- positive curvature
    intro y
    have hs : (0 : ℝ) < Real.sqrt (1 + k (phi y) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    exact div_pos (hKpos (phi y)) hs
  · -- same image
    have hsurj : Surjective phi := fun x => ⟨MarkedReparam.arcLength V x, hphileft x⟩
    rw [hY]
    exact (hsurj.range_comp T)

end UnitTangentOval
