import Mathlib

/-!
# Arclength reparametrization of a closed regular curve

The space of marked curves of `MarkedSpace.lean` consists of closed `C²`
curves carried in the **normalized parameter**: the parameter in which the
speed is constant, equal to the perimeter.  Any map of curves (in particular
the unit-tangent transform of *A Noncircular Oval with Convex Unit-Tangent
Iterates*) produces a curve in some other parameter, and must be followed by a
reparametrization before it can be read as marked data again.

This file constructs that reparametrization.  For a closed regular `C²` curve
`g` — `g' = V`, `V' = A`, all of period one, with `‖V‖ ≥ c > 0` — the arclength

```
  ℓ(u) = ∫₀^u ‖V‖
```

is a strictly increasing bijection of the line satisfying `ℓ(u+1) = ℓ(u) + L`,
`L = ∫₀¹‖V‖` the length; its inverse `φ` is differentiable with `φ' = 1/‖V∘φ‖`,
and `ψ(u) = φ(Lu)` reparametrizes `g` at constant speed `L`.

Main results:

* `hasDerivAt_norm_of_ne_zero` : the derivative of `t ↦ ‖V t‖` is
  `Re(V̄A)/‖V‖`;
* `hasDerivAt_arcLength`, `strictMono_arcLength`, `arcLength_add_period`,
  `surjective_arcLength` : the arclength function is a strictly increasing
  bijection commuting with the period;
* `exists_inverse_arcLength` : its inverse is differentiable, with derivative
  `1/‖V∘φ‖`;
* `exists_constant_speed_reparam` : **the reparametrization theorem** — a
  closed regular `C²` curve has a `C²` reparametrization of period one, of
  constant speed its length, with the same image and the same curvature, the
  new parameter being arclength divided by the length.
-/

noncomputable section

open Set Function Filter Topology MeasureTheory intervalIntegral

namespace MarkedReparam

/-! ### The derivative of the speed -/

/-- The derivative of the norm of a nonvanishing differentiable complex
function: `(‖V‖)' = Re(V̄ V')/‖V‖`. -/
theorem hasDerivAt_norm_of_ne_zero {V : ℝ → ℂ} {a : ℂ} {t : ℝ} (h : HasDerivAt V a t)
    (hne : V t ≠ 0) :
    HasDerivAt (fun x => ‖V x‖) (((starRingEnd ℂ) (V t) * a).re / ‖V t‖) t := by
  have hx : HasDerivAt (fun x => (V x).re) a.re t :=
    (Complex.reCLM.hasFDerivAt).comp_hasDerivAt t h
  have hy : HasDerivAt (fun x => (V x).im) a.im t :=
    (Complex.imCLM.hasFDerivAt).comp_hasDerivAt t h
  have hN : HasDerivAt (fun x => (V x).re ^ 2 + (V x).im ^ 2)
      (2 * (V t).re * a.re + 2 * (V t).im * a.im) t := by
    have h1 := (hx.pow 2).add (hy.pow 2)
    convert h1 using 1
    ring
  have hNpos : 0 < (V t).re ^ 2 + (V t).im ^ 2 := by
    have hnn : ‖V t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    have : 0 < ‖V t‖ ^ 2 := by positivity
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    nlinarith
  have hsqrt := (Real.hasDerivAt_sqrt (x := (V t).re ^ 2 + (V t).im ^ 2) (ne_of_gt hNpos)).comp t hN
  have hnorm : (fun x => ‖V x‖) = fun x => Real.sqrt ((V x).re ^ 2 + (V x).im ^ 2) := by
    funext x
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    ring
  have hval : Real.sqrt ((V t).re ^ 2 + (V t).im ^ 2) = ‖V t‖ := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  rw [hnorm]
  convert hsqrt using 1
  rw [hval]
  have hnn : ‖V t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-! ### The arclength function -/

/-- The arclength of a curve with velocity `V`, measured from `0`. -/
def arcLength (V : ℝ → ℂ) (u : ℝ) : ℝ := ∫ x in (0 : ℝ)..u, ‖V x‖

/-- The length of a closed curve of period one with velocity `V`. -/
def totalLength (V : ℝ → ℂ) : ℝ := ∫ x in (0 : ℝ)..1, ‖V x‖

theorem hasDerivAt_arcLength {V : ℝ → ℂ} (hVc : Continuous V) (u : ℝ) :
    HasDerivAt (arcLength V) ‖V u‖ u :=
  ((hVc.norm).integral_hasStrictDerivAt 0 u).hasDerivAt

theorem strictMono_arcLength {V : ℝ → ℂ} (hVc : Continuous V) (hpos : ∀ u, 0 < ‖V u‖) :
    StrictMono (arcLength V) := by
  refine strictMono_of_deriv_pos (fun u => ?_)
  rw [(hasDerivAt_arcLength hVc u).deriv]
  exact hpos u

theorem arcLength_add_period {V : ℝ → ℂ} (hVc : Continuous V) (hper : Periodic V 1) (u : ℝ) :
    arcLength V (u + 1) = arcLength V u + totalLength V := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x => ‖V x‖) volume a b := fun a b =>
    (hVc.norm).intervalIntegrable a b
  have hnormper : Periodic (fun x => ‖V x‖) 1 := fun x => by simp only [hper x]
  have hsplit : arcLength V (u + 1) = arcLength V u + ∫ x in u..(u + 1), ‖V x‖ := by
    rw [arcLength, arcLength, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 u)
      (hint u (u + 1))]
  rw [hsplit, hnormper.intervalIntegral_add_eq u 0, totalLength]
  norm_num

theorem totalLength_pos {V : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hVc : Continuous V)
    (hspeed : ∀ u, c ≤ ‖V u‖) : 0 < totalLength V := by
  have h : (∫ _x in (0 : ℝ)..1, c) ≤ ∫ x in (0 : ℝ)..1, ‖V x‖ :=
    intervalIntegral.integral_mono_on (by norm_num) (intervalIntegral.intervalIntegrable_const)
      ((hVc.norm).intervalIntegrable 0 1) (fun x _ => hspeed x)
  rw [intervalIntegral.integral_const] at h
  simp only [smul_eq_mul, sub_zero, one_mul] at h
  exact lt_of_lt_of_le hc h

theorem arcLength_ge {V : ℝ → ℂ} {c : ℝ} (hVc : Continuous V) (hspeed : ∀ u, c ≤ ‖V u‖)
    {u : ℝ} (hu : 0 ≤ u) : c * u ≤ arcLength V u := by
  have h : (∫ _x in (0 : ℝ)..u, c) ≤ ∫ x in (0 : ℝ)..u, ‖V x‖ :=
    intervalIntegral.integral_mono_on hu (intervalIntegral.intervalIntegrable_const)
      ((hVc.norm).intervalIntegrable 0 u) (fun x _ => hspeed x)
  rw [intervalIntegral.integral_const] at h
  simpa [arcLength, mul_comm] using h

theorem arcLength_le {V : ℝ → ℂ} {c : ℝ} (hVc : Continuous V) (hspeed : ∀ u, c ≤ ‖V u‖)
    {u : ℝ} (hu : u ≤ 0) : arcLength V u ≤ c * u := by
  have h : (∫ _x in u..(0 : ℝ), c) ≤ ∫ x in u..(0 : ℝ), ‖V x‖ :=
    intervalIntegral.integral_mono_on hu (intervalIntegral.intervalIntegrable_const)
      ((hVc.norm).intervalIntegrable u 0) (fun x _ => hspeed x)
  rw [intervalIntegral.integral_const] at h
  have hswap : (∫ x in u..(0 : ℝ), ‖V x‖) = -arcLength V u := by
    rw [arcLength, ← intervalIntegral.integral_symm]
  rw [hswap] at h
  simp only [smul_eq_mul, zero_sub] at h
  linarith

theorem surjective_arcLength {V : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hVc : Continuous V)
    (hspeed : ∀ u, c ≤ ‖V u‖) : Surjective (arcLength V) := by
  have hcont : Continuous (arcLength V) :=
    continuous_iff_continuousAt.2 fun u => (hasDerivAt_arcLength hVc u).continuousAt
  have hct : Tendsto (fun u : ℝ => c * u) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have hcb : Tendsto (fun u : ℝ => c * u) atBot atBot := by
    simpa using Filter.Tendsto.const_mul_atBot hc tendsto_id
  refine hcont.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ hct
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact arcLength_ge hVc hspeed hu
  · refine tendsto_atBot_mono' atBot ?_ hcb
    filter_upwards [eventually_le_atBot (0 : ℝ)] with u hu
    exact arcLength_le hVc hspeed hu

/-! ### The inverse of the arclength -/

/-- **The inverse of the arclength function.**  For a regular curve the
arclength is a differentiable increasing bijection of the line; its inverse is
differentiable with derivative `1/‖V∘φ‖` and shifts by one period. -/
theorem exists_inverse_arcLength {V : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hVc : Continuous V)
    (hper : Periodic V 1) (hspeed : ∀ u, c ≤ ‖V u‖) :
    ∃ phi : ℝ → ℝ, Continuous phi ∧ (∀ y, arcLength V (phi y) = y) ∧
      (∀ u, phi (arcLength V u) = u) ∧
      (∀ y, HasDerivAt phi (1 / ‖V (phi y)‖) y) ∧
      (∀ y, phi (y + totalLength V) = phi y + 1) := by
  have hpos : ∀ u, 0 < ‖V u‖ := fun u => lt_of_lt_of_le hc (hspeed u)
  have hmono : StrictMono (arcLength V) := strictMono_arcLength hVc hpos
  have hsurj : Surjective (arcLength V) := surjective_arcLength hc hVc hspeed
  set iso : ℝ ≃o ℝ := hmono.orderIsoOfSurjective (arcLength V) hsurj with hiso
  have hisoapp : ∀ x, iso x = arcLength V x := fun x => rfl
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
    have hderiv : HasDerivAt (arcLength V) ‖V (iso.symm y)‖ (iso.symm y) :=
      hasDerivAt_arcLength hVc _
    have hne : ‖V (iso.symm y)‖ ≠ 0 := ne_of_gt (hpos _)
    have heq : ∀ᶠ z in 𝓝 y, arcLength V (iso.symm z) = z := by
      filter_upwards with z
      have h := iso.apply_symm_apply z
      rw [hisoapp] at h
      exact h
    have h := HasDerivAt.of_local_left_inverse hcont hderiv hne heq
    simpa [one_div] using h
  · intro y
    have hy : arcLength V (iso.symm y) = y := by
      have h := iso.apply_symm_apply y
      rw [hisoapp] at h
      exact h
    have hb : arcLength V (iso.symm y + 1) = y + totalLength V := by
      rw [arcLength_add_period hVc hper, hy]
    have h2 : iso.symm (arcLength V (iso.symm y + 1)) = iso.symm y + 1 := by
      have h3 : iso.symm (iso (iso.symm y + 1)) = iso.symm y + 1 := iso.symm_apply_apply _
      rw [hisoapp] at h3
      exact h3
    rw [hb] at h2
    exact h2

/-! ### The reparametrization -/

/-- **Arclength reparametrization.**  A closed regular `C²` curve `g` of period
one, with velocity `V`, acceleration `A` and speed at least `c > 0`, admits a
reparametrization `Y = g ∘ ψ` of period one whose speed is constant, equal to
the length `L` of the curve.  The reparametrization is again `C²`, has the same
image, and has the same curvature at corresponding points. -/
theorem exists_constant_speed_reparam {g V A : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hg : ∀ u, HasDerivAt g (V u) u) (hV : ∀ u, HasDerivAt V (A u) u) (hAc : Continuous A)
    (hgper : Periodic g 1) (hVper : Periodic V 1) (hAper : Periodic A 1)
    (hspeed : ∀ u, c ≤ ‖V u‖) :
    ∃ (psi : ℝ → ℝ) (Y W B : ℝ → ℂ) (L : ℝ), L = totalLength V ∧ 0 < L ∧
      (∀ u, HasDerivAt Y (W u) u) ∧ (∀ u, HasDerivAt W (B u) u) ∧
      Continuous B ∧ Periodic Y 1 ∧ Periodic W 1 ∧ Periodic B 1 ∧
      (∀ u, ‖W u‖ = L) ∧ range Y = range g ∧
      (∀ u, Y u = g (psi u)) ∧ (∀ u, arcLength V (psi u) = L * u) ∧
      (∀ u, ((starRingEnd ℂ) (W u) * B u).im * ‖V (psi u)‖ ^ 3
        = L ^ 3 * ((starRingEnd ℂ) (V (psi u)) * A (psi u)).im) := by
  have hVc : Continuous V := continuous_iff_continuousAt.2 fun u => (hV u).continuousAt
  have hpos : ∀ u, 0 < ‖V u‖ := fun u => lt_of_lt_of_le hc (hspeed u)
  have hne : ∀ u, V u ≠ 0 := fun u => norm_ne_zero_iff.mp (ne_of_gt (hpos u))
  set L : ℝ := totalLength V with hLdef
  have hLpos : 0 < L := totalLength_pos hc hVc hspeed
  obtain ⟨phi, hphic, hphiright, hphileft, hphideriv, hphiper⟩ :=
    exists_inverse_arcLength hc hVc hVper hspeed
  -- the reparametrization of the parameter line
  set psi : ℝ → ℝ := fun u => phi (L * u) with hpsidef
  have hpsideriv : ∀ u, HasDerivAt psi (L / ‖V (psi u)‖) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => L * u) L u := by
      simpa using (hasDerivAt_id u).const_mul L
    have h2 := (hphideriv (L * u)).comp u h1
    rw [hpsidef]
    simpa [Function.comp_def, one_div, div_eq_mul_inv, mul_comm] using h2
  have hpsicont : Continuous psi := hphic.comp (continuous_const.mul continuous_id)
  have hpsiper : ∀ u, psi (u + 1) = psi u + 1 := by
    intro u
    have hLu : L * (u + 1) = L * u + L := by ring
    rw [hpsidef]
    simp only [hLu]
    exact hphiper (L * u)
  have hpsisurj : Surjective psi := by
    intro x
    refine ⟨arcLength V x / L, ?_⟩
    rw [hpsidef]
    simp only
    rw [mul_div_cancel₀ _ (ne_of_gt hLpos), hphileft]
  -- the speed and its derivative
  set s : ℝ → ℝ := fun t => ‖V t‖ with hsdef
  set sd : ℝ → ℝ := fun t => ((starRingEnd ℂ) (V t) * A t).re / ‖V t‖ with hsddef
  have hsderiv : ∀ t, HasDerivAt s (sd t) t := fun t => by
    rw [hsdef, hsddef]
    exact hasDerivAt_norm_of_ne_zero (hV t) (hne t)
  have hscont : Continuous s := hVc.norm
  have hsdcont : Continuous sd := by
    rw [hsddef]
    refine Continuous.div ?_ hVc.norm (fun t => ne_of_gt (hpos t))
    exact Complex.continuous_re.comp ((Complex.continuous_conj.comp hVc).mul hAc)
  have hsne : ∀ u, s (psi u) ≠ 0 := fun u => by rw [hsdef]; exact ne_of_gt (hpos _)
  -- the reparametrized curve, velocity and acceleration
  set Y : ℝ → ℂ := fun u => g (psi u) with hYdef
  set W : ℝ → ℂ := fun u => ((L / s (psi u) : ℝ) : ℂ) * V (psi u) with hWdef
  set B : ℝ → ℂ := fun u => ((-(L ^ 2 * sd (psi u) / s (psi u) ^ 3) : ℝ) : ℂ) * V (psi u)
    + (((L / s (psi u)) ^ 2 : ℝ) : ℂ) * A (psi u) with hBdef
  have hYderiv : ∀ u, HasDerivAt Y (W u) u := by
    intro u
    have h := (hg (psi u)).scomp u (hpsideriv u)
    rw [hYdef, hWdef]
    convert h using 1
  have hrderiv : ∀ u, HasDerivAt (fun u => (L / s (psi u) : ℝ))
      (-(L ^ 2 * sd (psi u) / s (psi u) ^ 3)) u := by
    intro u
    have hcomp : HasDerivAt (fun u => s (psi u)) (sd (psi u) * (L / s (psi u))) u := by
      have h := (hsderiv (psi u)).comp u (hpsideriv u)
      simpa [Function.comp_def, hsdef] using h
    have h := (hcomp.inv (hsne u)).const_mul L
    have hgoal : (fun u => (L / s (psi u) : ℝ)) = fun u => L * (s (psi u))⁻¹ := by
      funext x; rw [div_eq_mul_inv]
    rw [hgoal]
    convert h using 1
    field_simp
  have hWderiv : ∀ u, HasDerivAt W (B u) u := by
    intro u
    have h1 : HasDerivAt (fun u => (((L / s (psi u) : ℝ)) : ℂ))
        (((-(L ^ 2 * sd (psi u) / s (psi u) ^ 3) : ℝ) : ℂ)) u := (hrderiv u).ofReal_comp
    have h2 : HasDerivAt (fun u => V (psi u)) (((L / s (psi u) : ℝ) : ℂ) * A (psi u)) u := by
      have h := (hV (psi u)).scomp u (hpsideriv u)
      simpa [Function.comp_def, smul_eq_mul, hsdef] using h
    have h := h1.mul h2
    rw [hWdef, hBdef]
    convert h using 1
    push_cast
    ring
  have hWnorm : ∀ u, ‖W u‖ = L := by
    intro u
    have hp := hpos (psi u)
    rw [hWdef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hsdef]
    rw [abs_of_pos (div_pos hLpos hp), div_mul_cancel₀ _ (ne_of_gt hp)]
  have hBcont : Continuous B := by
    have h1 : Continuous fun u => s (psi u) := hscont.comp hpsicont
    have h2 : Continuous fun u => sd (psi u) := hsdcont.comp hpsicont
    have h3 : Continuous fun u => V (psi u) := hVc.comp hpsicont
    have h4 : Continuous fun u => A (psi u) := hAc.comp hpsicont
    rw [hBdef]
    refine Continuous.add (Continuous.mul ?_ h3) (Continuous.mul ?_ h4)
    · refine Complex.continuous_ofReal.comp (Continuous.neg ?_)
      exact (continuous_const.mul h2).div (h1.pow 3) (fun u => pow_ne_zero 3 (hsne u))
    · exact Complex.continuous_ofReal.comp ((continuous_const.div h1 hsne).pow 2)
  have hpsiarc : ∀ u, arcLength V (psi u) = L * u := by
    intro u
    rw [hpsidef]
    exact hphiright (L * u)
  refine ⟨psi, Y, W, B, L, hLdef, hLpos, hYderiv, hWderiv, hBcont, ?_, ?_, ?_, hWnorm, ?_, fun u => rfl,
    hpsiarc, ?_⟩
  · intro u
    rw [hYdef]
    simp only [hpsiper u]
    exact hgper (psi u)
  · intro u
    rw [hWdef]
    simp only [hpsiper u, hsdef]
    rw [hVper (psi u)]
  · intro u
    rw [hBdef]
    simp only [hpsiper u, hsdef, hsddef]
    rw [hVper (psi u), hAper (psi u)]
  · -- the image is unchanged
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨psi u, rfl⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨u, hu⟩ := hpsisurj t
      exact ⟨u, by rw [hYdef]; simp only [hu]⟩
  · -- the curvature is unchanged
    intro u
    have hp := hpos (psi u)
    have hconj : (starRingEnd ℂ) (W u) * B u
        = ((L / s (psi u) : ℝ) : ℂ) * ((-(L ^ 2 * sd (psi u) / s (psi u) ^ 3) : ℝ) : ℂ)
            * ((starRingEnd ℂ) (V (psi u)) * V (psi u))
          + (((L / s (psi u)) ^ 3 : ℝ) : ℂ) * ((starRingEnd ℂ) (V (psi u)) * A (psi u)) := by
      rw [hWdef, hBdef, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hconj]
    have hreal : ((starRingEnd ℂ) (V (psi u)) * V (psi u)) = ((s (psi u) ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hsdef]
    rw [hreal, hsdef]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      mul_zero, add_zero, zero_add]
    field_simp

end MarkedReparam
