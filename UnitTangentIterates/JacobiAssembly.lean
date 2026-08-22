import Mathlib
import UnitTangentIterates.JacobiEstimates

/-!
# The inverse Jacobi estimates, assembled

`UnitTangentIterates/JacobiEstimates.lean` formalizes the separate quantitative
cores of the lemma *Inverse Jacobi estimates* of the paper *A Noncircular Oval
with Convex Unit-Tangent Iterates*.  This file assembles them into the four
estimates of the lemma itself, for one slice of a path of fronts, in the
arclength normalization.

The setting is the one of the paper's proof.  The front is parametrized by its
own arclength `s`, with period `P`, normal velocity `η_F` and curvature `K`;
the selected rear is parametrized by its arclength `x`, with period `ℓ`, normal
velocity `η_R`; `δ` is the steering angle, `xf` is rear arclength as a function
of front arclength (`xf' = cos δ`) and `sf` its inverse (`sf' = sec δ`).  The
transported front velocity is `G = sec δ · η_F ∘ sf`, and the inverse Jacobi
identity reads

```
  (1 + ∂_x) η_R = G ,        i.e.   η_R' = G - η_R .
```

Main results:

* `eq_periodicInverse` — the `ℓ`-periodic solution of `u' + u = f` is unique,
  hence equal to the explicit operator `ℛ_ℓ` of `PeriodicInverse.lean`.  This
  is what identifies the rear velocity with `ℛ_ℓ G` and makes the cores of
  `JacobiEstimates.lean` applicable to it;
* `W_estimate` — `‖η_R‖_{L¹(0,ℓ)} ≤ ‖η_F‖_{L¹(0,P)}`, the non-expansiveness of
  `W`;
* `S0_estimate` — `‖η_R‖_∞ ≤ (1 - e^{-ℓ₀})⁻¹‖η_F‖_{L¹}`, the `L¹ → L^∞` gain;
* `S1_pointwise`, `S1_estimate` — `‖η_R'‖_∞ ≤ sec · ‖η_F‖_∞ + ‖η_R‖_∞`;
* `abs_steering_deriv_le`, `S2_pointwise`, `S2_estimate` — the second-order
  bound, using `δ_x = sec δ (K - sin δ)` to bound the coefficient
  `(sec δ)_x`;
* `jacobi_estimates` — the four estimates in a single statement, with explicit
  constants depending only on the curvature ceiling `κ̂` (through
  `c = √(1 - κ̂²)`) and on a lower bound `ℓ₀` for the rear perimeter.

As in the paper, the estimates have the shape

```
  W(BΓ) ≤ W(Γ),  S₀(BΓ) ≤ C₀W(Γ),  S₁(BΓ) ≤ C₁(W + S₀)(Γ),
  S₂(BΓ) ≤ C₂(W + S₀ + S₁)(Γ) ,
```

here in their pointwise/slice form.
-/

noncomputable section

open Real MeasureTheory intervalIntegral PeriodicInverse

namespace JacobiAssembly

/-! ### Uniqueness of the periodic solution -/

/-- **Uniqueness of the `ℓ`-periodic solution of `u' + u = f`.**  Any periodic
solution equals the explicit periodic inverse `ℛ_ℓ f`. -/
theorem eq_periodicInverse {l : ℝ} {u f : ℝ → ℝ} (hl : 0 < l) (hf : Continuous f)
    (hfper : Function.Periodic f l)
    (hu : ∀ x, HasDerivAt u (f x - u x) x) (huper : Function.Periodic u l) :
    u = periodicInverse l f := by
  set v := periodicInverse l f with hv
  have hvd : ∀ x, HasDerivAt v (f x - v x) x := periodicInverse_hasDerivAt hl hf hfper
  have hvper : Function.Periodic v l := periodicInverse_periodic hfper
  set w : ℝ → ℝ := fun x => Real.exp x * (u x - v x) with hw
  have hwd : ∀ x, HasDerivAt w 0 x := by
    intro x
    have h := (Real.hasDerivAt_exp x).mul ((hu x).sub (hvd x))
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  have hwconst : ∀ x, w x = w 0 := by
    intro x
    have hdiff : Differentiable ℝ w := fun y => (hwd y).differentiableAt
    have hd0 : ∀ y, deriv w y = 0 := fun y => (hwd y).deriv
    exact is_const_of_deriv_eq_zero hdiff hd0 x 0
  have ha : u l - v l = u 0 - v 0 := by
    have h1 := huper 0
    have h2 := hvper 0
    simp only [zero_add] at h1 h2
    rw [h1, h2]
  have h0 : u 0 - v 0 = 0 := by
    have hkey := hwconst l
    simp only [hw, Real.exp_zero, one_mul] at hkey
    rw [ha] at hkey
    have hne : Real.exp l ≠ 1 := by
      have h1 : (1:ℝ) < Real.exp l := by simpa using Real.exp_lt_exp.mpr hl
      linarith
    have hfac : (Real.exp l - 1) * (u 0 - v 0) = 0 := by linarith [hkey]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linarith : Real.exp l = 1) hne
    · exact h
  funext x
  have hx := hwconst x
  simp only [hw, Real.exp_zero, one_mul] at hx
  rw [h0] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact absurd h (ne_of_gt (Real.exp_pos x))
  · linarith [h]

/-! ### The zeroth-order estimates -/

variable {l P : ℝ} {etaR etaF G delta xf : ℝ → ℝ}

/-- **Non-expansiveness of `W`.**  The rear `L¹` norm over one rear period is at
most the front `L¹` norm over one front period. -/
theorem W_estimate (hl : 0 < l)
    (hG : Continuous G) (hGper : Function.Periodic G l)
    (hetaR : ∀ x, HasDerivAt etaR (G x - etaR x) x)
    (hetaRper : Function.Periodic etaR l)
    (hx : ∀ s, HasDerivAt xf (Real.cos (delta s)) s)
    (hdelta : Continuous delta) (hx0 : xf 0 = 0) (hxP : xf P = l)
    (hcos : ∀ s, 0 < Real.cos (delta s))
    (htransport : ∀ s, G (xf s) * Real.cos (delta s) = etaF s) :
    (∫ x in (0:ℝ)..l, |etaR x|) ≤ ∫ s in (0:ℝ)..P, |etaF s| := by
  rw [eq_periodicInverse hl hG hGper hetaR hetaRper]
  exact JacobiEstimates.W_nonexpansive hl hG hGper hx hdelta hx0 hxP hcos htransport

/-- **The `L¹ → L^∞` gain `S₀ ≤ C₀W`.**  For a rear period at least `ℓ₀ > 0`,
the rear normal velocity is bounded by `(1 - e^{-ℓ₀})⁻¹` times the front `L¹`
norm. -/
theorem S0_estimate {l0 : ℝ} (hl0 : 0 < l0) (hl : l0 ≤ l)
    (hG : Continuous G) (hGper : Function.Periodic G l)
    (hetaR : ∀ x, HasDerivAt etaR (G x - etaR x) x)
    (hetaRper : Function.Periodic etaR l)
    (hx : ∀ s, HasDerivAt xf (Real.cos (delta s)) s)
    (hdelta : Continuous delta) (hx0 : xf 0 = 0) (hxP : xf P = l)
    (hcos : ∀ s, 0 < Real.cos (delta s))
    (htransport : ∀ s, G (xf s) * Real.cos (delta s) = etaF s) (x : ℝ) :
    |etaR x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s| := by
  rw [eq_periodicInverse (lt_of_lt_of_le hl0 hl) hG hGper hetaR hetaRper]
  exact JacobiEstimates.S0_gain hl0 hl hG hGper hx hdelta hx0 hxP hcos htransport x

/-! ### The first-order estimate -/

/-- **The first-order gain, pointwise.**  From `η_R' = sec δ · η_F ∘ sf - η_R`
and `cos δ ≥ c > 0`. -/
theorem S1_pointwise {c SF0 SR0 : ℝ} {dl sf : ℝ → ℝ} {x : ℝ}
    (hcpos : 0 < c) (hcosl : c ≤ Real.cos (dl x))
    (hGx : G x = etaF (sf x) / Real.cos (dl x))
    (hF : |etaF (sf x)| ≤ SF0) (hR : |etaR x| ≤ SR0) :
    |G x - etaR x| ≤ SF0 / c + SR0 := by
  have hcos : 0 < Real.cos (dl x) := lt_of_lt_of_le hcpos hcosl
  have h1 : |G x| ≤ SF0 / c := by
    rw [hGx, abs_div, abs_of_pos hcos]
    exact div_le_div₀ (le_trans (abs_nonneg _) hF) hF hcpos hcosl
  calc |G x - etaR x| ≤ |G x| + |etaR x| := abs_sub _ _
    _ ≤ SF0 / c + SR0 := add_le_add h1 hR

/-- The same bound for `deriv η_R`. -/
theorem S1_estimate {c SF0 SR0 : ℝ} {dl sf : ℝ → ℝ} {x : ℝ}
    (hetaR : ∀ y, HasDerivAt etaR (G y - etaR y) y)
    (hcpos : 0 < c) (hcosl : c ≤ Real.cos (dl x))
    (hGx : G x = etaF (sf x) / Real.cos (dl x))
    (hF : |etaF (sf x)| ≤ SF0) (hR : |etaR x| ≤ SR0) :
    |deriv etaR x| ≤ SF0 / c + SR0 := by
  rw [(hetaR x).deriv]
  exact S1_pointwise hcpos hcosl hGx hF hR

/-! ### The second-order estimate -/

/-- The derivative of the transported front velocity `G = sec δ · η_F ∘ sf`. -/
theorem G_hasDerivAt {dl sf : ℝ → ℝ} {etaFs dxv : ℝ} {x : ℝ}
    (hG : G = fun y => etaF (sf y) / Real.cos (dl y))
    (hcos : Real.cos (dl x) ≠ 0)
    (hsf : HasDerivAt sf (1 / Real.cos (dl x)) x)
    (hdl : HasDerivAt dl dxv x)
    (hF : HasDerivAt etaF etaFs (sf x)) :
    HasDerivAt G (etaFs / Real.cos (dl x) ^ 2
      + etaF (sf x) * Real.sin (dl x) * dxv / Real.cos (dl x) ^ 2) x := by
  subst hG
  have hnum : HasDerivAt (fun y => etaF (sf y)) (etaFs * (1 / Real.cos (dl x))) x :=
    hF.comp x hsf
  have hden : HasDerivAt (fun y => Real.cos (dl y)) (-Real.sin (dl x) * dxv) x := by
    simpa using (Real.hasDerivAt_cos (dl x)).comp x hdl
  refine (hnum.div hden hcos).congr_deriv ?_
  field_simp
  ring

/-- **The steering angle moves slowly in rear arclength.**  From
`δ_x = sec δ (K - sin δ)`, the bounds `|K| ≤ κ̂`, `|sin δ| ≤ κ̂` and
`cos δ ≥ c > 0` give `|δ_x| ≤ 2κ̂/c`. -/
theorem abs_steering_deriv_le {c kh K dlx dxv : ℝ}
    (hcpos : 0 < c) (hcos : c ≤ Real.cos dlx) (hK : |K| ≤ kh)
    (hsin : |Real.sin dlx| ≤ kh)
    (hdx : dxv = (K - Real.sin dlx) / Real.cos dlx) :
    |dxv| ≤ 2 * kh / c := by
  have hcos0 : 0 < Real.cos dlx := lt_of_lt_of_le hcpos hcos
  have h1 : |K - Real.sin dlx| ≤ 2 * kh := by
    calc |K - Real.sin dlx| ≤ |K| + |Real.sin dlx| := abs_sub _ _
      _ ≤ 2 * kh := by linarith
  rw [hdx, abs_div, abs_of_pos hcos0]
  exact div_le_div₀ (by linarith [abs_nonneg (K - Real.sin dlx)]) h1 hcpos hcos

/-- **The second-order gain, pointwise.**  The second derivative of the rear
normal velocity is `G' - η_R'`, and the two terms of `G'` are bounded through
`cos δ ≥ c`, `|sin δ| ≤ κ̂` and `|δ_x| ≤ 2κ̂/c`. -/
theorem S2_pointwise {c kh SF0 SF1 SR1 etaFs dxv : ℝ} {dl sf : ℝ → ℝ} {x : ℝ}
    (hcpos : 0 < c) (hcos : c ≤ Real.cos (dl x))
    (hsin : |Real.sin (dl x)| ≤ kh)
    (hdxv : |dxv| ≤ 2 * kh / c)
    (hF0 : |etaF (sf x)| ≤ SF0) (hF1 : |etaFs| ≤ SF1)
    (hR1 : |G x - etaR x| ≤ SR1) :
    |(etaFs / Real.cos (dl x) ^ 2
        + etaF (sf x) * Real.sin (dl x) * dxv / Real.cos (dl x) ^ 2)
      - (G x - etaR x)| ≤ SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3 + SR1 := by
  have hcos0 : 0 < Real.cos (dl x) := lt_of_lt_of_le hcpos hcos
  have hsq : c ^ 2 ≤ Real.cos (dl x) ^ 2 := by nlinarith
  have hcsq : 0 < c ^ 2 := by positivity
  have hkh : 0 ≤ kh := le_trans (abs_nonneg _) hsin
  have hSF0 : 0 ≤ SF0 := le_trans (abs_nonneg _) hF0
  have hSF1 : 0 ≤ SF1 := le_trans (abs_nonneg _) hF1
  have h1 : |etaFs / Real.cos (dl x) ^ 2| ≤ SF1 / c ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cos (dl x) ^ 2)]
    exact div_le_div₀ hSF1 hF1 hcsq hsq
  have h2 : |etaF (sf x) * Real.sin (dl x) * dxv / Real.cos (dl x) ^ 2|
      ≤ 2 * kh ^ 2 * SF0 / c ^ 3 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cos (dl x) ^ 2)]
    have hnum : |etaF (sf x) * Real.sin (dl x) * dxv| ≤ SF0 * kh * (2 * kh / c) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hF0 hsin (abs_nonneg _) hSF0) hdxv (abs_nonneg _)
        (by positivity)
    have hstep : |etaF (sf x) * Real.sin (dl x) * dxv| / Real.cos (dl x) ^ 2
        ≤ SF0 * kh * (2 * kh / c) / c ^ 2 :=
      div_le_div₀ (by positivity) hnum hcsq hsq
    refine hstep.trans (le_of_eq ?_)
    field_simp
  calc |(etaFs / Real.cos (dl x) ^ 2
        + etaF (sf x) * Real.sin (dl x) * dxv / Real.cos (dl x) ^ 2) - (G x - etaR x)|
      ≤ |etaFs / Real.cos (dl x) ^ 2
          + etaF (sf x) * Real.sin (dl x) * dxv / Real.cos (dl x) ^ 2|
        + |G x - etaR x| := abs_sub _ _
    _ ≤ (|etaFs / Real.cos (dl x) ^ 2|
          + |etaF (sf x) * Real.sin (dl x) * dxv / Real.cos (dl x) ^ 2|)
        + |G x - etaR x| := by gcongr; exact abs_add_le _ _
    _ ≤ SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3 + SR1 := by gcongr

/-- The second derivative of the rear normal velocity: `η_R'' = G' - η_R'`. -/
theorem etaR_second_hasDerivAt {dl sf : ℝ → ℝ} {etaFs dxv : ℝ} {x : ℝ}
    (hetaR : ∀ y, HasDerivAt etaR (G y - etaR y) y)
    (hG : G = fun y => etaF (sf y) / Real.cos (dl y))
    (hcos : Real.cos (dl x) ≠ 0)
    (hsf : HasDerivAt sf (1 / Real.cos (dl x)) x)
    (hdl : HasDerivAt dl dxv x)
    (hF : HasDerivAt etaF etaFs (sf x)) :
    HasDerivAt (deriv etaR)
      ((etaFs / Real.cos (dl x) ^ 2
          + etaF (sf x) * Real.sin (dl x) * dxv / Real.cos (dl x) ^ 2)
        - (G x - etaR x)) x := by
  have hfun : deriv etaR = fun y => G y - etaR y := funext fun y => (hetaR y).deriv
  rw [hfun]
  exact (G_hasDerivAt hG hcos hsf hdl hF).sub (hetaR x)

/-- The second-order bound for `deriv (deriv η_R)`. -/
theorem S2_estimate {c kh SF0 SF1 SR1 : ℝ} {dl sf : ℝ → ℝ} {etaFs dxv : ℝ} {x : ℝ}
    (hetaR : ∀ y, HasDerivAt etaR (G y - etaR y) y)
    (hG : G = fun y => etaF (sf y) / Real.cos (dl y))
    (hsf : HasDerivAt sf (1 / Real.cos (dl x)) x)
    (hdl : HasDerivAt dl dxv x)
    (hFd : HasDerivAt etaF etaFs (sf x))
    (hcpos : 0 < c) (hcos : c ≤ Real.cos (dl x))
    (hsin : |Real.sin (dl x)| ≤ kh) (hdxv : |dxv| ≤ 2 * kh / c)
    (hF0 : |etaF (sf x)| ≤ SF0) (hF1 : |etaFs| ≤ SF1)
    (hR1 : |G x - etaR x| ≤ SR1) :
    |deriv (deriv etaR) x| ≤ SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3 + SR1 := by
  have hcos0 : Real.cos (dl x) ≠ 0 := ne_of_gt (lt_of_lt_of_le hcpos hcos)
  rw [(etaR_second_hasDerivAt hetaR hG hcos0 hsf hdl hFd).deriv]
  exact S2_pointwise hcpos hcos hsin hdxv hF0 hF1 hR1

/-! ### The four estimates in one statement -/

/-- **The inverse Jacobi estimates.**  Let the front be parametrized by its
arclength, with period `P`, normal velocity `η_F` of derivative `η_F'` and
curvature `K`; let the selected rear be parametrized by its arclength, with
period `ℓ ≥ ℓ₀ > 0` and normal velocity `η_R`; let `δ` be the steering angle,
with `cos δ ≥ c > 0` and `|sin δ|, |K| ≤ κ̂` on the selected strip, `xf` rear
arclength as a function of front arclength and `sf` its inverse.  Assume the
inverse Jacobi identity `η_R' = G - η_R` with `G = sec δ · η_F ∘ sf` the
transported front velocity.  Then, with `‖η_F‖₁ = ∫₀^P |η_F|`,
`‖η_F‖_∞ ≤ SF0` and `‖η_F'‖_∞ ≤ SF1`:

```
  ‖η_R‖₁ ≤ ‖η_F‖₁,
  ‖η_R‖_∞ ≤ (1 - e^{-ℓ₀})⁻¹‖η_F‖₁,
  ‖η_R'‖_∞ ≤ SF0/c + (1 - e^{-ℓ₀})⁻¹‖η_F‖₁,
  ‖η_R''‖_∞ ≤ SF1/c² + 2κ̂²SF0/c³ + SF0/c + (1 - e^{-ℓ₀})⁻¹‖η_F‖₁,
```

which are the four estimates of the paper's lemma, with constants depending
only on `κ̂` and `ℓ₀`. -/
theorem jacobi_estimates {l0 c kh SF0 SF1 : ℝ}
    {etaFs dl sf K dxv : ℝ → ℝ}
    (hl0 : 0 < l0) (hl : l0 ≤ l) (hcpos : 0 < c)
    (hetaFd : ∀ s, HasDerivAt etaF (etaFs s) s)
    (hF0 : ∀ s, |etaF s| ≤ SF0) (hF1 : ∀ s, |etaFs s| ≤ SF1)
    (hK : ∀ s, |K s| ≤ kh)
    (hdelta : Continuous delta) (hcos : ∀ s, 0 < Real.cos (delta s))
    (hdlcos : ∀ x, c ≤ Real.cos (dl x)) (hdlsin : ∀ x, |Real.sin (dl x)| ≤ kh)
    (hsf : ∀ x, HasDerivAt sf (1 / Real.cos (dl x)) x)
    (hdl : ∀ x, HasDerivAt dl (dxv x) x)
    (hdxv : ∀ x, dxv x = (K (sf x) - Real.sin (dl x)) / Real.cos (dl x))
    (hxf : ∀ s, HasDerivAt xf (Real.cos (delta s)) s) (hx0 : xf 0 = 0) (hxP : xf P = l)
    (hGdef : G = fun y => etaF (sf y) / Real.cos (dl y))
    (hGcont : Continuous G) (hGper : Function.Periodic G l)
    (hetaR : ∀ x, HasDerivAt etaR (G x - etaR x) x) (hetaRper : Function.Periodic etaR l)
    (htransport : ∀ s, G (xf s) * Real.cos (delta s) = etaF s) :
    (∫ x in (0:ℝ)..l, |etaR x|) ≤ (∫ s in (0:ℝ)..P, |etaF s|)
      ∧ (∀ x, |etaR x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)
      ∧ (∀ x, |deriv etaR x|
          ≤ SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)
      ∧ (∀ x, |deriv (deriv etaR) x| ≤ SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3
          + (SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)) := by
  have hlpos : 0 < l := lt_of_lt_of_le hl0 hl
  have hW := W_estimate hlpos hGcont hGper hetaR hetaRper hxf hdelta hx0 hxP hcos htransport
  have hS0 : ∀ x, |etaR x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s| :=
    S0_estimate hl0 hl hGcont hGper hetaR hetaRper hxf hdelta hx0 hxP hcos htransport
  have hGx : ∀ x, G x = etaF (sf x) / Real.cos (dl x) := fun x => by rw [hGdef]
  have hS1 : ∀ x, |G x - etaR x|
      ≤ SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s| := fun x =>
    S1_pointwise hcpos (hdlcos x) (hGx x) (hF0 (sf x)) (hS0 x)
  refine ⟨hW, hS0, fun x => ?_, fun x => ?_⟩
  · rw [(hetaR x).deriv]; exact hS1 x
  · refine S2_estimate hetaR hGdef (hsf x) (hdl x) (hetaFd (sf x)) hcpos (hdlcos x)
      (hdlsin x) ?_ (hF0 (sf x)) (hF1 (sf x)) (hS1 x)
    exact abs_steering_deriv_le hcpos (hdlcos x) (hK (sf x)) (hdlsin x) (hdxv x)

/-- A worked instance confirming that the hypotheses of `jacobi_estimates` are
not contradictory, with a nonzero front velocity: the steering angle vanishes
identically (front and rear arclength coincide), the front normal velocity is
`η_F = cos` of period `2π`, and the periodic solution of `η_R' = η_F - η_R` is
`η_R = (cos + sin)/2`. -/
example :
    (∫ x in (0:ℝ)..2 * Real.pi, |(Real.cos x + Real.sin x) / 2|)
        ≤ (∫ s in (0:ℝ)..2 * Real.pi, |Real.cos s|)
      ∧ (∀ x : ℝ, |(Real.cos x + Real.sin x) / 2|
          ≤ (1 - Real.exp (-1))⁻¹ * ∫ s in (0:ℝ)..2 * Real.pi, |Real.cos s|)
      ∧ (∀ x : ℝ, |deriv (fun x : ℝ => (Real.cos x + Real.sin x) / 2) x|
          ≤ 1 / 1 + (1 - Real.exp (-1))⁻¹ * ∫ s in (0:ℝ)..2 * Real.pi, |Real.cos s|)
      ∧ (∀ x : ℝ, |deriv (deriv fun x : ℝ => (Real.cos x + Real.sin x) / 2) x|
          ≤ 1 / 1 ^ 2 + 2 * 0 ^ 2 * 1 / 1 ^ 3
            + (1 / 1 + (1 - Real.exp (-1))⁻¹ * ∫ s in (0:ℝ)..2 * Real.pi, |Real.cos s|)) :=
  jacobi_estimates (l := 2 * Real.pi) (P := 2 * Real.pi)
    (etaR := fun x => (Real.cos x + Real.sin x) / 2) (etaF := Real.cos)
    (G := Real.cos) (delta := fun _ => 0) (xf := id)
    (l0 := 1) (c := 1) (kh := 0) (SF0 := 1) (SF1 := 1)
    (etaFs := fun s => -Real.sin s) (dl := fun _ => 0) (sf := id)
    (K := fun _ => 0) (dxv := fun _ => 0)
    (by norm_num) (by nlinarith [Real.pi_gt_three]) (by norm_num)
    (fun s => Real.hasDerivAt_cos s)
    (fun s => Real.abs_cos_le_one s) (fun s => by simpa using Real.abs_sin_le_one s)
    (fun _ => by norm_num)
    continuous_const (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)
    (fun x => by simpa using hasDerivAt_id x)
    (fun x => by simpa using hasDerivAt_const x (0:ℝ))
    (fun _ => by norm_num)
    (fun s => by simpa using hasDerivAt_id s) rfl rfl
    (by funext y; simp) Real.continuous_cos (by intro x; simp [Real.cos_add])
    (fun x => by
      have h1 : HasDerivAt (fun x : ℝ => (Real.cos x + Real.sin x) / 2)
          ((-Real.sin x + Real.cos x) / 2) x := by
        simpa using ((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).div_const 2
      exact h1.congr_deriv (by ring))
    (by intro x; simp [Real.cos_add, Real.sin_add])
    (fun _ => by norm_num)

end JacobiAssembly
