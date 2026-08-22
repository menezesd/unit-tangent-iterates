import Mathlib
import UnitTangentIterates.PeriodicInverse

/-!
# The inverse Jacobi estimates

This file formalizes the quantitative cores of the lemma *Inverse Jacobi
estimates* of the paper *A Noncircular Oval with Convex Unit-Tangent Iterates*.

The rear normal velocity is recovered from the front one by the explicit
periodic inverse `ℛ_ℓ` of `1 + ∂_x` (see `UnitTangentIterates.PeriodicInverse`):

```
  (1 + ∂_x) η_R = sec δ · η_F ∘ s ,        dx = cos δ · ds .
```

Writing `G` for the transported right-hand side `sec δ · η_F ∘ s`, the two
displayed facts of the paper's proof are:

* `ℛ_ℓ` is an `L¹` contraction on one period (`integral_abs_periodicInverse_le`),
  because its kernel is a probability kernel; combined with the change of
  variables `dx = cos δ ds` (`integral_abs_transport`) this gives the
  non-expansiveness of `W` (`W_nonexpansive`);
* `ℛ_ℓ` maps `L¹` into `L^∞` with a uniform constant, which gives the gain
  `S₀ ≤ C₀ W` (`S0_gain`).

The first-order gain `S₁ ≤ C₁(W + S₀)` comes from the differentiated identity
`η_{R,x} = sec δ η_F - η_R` (`S1_gain`), and the second-order gain from
differentiating once more, using `δ_x = sec δ (K - sin δ)`
(`second_derivative_identity`, `S2_bound`).

-/

noncomputable section

open Real MeasureTheory intervalIntegral PeriodicInverse

namespace JacobiEstimates

/-! ### `ℛ_ℓ` is an `L¹` contraction on a period -/

variable {l : ℝ} {f : ℝ → ℝ}

/-- The kernel of `ℛ_ℓ` is positive, so `|ℛ_ℓ f| ≤ ℛ_ℓ |f|` pointwise. -/
theorem abs_periodicInverse_le (hl : 0 < l) (x : ℝ) :
    |periodicInverse l f x| ≤ periodicInverse l (fun t => |f t|) x := by
  have hle : x - l ≤ x := by linarith
  have hpos : (0:ℝ) < 1 - Real.exp (-l) := by
    have : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hcpos : (0:ℝ) < (1 - Real.exp (-l))⁻¹ := inv_pos.mpr hpos
  have h1 : |∫ t in (x - l)..x, Real.exp (-(x - t)) * f t|
      ≤ ∫ t in (x - l)..x, |Real.exp (-(x - t)) * f t| :=
    intervalIntegral.abs_integral_le_integral_abs hle
  have h2 : (∫ t in (x - l)..x, |Real.exp (-(x - t)) * f t|)
      = ∫ t in (x - l)..x, Real.exp (-(x - t)) * |f t| := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [periodicInverse, periodicInverse, abs_mul, abs_of_pos hcpos]
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 hcpos.le

/-- The periodized inverse has the same mean as its right-hand side:
`∫₀^ℓ ℛ_ℓ f = ∫₀^ℓ f`.  This is the integrated form of `u' + u = f` over one
period. -/
theorem integral_periodicInverse_eq (hl : 0 < l) (hf : Continuous f)
    (hper : Function.Periodic f l) :
    (∫ x in (0:ℝ)..l, periodicInverse l f x) = ∫ x in (0:ℝ)..l, f x := by
  set u : ℝ → ℝ := periodicInverse l f with hu
  have hderiv : ∀ x, HasDerivAt u (f x - u x) x := fun x =>
    periodicInverse_hasDerivAt hl hf hper x
  have hucont : Continuous u := by
    have : Differentiable ℝ u := fun x => (hderiv x).differentiableAt
    exact this.continuous
  have hint : IntervalIntegrable (fun x => f x - u x) volume 0 l :=
    ((hf.sub hucont).intervalIntegrable _ _)
  have hFTC : (∫ x in (0:ℝ)..l, (f x - u x)) = u l - u 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint
  have hperu : u l = u 0 := by
    have := (periodicInverse_periodic (l := l) (f := f) hper) 0
    simpa [hu] using this
  rw [hperu, sub_self] at hFTC
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    (hucont.intervalIntegrable _ _)] at hFTC
  linarith

/-- **`ℛ_ℓ` is an `L¹` contraction over one period.**  This is the mechanism
behind `W(ℬΓ) ≤ W(Γ)`. -/
theorem integral_abs_periodicInverse_le (hl : 0 < l) (hf : Continuous f)
    (hper : Function.Periodic f l) :
    (∫ x in (0:ℝ)..l, |periodicInverse l f x|) ≤ ∫ x in (0:ℝ)..l, |f x| := by
  have habs : Continuous fun t => |f t| := hf.abs
  have habsper : Function.Periodic (fun t => |f t|) l := fun x => by simp [hper x]
  have hucont : Continuous (periodicInverse l f) := by
    have hd : ∀ x, HasDerivAt (periodicInverse l f) (f x - periodicInverse l f x) x := fun x =>
      periodicInverse_hasDerivAt hl hf hper x
    have hdiff : Differentiable ℝ (periodicInverse l f) := fun x => (hd x).differentiableAt
    exact hdiff.continuous
  have hvcont : Continuous (periodicInverse l fun t => |f t|) := by
    have hd : ∀ x, HasDerivAt (periodicInverse l fun t => |f t|)
        (|f x| - periodicInverse l (fun t => |f t|) x) x := fun x =>
      periodicInverse_hasDerivAt hl habs habsper x
    have hdiff : Differentiable ℝ (periodicInverse l fun t => |f t|) := fun x =>
      (hd x).differentiableAt
    exact hdiff.continuous
  have hmono : (∫ x in (0:ℝ)..l, |periodicInverse l f x|)
      ≤ ∫ x in (0:ℝ)..l, periodicInverse l (fun t => |f t|) x := by
    refine intervalIntegral.integral_mono_on hl.le (hucont.abs.intervalIntegrable _ _)
      (hvcont.intervalIntegrable _ _) (fun x _ => abs_periodicInverse_le hl x)
  calc (∫ x in (0:ℝ)..l, |periodicInverse l f x|)
      ≤ ∫ x in (0:ℝ)..l, periodicInverse l (fun t => |f t|) x := hmono
    _ = ∫ x in (0:ℝ)..l, |f x| := integral_periodicInverse_eq hl habs habsper

/-! ### The change of variables `dx = cos δ ds` -/

/-- **The change of variables between front and rear arclength.**  If `x` is
rear arclength as a function of front arclength, `x' = cos δ`, `x 0 = 0`,
`x P = ℓ`, and `G` is the transported front normal velocity, i.e.
`G (x s) cos δ(s) = η_F(s)`, then the two `L¹` norms agree. -/
theorem integral_abs_transport {P : ℝ} {xf delta etaF G : ℝ → ℝ}
    (hx : ∀ s, HasDerivAt xf (Real.cos (delta s)) s)
    (hdelta : Continuous delta) (hG : Continuous G)
    (hx0 : xf 0 = 0) (hxP : xf P = l)
    (hcos : ∀ s, 0 < Real.cos (delta s))
    (htransport : ∀ s, G (xf s) * Real.cos (delta s) = etaF s) :
    (∫ x in (0:ℝ)..l, |G x|) = ∫ s in (0:ℝ)..P, |etaF s| := by
  have hcomp : (∫ s in (0:ℝ)..P, Real.cos (delta s) • (fun x => |G x|) (xf s))
      = ∫ x in xf 0..xf P, |G x| :=
    intervalIntegral.integral_comp_smul_deriv (fun s _ => hx s) ((Real.continuous_cos.comp hdelta).continuousOn) hG.abs
  rw [hx0, hxP] at hcomp
  rw [← hcomp]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  have := htransport s
  simp only [smul_eq_mul]
  rw [← this, abs_mul, abs_of_pos (hcos s)]
  ring

/-- **`W` is non-expansive under the selected inverse.**  Combining the `L¹`
contraction with the change of variables: if the rear normal velocity `η_R`
is `ℛ_ℓ G` with `G` the transported front normal velocity, then the rear `L¹`
norm is at most the front one. -/
theorem W_nonexpansive {P : ℝ} {xf delta etaF G : ℝ → ℝ} (hl : 0 < l)
    (hG : Continuous G) (hGper : Function.Periodic G l)
    (hx : ∀ s, HasDerivAt xf (Real.cos (delta s)) s)
    (hdelta : Continuous delta) (hx0 : xf 0 = 0) (hxP : xf P = l)
    (hcos : ∀ s, 0 < Real.cos (delta s))
    (htransport : ∀ s, G (xf s) * Real.cos (delta s) = etaF s) :
    (∫ x in (0:ℝ)..l, |periodicInverse l G x|) ≤ ∫ s in (0:ℝ)..P, |etaF s| := by
  rw [← integral_abs_transport hx hdelta hG hx0 hxP hcos htransport]
  exact integral_abs_periodicInverse_le hl hG hGper

/-- **The `L¹ → L^∞` gain `S₀ ≤ C₀ W`.**  For a period bounded below by
`ℓ₀ > 0`, the sup norm of the rear normal velocity is at most
`(1 - e^{-ℓ₀})⁻¹` times the front `L¹` norm. -/
theorem S0_gain {P l0 : ℝ} {xf delta etaF G : ℝ → ℝ} (hl0 : 0 < l0) (hl : l0 ≤ l)
    (hG : Continuous G) (hGper : Function.Periodic G l)
    (hx : ∀ s, HasDerivAt xf (Real.cos (delta s)) s)
    (hdelta : Continuous delta) (hx0 : xf 0 = 0) (hxP : xf P = l)
    (hcos : ∀ s, 0 < Real.cos (delta s))
    (htransport : ∀ s, G (xf s) * Real.cos (delta s) = etaF s) (x : ℝ) :
    |periodicInverse l G x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s| := by
  have hlpos : 0 < l := lt_of_lt_of_le hl0 hl
  have habs : Continuous fun t => |G t| := hG.abs
  have habsper : Function.Periodic (fun t => |G t|) l := fun t => by simp [hGper t]
  have hshift : (∫ t in (x - l)..x, |G t|) = ∫ t in (0:ℝ)..l, |G t| := by
    have := habsper.intervalIntegral_add_eq (x - l) 0
    simpa using this
  have hbase := periodicInverse_abs_le hlpos hG x
  rw [hshift] at hbase
  have htr := integral_abs_transport (l := l) hx hdelta hG hx0 hxP hcos htransport
  rw [htr] at hbase
  refine hbase.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have h1 : Real.exp (-l) ≤ Real.exp (-l0) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (0:ℝ) < 1 - Real.exp (-l0) := by
      have : Real.exp (-l0) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have h3 : (0:ℝ) < 1 - Real.exp (-l) := by
      have : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    exact inv_anti₀ h2 (by linarith)
  · rw [← htr]
    exact intervalIntegral.integral_nonneg hlpos.le (fun t _ => abs_nonneg _)

/-! ### The first- and second-order gains -/

/-- **The first-order gain.**  From `η_{R,x} = sec δ η_F - η_R`, the sup norm
of `η_{R,x}` is controlled by those of `η_F` and `η_R`. -/
theorem S1_gain {etaR etaRx etaF delta A B : ℝ}
    (hid : etaRx = etaF / Real.cos delta - etaR)
    (hcos : 0 < Real.cos delta) (hlow : Real.sqrt (1 - A ^ 2) ≤ Real.cos delta)
    (hA : 0 < Real.sqrt (1 - A ^ 2)) (hF : |etaF| ≤ B) (hR : |etaR| ≤ B) :
    |etaRx| ≤ (1 / Real.sqrt (1 - A ^ 2) + 1) * B := by
  have h1 : |etaF / Real.cos delta| ≤ B / Real.sqrt (1 - A ^ 2) := by
    rw [abs_div, abs_of_pos hcos]
    exact div_le_div₀ (le_trans (abs_nonneg _) hF) hF hA hlow
  calc |etaRx| = |etaF / Real.cos delta - etaR| := by rw [hid]
    _ ≤ |etaF / Real.cos delta| + |etaR| := abs_sub _ _
    _ ≤ B / Real.sqrt (1 - A ^ 2) + B := add_le_add h1 hR
    _ = (1 / Real.sqrt (1 - A ^ 2) + 1) * B := by field_simp

/-- The steering angle in rear arclength satisfies `δ_x = sec δ (K - sin δ)`:
this is the front equation `δ_s = K - sin δ` transported by `ds = sec δ dx`. -/
theorem steering_deriv_rear {deltaF sf Kv : ℝ → ℝ} {x : ℝ}
    (hs : HasDerivAt sf (1 / Real.cos (deltaF (sf x))) x)
    (hd : ∀ s, HasDerivAt deltaF (Kv s - Real.sin (deltaF s)) s) :
    HasDerivAt (fun y => deltaF (sf y))
      ((Kv (sf x) - Real.sin (deltaF (sf x))) / Real.cos (deltaF (sf x))) x := by
  have := (hd (sf x)).comp x hs
  refine this.congr_deriv ?_
  field_simp

/-- **The second-order identity.**  Differentiating `η_{R,x} = sec δ η_F - η_R`
in rear arclength gives
`η_{R,xx} = (sec δ)_x η_F + sec²δ (η_F)_s - η_{R,x}`, the coefficient
`(sec δ)_x = sec δ tan δ · δ_x` being uniformly bounded on the selected
strip. -/
theorem second_derivative_identity {etaR etaF deltaf : ℝ → ℝ} {x : ℝ}
    {etaRx etaFs deltax : ℝ}
    (hcos : Real.cos (deltaf x) ≠ 0)
    (hetaR : ∀ y, HasDerivAt etaR (etaF y / Real.cos (deltaf y) - etaR y) y)
    (hetaF : HasDerivAt etaF etaFs x)
    (hdelta : HasDerivAt deltaf deltax x)
    (hRx : etaRx = etaF x / Real.cos (deltaf x) - etaR x) :
    HasDerivAt (deriv etaR)
      (Real.sin (deltaf x) / Real.cos (deltaf x) ^ 2 * deltax * etaF x
        + etaFs / Real.cos (deltaf x) - etaRx) x := by
  have hfun : deriv etaR = fun y => etaF y / Real.cos (deltaf y) - etaR y := by
    funext y; exact (hetaR y).deriv
  rw [hfun]
  have hcosd : HasDerivAt (fun y => Real.cos (deltaf y)) (-Real.sin (deltaf x) * deltax) x := by
    simpa using (Real.hasDerivAt_cos (deltaf x)).comp x hdelta
  have hdiv := hetaF.div hcosd hcos
  have hsub := hdiv.sub (hetaR x)
  refine hsub.congr_deriv ?_
  rw [hRx]
  field_simp
  ring

end JacobiEstimates
