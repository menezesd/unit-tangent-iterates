import Mathlib
import UnitTangentIterates.SteeringExistence
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.PeriodicInverse

/-!
# The selected data of a front, and of a whole path of fronts

The path-metric statements of `GaugeGeometryPathClosing.lean` take as data, at
every time of a normal path of fronts, a steering angle `δ`, a right inverse
`sf` of the rear arclength and a solution `η_R` of the inverse Jacobi ODE

`∂_x η_R + η_R = η_F(sf x) / cos δ(sf x)`,

periodic with the rear period and of class `C²`.  This file shows that these
data always **exist**, and are produced from the front alone: from a continuous
front curvature `0 ≤ K ≤ κ̂ < 1`, periodic with the front period, and a `C¹`
front normal velocity with the same period.

* `exists_selected_slice_data` — one time;
* `exists_selected_path_data` — the whole path, with the data measurable in
  nothing more than the pointwise choice, and with `η_R` vanishing at the times
  where the front velocity does (so that the "rest" hypothesis of the path
  metric is inherited from the path of fronts).

Together with `SteeringExistence.existsUnique_periodic_steering` (which says
that `δ` is unique) this removes from the assembled statements every hypothesis
concerning the *auxiliary* data of the selected inverse; what is left there
concerns the geometry of the rear family itself.
-/

noncomputable section

open Set Function ArclengthInverse RearTrack PeriodicInverse

namespace SelectedPathData

/-! ### An ODE regularity lemma -/

/-- A solution of `u' = f − u` with `f` of class `C¹` is of class `C²`. -/
theorem contDiff_two_of_ode {u f : ℝ → ℝ} (hf : ContDiff ℝ (1 : ℕ) f)
    (hu : ∀ x, HasDerivAt u (f x - u x) x) : ContDiff ℝ (2 : ℕ) u := by
  have hdiff : Differentiable ℝ u := fun x => (hu x).differentiableAt
  have hderiv : deriv u = fun x => f x - u x := funext fun x => (hu x).deriv
  have h1 : ContDiff ℝ (1 : ℕ) u := by
    rw [Nat.cast_one, contDiff_one_iff_deriv]
    exact ⟨hdiff, by rw [hderiv]; exact hf.continuous.sub hdiff.continuous⟩
  have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) u := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨hdiff, by simp, ?_⟩
    rw [hderiv]
    have hf' : ContDiff ℝ (1 : WithTop ℕ∞) f := by simpa using hf
    have h1' : ContDiff ℝ (1 : WithTop ℕ∞) u := by simpa using h1
    exact hf'.sub h1'
  norm_num at h2 ⊢
  exact h2

/-- **Uniqueness of the periodic solution of the inverse Jacobi ODE.**  Two
`Q`-periodic solutions of `u' = f − u` coincide: the difference solves
`w' = −w`, hence is a multiple of `e^{−x}`, and no nonzero such function is
periodic. -/
theorem eq_of_periodic_ode {Q : ℝ} (hQ : 0 < Q) {f u w : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (f x - u x) x) (hw : ∀ x, HasDerivAt w (f x - w x) x)
    (hup : Function.Periodic u Q) (hwp : Function.Periodic w Q) : u = w := by
  have hgd : ∀ x, HasDerivAt (fun y => Real.exp y * (u y - w y)) 0 x := by
    intro x
    have h := (Real.hasDerivAt_exp x).mul ((hu x).sub (hw x))
    convert h using 1
    simp only [Pi.sub_apply]
    ring
  have hgconst : ∀ x y : ℝ, Real.exp x * (u x - w x) = Real.exp y * (u y - w y) :=
    is_const_of_deriv_eq_zero (fun x => (hgd x).differentiableAt)
      (fun x => (hgd x).deriv)
  -- the constant is zero, since `e^x (u−w) x` is constant and `u−w` is periodic
  have hzero : ∀ x, u x - w x = 0 := by
    intro x
    by_contra hne
    have h1 : Real.exp (x + Q) * (u (x + Q) - w (x + Q)) = Real.exp x * (u x - w x) :=
      hgconst _ _
    have h2 : u (x + Q) - w (x + Q) = u x - w x := by rw [hup x, hwp x]
    rw [h2] at h1
    have hexp : Real.exp (x + Q) = Real.exp x := by
      have hux : u x - w x ≠ 0 := hne
      exact mul_right_cancel₀ hux h1
    have : Real.exp x < Real.exp (x + Q) := Real.exp_lt_exp.mpr (by linarith)
    rw [hexp] at this
    exact lt_irrefl _ this
  funext x
  have := hzero x
  linarith

/-! ### The auxiliary data of one front -/

section Slice

variable {K etaF etaFs delta sf : ℝ → ℝ} {P kh : ℝ}

/-- The steering angle is continuous. -/
theorem continuous_of_steering (hsteer : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) :
    Continuous delta :=
  Differentiable.continuous (fun s => (hsteer s).differentiableAt)

/-- On the selected strip the rear speed `cos δ` is positive. -/
theorem cos_steering_pos (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hstrip0 : ∀ s, 0 ≤ delta s) (hstrip1 : ∀ s, delta s ≤ Real.arcsin kh) (s : ℝ) :
    0 < Real.cos (delta s) :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr (by nlinarith))
    (Shadowing.cos_ge_of_mem_strip (hstrip0 s) (hstrip1 s))

/-- The rear period is positive. -/
theorem rearPeriod_pos (hP : 0 < P) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hdc : Continuous delta)
    (hstrip0 : ∀ s, 0 ≤ delta s) (hstrip1 : ∀ s, delta s ≤ Real.arcsin kh) :
    0 < rearArclength delta P := by
  have hc0 : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  exact lt_of_lt_of_le (by positivity)
    (rearArclength_ge hdc (fun s => Shadowing.cos_ge_of_mem_strip (hstrip0 s) (hstrip1 s)) hP.le)

/-- The change of variable translates the front period into the rear period. -/
theorem sf_add_rearPeriod (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hdc : Continuous delta)
    (hstrip0 : ∀ s, 0 ≤ delta s) (hstrip1 : ∀ s, delta s ≤ Real.arcsin kh)
    (hdper : Function.Periodic delta P) (hsfinv : ∀ x, rearArclength delta (sf x) = x)
    (x : ℝ) : sf (x + rearArclength delta P) = sf x + P :=
  rightInverse_add_of_shift
    (strictMono_rearArclength hdc hkh1 hkh0 hstrip0 hstrip1).injective
    (fun s => rearArclength_add_period hdc hdper s) hsfinv x

/-- The right-hand side of the inverse Jacobi ODE is periodic with the rear
period. -/
theorem jacobiRHS_periodic (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hdc : Continuous delta)
    (hstrip0 : ∀ s, 0 ≤ delta s) (hstrip1 : ∀ s, delta s ≤ Real.arcsin kh)
    (hdper : Function.Periodic delta P) (hsfinv : ∀ x, rearArclength delta (sf x) = x)
    (hetaFper : Function.Periodic etaF P) :
    Function.Periodic (fun x => etaF (sf x) / Real.cos (delta (sf x)))
      (rearArclength delta P) := by
  intro x
  simp only [sf_add_rearPeriod hkh0 hkh1 hdc hstrip0 hstrip1 hdper hsfinv x,
    hetaFper (sf x), hdper (sf x)]

/-- The change of variable is of class `C¹`. -/
theorem sf_contDiff (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hdc : Continuous delta)
    (hstrip0 : ∀ s, 0 ≤ delta s) (hstrip1 : ∀ s, delta s ≤ Real.arcsin kh)
    (hsfinv : ∀ x, rearArclength delta (sf x) = x) : ContDiff ℝ (1 : ℕ) sf := by
  have hc0 : 0 < Real.sqrt (1 - kh ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hcos := fun s => Shadowing.cos_ge_of_mem_strip (hstrip0 s) (hstrip1 s)
  have hxd : ∀ s, HasDerivAt (rearArclength delta) (Real.cos (delta s)) s :=
    hasDerivAt_rearArclength hdc
  have hsfd : ∀ x, HasDerivAt sf (1 / Real.cos (delta (sf x))) x :=
    hasDerivAt_of_rightInverse hc0 hxd hcos hsfinv
  have hsfc : Continuous sf := continuous_of_rightInverse hc0 hxd hcos hsfinv
  rw [Nat.cast_one, contDiff_one_iff_deriv]
  refine ⟨fun x => (hsfd x).differentiableAt, ?_⟩
  have hderiv : deriv sf = fun x => 1 / Real.cos (delta (sf x)) := funext fun x => (hsfd x).deriv
  rw [hderiv]
  exact continuous_const.div (Real.continuous_cos.comp (hdc.comp hsfc))
    (fun x => (cos_steering_pos hkh0 hkh1 hstrip0 hstrip1 (sf x)).ne')

/-- The right-hand side of the inverse Jacobi ODE is of class `C¹`. -/
theorem jacobiRHS_contDiff (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hKc : Continuous K)
    (hsteer : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hstrip0 : ∀ s, 0 ≤ delta s) (hstrip1 : ∀ s, delta s ≤ Real.arcsin kh)
    (hsfinv : ∀ x, rearArclength delta (sf x) = x)
    (hetaFd : ∀ s, HasDerivAt etaF (etaFs s) s) (hetaFsc : Continuous etaFs) :
    ContDiff ℝ (1 : ℕ) fun x => etaF (sf x) / Real.cos (delta (sf x)) := by
  have hdc : Continuous delta := continuous_of_steering hsteer
  have hetaFC1 : ContDiff ℝ (1 : ℕ) etaF := by
    rw [Nat.cast_one, contDiff_one_iff_deriv]
    refine ⟨fun s => (hetaFd s).differentiableAt, ?_⟩
    have hderiv : deriv etaF = etaFs := funext fun s => (hetaFd s).deriv
    rw [hderiv]; exact hetaFsc
  have hdeltaC1 : ContDiff ℝ (1 : ℕ) delta := by
    rw [Nat.cast_one, contDiff_one_iff_deriv]
    refine ⟨fun s => (hsteer s).differentiableAt, ?_⟩
    have hderiv : deriv delta = fun s => K s - Real.sin (delta s) := funext fun s => (hsteer s).deriv
    rw [hderiv]; exact hKc.sub (Real.continuous_sin.comp hdc)
  have hgC1 : ContDiff ℝ (1 : ℕ) fun s => etaF s / Real.cos (delta s) :=
    hetaFC1.div (Real.contDiff_cos.comp hdeltaC1)
      (fun s => (cos_steering_pos hkh0 hkh1 hstrip0 hstrip1 s).ne')
  exact hgC1.comp (sf_contDiff hkh0 hkh1 hdc hstrip0 hstrip1 hsfinv)

/-- **The rear normal velocity is automatically of class `C²`.**  Any periodic
solution of the inverse Jacobi ODE over a front whose curvature is continuous
and whose normal velocity is `C¹` is twice continuously differentiable: the
hypothesis `hetaC2` of the assembled path-metric statements is a consequence of
the others. -/
theorem contDiff_two_of_jacobi_ode {etaR : ℝ → ℝ} (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hKc : Continuous K)
    (hsteer : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hstrip0 : ∀ s, 0 ≤ delta s) (hstrip1 : ∀ s, delta s ≤ Real.arcsin kh)
    (hetaFd : ∀ s, HasDerivAt etaF (etaFs s) s) (hetaFsc : Continuous etaFs)
    (hsfinv : ∀ x, rearArclength delta (sf x) = x)
    (hetaR : ∀ x, HasDerivAt etaR (etaF (sf x) / Real.cos (delta (sf x)) - etaR x) x) :
    ContDiff ℝ (2 : ℕ) etaR := by
  have hfC1 : ContDiff ℝ (1 : ℕ) fun x => etaF (sf x) / Real.cos (delta (sf x)) :=
    jacobiRHS_contDiff hkh0 hkh1 hKc hsteer hstrip0 hstrip1 hsfinv hetaFd hetaFsc
  exact contDiff_two_of_ode hfC1 hetaR

/-- **The rear normal velocity is unique.**  Two periodic solutions of the
inverse Jacobi ODE of the same front coincide, so the data produced by
`exists_selected_slice_data` are the only ones. -/
theorem jacobi_solution_unique (hP : 0 < P) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hsteer : ∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s)
    (hstrip0 : ∀ s, 0 ≤ delta s) (hstrip1 : ∀ s, delta s ≤ Real.arcsin kh)
    {u w : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (etaF (sf x) / Real.cos (delta (sf x)) - u x) x)
    (hw : ∀ x, HasDerivAt w (etaF (sf x) / Real.cos (delta (sf x)) - w x) x)
    (hup : Function.Periodic u (rearArclength delta P))
    (hwp : Function.Periodic w (rearArclength delta P)) : u = w :=
  eq_of_periodic_ode
    (rearPeriod_pos hP hkh0 hkh1 (continuous_of_steering hsteer) hstrip0 hstrip1)
    hu hw hup hwp

end Slice

/-! ### The data of one slice -/

/-- **The selected data of a front exist.**

For a front of period `P > 0` whose curvature `K` is continuous, `P`-periodic
and pinched by `0 ≤ K ≤ κ̂ < 1`, and a `C¹`, `P`-periodic front normal velocity
`η_F`, there are a steering angle `δ` solving `δ' = K − sin δ` in the closed
selected strip `[0, arcsin κ̂]` and `P`-periodic, a right inverse `sf` of the
rear arclength of `δ`, and a solution `η_R` of the inverse Jacobi ODE which is
periodic with the rear period `Q = x(P)` and of class `C²`; moreover `η_R`
vanishes identically if `η_F` does. -/
theorem exists_selected_slice_data {K etaF etaFs : ℝ → ℝ} {P kh : ℝ}
    (hP : 0 < P) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hKc : Continuous K) (hKper : Function.Periodic K P)
    (hK0 : ∀ s, 0 ≤ K s) (hKk : ∀ s, K s ≤ kh)
    (hetaFd : ∀ s, HasDerivAt etaF (etaFs s) s) (hetaFsc : Continuous etaFs)
    (hetaFper : Function.Periodic etaF P) :
    ∃ delta sf etaR : ℝ → ℝ,
      (∀ s, HasDerivAt delta (K s - Real.sin (delta s)) s) ∧
      (∀ s, 0 ≤ delta s) ∧ (∀ s, delta s ≤ Real.arcsin kh) ∧
      Function.Periodic delta P ∧
      (∀ x, rearArclength delta (sf x) = x) ∧
      (∀ x, HasDerivAt etaR (etaF (sf x) / Real.cos (delta (sf x)) - etaR x) x) ∧
      Function.Periodic etaR (rearArclength delta P) ∧
      ContDiff ℝ (2 : ℕ) etaR ∧
      ((∀ s, etaF s = 0) → etaR = fun _ => 0) := by
  obtain ⟨delta, hdper, hdrange, -, hdode⟩ :=
    SteeringExistence.exists_periodic_steering hP hKc hKper hkh0 hkh1.le hK0 hKk
  have hstrip0 : ∀ s, 0 ≤ delta s := fun s => (hdrange s).1
  have hstrip1 : ∀ s, delta s ≤ Real.arcsin kh := fun s => (hdrange s).2
  have hdc : Continuous delta := continuous_of_steering hdode
  obtain ⟨sf, hsf⟩ := exists_inverse_rearArclength hkh0 hkh1 hdc hstrip0 hstrip1
  set Q : ℝ := rearArclength delta P with hQdef
  have hQ0 : 0 < Q := rearPeriod_pos hP hkh0 hkh1 hdc hstrip0 hstrip1
  set f : ℝ → ℝ := fun x => etaF (sf x) / Real.cos (delta (sf x)) with hfdef
  have hfper : Function.Periodic f Q :=
    jacobiRHS_periodic hkh0 hkh1 hdc hstrip0 hstrip1 hdper hsf hetaFper
  have hfC1 : ContDiff ℝ (1 : ℕ) f :=
    jacobiRHS_contDiff hkh0 hkh1 hKc hdode hstrip0 hstrip1 hsf hetaFd hetaFsc
  have hfc : Continuous f := hfC1.continuous
  refine ⟨delta, sf, periodicInverse Q f, hdode, hstrip0, hstrip1, hdper, hsf, ?_, ?_, ?_, ?_⟩
  · exact fun x => periodicInverse_hasDerivAt hQ0 hfc hfper x
  · exact periodicInverse_periodic hfper
  · exact contDiff_two_of_ode hfC1 (fun x => periodicInverse_hasDerivAt hQ0 hfc hfper x)
  · intro hzero
    have hf0 : f = fun _ => (0:ℝ) := by
      funext x; simp [hfdef, hzero (sf x)]
    funext x
    simp [periodicInverse, hf0]

/-! ### The data of a whole path -/

/-- **The selected data of a path of fronts exist.**  The pointwise choice of
`exists_selected_slice_data`, made at every time; the last conjunct lets the
"rest outside the time interval" hypothesis of the path metric be inherited
from the path of fronts. -/
theorem exists_selected_path_data {K etaF etaFs : ℝ → ℝ → ℝ} {P : ℝ → ℝ} {kh : ℝ}
    (hP : ∀ t, 0 < P t) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hKc : ∀ t, Continuous (K t)) (hKper : ∀ t, Function.Periodic (K t) (P t))
    (hK0 : ∀ t s, 0 ≤ K t s) (hKk : ∀ t s, K t s ≤ kh)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s) (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Function.Periodic (etaF t) (P t)) :
    ∃ delta sf etaR : ℝ → ℝ → ℝ,
      (∀ t s, HasDerivAt (delta t) (K t s - Real.sin (delta t s)) s) ∧
      (∀ t s, 0 ≤ delta t s) ∧ (∀ t s, delta t s ≤ Real.arcsin kh) ∧
      (∀ t, Function.Periodic (delta t) (P t)) ∧
      (∀ t x, rearArclength (delta t) (sf t x) = x) ∧
      (∀ t x, HasDerivAt (etaR t)
        (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x) ∧
      (∀ t, Function.Periodic (etaR t) (rearArclength (delta t) (P t))) ∧
      (∀ t, ContDiff ℝ (2 : ℕ) (etaR t)) ∧
      (∀ t, (∀ s, etaF t s = 0) → etaR t = fun _ => 0) := by
  have hslice : ∀ t : ℝ, ∃ d : (ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ),
      (∀ s, HasDerivAt d.1 (K t s - Real.sin (d.1 s)) s) ∧
      (∀ s, 0 ≤ d.1 s) ∧ (∀ s, d.1 s ≤ Real.arcsin kh) ∧
      Function.Periodic d.1 (P t) ∧
      (∀ x, rearArclength d.1 (d.2.1 x) = x) ∧
      (∀ x, HasDerivAt d.2.2
        (etaF t (d.2.1 x) / Real.cos (d.1 (d.2.1 x)) - d.2.2 x) x) ∧
      Function.Periodic d.2.2 (rearArclength d.1 (P t)) ∧
      ContDiff ℝ (2 : ℕ) d.2.2 ∧
      ((∀ s, etaF t s = 0) → d.2.2 = fun _ => 0) := by
    intro t
    obtain ⟨delta, sf, etaR, h⟩ := exists_selected_slice_data (hP t) hkh0 hkh1 (hKc t)
      (hKper t) (hK0 t) (hKk t) (hetaFd t) (hetaFsc t) (hetaFper t)
    exact ⟨⟨delta, sf, etaR⟩, h⟩
  choose d hd using hslice
  exact ⟨fun t => (d t).1, fun t => (d t).2.1, fun t => (d t).2.2,
    fun t => (hd t).1, fun t => (hd t).2.1, fun t => (hd t).2.2.1,
    fun t => (hd t).2.2.2.1, fun t => (hd t).2.2.2.2.1, fun t => (hd t).2.2.2.2.2.1,
    fun t => (hd t).2.2.2.2.2.2.1, fun t => (hd t).2.2.2.2.2.2.2.1,
    fun t => (hd t).2.2.2.2.2.2.2.2⟩

end SelectedPathData
