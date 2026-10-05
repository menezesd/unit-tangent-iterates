module

public import UnitTangentIterates.Reduction

/-!
# Reparametrization invariance, and orbits up to reparametrization

The unit-tangent transform and the curvature do not depend on the (orientation preserving,
regular) parametrization.  Consequently an orbit of ovals `X n` with `𝒯 (X n) = X (n+1) ∘ φₙ`
for increasing reparametrizations `φₙ` gives a single oval `Γ = X 0` all of whose iterates
`𝒯ⁿ Γ = X n ∘ Φₙ` are ovals (`Ovals.isOval_iterate_of_orbit`).
-/

@[expose] public section

namespace Ovals

open Complex Real
open scoped ContDiff

/-- Chain rule for reparametrizations. -/
lemma hasDerivAt_comp_reparam {X : ℝ → ℂ} {φ : ℝ → ℝ} {t : ℝ}
    (hX : DifferentiableAt ℝ X (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    HasDerivAt (X ∘ φ) (((deriv φ t : ℝ) : ℂ) * deriv X (φ t)) t := by
  have := hX.hasDerivAt.scomp t hφ.hasDerivAt
  simpa [Complex.real_smul] using this

lemma deriv_comp_reparam {X : ℝ → ℂ} {φ : ℝ → ℝ} (hX : Differentiable ℝ X)
    (hφ : Differentiable ℝ φ) :
    deriv (X ∘ φ) = fun t => ((deriv φ t : ℝ) : ℂ) * deriv X (φ t) :=
  funext fun t => (hasDerivAt_comp_reparam (hX _) (hφ t)).deriv

/-- **`𝒯` commutes with increasing reparametrizations.** -/
theorem unitTangentTransform_comp {X : ℝ → ℂ} {φ : ℝ → ℝ} (hX : Differentiable ℝ X)
    (hφ : Differentiable ℝ φ) (hφpos : ∀ t, 0 < deriv φ t) :
    unitTangentTransform (X ∘ φ) = unitTangentTransform X ∘ φ := by
  funext t
  simp only [unitTangentTransform, deriv_comp_reparam hX hφ, Function.comp]
  have hp := hφpos t
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  have : ((deriv φ t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  rw [mul_div_mul_left _ _ this]

/-- **Curvature is invariant under increasing reparametrizations.** -/
theorem curvature_comp {X : ℝ → ℂ} {φ : ℝ → ℝ} (hX : ContDiff ℝ 2 X) (hφ : ContDiff ℝ 2 φ)
    (hφpos : ∀ t, 0 < deriv φ t) (t : ℝ) :
    curvature (X ∘ φ) t = curvature X (φ t) := by
  have hX1 : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hdX : Differentiable ℝ (deriv X) :=
    (hX.iterate_deriv' 1 1).differentiable (by norm_num)
  have hdφ : Differentiable ℝ (deriv φ) :=
    (hφ.iterate_deriv' 1 1).differentiable (by norm_num)
  unfold curvature
  rw [deriv_comp_reparam hX1 hφ1]
  have h2 : deriv (fun t => ((deriv φ t : ℝ) : ℂ) * deriv X (φ t)) t =
      ((deriv (deriv φ) t : ℝ) : ℂ) * deriv X (φ t) +
        ((deriv φ t : ℝ) : ℂ) * (((deriv φ t : ℝ) : ℂ) * deriv (deriv X) (φ t)) := by
    have a : HasDerivAt (fun t => ((deriv φ t : ℝ) : ℂ)) ((deriv (deriv φ) t : ℝ) : ℂ) t :=
      (hdφ t).hasDerivAt.ofReal_comp
    have b := hasDerivAt_comp_reparam (X := deriv X) (hdX (φ t)) (hφ1 t)
    exact (a.mul b).deriv
  simp only
  rw [h2]
  set a := deriv φ t
  set b := deriv (deriv φ) t
  set u := deriv X (φ t)
  set w := deriv (deriv X) (φ t)
  have ha : 0 < a := hφpos t
  have hnorm : ‖(a : ℂ) * u‖ = a * ‖u‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  rw [hnorm]
  have him : ((starRingEnd ℂ) ((a : ℂ) * u) * ((b : ℂ) * u + (a : ℂ) * ((a : ℂ) * w))).im =
      a ^ 3 * ((starRingEnd ℂ) u * w).im := by
    simp only [map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re, Complex.add_im,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [him]
  rcases eq_or_ne ‖u‖ 0 with hu | hu
  · simp [hu]
  · have : a ≠ 0 := ha.ne'
    field_simp

/-- A periodic curve that is injective on `[0, p)` is injective on every `[a, a + p)`. -/
lemma injOn_Ico_shift {X : ℝ → ℂ} {p : ℝ} (hp : 0 < p) (hper : Function.Periodic X p)
    (hinj : Set.InjOn X (Set.Ico 0 p)) (a : ℝ) : Set.InjOn X (Set.Ico a (a + p)) := by
  intro u hu w hw huw
  have hu' : X u = X (toIcoMod hp 0 u) := by
    rw [← hper.sub_zsmul_eq (toIcoDiv hp 0 u)]; rfl
  have hw' : X w = X (toIcoMod hp 0 w) := by
    rw [← hper.sub_zsmul_eq (toIcoDiv hp 0 w)]; rfl
  have hm : ∀ x, toIcoMod hp 0 x ∈ Set.Ico 0 p := fun x => by
    simpa using toIcoMod_mem_Ico hp 0 x
  have heq : toIcoMod hp 0 u = toIcoMod hp 0 w := hinj (hm u) (hm w) (by rw [← hu', ← hw', huw])
  -- so `u ≡ w (mod p)`, and `|u - w| < p`
  rw [toIcoMod_eq_toIcoMod] at heq
  obtain ⟨n, hn⟩ := heq
  have h1 : (n : ℝ) * p < p := by
    have : w - u = n • p := hn
    rw [zsmul_eq_mul] at this
    linarith [hu.1, hw.2]
  have h2 : -p < (n : ℝ) * p := by
    have : w - u = n • p := hn
    rw [zsmul_eq_mul] at this
    linarith [hu.2, hw.1]
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have hn2 : -1 < (n : ℝ) := by nlinarith
  have : n = 0 := by
    have a : n < 1 := by exact_mod_cast hn1
    have b : -1 < n := by exact_mod_cast hn2
    omega
  have : w - u = 0 := by rw [hn, this, zero_smul]
  linarith

/-- **Ovals stay ovals under increasing reparametrizations** that are compatible with the
periods: if `X` is `q`-periodic and injective on `[0, q)`, and `φ(t + p) = φ(t) + q`, then
`X ∘ φ` is an oval with period `p`. -/
theorem isOval_comp {X : ℝ → ℂ} {φ : ℝ → ℝ} {p q : ℝ} (hX : IsOval X) (hq : 0 < q)
    (hXper : Function.Periodic X q) (hXinj : Set.InjOn X (Set.Ico 0 q))
    (hφ : ContDiff ℝ ∞ φ) (hφpos : ∀ t, 0 < deriv φ t) (hp : 0 < p)
    (hφp : ∀ t, φ (t + p) = φ t + q) : IsOval (X ∘ φ) where
  contDiff := hX.contDiff.comp hφ
  regular := fun t => by
    rw [deriv_comp_reparam (hX.contDiff.differentiable (by simp))
      (hφ.differentiable (by simp))]
    exact mul_ne_zero (by exact_mod_cast (hφpos t).ne') (hX.regular _)
  curvature_pos := fun t => by
    rw [curvature_comp (hX.contDiff.of_le (by norm_cast)) (hφ.of_le (by norm_cast)) hφpos]
    exact hX.curvature_pos _
  closed_simple := by
    refine ⟨p, hp, fun t => by simp [Function.comp, hφp, hXper (φ t)], ?_⟩
    have hmono : StrictMono φ :=
      strictMono_of_deriv_pos hφpos
    intro u hu w hw huw
    apply hmono.injective
    apply injOn_Ico_shift hq hXper hXinj (φ 0)
    · exact ⟨hmono.monotone hu.1, by rw [← hφp]; exact hmono (by linarith [hu.2])⟩
    · exact ⟨hmono.monotone hw.1, by rw [← hφp]; exact hmono (by linarith [hw.2])⟩
    · exact huw

/-- An orbit of ovals of the unit-tangent transform, up to reparametrization: `X n` is an oval
which is `p n`-periodic and injective on `[0, p n)`, and `𝒯 (X n) = X (n+1) ∘ φ n` for a smooth
increasing reparametrization `φ n` carrying the period `p n` to the period `p (n+1)`. -/
structure IsOvalOrbit (X : ℕ → ℝ → ℂ) (p : ℕ → ℝ) (φ : ℕ → ℝ → ℝ) : Prop where
  oval : ∀ n, IsOval (X n)
  period_pos : ∀ n, 0 < p n
  periodic : ∀ n, Function.Periodic (X n) (p n)
  injOn : ∀ n, Set.InjOn (X n) (Set.Ico 0 (p n))
  reparam_smooth : ∀ n, ContDiff ℝ ∞ (φ n)
  reparam_pos : ∀ n t, 0 < deriv (φ n) t
  reparam_period : ∀ n t, φ n (t + p n) = φ n t + p (n + 1)
  step : ∀ n, unitTangentTransform (X n) = X (n + 1) ∘ φ n

/-- Along an orbit up to reparametrization, `𝒯ⁿ (X 0) = X n ∘ Φ n` for a smooth increasing
`Φ n` carrying the period `p 0` to `p n`. -/
theorem iterate_eq_of_orbit {X : ℕ → ℝ → ℂ} {p : ℕ → ℝ} {φ : ℕ → ℝ → ℝ}
    (h : IsOvalOrbit X p φ) (n : ℕ) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ (∀ t, 0 < deriv Φ t) ∧ (∀ t, Φ (t + p 0) = Φ t + p n) ∧
      unitTangentTransform^[n] (X 0) = X n ∘ Φ := by
  induction n with
  | zero => exact ⟨id, contDiff_id, fun t => by simp, fun t => rfl, rfl⟩
  | succ k ih =>
    obtain ⟨Φ, hΦ, hΦpos, hΦp, hit⟩ := ih
    refine ⟨φ k ∘ Φ, (h.reparam_smooth k).comp hΦ, fun t => ?_, fun t => ?_, ?_⟩
    · have h1 : DifferentiableAt ℝ (φ k) (Φ t) :=
        ((h.reparam_smooth k).differentiable (by simp)) _
      have h2 : DifferentiableAt ℝ Φ t := (hΦ.differentiable (by simp)) _
      rw [deriv_comp t h1 h2]
      exact mul_pos (h.reparam_pos k _) (hΦpos t)
    · simp [Function.comp, hΦp, h.reparam_period]
    · rw [Function.iterate_succ_apply', hit,
        unitTangentTransform_comp ((h.oval k).contDiff.differentiable (by simp))
          (hΦ.differentiable (by simp)) hΦpos, h.step k]
      rfl

/-- Every iterate of the initial curve of an orbit is an oval. -/
theorem isOval_iterate_of_orbit {X : ℕ → ℝ → ℂ} {p : ℕ → ℝ} {φ : ℕ → ℝ → ℝ}
    (h : IsOvalOrbit X p φ) (n : ℕ) : IsOval (unitTangentTransform^[n] (X 0)) := by
  obtain ⟨Φ, hΦ, hΦpos, hΦp, hit⟩ := iterate_eq_of_orbit h n
  rw [hit]
  exact isOval_comp (h.oval n) (h.period_pos n) (h.periodic n) (h.injOn n) hΦ hΦpos
    (h.period_pos 0) hΦp

/-- **Reduction of Theorem 1.1.**  An orbit of ovals (up to reparametrization) whose curves all
lie in strips of a common width `W` yields the main theorem: its initial curve is a noncircular
oval all of whose unit-tangent iterates are ovals. -/
theorem main_of_orbit {X : ℕ → ℝ → ℂ} {p : ℕ → ℝ} {φ : ℕ → ℝ → ℝ} {W : ℝ}
    (h : IsOvalOrbit X p φ)
    (hW : ∀ n, ∃ v : ℂ, ‖v‖ = 1 ∧ ∀ t t', coord v (X n t - X n t') ≤ W) :
    ∃ Γ : ℝ → ℂ, IsOval Γ ∧ ¬ IsCircle Γ ∧ ∀ n : ℕ, IsOval (unitTangentTransform^[n] Γ) := by
  refine ⟨X 0, h.oval 0, ?_, isOval_iterate_of_orbit h⟩
  refine not_isCircle_of_iterates_width_le (W := W) (isOval_iterate_of_orbit h) fun n => ?_
  obtain ⟨Φ, -, -, -, hit⟩ := iterate_eq_of_orbit h n
  obtain ⟨v, hv, hvW⟩ := hW n
  exact ⟨v, hv, fun t t' => by rw [hit]; exact hvW _ _⟩

end Ovals

end
