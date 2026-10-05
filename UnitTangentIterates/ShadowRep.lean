module

public import UnitTangentIterates.ShadowPath
public import UnitTangentIterates.PulseAux

/-!
# Normalized intrinsic ovals and the selected inverse on them

An oval with half-perimeter `L` is described by its curvature `f` as a function of the
normalized arclength `σ = s / L` (a `1`-periodic function).  Data `(a, g)` in a material
parameter of period `p` (as in `Ovals.PathData`) *represent* `(L, f)` if `∫₀ᵖ g = L` and there
is a normalized arclength `s(u)` (`s' = g / L`, `s(u + p) = s(u) + 1`) with `a = g · f ∘ s`
(`Ovals.Represents`).

The selected inverse on normalized ovals is `Ovals.rearL`, `Ovals.rearF`: the steering angle
`dt` of `(L, f)` is the `1`-periodic solution of `dt' = L f - L sin dt`, the rear half-perimeter is
`∫₀¹ L cos dt` and the rear curvature is `tan dt` read in normalized rear arclength.  The main
result, `Ovals.represents_rear`, says that the selected inverse commutes with representation:
the steering angle of any data representing `(L, f)` is `dt ∘ s`, and the rear data represent
`(rearL L f, rearF L f)`.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- Data `(a, g)` of period `p` represent the normalized oval `(L, f)`. -/
def Represents (p : ℝ) (a g : ℝ → ℝ) (L : ℝ) (f : ℝ → ℝ) : Prop :=
  (∫ u in (0 : ℝ)..p, g u) = L ∧ ∃ s : ℝ → ℝ, (∀ u, HasDerivAt s (g u / L) u) ∧
    (∀ u, s (u + p) = s u + 1) ∧ ∀ u, a u = g u * f (s u)

/-- Normalized arclength `u ↦ (∫₀ᵘ g) / ∫₀ᵖ g`. -/
noncomputable def normArc (p : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  (∫ v in (0 : ℝ)..u, g v) / ∫ v in (0 : ℝ)..p, g v

/-- The curvature `a / g` read in normalized arclength. -/
noncomputable def normF (p : ℝ) (a g : ℝ → ℝ) (y : ℝ) : ℝ :=
  a (Function.invFun (normArc p g) y) / g (Function.invFun (normArc p g) y)

/-- The steering angle of the normalized oval `(L, f)`. -/
noncomputable def rδ (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  steerAngle 1 (fun σ => L * f σ) (fun _ => L)

/-- The half-perimeter of the selected rear of `(L, f)`. -/
noncomputable def rearL (L : ℝ) (f : ℝ → ℝ) : ℝ := ∫ σ in (0 : ℝ)..1, L * Real.cos (rδ L f σ)

/-- The normalized curvature of the selected rear of `(L, f)`. -/
noncomputable def rearF (L : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  normF 1 (fun σ => L * Real.sin (rδ L f σ)) (fun σ => L * Real.cos (rδ L f σ))

lemma integral_add_period {g : ℝ → ℝ} {p : ℝ} (hg : Continuous g) (hgp : Function.Periodic g p)
    (u : ℝ) : ∫ v in (0 : ℝ)..u + p, g v = (∫ v in (0 : ℝ)..u, g v) + ∫ v in (0 : ℝ)..p, g v := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := u) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), hgp.intervalIntegral_add_eq u 0, zero_add]

lemma integral_pos_of_periodic {g : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hg : Continuous g)
    (hg0 : ∀ u, 0 < g u) : 0 < ∫ v in (0 : ℝ)..p, g v :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hg.intervalIntegrable _ _)
    (fun u _ => hg0 u) hp

section normArc

variable {p : ℝ} {g : ℝ → ℝ}

lemma hasDerivAt_normArc (hg : Continuous g) (u : ℝ) :
    HasDerivAt (normArc p g) (g u / ∫ v in (0 : ℝ)..p, g v) u :=
  (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt).div_const _

lemma normArc_add_period (hp : 0 < p) (hg : Continuous g) (hgp : Function.Periodic g p)
    (hg0 : ∀ u, 0 < g u) (u : ℝ) : normArc p g (u + p) = normArc p g u + 1 := by
  have := integral_pos_of_periodic hp hg hg0
  unfold normArc
  rw [integral_add_period hg hgp, add_div, div_self this.ne']

lemma normArc_strictMono (hp : 0 < p) (hg : Continuous g) (hg0 : ∀ u, 0 < g u) :
    StrictMono (normArc p g) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_normArc hg) fun u =>
    div_pos (hg0 u) (integral_pos_of_periodic hp hg hg0)

lemma invFun_normArc (hp : 0 < p) (hg : Continuous g) (hg0 : ∀ u, 0 < g u) (u : ℝ) :
    Function.invFun (normArc p g) (normArc p g u) = u :=
  Function.leftInverse_invFun (normArc_strictMono hp hg hg0).injective u

/-- **Normalization**: periodic data represent their own normalization. -/
theorem represents_normF (hp : 0 < p) {a : ℝ → ℝ} (hg : Continuous g)
    (hgp : Function.Periodic g p) (hg0 : ∀ u, 0 < g u) :
    Represents p a g (∫ v in (0 : ℝ)..p, g v) (normF p a g) := by
  refine ⟨rfl, normArc p g, hasDerivAt_normArc hg, normArc_add_period hp hg hgp hg0,
    fun u => ?_⟩
  simp only [normF, invFun_normArc hp hg hg0]
  field_simp [(hg0 u).ne']

end normArc

/-- A lower bound for a continuous positive periodic function, divided by `L`. -/
lemma Represents.L_pos {p L : ℝ} {a g f : ℝ → ℝ} (h : Represents p a g L f) (hp : 0 < p)
    (hg : Continuous g) (hg0 : ∀ u, 0 < g u) : 0 < L :=
  h.1 ▸ integral_pos_of_periodic hp hg hg0

/-- The normalized arclength of a representation is a bijection with a differentiable
inverse. -/
lemma Represents.exists_inverse {p L : ℝ} {g : ℝ → ℝ} {s : ℝ → ℝ} (hp : 0 < p)
    (hg : Continuous g) (hgp : Function.Periodic g p) (hg0 : ∀ u, 0 < g u) (hL : 0 < L)
    (hs : ∀ u, HasDerivAt s (g u / L) u) :
    ∃ G : ℝ → ℝ, (∀ y, s (G y) = y) ∧ (∀ x, G (s x) = x) ∧ Continuous G := by
  obtain ⟨m, hm, hgm⟩ := exists_pos_lower_bound_of_periodic hp hg hgp hg0
  obtain ⟨G, h1, h2, h3⟩ := exists_inverse_of_deriv_ge (c := m / L) (by positivity) hs
    (fun u => div_le_div_of_nonneg_right (hgm u) hL.le)
  exact ⟨G, h1, h2, continuous_iff_continuousAt.2 fun y => (h3 y).continuousAt⟩

/-- **Curvature bounds transfer** between two data representing the same normalized oval. -/
theorem Represents.curv_le_transfer {p₁ p₂ L c : ℝ} {a₁ g₁ a₂ g₂ f : ℝ → ℝ}
    (h₁ : Represents p₁ a₁ g₁ L f) (h₂ : Represents p₂ a₂ g₂ L f) (hp₁ : 0 < p₁)
    (hg₁ : Continuous g₁) (hg₁p : Function.Periodic g₁ p₁) (hg₁0 : ∀ u, 0 < g₁ u)
    (hg₂0 : ∀ u, 0 < g₂ u) (hle : ∀ u, a₁ u ≤ c * g₁ u) : ∀ u, a₂ u ≤ c * g₂ u := by
  have hL := h₁.L_pos hp₁ hg₁ hg₁0
  obtain ⟨-, s₁, hs₁, -, ha₁⟩ := h₁
  obtain ⟨-, s₂, -, -, ha₂⟩ := h₂
  obtain ⟨G, hG, -, -⟩ := Represents.exists_inverse hp₁ hg₁ hg₁p hg₁0 hL hs₁
  intro u
  have h1 := hle (G (s₂ u))
  rw [ha₁, hG] at h1
  rw [ha₂]
  have := hg₁0 (G (s₂ u))
  have hf : f (s₂ u) ≤ c := by
    by_contra hc
    push_neg at hc
    nlinarith
  exact (mul_comm c _ ▸ mul_le_mul_of_nonneg_left hf (hg₂0 u).le)

/-- Data `(K, 1)` of period `L` represent `(L, σ ↦ K (c + L σ))`. -/
theorem represents_arclength {K : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (c : ℝ) :
    Represents L K (fun _ => 1) L (fun σ => K (c + L * σ)) := by
  refine ⟨by simp, fun u => (u - c) / L, fun u => ?_, fun u => ?_, fun u => ?_⟩
  · have := ((hasDerivAt_id u).sub_const c).div_const L
    simpa using this
  · field_simp; ring
  · simp only [one_mul]; congr 1; field_simp; ring

section rear

variable {p κ L : ℝ} {a g f : ℝ → ℝ}

/-- **The selected inverse commutes with representation.** -/
theorem represents_rear (hp : 0 < p) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ha : Continuous a)
    (hg : Continuous g) (hap : Function.Periodic a p) (hgp : Function.Periodic g p)
    (hg0 : ∀ u, 0 < g u) (ha0 : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ κ * g u)
    (hR : Represents p a g L f) :
    (∃ s : ℝ → ℝ, steerAngle p a g = rδ L f ∘ s) ∧
      Represents p (fun u => g u * Real.sin (steerAngle p a g u))
        (fun u => g u * Real.cos (steerAngle p a g u)) (rearL L f) (rearF L f) := by
  have hL := hR.L_pos hp hg hg0
  obtain ⟨hint, s, hs, hsp, hsa⟩ := hR
  obtain ⟨G, hG1, hG2, hGc⟩ := Represents.exists_inverse hp hg hgp hg0 hL hs
  have hsc : Continuous s := continuous_iff_continuousAt.2 fun u => (hs u).continuousAt
  -- properties of `f`
  have hfG : ∀ y, f y = a (G y) / g (G y) := fun y => by
    have := hsa (G y)
    rw [hG1] at this
    rw [eq_div_iff (hg0 _).ne', this]; ring
  have hf : f = fun y => a (G y) / g (G y) := funext hfG
  have hfc : Continuous f := by
    rw [hf]; exact (ha.comp hGc).div (hg.comp hGc) fun y => (hg0 _).ne'
  have hfp : Function.Periodic f 1 := fun y => by
    have : y + 1 = s (G y + p) := by rw [hsp, hG1]
    rw [this, hfG, hfG y, hG2, hap, hgp]
  have hf0 : ∀ y, 0 ≤ f y := fun y => by rw [hfG]; exact div_nonneg (ha0 _) (hg0 _).le
  have hfκ : ∀ y, f y ≤ κ := fun y => by
    rw [hfG, div_le_iff₀ (hg0 _)]; exact hab _
  -- the steering angle of `(L, f)`
  obtain ⟨hδp, hδd, hδb⟩ : Function.Periodic (rδ L f) 1 ∧
      (∀ σ, HasDerivAt (rδ L f) (L * f σ - L * Real.sin (rδ L f σ)) σ) ∧
      ∀ σ, rδ L f σ ∈ Set.Icc 0 (Real.arcsin κ) :=
    steerAngle_spec (p := 1) (κ := κ) (a := fun σ => L * f σ)
    (b := fun _ => L) one_pos hκ0 hκ1 (continuous_const.mul hfc) continuous_const
    (fun σ => by simp only [hfp σ]) (fun _ => rfl) (fun _ => hL)
    (fun σ => mul_nonneg hL.le (hf0 σ)) (fun σ => by nlinarith [hfκ σ])
  set dt := rδ L f with hdt
  have hdtc : Continuous dt := continuous_iff_continuousAt.2 fun σ => (hδd σ).continuousAt
  have hA := arcsin_lt_pi_div_two hκ1
  have hcos : ∀ σ, 0 < Real.cos (dt σ) := fun σ => Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(hδb σ).1, Real.pi_pos], (hδb σ).2.trans_lt hA⟩
  -- the steering angle of the data is `dt ∘ s`
  have hcomp : ∀ u, HasDerivAt (dt ∘ s) (a u - g u * Real.sin ((dt ∘ s) u)) u := fun u => by
    have := (hδd (s u)).comp u (hs u)
    convert this using 1
    rw [hsa u]; simp only [Function.comp]; field_simp
  have heq : steerAngle p a g = dt ∘ s :=
    steerAngle_eq hp hκ0 hκ1 ha hg hap hgp hg0 ha0 hab hA
      (fun u => by simp only [Function.comp, hsp u, hδp (s u)]) hcomp
      (fun u => hδb (s u))
  refine ⟨⟨s, heq⟩, ?_⟩
  rw [heq]
  -- the rear half-perimeter
  have hcL : Continuous fun σ => L * Real.cos (dt σ) :=
    continuous_const.mul (Real.continuous_cos.comp hdtc)
  have hcLp : Function.Periodic (fun σ => L * Real.cos (dt σ)) 1 := fun σ => by
    simp only [hδp σ]
  have hcL0 : ∀ σ, 0 < L * Real.cos (dt σ) := fun σ => mul_pos hL (hcos σ)
  have hint' : ∫ u in (0 : ℝ)..p, g u * Real.cos ((dt ∘ s) u) = rearL L f := by
    have e : (fun u => g u * Real.cos ((dt ∘ s) u)) =
        fun u => ((fun σ => L * Real.cos (dt σ)) ∘ s) u * (g u / L) := by
      funext u; simp only [Function.comp]; field_simp
    rw [e, intervalIntegral.integral_comp_mul_deriv (fun u _ => hs u)
      ((hg.div_const L).continuousOn) hcL, show s p = s 0 + 1 by simpa using hsp 0, hcLp.intervalIntegral_add_eq (s 0) 0,
      zero_add]
    rfl
  -- the rear normalized arclength
  have hRpos : 0 < rearL L f := integral_pos_of_periodic one_pos hcL hcL0
  refine ⟨hint', normArc 1 (fun σ => L * Real.cos (dt σ)) ∘ s, fun u => ?_, fun u => ?_,
    fun u => ?_⟩
  · have := (hasDerivAt_normArc (p := 1) hcL (s u)).comp u (hs u)
    convert this using 1
    simp only [Function.comp, rearL]
    rw [← hdt]
    field_simp
  · simp only [Function.comp, hsp u]
    exact normArc_add_period one_pos hcL hcLp hcL0 _
  · simp only [rearF, normF, Function.comp, ← hdt, invFun_normArc one_pos hcL hcL0]
    field_simp [(hcos (s u)).ne', hL.ne']

end rear

end Ovals

end
