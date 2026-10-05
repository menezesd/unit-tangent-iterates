module

public import UnitTangentIterates.Resolvent

/-!
# The steering equation and the selected inverse (Lemma 2.1, analytic part)

Let `F` be a convex closed front of length `L` with curvature `0 ≤ K ≤ κ < 1`
(as a function of front arclength `s`).  The steering angle `δ` between the front
and rear tangents satisfies `δ' = K - sin δ`.  We prove:

* there is a unique `L`-periodic solution with values in `[0, π/2)`
  (`Ovals.steering_existsUnique`); it takes values in `[0, arcsin κ]`;
* if `∫₀ᴸ K > 0` (e.g. `= 2π`), this solution is strictly positive and
  `tan δ ≤ κ / √(1 - κ²)`, which is the rear curvature bound (2.3)
  (`Ovals.steering_pos`, `Ovals.tan_steering_le`).

Existence is proved by writing the periodic problem as the fixed point equation
`δ = ℛ_L (K + δ - sin δ)` and applying the Banach fixed point theorem: on
`[0, arcsin κ]` the map `δ ↦ δ - sin δ` has Lipschitz constant `1 - √(1-κ²) < 1`,
and `ℛ_L` is a sup-norm contraction of norm one preserving bounds.
-/

@[expose] public section

namespace Ovals

open Real BoundedContinuousFunction

section TrigEstimates

variable {a : ℝ}

/-- For `0 ≤ v ≤ u ≤ a < π/2`: `cos a · (u - v) ≤ sin u - sin v`. -/
theorem cos_mul_sub_le_sin_sub_sin (ha : a < π / 2) {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u)
    (hu : u ≤ a) : Real.cos a * (u - v) ≤ Real.sin u - Real.sin v := by
  have hmono : MonotoneOn (fun t => Real.sin t - t * Real.cos a) (Set.Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a)
    · exact (Real.continuous_sin.sub (continuous_id.mul continuous_const)).continuousOn
    · exact (Real.differentiable_sin.sub (differentiable_id.mul
        (differentiable_const _))).differentiableOn
    · intro t ht
      rw [interior_Icc] at ht
      have hd : HasDerivAt (fun t => Real.sin t - t * Real.cos a)
          (Real.cos t - 1 * Real.cos a) t :=
        (Real.hasDerivAt_sin t).sub ((hasDerivAt_id t).mul_const _)
      rw [hd.deriv, one_mul, sub_nonneg]
      exact Real.cos_le_cos_of_nonneg_of_le_pi ht.1.le (by linarith [Real.pi_pos]) ht.2.le
  have := hmono ⟨hv, hvu.trans hu⟩ ⟨hv.trans hvu, hu⟩ hvu
  simp only at this
  linarith

/-- On `[0, a]` with `a < π/2`, `t ↦ t - sin t` is `(1 - cos a)`-Lipschitz. -/
theorem abs_sub_sin_sub_le (ha : a < π / 2) {u v : ℝ} (hu : u ∈ Set.Icc 0 a)
    (hv : v ∈ Set.Icc 0 a) :
    |(u - Real.sin u) - (v - Real.sin v)| ≤ (1 - Real.cos a) * |u - v| := by
  rcases le_total v u with h | h
  · have h1 := cos_mul_sub_le_sin_sub_sin ha hv.1 h hu.2
    have h2 : Real.sin u - Real.sin v ≤ u - v := by
      have := Real.abs_sin_sub_sin_le u v
      rw [abs_of_nonneg (show 0 ≤ u - v by linarith)] at this
      exact (le_abs_self _).trans this
    rw [abs_of_nonneg (by linarith : 0 ≤ u - v), abs_of_nonneg (by linarith)]
    nlinarith
  · have h1 := cos_mul_sub_le_sin_sub_sin ha hu.1 h hv.2
    have h2 : Real.sin v - Real.sin u ≤ v - u := by
      have := Real.abs_sin_sub_sin_le v u
      rw [abs_of_nonneg (show 0 ≤ v - u by linarith)] at this
      exact (le_abs_self _).trans this
    rw [abs_of_nonpos (by linarith : u - v ≤ 0), abs_of_nonpos (by linarith)]
    nlinarith

end TrigEstimates

variable {L κ : ℝ} {K : ℝ → ℝ}

/-- The steering map `δ ↦ K + δ - sin δ` keeps values in `[0, arcsin κ]`. -/
theorem steering_rhs_mem (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hK0 : ∀ s, 0 ≤ K s)
    (hK1 : ∀ s, K s ≤ κ) {d : ℝ} (hd : d ∈ Set.Icc 0 (Real.arcsin κ)) (s : ℝ) :
    K s + d - Real.sin d ∈ Set.Icc 0 (Real.arcsin κ) := by
  have hsin : Real.sin (Real.arcsin κ) = κ := Real.sin_arcsin (by linarith) hκ1.le
  have h1 : Real.sin d ≤ d := Real.sin_le hd.1
  have h2 : Real.sin (Real.arcsin κ) - Real.sin d ≤ Real.arcsin κ - d := by
    have := Real.abs_sin_sub_sin_le (Real.arcsin κ) d
    rw [abs_of_nonneg (show 0 ≤ Real.arcsin κ - d by linarith [hd.2])] at this
    exact (le_abs_self _).trans this
  constructor
  · linarith [hK0 s]
  · linarith [hK1 s]

theorem arcsin_lt_pi_div_two (hκ1 : κ < 1) : Real.arcsin κ < π / 2 := by
  have := Real.arcsin_lt_pi_div_two.2 hκ1
  exact this

/-- **Existence** of a periodic steering angle with values in `[0, arcsin κ]`. -/
theorem steering_exists (hL : 0 < L) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hK : Continuous K)
    (hKp : Function.Periodic K L) (hK0 : ∀ s, 0 ≤ K s) (hK1 : ∀ s, K s ≤ κ) :
    ∃ δ : ℝ → ℝ, Function.Periodic δ L ∧ (∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) ∧
      ∀ s, δ s ∈ Set.Icc 0 (Real.arcsin κ) := by
  set a := Real.arcsin κ with ha_def
  have ha2 : a < π / 2 := arcsin_lt_pi_div_two hκ1
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.2 hκ0
  have hcos : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha2⟩
  let S : Set (ℝ →ᵇ ℝ) := {f | Function.Periodic f L ∧ ∀ x, f x ∈ Set.Icc 0 a}
  have hS : IsClosed S := by
    have h1 : IsClosed {f : ℝ →ᵇ ℝ | Function.Periodic f L} := by
      have : {f : ℝ →ᵇ ℝ | Function.Periodic f L} = ⋂ x, {f | f (x + L) = f x} := by
        ext f; simp [Function.Periodic]
      rw [this]
      exact isClosed_iInter fun x => isClosed_eq
        (ContinuousEvalConst.continuous_eval_const _)
        (ContinuousEvalConst.continuous_eval_const _)
    have h2 : IsClosed {f : ℝ →ᵇ ℝ | ∀ x, f x ∈ Set.Icc 0 a} := by
      have : {f : ℝ →ᵇ ℝ | ∀ x, f x ∈ Set.Icc 0 a} =
          ⋂ x, (fun f : ℝ →ᵇ ℝ => f x) ⁻¹' Set.Icc 0 a := by ext; simp
      rw [this]
      exact isClosed_iInter fun x =>
        isClosed_Icc.preimage (ContinuousEvalConst.continuous_eval_const x)
    exact h1.inter h2
  haveI : CompleteSpace S := hS.completeSpace_coe
  haveI : Nonempty S := ⟨⟨0, fun x => rfl, fun x => ⟨by simp, by simpa using ha0⟩⟩⟩
  let g : S → ℝ → ℝ := fun δ t => K t + δ.1 t - Real.sin (δ.1 t)
  have hgc : ∀ δ : S, Continuous (g δ) := fun δ =>
    (hK.add δ.1.continuous).sub (Real.continuous_sin.comp δ.1.continuous)
  have hgp : ∀ δ : S, Function.Periodic (g δ) L := fun δ t => by
    simp only [g]; rw [hKp t, δ.2.1 t]
  have hgm : ∀ δ : S, ∀ t, g δ t ∈ Set.Icc 0 a := fun δ t =>
    steering_rhs_mem hκ0 hκ1 hK0 hK1 (δ.2.2 t) t
  have hRm : ∀ δ : S, ∀ x, periodicResolvent L (g δ) x ∈ Set.Icc 0 a := fun δ x =>
    periodicResolvent_mem_Icc hL (hgc δ) (hgm δ) x
  let Φ : S → S := fun δ => ⟨BoundedContinuousFunction.mkOfBound
      ⟨periodicResolvent L (g δ), continuous_periodicResolvent hL (hgc δ) (hgp δ)⟩ a
      (fun x y => by
        simp only [ContinuousMap.coe_mk]
        rw [Real.dist_eq, abs_le]
        have := hRm δ x; have := hRm δ y
        constructor <;> linarith [(hRm δ x).1, (hRm δ x).2, (hRm δ y).1, (hRm δ y).2]),
      fun x => periodicResolvent_periodic (hgp δ) x, hRm δ⟩
  have hΦapp : ∀ δ x, (Φ δ).1 x = periodicResolvent L (g δ) x := fun δ x => rfl
  have hcontr : ContractingWith (Real.toNNReal (1 - Real.cos a)) Φ := by
    constructor
    · rw [Real.toNNReal_lt_one]
      linarith
    · apply LipschitzWith.of_dist_le_mul
      intro δ₁ δ₂
      rw [Subtype.dist_eq, Subtype.dist_eq, Real.coe_toNNReal _ (by linarith [Real.cos_le_one a])]
      apply (BoundedContinuousFunction.dist_le
        (mul_nonneg (by linarith [Real.cos_le_one a]) dist_nonneg)).2
      intro x
      rw [hΦapp, hΦapp, Real.dist_eq]
      apply abs_periodicResolvent_sub_le hL (hgc δ₁) (hgc δ₂)
      intro t
      simp only [g]
      have h1 := abs_sub_sin_sub_le ha2 (δ₁.2.2 t) (δ₂.2.2 t)
      have h2 : |δ₁.1 t - δ₂.1 t| ≤ dist δ₁.1 δ₂.1 := by
        rw [← Real.dist_eq]; exact BoundedContinuousFunction.dist_coe_le_dist t
      calc |K t + δ₁.1 t - Real.sin (δ₁.1 t) - (K t + δ₂.1 t - Real.sin (δ₂.1 t))|
          = |(δ₁.1 t - Real.sin (δ₁.1 t)) - (δ₂.1 t - Real.sin (δ₂.1 t))| := by ring_nf
        _ ≤ (1 - Real.cos a) * |δ₁.1 t - δ₂.1 t| := h1
        _ ≤ (1 - Real.cos a) * dist δ₁.1 δ₂.1 :=
          mul_le_mul_of_nonneg_left h2 (by linarith [Real.cos_le_one a])
  set δ := ContractingWith.fixedPoint Φ hcontr
  have hfix : Φ δ = δ := ContractingWith.fixedPoint_isFixedPt hcontr
  have he : ∀ x, δ.1 x = periodicResolvent L (g δ) x := fun x => by
    rw [← hΦapp δ x, hfix]
  have hfun : (δ.1 : ℝ → ℝ) = periodicResolvent L (g δ) := funext he
  refine ⟨δ.1, δ.2.1, fun s => ?_, δ.2.2⟩
  have hd := hasDerivAt_periodicResolvent hL (hgc δ) (hgp δ) s
  rw [← hfun] at hd
  convert hd using 1
  simp only [g]; ring

/-- A periodic solution with values in `[0, π/2)` automatically lies in `[0, arcsin κ]`
(look at a maximum of `δ`). -/
theorem steering_le_arcsin (hL : 0 < L) (hK1 : ∀ s, K s ≤ κ) {δ : ℝ → ℝ}
    (hδp : Function.Periodic δ L) (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s)
    (hδb : ∀ s, 0 ≤ δ s ∧ δ s < π / 2) (s : ℝ) : δ s ≤ Real.arcsin κ := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun x => (hδ x).continuousAt
  obtain ⟨x0, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hL.le)
    hδc.continuousOn
  have hglob : ∀ y, δ y ≤ δ x0 := by
    intro y
    obtain ⟨y', hy', hyy⟩ := hδp.exists_mem_Ico₀ hL y
    rw [hyy]; exact hmax (Set.Ico_subset_Icc_self hy')
  have hlm : IsLocalMax δ x0 := Filter.Eventually.of_forall hglob
  have hd0 := hlm.hasDerivAt_eq_zero (hδ x0)
  have hsin : Real.sin (δ x0) ≤ κ := by linarith [hK1 x0]
  have : δ x0 ≤ Real.arcsin κ := by
    rw [← Real.arcsin_sin (x := δ x0) (by linarith [hδb x0, Real.pi_pos]) (hδb x0).2.le]
    exact Real.arcsin_le_arcsin hsin
  exact (hglob s).trans this

/-- **Uniqueness** of periodic solutions with values in `[0, arcsin κ]`. -/
theorem steering_unique (hL : 0 < L) (hκ1 : κ < 1) {δ₁ δ₂ : ℝ → ℝ}
    (h₁p : Function.Periodic δ₁ L) (h₁ : ∀ s, HasDerivAt δ₁ (K s - Real.sin (δ₁ s)) s)
    (h₁b : ∀ s, δ₁ s ∈ Set.Icc 0 (Real.arcsin κ))
    (h₂p : Function.Periodic δ₂ L) (h₂ : ∀ s, HasDerivAt δ₂ (K s - Real.sin (δ₂ s)) s)
    (h₂b : ∀ s, δ₂ s ∈ Set.Icc 0 (Real.arcsin κ)) : δ₁ = δ₂ := by
  set a := Real.arcsin κ
  have ha : a < π / 2 := arcsin_lt_pi_div_two hκ1
  have hcos : 0 < Real.cos a :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(h₁b 0).1, (h₁b 0).2, Real.pi_pos], ha⟩
  have key : ∀ s, Real.cos a * (δ₁ s - δ₂ s) ^ 2 ≤
      (δ₁ s - δ₂ s) * (Real.sin (δ₁ s) - Real.sin (δ₂ s)) := by
    intro s
    rcases le_total (δ₂ s) (δ₁ s) with h | h
    · have := cos_mul_sub_le_sin_sub_sin ha (h₂b s).1 h (h₁b s).2
      nlinarith
    · have := cos_mul_sub_le_sin_sub_sin ha (h₁b s).1 h (h₂b s).2
      nlinarith
  set V := fun s => (δ₁ s - δ₂ s) ^ 2 with hV_def
  have hV : ∀ s, HasDerivAt V
      (-(2 * ((δ₁ s - δ₂ s) * (Real.sin (δ₁ s) - Real.sin (δ₂ s))))) s := by
    intro s
    have := ((h₁ s).sub (h₂ s)).pow 2
    convert this using 1
    simp only [Pi.sub_apply]
    push_cast; ring
  have hanti : Antitone V := antitone_of_deriv_nonpos (fun s => (hV s).differentiableAt)
    (fun s => by rw [(hV s).deriv]; nlinarith [key s, hcos, sq_nonneg (δ₁ s - δ₂ s)])
  have hVp : Function.Periodic V L := fun s => by simp only [V]; rw [h₁p s, h₂p s]
  have hle : ∀ x y, x ≤ y → V x = V y := by
    intro x y hxy
    obtain ⟨n, hn⟩ := exists_nat_ge ((y - x) / L)
    have hy : y ≤ x + n * L := by
      rw [div_le_iff₀ hL] at hn; linarith
    have h1 := hanti hxy
    have h2 := hanti hy
    rw [hVp.nat_mul n x] at h2
    linarith
  have hconst : V = fun _ => V 0 := by
    funext s
    rcases le_total 0 s with h | h
    · exact (hle 0 s h).symm
    · exact hle s 0 h
  funext s
  have hd := hV s
  rw [hconst] at hd
  have h0 := (hasDerivAt_const s (V 0)).unique hd
  have hk := key s
  have : (δ₁ s - δ₂ s) ^ 2 = 0 := by
    have : Real.cos a * (δ₁ s - δ₂ s) ^ 2 ≤ 0 := by linarith
    nlinarith [sq_nonneg (δ₁ s - δ₂ s)]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

/-- **Lemma 2.1 (steering equation).**  For an `L`-periodic continuous front curvature
`0 ≤ K ≤ κ < 1`, there is a unique `L`-periodic solution of `δ' = K - sin δ` on the branch
`0 ≤ δ < π/2`; it satisfies `0 ≤ δ ≤ arcsin κ`. -/
theorem steering_existsUnique (hL : 0 < L) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hK : Continuous K)
    (hKp : Function.Periodic K L) (hK0 : ∀ s, 0 ≤ K s) (hK1 : ∀ s, K s ≤ κ) :
    ∃! δ : ℝ → ℝ, Function.Periodic δ L ∧ (∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) ∧
      ∀ s, 0 ≤ δ s ∧ δ s < π / 2 := by
  obtain ⟨δ, hp, hd, hb⟩ := steering_exists hL hκ0 hκ1 hK hKp hK0 hK1
  refine ⟨δ, ⟨hp, hd, fun s => ⟨(hb s).1, (hb s).2.trans_lt (arcsin_lt_pi_div_two hκ1)⟩⟩, ?_⟩
  rintro δ' ⟨hp', hd', hb'⟩
  refine steering_unique hL hκ1 hp' hd' (fun s => ⟨(hb' s).1, ?_⟩) hp hd hb
  exact steering_le_arcsin hL hK1 hp' hd' hb' s

/-- The selected steering angle is strictly positive when the front has positive total
curvature (for a closed convex front, `∫₀ᴸ K = 2π`). -/
theorem steering_pos (hL : 0 < L) (hK : Continuous K)
    (hKp : Function.Periodic K L) (hK0 : ∀ s, 0 ≤ K s) (hKint : 0 < ∫ s in (0:ℝ)..L, K s)
    {δ : ℝ → ℝ} (hδp : Function.Periodic δ L) (hδ : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s)
    (hδ0 : ∀ s, 0 ≤ δ s) (s : ℝ) : 0 < δ s := by
  have hδc : Continuous δ := continuous_iff_continuousAt.2 fun x => (hδ x).continuousAt
  set g := fun t => K t + δ t - Real.sin (δ t) with hg
  have hgc : Continuous g := (hK.add hδc).sub (Real.continuous_sin.comp hδc)
  have hgp : Function.Periodic g L := fun t => by simp only [g]; rw [hKp t, hδp t]
  have heq : δ = periodicResolvent L g :=
    eq_periodicResolvent_of_hasDerivAt hL hgc hgp hδp (fun x => by
      convert hδ x using 1; simp only [g]; ring)
  have hmono := periodicResolvent_mono hL hK hgc (fun t => by
    simp only [g]; linarith [Real.sin_le (hδ0 t)]) s
  have hlow := periodicResolvent_ge hL hK hKp hK0 s
  have hpos : 0 < (1 - Real.exp (-L))⁻¹ * (Real.exp (-L) * ∫ t in (0:ℝ)..L, K t) := by
    have := one_sub_exp_neg_pos hL; positivity
  rw [heq]; linarith

/-- The rear curvature bound (2.3): `k = tan δ ≤ κ / √(1 - κ²)`. -/
theorem tan_steering_le (hκ1 : κ < 1) {d : ℝ} (hd : d ∈ Set.Icc 0 (Real.arcsin κ)) :
    Real.tan d ≤ κ / √(1 - κ ^ 2) := by
  rw [← Real.tan_arcsin]
  have hpi := Real.pi_pos
  have h2 := Real.arcsin_lt_pi_div_two.2 hκ1
  exact Real.strictMonoOn_tan.monotoneOn ⟨by linarith [hd.1], by linarith [hd.2]⟩
    ⟨by linarith [hd.1, hd.2], h2⟩ hd.2

end Ovals

end
