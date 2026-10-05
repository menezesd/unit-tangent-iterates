module

public import UnitTangentIterates.WeightedSteering

/-!
# Differentiable dependence of the selected rear on a parameter

Lemma 6.2 applies the selected inverse to a *path* of fronts, and needs the rears to form a
differentiable path.  For the steering equation this means: if the data `a(t, ·), b(t, ·)` of
`δ' = a - b sin δ` depend differentiably on `t` (uniformly in the curve parameter `u`), then so
does the selected periodic solution `δ(t, ·)`, and its `t`-derivative `D` is the periodic
solution of the linearized equation

`D' = da - db sin δ - b cos δ · D`.

The proof uses only the maximum principle:

* `Ovals.linear_periodic_abs_le`: a periodic solution of `w' = R - β w` with `β ≥ μ > 0`
  satisfies `|w| ≤ sup |R| / μ`;
* `Ovals.linear_periodic_exists`: such a periodic solution exists (explicit formula);
* `Ovals.steering_hasDerivAt_param`: the remainder `δ(t) - δ(t₀) - (t - t₀) D` solves a linear
  equation of this form with a right side that is `o(t - t₀)` uniformly in `u`.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- **Maximum principle for linear periodic equations.**  If `w` is `p`-periodic with
`w' = R - β w`, `β ≥ μ > 0` and `|R| ≤ ρ`, then `|w| ≤ ρ / μ`. -/
theorem linear_periodic_abs_le {w R β : ℝ → ℝ} {p μ ρ : ℝ} (hp : 0 < p) (hμ : 0 < μ)
    (hw : ∀ u, HasDerivAt w (R u - β u * w u) u) (hwp : Function.Periodic w p)
    (hβ : ∀ u, μ ≤ β u) (hR : ∀ u, |R u| ≤ ρ) (u : ℝ) : |w u| ≤ ρ / μ := by
  have one_side : ∀ {w R : ℝ → ℝ}, (∀ u, HasDerivAt w (R u - β u * w u) u) →
      Function.Periodic w p → (∀ u, |R u| ≤ ρ) → ∀ u, w u ≤ ρ / μ := by
    intro w R hw hwp hR u
    have hc : Continuous w := continuous_iff_continuousAt.2 fun x => (hw x).continuousAt
    obtain ⟨u₀, hu₀⟩ := exists_max_of_periodic hp hc (fun u => by simp only [hwp u])
    have h0 := IsLocalMax.hasDerivAt_eq_zero (Filter.Eventually.of_forall hu₀) (hw u₀)
    have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hR u₀)
    refine (hu₀ u).trans ?_
    rcases le_or_gt (w u₀) 0 with h | h
    · exact h.trans (div_nonneg hρ hμ.le)
    · rw [le_div_iff₀ hμ]
      have : β u₀ * w u₀ = R u₀ := by linarith
      have h1 := mul_le_mul_of_nonneg_right (hβ u₀) h.le
      have h2 := (le_abs_self _).trans (hR u₀)
      nlinarith
  rw [abs_le]
  refine ⟨?_, one_side hw hwp hR u⟩
  have := one_side (w := fun u => -w u) (R := fun u => -R u)
    (fun u => by have := (hw u).neg; convert this using 1; ring)
    (fun u => by simp only [hwp u]) (fun u => by rw [abs_neg]; exact hR u) u
  linarith

/-- **Existence of periodic solutions** of `D' = f - β D` for continuous `p`-periodic `f, β`
with `β > 0`. -/
theorem linear_periodic_exists {f β : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hf : Continuous f)
    (hβ : Continuous β) (hfp : Function.Periodic f p) (hβp : Function.Periodic β p)
    (hβ0 : ∀ u, 0 < β u) :
    ∃ D : ℝ → ℝ, Function.Periodic D p ∧ ∀ u, HasDerivAt D (f u - β u * D u) u := by
  set B : ℝ → ℝ := fun u => ∫ r in (0 : ℝ)..u, β r
  have hB : ∀ u, HasDerivAt B (β u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hβ.intervalIntegrable _ _)
      (hβ.stronglyMeasurableAtFilter _ _) hβ.continuousAt
  have hBc : Continuous B := continuous_iff_continuousAt.2 fun u => (hB u).continuousAt
  have hBper : ∀ u, B (u + p) = B u + B p := fun u => by
    simp only [B]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := u)
      (hβ.intervalIntegrable _ _) (hβ.intervalIntegrable _ _),
      hβp.intervalIntegral_add_eq u 0, zero_add]
  have hBp : 0 < B p := intervalIntegral.intervalIntegral_pos_of_pos
    (hβ.intervalIntegrable _ _) hβ0 hp
  set E : ℝ → ℝ := fun u => Real.exp (B u)
  have hE : ∀ u, HasDerivAt E (E u * β u) u := fun u => (hB u).exp
  have hEc : Continuous E := Real.continuous_exp.comp hBc
  have hEper : ∀ u, E (u + p) = E u * E p := fun u => by
    simp only [E, hBper, Real.exp_add]
  set I : ℝ → ℝ := fun u => ∫ r in (0 : ℝ)..u, E r * f r
  have hEf : Continuous fun r => E r * f r := hEc.mul hf
  have hI : ∀ u, HasDerivAt I (E u * f u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hEf.intervalIntegrable _ _)
      (hEf.stronglyMeasurableAtFilter _ _) hEf.continuousAt
  have hIper : ∀ u, I (u + p) = I p + E p * I u := fun u => by
    simp only [I]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := p)
      (hEf.intervalIntegrable _ _) (hEf.intervalIntegrable _ _)]
    congr 1
    have := intervalIntegral.integral_comp_add_right (fun r => E r * f r) (a := 0) (b := u) p
    rw [zero_add] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
    congr 1; funext r
    rw [hEper, hfp]; ring
  have hEp1 : 1 < E p := Real.one_lt_exp_iff.2 hBp
  set C := I p / (E p - 1)
  have hEpos : ∀ u, 0 < E u := fun u => Real.exp_pos _
  refine ⟨fun u => (C + I u) / E u, fun u => ?_, fun u => ?_⟩
  · simp only
    rw [hIper, hEper]
    have h1 : E p - 1 ≠ 0 := by linarith
    have h2 := (hEpos u).ne'
    have h3 := (hEpos p).ne'
    field_simp
    simp only [C]
    field_simp
    ring
  · have := ((hasDerivAt_const u C).add (hI u)).div (hE u) (hEpos u).ne'
    convert this using 1
    simp only [Pi.add_apply]
    have := (hEpos u).ne'
    field_simp
    ring

/-- `|sin x - sin y - cos y (x - y)| ≤ (x - y)²`. -/
lemma abs_sin_sub_sin_sub_cos_mul_le (x y : ℝ) :
    |Real.sin x - Real.sin y - Real.cos y * (x - y)| ≤ (x - y) ^ 2 := by
  set g : ℝ → ℝ := fun z => Real.sin z - Real.cos y * z
  have hg : ∀ z, HasDerivAt g (Real.cos z - Real.cos y) z := fun z => by
    have := (Real.hasDerivAt_sin z).sub ((hasDerivAt_id z).const_mul (Real.cos y))
    simpa using this
  have hbound : ∀ z ∈ Set.uIcc y x, ‖Real.cos z - Real.cos y‖ ≤ |x - y| := fun z hz => by
    rw [Real.norm_eq_abs]
    refine (Real.abs_cos_sub_cos_le z y).trans ?_
    rw [Set.mem_uIcc] at hz
    rcases hz with hz | hz
    · rw [abs_of_nonneg (by linarith [hz.1]), abs_of_nonneg (by linarith [hz.1, hz.2])]
      linarith [hz.2]
    · rw [abs_of_nonpos (by linarith [hz.2]), abs_of_nonpos (by linarith [hz.1, hz.2])]
      linarith [hz.1]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hg z).hasDerivWithinAt) hbound (convex_uIcc y x) Set.right_mem_uIcc
    Set.left_mem_uIcc
  simp only [g, Real.norm_eq_abs] at this
  rw [abs_sub_comm y x] at this
  have e : Real.sin x - Real.sin y - Real.cos y * (x - y) =
      -(Real.sin y - Real.cos y * y - (Real.sin x - Real.cos y * x)) := by ring
  rw [e, abs_neg, sq, ← abs_mul_self (x - y), abs_mul]
  exact this

/-- **Differentiable dependence of the selected steering angle on a parameter.**  Let
`δ(t, ·)` be the `p`-periodic solutions of `δ' = a(t) - b(t) sin δ` with values in `[0, A]`,
`A < π/2`, and `b ≥ m > 0`.  Suppose that at `t₀` the data are differentiable in `t`
uniformly in `u`, with bounded derivatives `da, db`, and let `D` be a periodic solution of the
linearized equation `D' = da - db sin δ - b cos δ · D` at `t₀`.  Then `δ(t, u)` is
differentiable in `t` at `t₀`, uniformly in `u`, with derivative `D(u)`. -/
theorem steering_param_deriv {a b δ : ℝ → ℝ → ℝ} {da db D : ℝ → ℝ} {t₀ p A m M M' : ℝ}
    (hp : 0 < p) (hA : A < π / 2) (hm : 0 < m)
    (hδ : ∀ t u, HasDerivAt (δ t) (a t u - b t u * Real.sin (δ t u)) u)
    (hδp : ∀ t, Function.Periodic (δ t) p) (hδb : ∀ t u, δ t u ∈ Set.Icc 0 A)
    (hb : ∀ t u, m ≤ b t u) (hbM : ∀ u, b t₀ u ≤ M) (hda : ∀ u, |da u| ≤ M')
    (hdb : ∀ u, |db u| ≤ M')
    (ha_diff : ∀ ε > 0, ∀ᶠ t in 𝓝 t₀, ∀ u, |a t u - a t₀ u - (t - t₀) * da u| ≤ ε * |t - t₀|)
    (hb_diff : ∀ ε > 0, ∀ᶠ t in 𝓝 t₀, ∀ u, |b t u - b t₀ u - (t - t₀) * db u| ≤ ε * |t - t₀|)
    (hD : ∀ u, HasDerivAt D (da u - db u * Real.sin (δ t₀ u) -
      b t₀ u * Real.cos (δ t₀ u) * D u) u)
    (hDp : Function.Periodic D p) :
    ∀ ε > 0, ∀ᶠ t in 𝓝 t₀, ∀ u, |δ t u - δ t₀ u - (t - t₀) * D u| ≤ ε * |t - t₀| := by
  intro ε hε
  have hcosA : 0 < Real.cos A := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(hδb t₀ 0).1, (hδb t₀ 0).2, Real.pi_pos], hA⟩
  set μ := m * Real.cos A
  have hμ : 0 < μ := mul_pos hm hcosA
  have hM'0 : 0 ≤ M' := (abs_nonneg _).trans (hda 0)
  have hM0 : 0 ≤ M := hm.le.trans ((hb t₀ 0).trans (hbM 0))
  -- Lipschitz dependence: `|δ t - δ t₀| ≤ Λ |t - t₀|`
  set Λ := 2 * (M' + 1) / μ
  have hΛ : 0 ≤ Λ := by positivity
  have hlip : ∀ᶠ t in 𝓝 t₀, ∀ u, |δ t u - δ t₀ u| ≤ Λ * |t - t₀| := by
    filter_upwards [ha_diff 1 one_pos, hb_diff 1 one_pos] with t hat hbt u
    have hα : ∀ u, |a t u - a t₀ u| ≤ (M' + 1) * |t - t₀| := fun u => by
      have h1 := hat u
      have h2 : |(t - t₀) * da u| ≤ M' * |t - t₀| := by
        rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hda u) (abs_nonneg _)
      calc |a t u - a t₀ u| = |(a t u - a t₀ u - (t - t₀) * da u) + (t - t₀) * da u| := by ring_nf
        _ ≤ |a t u - a t₀ u - (t - t₀) * da u| + |(t - t₀) * da u| := abs_add_le _ _
        _ ≤ 1 * |t - t₀| + M' * |t - t₀| := add_le_add h1 h2
        _ = (M' + 1) * |t - t₀| := by ring
    have hβ : ∀ u, |b t u - b t₀ u| ≤ (M' + 1) * |t - t₀| := fun u => by
      have h1 := hbt u
      have h2 : |(t - t₀) * db u| ≤ M' * |t - t₀| := by
        rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hdb u) (abs_nonneg _)
      calc |b t u - b t₀ u| = |(b t u - b t₀ u - (t - t₀) * db u) + (t - t₀) * db u| := by ring_nf
        _ ≤ |b t u - b t₀ u - (t - t₀) * db u| + |(t - t₀) * db u| := abs_add_le _ _
        _ ≤ 1 * |t - t₀| + M' * |t - t₀| := add_le_add h1 h2
        _ = (M' + 1) * |t - t₀| := by ring
    have := weightedSteering_diff_le hp hA hm (hδ t) (hδ t₀) (hδp t) (hδp t₀) (hδb t)
      (hδb t₀) (hb t) (hb t₀) hα hβ u
    calc |δ t u - δ t₀ u| ≤ _ := this
      _ = Λ * |t - t₀| := by simp only [Λ, μ]; ring
  -- choose the size of the neighbourhood
  set c := M' * Λ + M * Λ ^ 2
  have hc : 0 ≤ c := by positivity
  set ε₁ := ε * μ / 4
  have hε₁ : 0 < ε₁ := by positivity
  have hsmall : ∀ᶠ t in 𝓝 t₀, c * |t - t₀| ≤ ε * μ / 2 := by
    have : Tendsto (fun t => c * |t - t₀|) (𝓝 t₀) (𝓝 (c * |t₀ - t₀|)) :=
      (continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).tendsto t₀
    simp only [sub_self, abs_zero, mul_zero] at this
    exact this.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hlip, ha_diff ε₁ hε₁, hb_diff ε₁ hε₁, hsmall] with t hlipt hat hbt hst
  set h := t - t₀
  -- the remainder solves a linear equation
  set w : ℝ → ℝ := fun u => δ t u - δ t₀ u - h * D u
  set β : ℝ → ℝ := fun u => b t₀ u * Real.cos (δ t₀ u)
  set R : ℝ → ℝ := fun u => (a t u - a t₀ u - h * da u)
      - ((b t u - b t₀ u - h * db u) * Real.sin (δ t u)
        + h * db u * (Real.sin (δ t u) - Real.sin (δ t₀ u)))
      - b t₀ u * (Real.sin (δ t u) - Real.sin (δ t₀ u)
        - Real.cos (δ t₀ u) * (δ t u - δ t₀ u))
  have hw : ∀ u, HasDerivAt w (R u - β u * w u) u := fun u => by
    have := ((hδ t u).sub (hδ t₀ u)).sub ((hD u).const_mul h)
    convert this using 1
    simp only [R, β, w]; ring
  have hwp : Function.Periodic w p := fun u => by simp only [w, hδp t u, hδp t₀ u, hDp u]
  have hβ : ∀ u, μ ≤ β u := fun u => by
    have hcos : Real.cos A ≤ Real.cos (δ t₀ u) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (hδb t₀ u).1 (by linarith [Real.pi_pos])
        (hδb t₀ u).2
    exact mul_le_mul (hb t₀ u) hcos hcosA.le (hm.le.trans (hb t₀ u))
  have hR : ∀ u, |R u| ≤ (2 * ε₁ + c * |h|) * |h| := fun u => by
    have hd := hlipt u
    have h1 := hat u
    have h2 : |(b t u - b t₀ u - h * db u) * Real.sin (δ t u)| ≤ ε₁ * |h| := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans (hbt u)
    have h3 : |h * db u * (Real.sin (δ t u) - Real.sin (δ t₀ u))| ≤ M' * Λ * |h| ^ 2 := by
      rw [abs_mul, abs_mul]
      have hs := (Real.abs_sin_sub_sin_le (δ t u) (δ t₀ u)).trans hd
      calc |h| * |db u| * |Real.sin (δ t u) - Real.sin (δ t₀ u)|
          ≤ |h| * M' * (Λ * |h|) := by gcongr; exact hdb u
        _ = M' * Λ * |h| ^ 2 := by ring
    have h4 : |b t₀ u * (Real.sin (δ t u) - Real.sin (δ t₀ u)
        - Real.cos (δ t₀ u) * (δ t u - δ t₀ u))| ≤ M * Λ ^ 2 * |h| ^ 2 := by
      rw [abs_mul]
      have hs := abs_sin_sub_sin_sub_cos_mul_le (δ t u) (δ t₀ u)
      have hsq : (δ t u - δ t₀ u) ^ 2 ≤ (Λ * |h|) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      have hb0 : |b t₀ u| ≤ M := by
        rw [abs_of_pos (hm.trans_le (hb t₀ u))]; exact hbM u
      calc |b t₀ u| * |Real.sin (δ t u) - Real.sin (δ t₀ u)
            - Real.cos (δ t₀ u) * (δ t u - δ t₀ u)|
          ≤ M * (Λ * |h|) ^ 2 := mul_le_mul hb0 (hs.trans hsq) (abs_nonneg _) hM0
        _ = M * Λ ^ 2 * |h| ^ 2 := by ring
    calc |R u| ≤ |a t u - a t₀ u - h * da u|
          + (|(b t u - b t₀ u - h * db u) * Real.sin (δ t u)|
            + |h * db u * (Real.sin (δ t u) - Real.sin (δ t₀ u))|)
          + |b t₀ u * (Real.sin (δ t u) - Real.sin (δ t₀ u)
            - Real.cos (δ t₀ u) * (δ t u - δ t₀ u))| := by
          simp only [R]
          refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
            (add_le_add le_rfl (abs_add_le _ _))) le_rfl)
      _ ≤ ε₁ * |h| + (ε₁ * |h| + M' * Λ * |h| ^ 2) + M * Λ ^ 2 * |h| ^ 2 := by
          gcongr
      _ = (2 * ε₁ + c * |h|) * |h| := by simp only [c]; ring
  intro u
  have := linear_periodic_abs_le hp hμ hw hwp hβ hR u
  calc |δ t u - δ t₀ u - (t - t₀) * D u| = |w u| := rfl
    _ ≤ (2 * ε₁ + c * |h|) * |h| / μ := this
    _ ≤ ε * |h| := by
      rw [div_le_iff₀ hμ]
      have : (2 * ε₁ + c * |h|) ≤ ε * μ := by simp only [ε₁]; linarith
      nlinarith [abs_nonneg h]

end Ovals

end
