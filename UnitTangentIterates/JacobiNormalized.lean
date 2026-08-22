import Mathlib
import UnitTangentIterates.MarkedTopology
import UnitTangentIterates.JacobiAssembly

/-!
# The inverse Jacobi estimates in the normalized parameter

The estimates of `UnitTangentIterates/JacobiAssembly.lean` are stated in the
arclength parameter of the front and of the rear: the `L¹` norms are integrals
over one period of arclength and the derivatives are arclength derivatives.
The path functionals of `MarkedTopology.lean` and the normal paths of
`PathMetric.lean` use instead the *normalized* parameter `u ∈ [0,1]`, in which
one period of a curve of perimeter `L` is `u ↦ L u`.

This file performs the change of normalization.  With

```
  η_R^n(u) = η_R(ℓ u),      η_F^n(u) = η_F(P u)
```

the `L¹` density picks up the factor `1/ℓ` resp. `1/P` and the `j`-th
derivative picks up the factor `ℓ^j` resp. `P^j`, so the four estimates become

```
  W(η_R^n) ≤ (P/ℓ) W(η_F^n),
  S₀(η_R^n) ≤ (P/(1 - e^{-ℓ₀})) W(η_F^n),
  S₁(η_R^n) ≤ C₁ (W + S₀)(η_F^n),
  S₂(η_R^n) ≤ C₂ (W + S₀ + S₁)(η_F^n)
```

with the explicit constants `constW`, `const0`, `const1`, `const2` below.  This
is exactly the shape of the hypotheses of
`PathMetricJacobi.exists_normalPath_of_jacobi`, whose `L¹` estimate is allowed
a constant precisely because of the ratio of the two periods appearing here.

Main results:

* `supNorm_comp_mul`, `integral_abs_comp_mul`, `deriv_comp_mul`,
  `iteratedDeriv_two_comp_mul` — the scaling rules;
* `jacobi_estimates_normalized` — the four estimates in the normalized
  parameter.
-/

noncomputable section

open MeasureTheory intervalIntegral MarkedTopology

namespace JacobiNormalized

/-! ### Scaling rules -/

/-- The sup norm is invariant under rescaling of the parameter. -/
theorem supNorm_comp_mul {L : ℝ} (hL : L ≠ 0) (f : ℝ → ℝ) :
    supNorm (fun u => f (L * u)) = supNorm f := by
  unfold supNorm
  have hsurj : Function.Surjective (fun u : ℝ => L * u) := fun y => ⟨y / L, by field_simp⟩
  exact hsurj.iSup_comp (fun x => |f x|)

/-- The `L¹` density in the normalized parameter is the arclength `L¹` norm
divided by the period. -/
theorem integral_abs_comp_mul {L : ℝ} (hL : L ≠ 0) (f : ℝ → ℝ) :
    (∫ u in (0:ℝ)..1, |f (L * u)|) = L⁻¹ * ∫ x in (0:ℝ)..L, |f x| := by
  simpa using intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1) (fun x => |f x|) hL

/-- The first derivative in the normalized parameter. -/
theorem deriv_comp_mul {L : ℝ} {f f1 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x) :
    deriv (fun u => f (L * u)) = fun u => L * f1 (L * u) := by
  funext u
  have hg : HasDerivAt (fun u : ℝ => L * u) L u := by simpa using (hasDerivAt_id u).const_mul L
  have h : HasDerivAt (fun u : ℝ => f (L * u)) (f1 (L * u) * L) u := (hf (L * u)).comp u hg
  rw [h.deriv]; ring

/-- The first derivative in the normalized parameter, as an iterated
derivative. -/
theorem iteratedDeriv_one_comp_mul {L : ℝ} {f f1 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x) :
    iteratedDeriv 1 (fun u => f (L * u)) = fun u => L * f1 (L * u) := by
  rw [iteratedDeriv_one]
  exact deriv_comp_mul hf

/-- The second derivative in the normalized parameter. -/
theorem iteratedDeriv_two_comp_mul {L : ℝ} {f f1 f2 : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f1 x) x) (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) :
    iteratedDeriv 2 (fun u => f (L * u)) = fun u => L ^ 2 * f2 (L * u) := by
  have h1 : iteratedDeriv 2 (fun u => f (L * u))
      = deriv (iteratedDeriv 1 fun u => f (L * u)) := by
    rw [iteratedDeriv_succ]
  rw [h1, iteratedDeriv_one_comp_mul hf]
  funext u
  have hg : HasDerivAt (fun u : ℝ => L * u) L u := by simpa using (hasDerivAt_id u).const_mul L
  have h : HasDerivAt (fun u : ℝ => L * f1 (L * u)) (L * (f2 (L * u) * L)) u :=
    ((hf1 (L * u)).comp u hg).const_mul L
  rw [h.deriv]; ring

/-! ### The constants -/

/-- The `L¹` constant `P/ℓ`: the ratio of the front and rear perimeters. -/
def constW (P l : ℝ) : ℝ := P / l

/-- The `L¹ → L^∞` constant `P/(1 - e^{-ℓ₀})`. -/
def const0 (P l0 : ℝ) : ℝ := P / (1 - Real.exp (-l0))

/-- The first-order constant. -/
def const1 (P l l0 c : ℝ) : ℝ := l / c + l * P / (1 - Real.exp (-l0))

/-- The second-order constant. -/
def const2 (P l l0 c kh : ℝ) : ℝ :=
  l ^ 2 / (P * c ^ 2) + l ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c) + l ^ 2 * P / (1 - Real.exp (-l0))

theorem one_sub_exp_pos {l0 : ℝ} (hl0 : 0 < l0) : 0 < 1 - Real.exp (-l0) := by
  have : Real.exp (-l0) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

theorem constW_nonneg {P l : ℝ} (hP : 0 < P) (hl : 0 < l) : 0 ≤ constW P l := by
  unfold constW; positivity

theorem const0_nonneg {P l0 : ℝ} (hP : 0 < P) (hl0 : 0 < l0) : 0 ≤ const0 P l0 := by
  have := one_sub_exp_pos hl0
  unfold const0; positivity

theorem const1_nonneg {P l l0 c : ℝ} (hP : 0 < P) (hl : 0 < l) (hl0 : 0 < l0) (hc : 0 < c) :
    0 ≤ const1 P l l0 c := by
  have := one_sub_exp_pos hl0
  unfold const1; positivity

theorem const2_nonneg {P l l0 c kh : ℝ} (hP : 0 < P) (hl : 0 < l) (hl0 : 0 < l0) (hc : 0 < c) :
    0 ≤ const2 P l l0 c kh := by
  have := one_sub_exp_pos hl0
  unfold const2; positivity

/-! ### The estimates in the normalized parameter -/

/-- **The inverse Jacobi estimates in the normalized parameter.**  Given the
four estimates in arclength — the `L¹` non-expansiveness, the `L¹ → L^∞` gain
and the first- and second-order pointwise bounds, as produced by
`JacobiAssembly.jacobi_estimates` — the corresponding estimates hold for the
functionals of the normalized parameter, with the explicit constants `constW`,
`const0`, `const1` and `const2`.

Here `η_R` is the rear normal velocity in rear arclength (period `ℓ`), with
derivatives `η_R'` and `η_R''`, and `η_F` is the front normal velocity in front
arclength (period `P`); `SF0` and `SF1` are the arclength sup bounds used in the
arclength estimates, related to the normalized sup norms by the last two
hypotheses. -/
theorem jacobi_estimates_normalized {l P l0 c kh SF0 SF1 : ℝ}
    {etaR etaR1 etaR2 etaF : ℝ → ℝ}
    (hl : 0 < l) (hP : 0 < P) (hl0 : 0 < l0) (hc : 0 < c)
    (hR1 : ∀ x, HasDerivAt etaR (etaR1 x) x) (hR2 : ∀ x, HasDerivAt etaR1 (etaR2 x) x)
    (hSF0 : 0 ≤ SF0)
    (hW : (∫ x in (0:ℝ)..l, |etaR x|) ≤ ∫ s in (0:ℝ)..P, |etaF s|)
    (hS0 : ∀ x, |etaR x| ≤ (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)
    (hS1 : ∀ x, |etaR1 x|
      ≤ SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|)
    (hS2 : ∀ x, |etaR2 x| ≤ SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3
      + (SF0 / c + (1 - Real.exp (-l0))⁻¹ * ∫ s in (0:ℝ)..P, |etaF s|))
    (hnorm0 : SF0 ≤ supNorm (fun u => etaF (P * u)))
    (hnorm1 : P * SF1 ≤ supNorm (iteratedDeriv 1 fun u => etaF (P * u))) :
    (∫ u in (0:ℝ)..1, |etaR (l * u)|) ≤ constW P l * ∫ u in (0:ℝ)..1, |etaF (P * u)|
      ∧ supNorm (fun u => etaR (l * u)) ≤ const0 P l0 * ∫ u in (0:ℝ)..1, |etaF (P * u)|
      ∧ supNorm (iteratedDeriv 1 fun u => etaR (l * u))
          ≤ const1 P l l0 c * ((∫ u in (0:ℝ)..1, |etaF (P * u)|)
            + supNorm (fun u => etaF (P * u)))
      ∧ supNorm (iteratedDeriv 2 fun u => etaR (l * u))
          ≤ const2 P l l0 c kh * ((∫ u in (0:ℝ)..1, |etaF (P * u)|)
            + supNorm (fun u => etaF (P * u))
            + supNorm (iteratedDeriv 1 fun u => etaF (P * u))) := by
  have hexp := one_sub_exp_pos hl0
  set A : ℝ := ∫ s in (0:ℝ)..P, |etaF s| with hA
  set Wn : ℝ := ∫ u in (0:ℝ)..1, |etaF (P * u)| with hWn
  set S0n : ℝ := supNorm (fun u => etaF (P * u)) with hS0n
  set S1n : ℝ := supNorm (iteratedDeriv 1 fun u => etaF (P * u)) with hS1n
  have hAW : A = P * Wn := by
    rw [hWn, integral_abs_comp_mul (ne_of_gt hP) etaF, ← hA]
    field_simp
  have hWn_nonneg : 0 ≤ Wn := by
    rw [hWn]; exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _)
  have hS0n_nonneg : 0 ≤ S0n := supNorm_nonneg _
  have hS1n_nonneg : 0 ≤ S1n := supNorm_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the `L¹` estimate
    rw [integral_abs_comp_mul (ne_of_gt hl) etaR]
    have h1 : l⁻¹ * (∫ x in (0:ℝ)..l, |etaR x|) ≤ l⁻¹ * A :=
      mul_le_mul_of_nonneg_left hW (by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [hAW]
    unfold constW
    field_simp
  · -- the `L¹ → L^∞` gain
    refine Real.iSup_le (fun u => ?_) (by
      have := const0_nonneg (P := P) (l0 := l0) hP hl0
      positivity)
    refine (hS0 (l * u)).trans (le_of_eq ?_)
    rw [hAW]
    unfold const0
    field_simp
  · -- the first-order gain
    rw [iteratedDeriv_one_comp_mul hR1]
    have hconst := const1_nonneg (P := P) (l := l) (l0 := l0) (c := c) hP hl hl0 hc
    refine Real.iSup_le (fun u => ?_) (by positivity)
    have hb : |l * etaR1 (l * u)| = l * |etaR1 (l * u)| := by
      rw [abs_mul, abs_of_pos hl]
    rw [hb]
    have h1 : l * |etaR1 (l * u)| ≤ l * (SF0 / c + (1 - Real.exp (-l0))⁻¹ * A) :=
      mul_le_mul_of_nonneg_left (hS1 (l * u)) hl.le
    refine h1.trans ?_
    have h2 : l * (SF0 / c + (1 - Real.exp (-l0))⁻¹ * A)
        = (l / c) * SF0 + (l * P / (1 - Real.exp (-l0))) * Wn := by
      rw [hAW]; field_simp
    rw [h2]
    have hle0 : (l / c) * SF0 ≤ (l / c) * S0n :=
      mul_le_mul_of_nonneg_left hnorm0 (by positivity)
    have hsum : (l / c) * S0n + (l * P / (1 - Real.exp (-l0))) * Wn
        ≤ const1 P l l0 c * (Wn + S0n) := by
      unfold const1
      have h3 : 0 ≤ l / c := by positivity
      have h4 : 0 ≤ l * P / (1 - Real.exp (-l0)) := by positivity
      nlinarith [hWn_nonneg, hS0n_nonneg]
    linarith
  · -- the second-order gain
    rw [iteratedDeriv_two_comp_mul hR1 hR2]
    have hconst := const2_nonneg (P := P) (l := l) (l0 := l0) (c := c) (kh := kh) hP hl hl0 hc
    refine Real.iSup_le (fun u => ?_) (by positivity)
    have hb : |l ^ 2 * etaR2 (l * u)| = l ^ 2 * |etaR2 (l * u)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < l ^ 2)]
    rw [hb]
    have h1 : l ^ 2 * |etaR2 (l * u)|
        ≤ l ^ 2 * (SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3
          + (SF0 / c + (1 - Real.exp (-l0))⁻¹ * A)) :=
      mul_le_mul_of_nonneg_left (hS2 (l * u)) (by positivity)
    refine h1.trans ?_
    have hSF1' : SF1 ≤ S1n / P := by
      rw [le_div_iff₀ hP]; linarith [hnorm1]
    have h2 : l ^ 2 * (SF1 / c ^ 2 + 2 * kh ^ 2 * SF0 / c ^ 3
          + (SF0 / c + (1 - Real.exp (-l0))⁻¹ * A))
        = (l ^ 2 / c ^ 2) * SF1 + (l ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c)) * SF0
          + (l ^ 2 * P / (1 - Real.exp (-l0))) * Wn := by
      rw [hAW]; field_simp; ring
    rw [h2]
    have e1 : (l ^ 2 / c ^ 2) * SF1 ≤ (l ^ 2 / c ^ 2) * (S1n / P) :=
      mul_le_mul_of_nonneg_left hSF1' (by positivity)
    have e1' : (l ^ 2 / c ^ 2) * (S1n / P) = (l ^ 2 / (P * c ^ 2)) * S1n := by
      field_simp
    have e2 : (l ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c)) * SF0
        ≤ (l ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c)) * S0n :=
      mul_le_mul_of_nonneg_left hnorm0 (by positivity)
    have hsum : (l ^ 2 / (P * c ^ 2)) * S1n + (l ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c)) * S0n
        + (l ^ 2 * P / (1 - Real.exp (-l0))) * Wn
        ≤ const2 P l l0 c kh * (Wn + S0n + S1n) := by
      unfold const2
      have h3 : 0 ≤ l ^ 2 / (P * c ^ 2) := by positivity
      have h4 : 0 ≤ l ^ 2 * (2 * kh ^ 2 / c ^ 3 + 1 / c) := by positivity
      have h5 : 0 ≤ l ^ 2 * P / (1 - Real.exp (-l0)) := by positivity
      nlinarith [hWn_nonneg, hS0n_nonneg, hS1n_nonneg]
    rw [e1'] at e1
    linarith

/-- The sup norm scales by a nonnegative factor. -/
theorem supNorm_const_mul {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) :
    supNorm (fun u => a * f u) = a * supNorm f := by
  unfold supNorm
  rw [Real.mul_iSup_of_nonneg ha]
  congr 1
  funext u
  rw [abs_mul, abs_of_nonneg ha]

/-- **The inverse Jacobi estimates in the normalization of the path metric.**
The geometric hypotheses are those of `JacobiAssembly.jacobi_estimates` (the
inverse Jacobi identity `η_R' = G - η_R` for the transported front velocity
`G = sec δ · η_F ∘ sf`, the selected-strip bounds `cos δ ≥ c > 0`,
`|sin δ|, |K| ≤ κ̂`, and the arclength change of variables), together with
boundedness of the front normal velocity and of its derivative.  The conclusion
is the four estimates of the paper's lemma for the functionals of the
normalized parameter `u ∈ [0,1]`, with the explicit constants `constW`,
`const0`, `const1`, `const2`. -/
theorem jacobi_estimates_normalized_of_geometry {l P l0 c kh : ℝ}
    {etaR etaF etaFs delta xf G dl sf K dxv : ℝ → ℝ}
    (hl0 : 0 < l0) (hll : l0 ≤ l) (hP : 0 < P) (hcpos : 0 < c)
    (hetaFd : ∀ s, HasDerivAt etaF (etaFs s) s)
    (hFbdd : BddAbove (Set.range fun s => |etaF s|))
    (hF1bdd : BddAbove (Set.range fun s => |etaFs s|))
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
    (∫ u in (0:ℝ)..1, |etaR (l * u)|) ≤ constW P l * ∫ u in (0:ℝ)..1, |etaF (P * u)|
      ∧ supNorm (fun u => etaR (l * u)) ≤ const0 P l0 * ∫ u in (0:ℝ)..1, |etaF (P * u)|
      ∧ supNorm (iteratedDeriv 1 fun u => etaR (l * u))
          ≤ const1 P l l0 c * ((∫ u in (0:ℝ)..1, |etaF (P * u)|)
            + supNorm (fun u => etaF (P * u)))
      ∧ supNorm (iteratedDeriv 2 fun u => etaR (l * u))
          ≤ const2 P l l0 c kh * ((∫ u in (0:ℝ)..1, |etaF (P * u)|)
            + supNorm (fun u => etaF (P * u))
            + supNorm (iteratedDeriv 1 fun u => etaF (P * u))) := by
  have hl : 0 < l := lt_of_lt_of_le hl0 hll
  -- the arclength estimates, with the sup norms as the front bounds
  have hF0 : ∀ s, |etaF s| ≤ supNorm etaF := fun s => le_supNorm hFbdd s
  have hF1 : ∀ s, |etaFs s| ≤ supNorm etaFs := fun s => le_supNorm hF1bdd s
  obtain ⟨hW, hS0, hS1, hS2⟩ :=
    JacobiAssembly.jacobi_estimates (l := l) (P := P) (l0 := l0) (c := c) (kh := kh)
      (SF0 := supNorm etaF) (SF1 := supNorm etaFs) (etaR := etaR) (etaF := etaF)
      (G := G) (delta := delta) (xf := xf) (etaFs := etaFs) (dl := dl) (sf := sf)
      (K := K) (dxv := dxv) hl0 hll hcpos hetaFd hF0 hF1 hK hdelta hcos hdlcos hdlsin
      hsf hdl hdxv hxf hx0 hxP hGdef hGcont hGper hetaR hetaRper htransport
  -- the derivatives of the rear normal velocity
  have hR1 : ∀ x, HasDerivAt etaR (deriv etaR x) x := fun x => by
    rw [(hetaR x).deriv]; exact hetaR x
  have hR2 : ∀ x, HasDerivAt (deriv etaR) (deriv (deriv etaR) x) x := fun x => by
    have hcos0 : Real.cos (dl x) ≠ 0 := ne_of_gt (lt_of_lt_of_le hcpos (hdlcos x))
    have h := JacobiAssembly.etaR_second_hasDerivAt (etaR := etaR) (etaF := etaF) (G := G)
      (dl := dl) (sf := sf) (etaFs := etaFs (sf x)) (dxv := dxv x) hetaR hGdef hcos0
      (hsf x) (hdl x) (hetaFd (sf x))
    rw [h.deriv]
    exact h
  -- the relation between the arclength and the normalized sup norms
  have hnorm0 : supNorm etaF ≤ supNorm (fun u => etaF (P * u)) :=
    le_of_eq (supNorm_comp_mul (ne_of_gt hP) etaF).symm
  have hnorm1 : P * supNorm etaFs ≤ supNorm (iteratedDeriv 1 fun u => etaF (P * u)) := by
    rw [iteratedDeriv_one_comp_mul hetaFd, supNorm_const_mul hP.le,
      supNorm_comp_mul (ne_of_gt hP) etaFs]
  exact jacobi_estimates_normalized (etaR1 := deriv etaR) (etaR2 := deriv (deriv etaR))
    hl hP hl0 hcpos hR1 hR2 (supNorm_nonneg _) hW hS0 hS1 hS2 hnorm0 hnorm1

end JacobiNormalized
