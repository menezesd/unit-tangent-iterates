import Mathlib
import UnitTangentIterates.L1Matching

/-!
# From the centred cell to the whole line

This file supplies the approximation step used twice in the proposition
*Exact two-cap pairs* and in the lemma *Uniform transverse width* of the paper
*A Noncircular Oval with Convex Unit-Tangent Iterates*:

> On the centred cell, `H − P(H) = ∫_{−H/2}^{H/2} Φ(Y_H(s)) ds`.  The
> periodization estimates, smoothness of `Φ` on a fixed interval, and the
> omitted exponential tails give
> `H − P(H) = ∫_ℝ Φ(y(s)) ds + O(e^{−βH}) = Δ + O(e^{−βH})`.

The content is the quantitative comparison of a *cell* integral of a
periodized integrand with the *line* integral of the isolated integrand: the
error is the uniform error on the cell times its length, plus the exponential
tails outside the cell.

Main results:

* `integral_expabs_Ioi` : `∫_{s>b} e^{−α|s|} ds = e^{−αb}/α` for `b ≥ 0`;
* `abs_integral_Ioi_le`, `abs_integral_Iic_le` : the tails of an
  exponentially localized function are exponentially small;
* `abs_integral_sub_cell_le` : `|∫_ℝ g − ∫_{−H/2}^{H/2} g| ≤ (2C/α)e^{−αH/2}`;
* `abs_cell_sub_line_le` : **the comparison** —
  `|∫_{−H/2}^{H/2} G − ∫_ℝ g| ≤ εH + (2C/α)e^{−αH/2}`
  whenever `|G − g| ≤ ε` on the cell and `|g| ≤ C e^{−α|·|}` on the line.
-/

noncomputable section

open MeasureTheory Set Real

namespace CellAsymptotics

variable {g G : ℝ → ℝ} {C alpha eps H b : ℝ}

/-! ### The exponential tail -/

/-- `∫_{s > b} e^{−α|s|} ds = e^{−αb}/α` for `b ≥ 0`. -/
theorem integral_expabs_Ioi (ha : 0 < alpha) (hb : 0 ≤ b) :
    ∫ s in Ioi b, Real.exp (-alpha * |s|) = Real.exp (-alpha * b) / alpha := by
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s : ℝ => Real.exp (-(alpha * s)))
    (fun x hx => by
      have hx' : 0 < x := lt_of_le_of_lt hb (mem_Ioi.mp hx)
      simp only
      rw [abs_of_pos hx']
      ring_nf)]
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) b ha
  simp only at h
  rw [h, integral_exp_neg_Ioi, smul_eq_mul]
  field_simp

/-- **The right tail of an exponentially localized function is exponentially
small.** -/
theorem abs_integral_Ioi_le (ha : 0 < alpha) (hb : 0 ≤ b) (hg : Integrable g)
    (hbd : ∀ s, |g s| ≤ C * Real.exp (-alpha * |s|)) :
    |∫ s in Ioi b, g s| ≤ C * Real.exp (-alpha * b) / alpha := by
  have hmaj : Integrable (fun s : ℝ => C * Real.exp (-alpha * |s|)) :=
    (L1Matching.integrable_expabs ha).const_mul C
  have h1 : |∫ s in Ioi b, g s| ≤ ∫ s in Ioi b, |g s| := by
    have := norm_integral_le_integral_norm (μ := volume.restrict (Ioi b)) g
    simpa [Real.norm_eq_abs] using this
  have h2 : (∫ s in Ioi b, |g s|) ≤ ∫ s in Ioi b, C * Real.exp (-alpha * |s|) :=
    setIntegral_mono_on hg.abs.integrableOn hmaj.integrableOn measurableSet_Ioi
      (fun s _ => hbd s)
  have h3 : (∫ s in Ioi b, C * Real.exp (-alpha * |s|))
      = C * (Real.exp (-alpha * b) / alpha) := by
    rw [integral_const_mul, integral_expabs_Ioi ha hb]
  rw [mul_div_assoc]
  calc |∫ s in Ioi b, g s| ≤ ∫ s in Ioi b, |g s| := h1
    _ ≤ ∫ s in Ioi b, C * Real.exp (-alpha * |s|) := h2
    _ = C * (Real.exp (-alpha * b) / alpha) := h3

/-- **The left tail of an exponentially localized function is exponentially
small.** -/
theorem abs_integral_Iic_le (ha : 0 < alpha) (hb : b ≤ 0) (hg : Integrable g)
    (hbd : ∀ s, |g s| ≤ C * Real.exp (-alpha * |s|)) :
    |∫ s in Iic b, g s| ≤ C * Real.exp (alpha * b) / alpha := by
  have hflip : (∫ s in Iic b, g s) = ∫ s in Ioi (-b), g (-s) := by
    simp
  have hbd' : ∀ s, |g (-s)| ≤ C * Real.exp (-alpha * |s|) := by
    intro s
    simpa [abs_neg] using hbd (-s)
  have h := abs_integral_Ioi_le (g := fun s => g (-s)) (b := -b) ha (by linarith)
    hg.comp_neg hbd'
  rw [hflip]
  calc |∫ s in Ioi (-b), g (-s)| ≤ C * Real.exp (-alpha * -b) / alpha := h
    _ = C * Real.exp (alpha * b) / alpha := by ring_nf

/-! ### The cell approximates the line -/

/-- **The cell integral approximates the line integral** of an exponentially
localized function, with error the two tails. -/
theorem abs_integral_sub_cell_le (ha : 0 < alpha) (hH : 0 ≤ H) (hg : Integrable g)
    (hbd : ∀ s, |g s| ≤ C * Real.exp (-alpha * |s|)) :
    |(∫ s : ℝ, g s) - ∫ s in (-(H/2))..(H/2), g s|
      ≤ 2 * C * Real.exp (-alpha * (H/2)) / alpha := by
  have hsplit1 : (∫ s in Iic (-(H/2)), g s) + (∫ s in Ioi (-(H/2)), g s) = ∫ s : ℝ, g s :=
    intervalIntegral.integral_Iic_add_Ioi hg.integrableOn hg.integrableOn
  have hsplit2 : (∫ s in (-(H/2))..(H/2), g s) + (∫ s in Ioi (H/2), g s)
      = ∫ s in Ioi (-(H/2)), g s :=
    intervalIntegral.integral_interval_add_Ioi hg.integrableOn hg.integrableOn
  have hkey : (∫ s : ℝ, g s) - ∫ s in (-(H/2))..(H/2), g s
      = (∫ s in Iic (-(H/2)), g s) + ∫ s in Ioi (H/2), g s := by
    linarith [hsplit1, hsplit2]
  have hleft := abs_integral_Iic_le (g := g) ha (by linarith : -(H/2) ≤ 0) hg hbd
  have hright := abs_integral_Ioi_le (g := g) ha (by linarith : (0:ℝ) ≤ H/2) hg hbd
  have hexp : Real.exp (alpha * -(H/2)) = Real.exp (-alpha * (H/2)) := by ring_nf
  rw [hexp] at hleft
  calc |(∫ s : ℝ, g s) - ∫ s in (-(H/2))..(H/2), g s|
      = |(∫ s in Iic (-(H/2)), g s) + ∫ s in Ioi (H/2), g s| := by rw [hkey]
    _ ≤ |∫ s in Iic (-(H/2)), g s| + |∫ s in Ioi (H/2), g s| := abs_add_le _ _
    _ ≤ C * Real.exp (-alpha * (H/2)) / alpha + C * Real.exp (-alpha * (H/2)) / alpha :=
        add_le_add hleft hright
    _ = 2 * C * Real.exp (-alpha * (H/2)) / alpha := by ring

/-- **The comparison of the cell integral of the periodized integrand with the
line integral of the isolated one.**  If `|G − g| ≤ ε` on the centred cell
`[−H/2, H/2]`, and `g` is integrable with `|g| ≤ C e^{−α|·|}`, then

`|∫_{−H/2}^{H/2} G − ∫_ℝ g| ≤ εH + (2C/α) e^{−αH/2}`. -/
theorem abs_cell_sub_line_le (ha : 0 < alpha) (hH : 0 ≤ H) (hg : Integrable g)
    (hGi : IntervalIntegrable G volume (-(H/2)) (H/2))
    (hbd : ∀ s, |g s| ≤ C * Real.exp (-alpha * |s|))
    (hGg : ∀ s ∈ Icc (-(H/2)) (H/2), |G s - g s| ≤ eps) :
    |(∫ s in (-(H/2))..(H/2), G s) - ∫ s : ℝ, g s|
      ≤ eps * H + 2 * C * Real.exp (-alpha * (H/2)) / alpha := by
  have hle : -(H/2) ≤ H/2 := by linarith
  have hcell : |(∫ s in (-(H/2))..(H/2), G s) - ∫ s in (-(H/2))..(H/2), g s| ≤ eps * H := by
    have hsub : (∫ s in (-(H/2))..(H/2), G s) - ∫ s in (-(H/2))..(H/2), g s
        = ∫ s in (-(H/2))..(H/2), (G s - g s) := by
      rw [intervalIntegral.integral_sub hGi hg.intervalIntegrable]
    rw [hsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(H/2)) (b := H/2) (C := eps) (f := fun s => G s - g s)
      (fun s hs => by
        rw [uIoc_of_le hle] at hs
        simpa [Real.norm_eq_abs] using hGg s ⟨hs.1.le, hs.2⟩)
    have hlen : |H/2 - -(H/2)| = H := by
      rw [abs_of_nonneg (by linarith)]; ring
    rw [Real.norm_eq_abs, hlen] at this
    linarith [this]
  have htail := abs_integral_sub_cell_le (g := g) ha hH hg hbd
  calc |(∫ s in (-(H/2))..(H/2), G s) - ∫ s : ℝ, g s|
      ≤ |(∫ s in (-(H/2))..(H/2), G s) - ∫ s in (-(H/2))..(H/2), g s|
        + |(∫ s in (-(H/2))..(H/2), g s) - ∫ s : ℝ, g s| := by
        have := abs_add_le ((∫ s in (-(H/2))..(H/2), G s) - ∫ s in (-(H/2))..(H/2), g s)
          ((∫ s in (-(H/2))..(H/2), g s) - ∫ s : ℝ, g s)
        simpa using this
    _ ≤ eps * H + 2 * C * Real.exp (-alpha * (H/2)) / alpha := by
        have hsymm : |(∫ s in (-(H/2))..(H/2), g s) - ∫ s : ℝ, g s|
            = |(∫ s : ℝ, g s) - ∫ s in (-(H/2))..(H/2), g s| := abs_sub_comm _ _
        rw [hsymm]
        exact add_le_add hcell htail

end CellAsymptotics
