import Mathlib
import UnitTangentIterates.RearOwnTangential

/-!
# The source of the inverse Jacobi ODE is dominated by the cost density

The normal rate `η` of the family of selected rears, written in the rear
arclength, solves the inverse Jacobi ODE `∂ₓη = g − η` with source

`g(x) = η_F(sf x)/cos δ(sf x)` ,

`η_F` being the normal velocity of the fronts, `δ` the selected steering angle
and `sf` the change of variable from the rear to the front arclength.  The
assembled `C²` estimate for the selected inverse asks for a bound `D` on the
arclength derivative of that source, dominated by the cost density of the path.

This file supplies it.  Differentiating the source,

`∂ₓg = (η_F' + η_F sin δ (K − sin δ)/cos δ)/cos²δ` ,

and using the bounds of the selected strip (`sin δ ≤ κ̂`, `cos δ ≥ √(1−κ̂²)`)
together with `|K| ≤ κ̂`, a sup bound `M` for `η_F` and a sup bound `M/v` for
its arclength derivative give

`|∂ₓg| ≤ jacobiSourceConst κ̂ v · M` , with
`jacobiSourceConst κ̂ v = (1/v + 2κ̂²)/(1−κ̂²)^{3/2}` .

Main result: `abs_source_deriv_le`.
-/

noncomputable section

namespace RearJacobiSourceCost

open RearOwnTangential

/-- **The constant of the source bound**, `(1/v + 2κ̂²)/(1−κ̂²)^{3/2}`: `v` is the
lower bound for the perimeter of the fronts, which converts a bound for the
parameter derivative of the normal velocity into one for its arclength
derivative. -/
def jacobiSourceConst (kh Pv : ℝ) : ℝ := (1 / Pv + 2 * kh ^ 2) / Real.sqrt (1 - kh ^ 2) ^ 3

theorem jacobiSourceConst_nonneg {kh Pv : ℝ} (hPv : 0 < Pv) :
    0 ≤ jacobiSourceConst kh Pv := by
  unfold jacobiSourceConst
  positivity

/-- **The arclength derivative of the source of the inverse Jacobi ODE is
bounded by the sup bounds of the front normal velocity.**  On the selected strip
the steering angle has `sin δ ≤ κ̂` and `cos δ ≥ √(1−κ̂²)`, and the change of
variable has derivative `1/cos δ`, so differentiating `η_F(sf x)/cos δ(sf x)`
and bounding each factor gives the constant `jacobiSourceConst κ̂ v`. -/
theorem abs_source_deriv_le {eta etas dl Kf sfun g : ℝ → ℝ} {kh Pv M : ℝ}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hPv : 0 < Pv)
    (hetaD : ∀ s, HasDerivAt eta (etas s) s)
    (hetabd : ∀ s, |eta s| ≤ M) (hetasbd : ∀ s, |etas s| ≤ M / Pv)
    (hdl0 : ∀ s, 0 ≤ dl s) (hdl1 : ∀ s, dl s ≤ Real.arcsin kh)
    (hsteer : ∀ s, HasDerivAt dl (Kf s - Real.sin (dl s)) s)
    (hK : ∀ s, |Kf s| ≤ kh)
    (hsf : ∀ x, HasDerivAt sfun (1 / Real.cos (dl (sfun x))) x)
    (hg : ∀ x, HasDerivAt (fun x' => eta (sfun x') / Real.cos (dl (sfun x'))) (g x) x)
    (x : ℝ) :
    |g x| ≤ jacobiSourceConst kh Pv * M := by
  set s := sfun x with hs
  set c := Real.cos (dl s) with hcdef
  obtain ⟨hsin, hcge, hgpos, hsin0⟩ := strip_bounds hkh0 hkh1 (hdl0 s) (hdl1 s)
  set gam := Real.sqrt (1 - kh ^ 2) with hgam
  have hcpos : 0 < c := lt_of_lt_of_le hgpos hcge
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hgam1 : gam ≤ 1 := by
    rw [hgam]
    have h : Real.sqrt (1 - kh ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith)
    simpa using h
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hetabd 0)
  -- the derivative of the source
  have h1 : HasDerivAt (fun x' => eta (sfun x')) (etas s * (1 / c)) x :=
    (hetaD s).comp x (hsf x)
  have h2 : HasDerivAt (fun x' => dl (sfun x'))
      ((Kf s - Real.sin (dl s)) * (1 / c)) x := (hsteer s).comp x (hsf x)
  have h3 : HasDerivAt (fun x' => Real.cos (dl (sfun x')))
      (-Real.sin (dl s) * ((Kf s - Real.sin (dl s)) * (1 / c))) x := h2.cos
  have hval := (hg x).unique (h1.div h3 hcne)
  rw [hval]
  have hnum : (etas s * (1 / c) * c
      - eta s * (-Real.sin (dl s) * ((Kf s - Real.sin (dl s)) * (1 / c)))) / c ^ 2
      = (etas s + eta s * (Real.sin (dl s) * (Kf s - Real.sin (dl s)) / c)) / c ^ 2 := by
    field_simp
    ring
  rw [hnum, jacobiSourceConst, ← hgam]
  -- the bounds of the selected strip
  have hsabs : |Real.sin (dl s)| ≤ kh := by rwa [abs_of_nonneg hsin0]
  have hdiff : |Kf s - Real.sin (dl s)| ≤ 2 * kh := by
    have hKs := hK s
    rw [abs_le] at hKs ⊢
    constructor <;> linarith [hKs.1, hKs.2]
  have hfrac : |Real.sin (dl s) * (Kf s - Real.sin (dl s)) / c| ≤ kh * (2 * kh) / gam := by
    rw [abs_div, abs_mul, abs_of_pos hcpos]
    exact div_le_div₀ (by positivity) (mul_le_mul hsabs hdiff (abs_nonneg _) hkh0) hgpos hcge
  have hprod : |eta s * (Real.sin (dl s) * (Kf s - Real.sin (dl s)) / c)|
      ≤ M * (kh * (2 * kh) / gam) := by
    rw [abs_mul]
    exact mul_le_mul (hetabd s) hfrac (abs_nonneg _) hMnn
  have hnumbd : |etas s + eta s * (Real.sin (dl s) * (Kf s - Real.sin (dl s)) / c)|
      ≤ M / Pv + M * (kh * (2 * kh) / gam) :=
    le_trans (abs_add_le _ _) (add_le_add (hetasbd s) hprod)
  have hden : gam ^ 2 ≤ c ^ 2 := by nlinarith
  have hstep : |(etas s + eta s * (Real.sin (dl s) * (Kf s - Real.sin (dl s)) / c)) / c ^ 2|
      ≤ (M / Pv + M * (kh * (2 * kh) / gam)) / gam ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < c ^ 2)]
    exact div_le_div₀ (by positivity) hnumbd (by positivity) hden
  refine hstep.trans ?_
  have hlhs : (M / Pv + M * (kh * (2 * kh) / gam)) / gam ^ 2
      = M / (Pv * gam ^ 2) + 2 * kh ^ 2 * M / gam ^ 3 := by
    field_simp
  have hrhs : (1 / Pv + 2 * kh ^ 2) / gam ^ 3 * M
      = M / (Pv * gam ^ 3) + 2 * kh ^ 2 * M / gam ^ 3 := by
    field_simp
  rw [hlhs, hrhs]
  have hcube : gam ^ 3 ≤ gam ^ 2 := by nlinarith [pow_pos hgpos 2]
  have hfin : M / (Pv * gam ^ 2) ≤ M / (Pv * gam ^ 3) := by
    apply div_le_div_of_nonneg_left hMnn (by positivity)
    nlinarith
  linarith

end RearJacobiSourceCost
