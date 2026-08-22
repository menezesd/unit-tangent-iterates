import Mathlib
import UnitTangentIterates.PerimeterDerivativeProduced
import UnitTangentIterates.PeriodizationDeriv
import UnitTangentIterates.ExpDecay

/-!
# The interior term of the perimeter derivative

The derivative clause `P'(H) = 1 + O(e^{-βH})` of the proposition *Exact
two-cap pairs* of *A Noncircular Oval with Convex Unit-Tangent Iterates* is
obtained from the Leibniz rule for the centred cell integral of `Φ(Y_H)`, whose
three terms are the two endpoint values — produced in
`UnitTangentIterates/PerimeterDerivativeProduced.lean` — and the interior term

```
  ∫_{-H/2}^{H/2} ∂_H Φ(Y_H(s)) ds ,      Y_H(s) = ∑_{m∈ℤ} y(s - mH).
```

This file produces the interior term.  Termwise differentiation in the period
(`PeriodizationDeriv.hasDerivAt_periodization_period`) gives
`∂_H Y_H(s) = ∑_m (-m)y'(s - mH)`, a series whose `m = 0` term vanishes, so
every surviving translate sits at distance at least `(|m| - ½)H` from the
centre of its pulse and the polynomially weighted geometric series is
`O(e^{-(α/2)H})`; the chain rule and the bound `|Φ'(z)| ≤ a/√(1-a²)` then make
the whole integrand that small, and the integral gains only a factor `H`, which
is absorbed into a slightly smaller exponent.

Main results:

* `tsum_natAbs_geom_le` : `∑_{m∈ℤ}|m|q^{|m|} ≤ 8q` for `0 ≤ q ≤ ½`;
* `abs_tsum_deriv_le` : `|∂_H Y_H(s)| ≤ 8Ce^{-(α/2)H}` on the centred cell;
* `hasDerivAt_Phi`, `hasDerivAt_Phi_periodization` : the chain rule identifying
  the interior integrand as `Φ'(Y_H)∂_H Y_H`;
* `abs_interior_integrand_le`, `abs_interior_integral_le` : the interior term
  is at most `(a/√(1-a²))·8C·H·e^{-(α/2)H}`;
* `hasDerivAt_perimeter_of_pulse_full` : hence, for `β' < α/2`,
  `|P'(H) - 1| ≤ (25C² + (a/√(1-a²))·8C/((α/2-β')e))e^{-β'H}`, the only
  remaining hypothesis being the Leibniz rule itself.
-/

noncomputable section

open Real Set MeasureTheory

namespace PerimeterInteriorTerm

open PerimeterAsymptotics PerimeterAsymptoticsProduced PerimeterDerivativeProduced

/-! ### The polynomially weighted geometric series -/

/-- **`∑_{m∈ℤ}|m|q^{|m|} ≤ 8q`** for `0 ≤ q ≤ ½`. -/
theorem tsum_natAbs_geom_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    ∑' m : ℤ, ((m.natAbs : ℝ) * q ^ m.natAbs) ≤ 8 * q := by
  have hq1 : q < 1 := by linarith
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have hval : ∑' n : ℕ, (n : ℝ) * q ^ n = q / (1 - q) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hsplit := tsum_of_nat_of_neg_add_one
    (f := fun m : ℤ => ((m.natAbs : ℝ) * q ^ m.natAbs)) (by simpa using hgeo) (by
      have hshape : (fun n : ℕ => (((-((n : ℤ) + 1)).natAbs : ℝ) * q ^ (-((n : ℤ) + 1)).natAbs))
          = fun n : ℕ => ((n + 1 : ℕ) : ℝ) * q ^ (n + 1) := by
        funext n
        have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
        rw [hn]
      rw [hshape]
      simpa using (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) * q ^ n) 1).2 hgeo)
  have hneg : ∑' n : ℕ, (((-((n : ℤ) + 1)).natAbs : ℝ) * q ^ (-((n : ℤ) + 1)).natAbs)
      = ∑' n : ℕ, (n : ℝ) * q ^ n := by
    have hshape : (fun n : ℕ => (((-((n : ℤ) + 1)).natAbs : ℝ) * q ^ (-((n : ℤ) + 1)).natAbs))
        = fun n : ℕ => ((n + 1 : ℕ) : ℝ) * q ^ (n + 1) := by
      funext n
      have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [hn]
    rw [hshape]
    have hzero := Summable.tsum_eq_zero_add (f := fun n : ℕ => (n : ℝ) * q ^ n) hgeo
    simp only [Nat.cast_zero, zero_mul, zero_add] at hzero
    rw [← hzero]
  have hpos : ∑' m : ℤ, ((m.natAbs : ℝ) * q ^ m.natAbs) = 2 * (q / (1 - q) ^ 2) := by
    rw [hsplit, hneg]
    simp only [Int.natAbs_natCast]
    rw [hval]
    ring
  rw [hpos]
  have hden : (1 : ℝ) / 4 ≤ (1 - q) ^ 2 := by nlinarith
  have hden0 : (0 : ℝ) < (1 - q) ^ 2 := by nlinarith
  have hstep : q / (1 - q) ^ 2 ≤ 4 * q := by
    rw [div_le_iff₀ hden0]
    nlinarith
  linarith

/-! ### The derivative of the periodization in the period -/

variable {y yp : ℝ → ℝ} {C a alpha H s : ℝ}

/-- **The derivative of the periodized profile in the period is exponentially
small on the centred cell**: `|∂_H Y_H(s)| ≤ 8Ce^{-(α/2)H}`. -/
theorem abs_tsum_deriv_le (halpha : 0 < alpha) (hH : 0 < H)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (hs : |s| ≤ H / 2) :
    |∑' m : ℤ, (-(m : ℝ)) * yp (s - m * H)| ≤ 8 * C * Real.exp (-(alpha / 2) * H) := by
  have hC : 0 ≤ C := PeriodizationDeriv.const_nonneg hypb
  set q : ℝ := Real.exp (-alpha * H) with hqdef
  have hq0 : (0 : ℝ) ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by linarith
  set K : ℝ := C * Real.exp (alpha * (H / 2)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hsum : Summable (fun m : ℤ => K * ((m.natAbs : ℝ) * q ^ m.natAbs)) :=
    PeriodizationDeriv.summable_natAbs_geometric hq0 hq1
  have hterm : ∀ m : ℤ, ‖(-(m : ℝ)) * yp (s - m * H)‖
      ≤ K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by
    intro m
    have hshift := PeriodizationDeriv.abs_shift_le (w := yp) (C := C) (a := alpha)
      (H₀ := H) (H := H) (s := s) halpha hypb hH le_rfl m
    have hexp : Real.exp (alpha * |s|) ≤ Real.exp (alpha * (H / 2)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hmabs : |(-(m : ℝ))| = (m.natAbs : ℝ) := by
      rw [abs_neg, ← Int.cast_abs, Int.abs_eq_natAbs]; norm_num
    have hpow : (0 : ℝ) ≤ q ^ m.natAbs := by positivity
    calc ‖(-(m : ℝ)) * yp (s - m * H)‖ = (m.natAbs : ℝ) * |yp (s - m * H)| := by
          rw [Real.norm_eq_abs, abs_mul, hmabs]
      _ ≤ (m.natAbs : ℝ) * ((C * Real.exp (alpha * |s|)) * q ^ m.natAbs) :=
          mul_le_mul_of_nonneg_left hshift (Nat.cast_nonneg _)
      _ ≤ (m.natAbs : ℝ) * ((C * Real.exp (alpha * (H / 2))) * q ^ m.natAbs) := by
          have : (C * Real.exp (alpha * |s|)) * q ^ m.natAbs
              ≤ (C * Real.exp (alpha * (H / 2))) * q ^ m.natAbs := by
            have := mul_le_mul_of_nonneg_left hexp hC
            exact mul_le_mul_of_nonneg_right this hpow
          exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by rw [hKdef]; ring
  have hbound : |∑' m : ℤ, (-(m : ℝ)) * yp (s - m * H)|
      ≤ ∑' m : ℤ, K * ((m.natAbs : ℝ) * q ^ m.natAbs) := by
    simpa [Real.norm_eq_abs] using tsum_of_norm_bounded hsum.hasSum hterm
  have hgeo : ∑' m : ℤ, K * ((m.natAbs : ℝ) * q ^ m.natAbs)
      = K * ∑' m : ℤ, ((m.natAbs : ℝ) * q ^ m.natAbs) := tsum_mul_left
  have hle : ∑' m : ℤ, ((m.natAbs : ℝ) * q ^ m.natAbs) ≤ 8 * q :=
    tsum_natAbs_geom_le hq0 hq
  have hfin : K * (8 * q) = 8 * C * Real.exp (-(alpha / 2) * H) := by
    have hmul : Real.exp (alpha * (H / 2)) * Real.exp (-alpha * H)
        = Real.exp (-(alpha / 2) * H) := by
      rw [← Real.exp_add]; ring_nf
    rw [hKdef, hqdef]
    calc C * Real.exp (alpha * (H / 2)) * (8 * Real.exp (-alpha * H))
        = 8 * C * (Real.exp (alpha * (H / 2)) * Real.exp (-alpha * H)) := by ring
      _ = 8 * C * Real.exp (-(alpha / 2) * H) := by rw [hmul]
  calc |∑' m : ℤ, (-(m : ℝ)) * yp (s - m * H)|
      ≤ ∑' m : ℤ, K * ((m.natAbs : ℝ) * q ^ m.natAbs) := hbound
    _ = K * ∑' m : ℤ, ((m.natAbs : ℝ) * q ^ m.natAbs) := hgeo
    _ ≤ K * (8 * q) := mul_le_mul_of_nonneg_left hle hK0
    _ = 8 * C * Real.exp (-(alpha / 2) * H) := hfin

/-! ### The interior integrand -/

/-- The derivative of the defect integrand, `Φ'(z) = z/√(1-z²)`. -/
theorem hasDerivAt_Phi {z : ℝ} (hz : |z| < 1) :
    HasDerivAt Phi (z / Real.sqrt (1 - z ^ 2)) z := by
  have hlt := abs_lt.mp hz
  have hpos : 0 < 1 - z ^ 2 := by nlinarith [hlt.1, hlt.2]
  have hsqrt : 0 < Real.sqrt (1 - z ^ 2) := Real.sqrt_pos.mpr hpos
  have hu : HasDerivAt (fun w : ℝ => 1 - w ^ 2) (-(2 * z)) z := by
    have := (hasDerivAt_pow 2 z).const_sub 1
    simpa using this
  have hcomp := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp z hu
  have hval : 1 / (2 * Real.sqrt (1 - z ^ 2)) * -(2 * z) = -(z / Real.sqrt (1 - z ^ 2)) := by
    field_simp
  rw [hval] at hcomp
  have := (hasDerivAt_const z (1 : ℝ)).sub hcomp
  simpa [Phi, Function.comp] using this

/-- **The chain rule for the interior integrand.**  With `s` held fixed, the
defect integrand of the periodized profile is differentiable in the period,
with derivative `Φ'(Y_H(s))·∂_H Y_H(s)`. -/
theorem hasDerivAt_Phi_periodization {H₀ : ℝ} (halpha : 0 < alpha) (hH₀ : 0 < H₀)
    (hH : H₀ < H)
    (hy : ∀ x, HasDerivAt y (yp x) x)
    (hyb : ∀ x, |y x| ≤ C * Real.exp (-alpha * |x|))
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (hlt : |∑' m : ℤ, y (s - m * H)| < 1) :
    HasDerivAt (fun t => Phi (∑' m : ℤ, y (s - m * t)))
      ((∑' m : ℤ, y (s - m * H)) / Real.sqrt (1 - (∑' m : ℤ, y (s - m * H)) ^ 2)
        * ∑' m : ℤ, (-(m : ℝ)) * yp (s - m * H)) H := by
  have hinner := PeriodizationDeriv.hasDerivAt_periodization_period (z := y) (z' := yp)
    (C := C) (a := alpha) (H₀ := H₀) (H := H) (s := s) halpha hH₀ hy hyb hypb hH
  have hcomp : HasDerivAt (Phi ∘ fun t => ∑' m : ℤ, y (s - m * t))
      ((∑' m : ℤ, y (s - m * H)) / Real.sqrt (1 - (∑' m : ℤ, y (s - m * H)) ^ 2)
        * ∑' m : ℤ, (-(m : ℝ)) * yp (s - m * H)) H :=
    (hasDerivAt_Phi hlt).comp H hinner
  exact hcomp

/-- **The interior integrand is exponentially small on the centred cell.** -/
theorem abs_interior_integrand_le (halpha : 0 < alpha) (hH : 0 < H)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : |∑' m : ℤ, y (s - m * H)| ≤ a)
    (hs : |s| ≤ H / 2) :
    |(∑' m : ℤ, y (s - m * H)) / Real.sqrt (1 - (∑' m : ℤ, y (s - m * H)) ^ 2)
        * ∑' m : ℤ, (-(m : ℝ)) * yp (s - m * H)|
      ≤ a / Real.sqrt (1 - a ^ 2) * (8 * C) * Real.exp (-(alpha / 2) * H) := by
  set Y : ℝ := ∑' m : ℤ, y (s - m * H) with hY
  have hC : 0 ≤ C := PeriodizationDeriv.const_nonneg hypb
  have ha2 : a ^ 2 < 1 := by nlinarith
  have hda : 0 < Real.sqrt (1 - a ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hY2 : Y ^ 2 ≤ a ^ 2 := by
    have := abs_le.mp hYa
    nlinarith [this.1, this.2]
  have hdY : Real.sqrt (1 - a ^ 2) ≤ Real.sqrt (1 - Y ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hdY0 : 0 < Real.sqrt (1 - Y ^ 2) := lt_of_lt_of_le hda hdY
  have hfac : |Y / Real.sqrt (1 - Y ^ 2)| ≤ a / Real.sqrt (1 - a ^ 2) := by
    rw [abs_div, abs_of_pos hdY0]
    gcongr
  have hderiv := abs_tsum_deriv_le halpha hH hq hypb hs
  have hpos : 0 ≤ a / Real.sqrt (1 - a ^ 2) := by positivity
  calc |Y / Real.sqrt (1 - Y ^ 2) * ∑' m : ℤ, (-(m : ℝ)) * yp (s - m * H)|
      = |Y / Real.sqrt (1 - Y ^ 2)| * |∑' m : ℤ, (-(m : ℝ)) * yp (s - m * H)| := abs_mul _ _
    _ ≤ a / Real.sqrt (1 - a ^ 2) * (8 * C * Real.exp (-(alpha / 2) * H)) :=
        mul_le_mul hfac hderiv (abs_nonneg _) hpos
    _ = a / Real.sqrt (1 - a ^ 2) * (8 * C) * Real.exp (-(alpha / 2) * H) := by ring

/-! ### The interior term and the derivative clause -/

/-- **The interior term of the Leibniz rule is exponentially small**, up to the
length `H` of the cell. -/
theorem abs_interior_integral_le {gH : ℝ → ℝ} (halpha : 0 < alpha) (hH : 0 < H)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u : ℝ, |∑' m : ℤ, y (u - m * H)| ≤ a)
    (hgH : ∀ u, gH u
      = (∑' m : ℤ, y (u - m * H)) / Real.sqrt (1 - (∑' m : ℤ, y (u - m * H)) ^ 2)
        * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * H)) :
    |∫ u in (-(H / 2))..(H / 2), gH u|
      ≤ a / Real.sqrt (1 - a ^ 2) * (8 * C) * Real.exp (-(alpha / 2) * H) * H := by
  have hle : -(H / 2) ≤ H / 2 := by linarith
  have hbd : ∀ u ∈ Set.uIoc (-(H / 2)) (H / 2),
      ‖gH u‖ ≤ a / Real.sqrt (1 - a ^ 2) * (8 * C) * Real.exp (-(alpha / 2) * H) := by
    intro u hu
    rw [Set.uIoc_of_le hle] at hu
    have hs : |u| ≤ H / 2 := abs_le.mpr ⟨hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs, hgH u]
    exact abs_interior_integrand_le halpha hH hq hypb ha0 ha1 (hYa u) hs
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs] at h
  have habs : |H / 2 - -(H / 2)| = H := by
    rw [abs_of_nonneg (by linarith)]; ring
  rwa [habs] at h

/-- **`P'(H) = 1 + O(e^{-β'H})`, with both the endpoint terms and the interior
term produced.**  For a nonnegative pulse `y` with `|y|, |y'| ≤ Ce^{-α|·|}`
whose periodization stays below `a < 1`, if the perimeter defect is the centred
cell integral of `Φ(Y_H)`, the Leibniz rule holds at `H` with the interior
integrand `∂_HΦ(Y_H) = Φ'(Y_H)∂_HY_H`, then for every `β' < α/2`

`|P'(H) - 1| ≤ (25C² + (a/√(1-a²))·8C/((α/2-β')e))e^{-β'H}`. -/
theorem hasDerivAt_perimeter_of_pulse_full {P : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {gH : ℝ → ℝ}
    {beta' : ℝ} (halpha : 0 < alpha) (hH : 0 < H) (hb : beta' < alpha / 2)
    (hq : Real.exp (-alpha * H) ≤ 1 / 2)
    (hy0 : ∀ x, 0 ≤ y x) (hyb : ∀ x, y x ≤ C * Real.exp (-alpha * |x|))
    (hypb : ∀ x, |yp x| ≤ C * Real.exp (-alpha * |x|))
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hYa : ∀ u : ℝ, |∑' m : ℤ, y (u - m * H)| ≤ a)
    (hg : ∀ H' u, g H' u = Phi (∑' m : ℤ, y (u - m * H')))
    (hgH : ∀ u, gH u
      = (∑' m : ℤ, y (u - m * H)) / Real.sqrt (1 - (∑' m : ℤ, y (u - m * H)) ^ 2)
        * ∑' m : ℤ, (-(m : ℝ)) * yp (u - m * H))
    (hid : ∀ H', H' - P H' = ∫ u in (-(H'/2))..(H'/2), g H' u)
    (hderiv : HasDerivAt (fun H' => ∫ u in (-(H'/2))..(H'/2), g H' u)
      (g H (H/2) / 2 + g H (-(H/2)) / 2 + ∫ u in (-(H/2))..(H/2), gH u) H) :
    ∃ p : ℝ, HasDerivAt P p H ∧
      |p - 1| ≤ (25 * C ^ 2
        + a / Real.sqrt (1 - a ^ 2) * (8 * C) / ((alpha / 2 - beta') * Real.exp 1))
          * Real.exp (-beta' * H) := by
  have hC : 0 ≤ C := Periodization.const_nonneg hy0 hyb
  have hexpmono : Real.exp (-alpha * H) ≤ Real.exp (-beta' * H) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hY1 : ∀ u : ℝ, (∑' m : ℤ, y (u - m * H)) ≤ 1 := by
    intro u
    exact le_trans (le_trans (le_abs_self _) (hYa u)) ha1.le
  have habs1 : |H / 2| = H / 2 := abs_of_nonneg (by linarith)
  have habs2 : |(-(H / 2) : ℝ)| = H / 2 := by rw [abs_neg]; exact habs1
  have hend1 : |g H (H/2)| ≤ 25 * C ^ 2 * Real.exp (-beta' * H) := by
    rw [hg]
    refine le_trans (abs_Phi_edge_le halpha hH hq hy0 hyb habs1 (hY1 _)) ?_
    exact mul_le_mul_of_nonneg_left hexpmono (by positivity)
  have hend2 : |g H (-(H/2))| ≤ 25 * C ^ 2 * Real.exp (-beta' * H) := by
    rw [hg]
    refine le_trans (abs_Phi_edge_le halpha hH hq hy0 hyb habs2 (hY1 _)) ?_
    exact mul_le_mul_of_nonneg_left hexpmono (by positivity)
  have hA : 0 ≤ a / Real.sqrt (1 - a ^ 2) * (8 * C) := by positivity
  have hint : |∫ u in (-(H/2))..(H/2), gH u|
      ≤ a / Real.sqrt (1 - a ^ 2) * (8 * C) / ((alpha / 2 - beta') * Real.exp 1)
        * Real.exp (-beta' * H) := by
    refine le_trans (abs_interior_integral_le halpha hH hq hypb ha0 ha1 hYa hgH) ?_
    have hdec := ExpDecay.linear_exp_decay (b := alpha / 2) (b' := beta') (x := H) hb
    have hrw1 : Real.exp (-(alpha / 2) * H) = Real.exp (-(alpha / 2 * H)) := by ring_nf
    have hrw2 : Real.exp (-beta' * H) = Real.exp (-(beta' * H)) := by ring_nf
    rw [hrw1, hrw2]
    calc a / Real.sqrt (1 - a ^ 2) * (8 * C) * Real.exp (-(alpha / 2 * H)) * H
        = a / Real.sqrt (1 - a ^ 2) * (8 * C) * (H * Real.exp (-(alpha / 2 * H))) := by ring
      _ ≤ a / Real.sqrt (1 - a ^ 2) * (8 * C)
            * (1 / ((alpha / 2 - beta') * Real.exp 1) * Real.exp (-(beta' * H))) :=
          mul_le_mul_of_nonneg_left hdec hA
      _ = a / Real.sqrt (1 - a ^ 2) * (8 * C) / ((alpha / 2 - beta') * Real.exp 1)
            * Real.exp (-(beta' * H)) := by ring
  exact PerimeterAsymptotics.hasDerivAt_perimeter_exp hid hderiv hend1 hend2 hint

end PerimeterInteriorTerm
