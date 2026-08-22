import Mathlib
import UnitTangentIterates.PathMetric
import UnitTangentIterates.JacobiEstimates

/-!
# From the inverse Jacobi estimates to a Lipschitz bound for the path metric

The lemma *Inverse Jacobi estimates* of the paper *A Noncircular Oval with
Convex Unit-Tangent Iterates* compares the path functionals of a path of fronts
with those of the path of its selected rears:

```
  W(BΓ) ≤ W(Γ),   S₀(BΓ) ≤ C₀W(Γ),   S₁(BΓ) ≤ C₁(W+S₀)(Γ),
  S₂(BΓ) ≤ C₂(W+S₀+S₁)(Γ).
```

Its scalar cores — the `L¹` contractivity and the `L¹ → L^∞` bound of the
periodic inverse of `1 + ∂_x`, and the differentiated identities — are
formalized in `JacobiEstimates.lean`.  This file turns estimates of that shape
into a statement about the path pseudometric of `PathMetric.lean`.  As
everywhere in `PathMetric.lean`, the densities are those of the normalized
parameter: the `L¹` density is `∫₀¹ |η_t|` over one period of the normalized
parameter rather than over one period of arclength, and the estimates below are
assumed in that normalization — the `L¹` estimate in the form
`W(BΓ) ≤ C_W W(Γ)`, since passing from arclength to the normalized parameter
contributes the ratio of the two periods.

* `exists_normalPath_of_jacobi_data` : a family of rear curves whose normal
  velocities obey the four estimates *slice by slice*, against the cost density
  of the front path, is itself a normal path — one whose moving curve is that
  very family and whose cost density is `(C_W + C₀ + 2C₁ + 3C₂)` times that of
  the front path;
* `exists_normalPath_of_jacobi` : a family of rear curves whose normal
  velocities obey the four estimates *slice by slice*, against the cost density
  of the front path, is itself a normal path, with cost density
  `(C_W + C₀ + 2C₁ + 3C₂)` times that of the front path — hence of cost that many
  times the front's;
* `pathDist_le_of_jacobi` : consequently, a map of marked curves whose paths of
  images obey the estimates is Lipschitz for the path pseudodistance, with
  constant `C_W + C₀ + 2C₁ + 3C₂`.

What is *not* proved here (nor anywhere in this project) is that the selected
inverse does satisfy the hypotheses: that needs the paper's lemma *Smooth
dependence of the selected rear* — which is not formalized — and the estimates
in the normalization used here.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath

namespace PathMetricJacobi

/-- The Lipschitz constant produced by the inverse Jacobi estimates.  In the
paper the `L¹` estimate is an exact contraction, `CW = 1`; a constant is allowed
here because the `L¹` density is taken in the normalized parameter, in which the
change of period contributes the ratio of the two perimeters. -/
def jacobiConst (CW C0 C1 C2 : ℝ) : ℝ := CW + C0 + 2 * C1 + 3 * C2

theorem jacobiConst_nonneg {CW C0 C1 C2 : ℝ} (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hC2 : 0 ≤ C2) : 0 ≤ jacobiConst CW C0 C1 C2 := by unfold jacobiConst; linarith

/-- **The inverse Jacobi estimates produce a normal path.**  Let `Γ` be a normal
path of fronts and let `XR` be a family of curves joining `p'` to `q'` over the
same time interval, moving with normal velocity `etaR · nuR`.  If, at every
time, the four path densities of `etaR` obey the estimates of the paper's lemma
*Inverse Jacobi estimates* (in the normalized parameter) against the densities
of `Γ`, then `XR` is a normal path whose cost density is `1 + C₀ + 2C₁ + 3C₂` times that of `Γ`, hence whose
cost is that multiple of the cost of `Γ`. -/
theorem exists_normalPath_of_jacobi_data {p q p' q' : Data} (Γ : NormalPath p q)
    {CW C0 C1 C2 : ℝ} (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    {XR nuR : ℝ → ℝ → ℂ} {etaR : ℝ → ℝ → ℝ}
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t u : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t u : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hbdd : ∀ t u, |etaR t u| ≤ MarkedTopology.supNorm (etaR t))
    (hW : ∀ t, (∫ u in (0:ℝ)..1, |etaR t u|) ≤ CW * ∫ u in (0:ℝ)..1, |Γ.eta t u|)
    (hS0 : ∀ t, MarkedTopology.supNorm (etaR t) ≤ C0 * ∫ u in (0:ℝ)..1, |Γ.eta t u|)
    (hS1 : ∀ t, MarkedTopology.supNorm (iteratedDeriv 1 (etaR t))
      ≤ C1 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + MarkedTopology.supNorm (Γ.eta t)))
    (hS2 : ∀ t, MarkedTopology.supNorm (iteratedDeriv 2 (etaR t))
      ≤ C2 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + MarkedTopology.supNorm (Γ.eta t)
        + MarkedTopology.supNorm (iteratedDeriv 1 (Γ.eta t)))) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧ Δ.X = XR ∧
      (∀ t, Δ.m t = jacobiConst CW C0 C1 C2 * Γ.m t) ∧
      cost Δ = jacobiConst CW C0 C1 C2 * cost Γ := by
  set C := jacobiConst CW C0 C1 C2 with hCdef
  have hCval : C = CW + C0 + 2 * C1 + 3 * C2 := hCdef
  have hCnn : 0 ≤ C := jacobiConst_nonneg hCW hC0 hC1 hC2
  -- the front densities are all dominated by the front cost density
  have hWF : ∀ t, (∫ u in (0:ℝ)..1, |Γ.eta t u|) ≤ Γ.m t := Γ.le_m_L1
  have hS0F : ∀ t, MarkedTopology.supNorm (Γ.eta t) ≤ Γ.m t := by
    intro t
    simpa [iteratedDeriv_zero] using Γ.le_m_sup t 0 (by norm_num)
  have hS1F : ∀ t, MarkedTopology.supNorm (iteratedDeriv 1 (Γ.eta t)) ≤ Γ.m t :=
    fun t => Γ.le_m_sup t 1 (by norm_num)
  have hm : ∀ t, 0 ≤ Γ.m t := Γ.m_nonneg
  -- the rear densities are dominated by `C` times the front cost density
  have hS0R : ∀ t, MarkedTopology.supNorm (etaR t) ≤ C * Γ.m t := by
    intro t
    refine le_trans (hS0 t) ?_
    have h1 : C0 * (∫ u in (0:ℝ)..1, |Γ.eta t u|) ≤ C0 * Γ.m t :=
      mul_le_mul_of_nonneg_left (hWF t) hC0
    have h2 : C0 * Γ.m t ≤ C * Γ.m t := by
      refine mul_le_mul_of_nonneg_right ?_ (hm t)
      linarith [hCval]
    linarith
  have hS1R : ∀ t, MarkedTopology.supNorm (iteratedDeriv 1 (etaR t)) ≤ C * Γ.m t := by
    intro t
    refine le_trans (hS1 t) ?_
    have h1 : (∫ u in (0:ℝ)..1, |Γ.eta t u|) + MarkedTopology.supNorm (Γ.eta t)
        ≤ 2 * Γ.m t := by linarith [hWF t, hS0F t]
    have h2 : C1 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + MarkedTopology.supNorm (Γ.eta t))
        ≤ C1 * (2 * Γ.m t) := mul_le_mul_of_nonneg_left h1 hC1
    have h3 : C1 * (2 * Γ.m t) ≤ C * Γ.m t := by
      have : 2 * C1 ≤ C := by linarith [hCval]
      nlinarith [hm t]
    linarith
  have hS2R : ∀ t, MarkedTopology.supNorm (iteratedDeriv 2 (etaR t)) ≤ C * Γ.m t := by
    intro t
    refine le_trans (hS2 t) ?_
    have h1 : (∫ u in (0:ℝ)..1, |Γ.eta t u|) + MarkedTopology.supNorm (Γ.eta t)
        + MarkedTopology.supNorm (iteratedDeriv 1 (Γ.eta t)) ≤ 3 * Γ.m t := by
      linarith [hWF t, hS0F t, hS1F t]
    have h2 : C2 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + MarkedTopology.supNorm (Γ.eta t)
        + MarkedTopology.supNorm (iteratedDeriv 1 (Γ.eta t))) ≤ C2 * (3 * Γ.m t) :=
      mul_le_mul_of_nonneg_left h1 hC2
    have h3 : C2 * (3 * Γ.m t) ≤ C * Γ.m t := by
      have : 3 * C2 ≤ C := by linarith [hCval]
      nlinarith [hm t]
    linarith
  have hWR : ∀ t, (∫ u in (0:ℝ)..1, |etaR t u|) ≤ C * Γ.m t := by
    intro t
    refine le_trans (hW t) ?_
    have h1 : CW * (∫ u in (0:ℝ)..1, |Γ.eta t u|) ≤ CW * Γ.m t :=
      mul_le_mul_of_nonneg_left (hWF t) hCW
    have h2 : CW ≤ C := by linarith [hCval]
    nlinarith [hm t]
  refine ⟨{ T := Γ.T
            T_pos := Γ.T_pos
            X := XR
            eta := etaR
            nu := nuR
            m := fun t => C * Γ.m t
            start := hstart
            finish := hfinish
            hasDerivAt_time := hderiv
            cont_vel := hcont
            norm_nu := hnu
            cont_m := continuous_const.mul Γ.cont_m
            m_nonneg := fun t => mul_nonneg hCnn (hm t)
            m_stop := fun t ht => by rw [Γ.m_stop t ht, mul_zero]
            abs_eta_le := fun t u => le_trans (hbdd t u) (hS0R t)
            le_m_L1 := hWR
            le_m_sup := ?_ }, rfl, rfl, fun _ => rfl, ?_⟩
  · intro t j hj
    match j, hj with
    | 0, _ => simpa [iteratedDeriv_zero] using hS0R t
    | 1, _ => exact hS1R t
    | 2, _ => exact hS2R t
  · show (∫ t in (0:ℝ)..Γ.T, C * Γ.m t) = C * cost Γ
    rw [intervalIntegral.integral_const_mul]
    rfl

/-- **The inverse Jacobi estimates produce a normal path** (the form used
downstream, which only records the time interval and the cost). -/
theorem exists_normalPath_of_jacobi {p q p' q' : Data} (Γ : NormalPath p q)
    {CW C0 C1 C2 : ℝ} (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    {XR nuR : ℝ → ℝ → ℂ} {etaR : ℝ → ℝ → ℝ}
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t u : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t u : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hbdd : ∀ t u, |etaR t u| ≤ MarkedTopology.supNorm (etaR t))
    (hW : ∀ t, (∫ u in (0:ℝ)..1, |etaR t u|) ≤ CW * ∫ u in (0:ℝ)..1, |Γ.eta t u|)
    (hS0 : ∀ t, MarkedTopology.supNorm (etaR t) ≤ C0 * ∫ u in (0:ℝ)..1, |Γ.eta t u|)
    (hS1 : ∀ t, MarkedTopology.supNorm (iteratedDeriv 1 (etaR t))
      ≤ C1 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + MarkedTopology.supNorm (Γ.eta t)))
    (hS2 : ∀ t, MarkedTopology.supNorm (iteratedDeriv 2 (etaR t))
      ≤ C2 * ((∫ u in (0:ℝ)..1, |Γ.eta t u|) + MarkedTopology.supNorm (Γ.eta t)
        + MarkedTopology.supNorm (iteratedDeriv 1 (Γ.eta t)))) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧ cost Δ = jacobiConst CW C0 C1 C2 * cost Γ := by
  obtain ⟨Δ, hT, -, -, hcost⟩ := exists_normalPath_of_jacobi_data Γ hCW hC0 hC1 hC2
    hstart hfinish hderiv hcont hnu hbdd hW hS0 hS1 hS2
  exact ⟨Δ, hT, hcost⟩

/-- **A Lipschitz bound for the path pseudodistance from the inverse Jacobi
estimates.**  If a map of marked curves takes every normal path from `p` to `q`
to a normal path whose cost is at most `C_W + C₀ + 2C₁ + 3C₂` times as large — for
instance, by `exists_normalPath_of_jacobi`, if the images obey the four
estimates of the paper's lemma *Inverse Jacobi estimates* — then it is
Lipschitz with that constant for the path pseudodistance. -/
theorem pathDist_le_of_jacobi {F : Data → Data} {p q : Data} {CW C0 C1 C2 : ℝ}
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h : ∀ Γ : NormalPath p q, ∃ Δ : NormalPath (F p) (F q),
      cost Δ ≤ jacobiConst CW C0 C1 C2 * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ jacobiConst CW C0 C1 C2 * pathDist p q :=
  pathDist_le_mul_of_maps_paths (jacobiConst_nonneg hCW hC0 hC1 hC2) h hne

end PathMetricJacobi
