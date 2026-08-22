import Mathlib
import UnitTangentIterates.PathMetricJacobi
import UnitTangentIterates.NormalPathC2IncrementVariableSpeed

/-!
# The inverse Jacobi estimates in the `C²` marked distance

`PathMetricJacobi.exists_normalPath_of_jacobi` turns the four inverse Jacobi
estimates into a normal path of rears whose cost is `jacobiConst` times the cost
of the path of fronts; `PathMetricJacobi.pathDist_le_of_jacobi` then reads that
as a Lipschitz bound *for the path pseudodistance*.  The path pseudodistance is
a weaker statement than the paper wants: what the comparison of the two selected
inverses needs is a bound for the marked (`C²`) distance of the two rear ends.

`NormalPathC2IncrementVariableSpeed.dist_le_cost_variableSpeed` supplies exactly
the missing step, and — unlike the constant-speed version — it applies to the
family of rear curves as it comes out of the Jacobi construction: the rears are
carried in the normalized parameter of the fronts, so their slices have a
variable speed, and the ends are not asked to be members of a tube.

* `exists_variableSpeed_normalPath_of_jacobi` : the normal path produced by the
  Jacobi estimates has variable-speed slices as soon as the family of rear
  curves does, against the *rescaled* cost density;
* `dist_le_of_jacobi_c2` : **the marked distance of the two rear ends is at most
  `c2ConstVar P₀ P₁ κ̂ G₁ C_g · jacobiConst C_W C₀ C₁ C₂ · cost Γ`**, where `Γ` is
  the path of fronts.

Both are stated for the geometric data of the rear family (`IsVariableSpeedFamily`)
taken against the rescaled density `jacobiConst · Γ.m`, which is the cost density
of the path the Jacobi estimates produce.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath
open PathMetricJacobi NormalPathC2IncrementVariableSpeed

namespace PathMetricJacobiC2

/-- **The normal path of rears produced by the inverse Jacobi estimates has
variable-speed slices**, as soon as the family of rear curves carries the
geometric data of such a family against the rescaled cost density. -/
theorem exists_variableSpeed_normalPath_of_jacobi {p q p' q' : Data} (Γ : NormalPath p q)
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
        + MarkedTopology.supNorm (iteratedDeriv 1 (Γ.eta t))))
    {P0 P1 khat G1 Cg : ℝ}
    (hvar : IsVariableSpeedFamily P0 P1 khat G1 Cg XR
      (fun t => jacobiConst CW C0 C1 C2 * Γ.m t)) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      IsVariableSpeedNormalPath P0 P1 khat G1 Cg Δ ∧
      cost Δ = jacobiConst CW C0 C1 C2 * cost Γ := by
  obtain ⟨Δ, hT, hX, hm, hcost⟩ := exists_normalPath_of_jacobi_data Γ hCW hC0 hC1 hC2
    hstart hfinish hderiv hcont hnu hbdd hW hS0 hS1 hS2
  refine ⟨Δ, hT, ?_, hcost⟩
  have hmeq : Δ.m = fun t => jacobiConst CW C0 C1 C2 * Γ.m t := funext hm
  rw [IsVariableSpeedNormalPath, hX, hmeq]
  exact hvar

/-- **The inverse Jacobi estimates in the `C²` marked distance.**  If the family
of rear curves obeys the four estimates of the paper's lemma *Inverse Jacobi
estimates* against the densities of the path of fronts, and carries the
geometric data of a family of variable speed against the rescaled cost density,
then the marked distance of the two rear ends is at most
`c2ConstVar P₀ P₁ κ̂ G₁ C_g` times `jacobiConst C_W C₀ C₁ C₂ · cost Γ`.

Neither rear end has to be a member of a tube: only that its velocity and
acceleration components are the derivatives of its curve, which is what makes it
a marked datum.  This is the `C²` upgrade of `pathDist_le_of_jacobi`. -/
theorem dist_le_of_jacobi_c2 {p q p' q' : Data} (Γ : NormalPath p q)
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
        + MarkedTopology.supNorm (iteratedDeriv 1 (Γ.eta t))))
    {P0 P1 khat G1 Cg : ℝ}
    (hvar : IsVariableSpeedFamily P0 P1 khat G1 Cg XR
      (fun t => jacobiConst CW C0 C1 C2 * Γ.m t))
    (hpd : ∀ u, HasDerivAt (⇑p'.1) (p'.2.1 u) u) (hqd : ∀ u, HasDerivAt (⇑q'.1) (q'.2.1 u) u)
    (hpv : ∀ u, HasDerivAt (⇑p'.2.1) (p'.2.2 u) u)
    (hqv : ∀ u, HasDerivAt (⇑q'.2.1) (q'.2.2 u) u) :
    dist p' q' ≤ c2ConstVar P0 P1 khat G1 Cg * (jacobiConst CW C0 C1 C2 * cost Γ) := by
  obtain ⟨Δ, -, hvarΔ, hcost⟩ := exists_variableSpeed_normalPath_of_jacobi Γ hCW hC0 hC1 hC2
    hstart hfinish hderiv hcont hnu hbdd hW hS0 hS1 hS2 hvar
  have h := dist_le_cost_variableSpeed Δ hpd hqd hpv hqv hvarΔ
  rwa [hcost] at h

end PathMetricJacobiC2
