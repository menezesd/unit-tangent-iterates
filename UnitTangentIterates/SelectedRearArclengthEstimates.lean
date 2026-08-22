import Mathlib
import UnitTangentIterates.JacobiArclengthUniform

/-!
# The arclength Jacobi estimates of one slice, from its geometry

`JacobiNormalized.jacobi_estimates_normalized_of_geometry` derives the four
estimates of the paper's lemma *Inverse Jacobi estimates* — with **both** sides
in the normalized parameter — from the geometry of a single pair of front and
selected rear: the steering equation, the bounds `c ≤ cos δ`, `|sin δ| ≤ κ̂`,
the change of variable given by the rear arclength, and the inverse Jacobi ODE
`η_R' = G − η_R` for the rear normal velocity.

This file does the same for the shape the gauge machinery consumes: the rear
side is left in **its own arclength** and only the front is normalized, and the
constants are the uniform ones of `JacobiArclengthUniform.lean`, which depend on
the front period only through two-sided bounds `P₀ ≤ P ≤ P₁` and hence are the
same at every time of a path.

Main result: `jacobi_estimates_arclength_of_geometry`.
-/

noncomputable section

open MeasureTheory MarkedTopology

namespace SelectedRearArclengthEstimates

open JacobiNormalized JacobiArclengthUniform

/-- **The arclength Jacobi estimates of one slice, from its geometry.**

Same hypotheses as `JacobiNormalized.jacobi_estimates_normalized_of_geometry`,
except that the front period is only bounded two-sidedly by `P₀` and `P₁`; the
conclusion is the four estimates with the rear velocity in its own arclength,
the front velocity in its normalized parameter, and the uniform constants
`uarcW`, `uarc0`, `uarc1`, `uarc2`, which do not mention `P`. -/
theorem jacobi_estimates_arclength_of_geometry {l P P0 P1 l0 c kh : ℝ}
    {etaR etaF etaFs delta xf G dl sf K dxv : ℝ → ℝ}
    (hl0 : 0 < l0) (hll : l0 ≤ l) (hP0 : 0 < P0) (hPl : P0 ≤ P) (hPu : P ≤ P1)
    (hcpos : 0 < c)
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
    (∫ x in (0:ℝ)..l, |etaR x|) ≤ uarcW P1 * ∫ u in (0:ℝ)..1, |etaF (P * u)|
      ∧ supNorm etaR ≤ uarc0 P1 l0 * ∫ u in (0:ℝ)..1, |etaF (P * u)|
      ∧ supNorm (deriv etaR) ≤ uarc1 P1 l0 c * ((∫ u in (0:ℝ)..1, |etaF (P * u)|)
          + supNorm (fun u => etaF (P * u)))
      ∧ supNorm (deriv (deriv etaR)) ≤ uarc2 P0 P1 l0 c kh
          * ((∫ u in (0:ℝ)..1, |etaF (P * u)|) + supNorm (fun u => etaF (P * u))
            + supNorm (iteratedDeriv 1 fun u => etaF (P * u))) := by
  have hP : 0 < P := lt_of_lt_of_le hP0 hPl
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
  exact jacobi_estimates_arclength_uniform (etaR1 := deriv etaR)
    (etaR2 := deriv (deriv etaR)) (etaN := fun u => etaF (P * u))
    hP0 hPl hPu hl0 hcpos hR1 hR2 (supNorm_nonneg _) hW hS0 hS1 hS2 hnorm0 hnorm1
    (fun _ => rfl)

end SelectedRearArclengthEstimates
