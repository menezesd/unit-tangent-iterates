import Mathlib
import UnitTangentIterates.JacobiNormalized
import UnitTangentIterates.PathMetricJacobi

/-!
# From the inverse Jacobi estimates to a normal path of selected rears

`UnitTangentIterates/PathMetricJacobi.lean` shows that a family of rear curves whose
normal velocities obey the four estimates of the paper's lemma *Inverse Jacobi
estimates* — *in the normalized parameter*, slice by slice — is a normal path
whose cost is a fixed multiple of the cost of the front path, hence that the
selected inverse is Lipschitz for the path pseudodistance.  Those four
estimates were assumed there.  `UnitTangentIterates/JacobiAssembly.lean` proves them
in arclength, and `UnitTangentIterates/JacobiNormalized.lean` converts them to the
normalized parameter.

This file performs the composition: from the *geometric* hypotheses of the
paper's proof, holding at every time of the path — the inverse Jacobi identity
`η_R' = G - η_R` for the transported front velocity `G = sec δ · η_F ∘ sf`, the
selected-strip bounds `cos δ ≥ c > 0` and `|sin δ|, |K| ≤ κ̂`, and the
arclength change of variables `dx = cos δ ds` — together with uniform bounds
for the constants of `JacobiNormalized`, the rear family is a normal path of
cost `(C_W + C₀ + 2C₁ + 3C₂)` times that of the front path.

* `exists_normalPath_of_selected_rears` — the normal path of rears and its
  cost;
* `pathDist_le_of_selected_rears` — the resulting Lipschitz bound for the path
  pseudodistance, when every normal path from `p` to `q` admits such a family
  of rears.

What is still assumed — and is not proved anywhere in this project — is that
the selected rears of a path of fronts do form such a family: that is the
paper's lemma *Smooth dependence of the selected rear*.
-/

noncomputable section

open Set MeasureTheory MarkedSpace PathMetric PathMetric.NormalPath MarkedTopology

namespace SelectedInverseLipschitz

/-- **The selected rears of a normal path of fronts form a normal path.**  The
hypotheses are, at every time `t`, those of
`JacobiNormalized.jacobi_estimates_normalized_of_geometry` for the front
velocity `etaF t` of period `P t` and the rear velocity `etaR t` of period
`l t`, the identification `Γ.eta t u = etaF t (P t · u)` of the front normal
velocity with the velocity of the given normal path, uniform bounds for the
four constants, and the structural data of the rear family (its curves `XR`,
unit normals `nuR` and endpoints). -/
theorem exists_normalPath_of_selected_rears {p q p' q' : Data} (Γ : NormalPath p q)
    {l0 c kh CW C0 C1 C2 : ℝ} {P l : ℝ → ℝ}
    {etaF etaFs etaR delta xf G dl sf K dxv : ℝ → ℝ → ℝ}
    {XR : ℝ → ℝ → ℂ} {nuR : ℝ → ℝ → ℂ}
    (hl0 : 0 < l0) (hcpos : 0 < c)
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    -- the geometric hypotheses at every time
    (hll : ∀ t, l0 ≤ l t) (hP : ∀ t, 0 < P t)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hFbdd : ∀ t, BddAbove (Set.range fun s => |etaF t s|))
    (hF1bdd : ∀ t, BddAbove (Set.range fun s => |etaFs t s|))
    (hK : ∀ t s, |K t s| ≤ kh)
    (hdelta : ∀ t, Continuous (delta t)) (hcos : ∀ t s, 0 < Real.cos (delta t s))
    (hdlcos : ∀ t x, c ≤ Real.cos (dl t x)) (hdlsin : ∀ t x, |Real.sin (dl t x)| ≤ kh)
    (hsf : ∀ t x, HasDerivAt (sf t) (1 / Real.cos (dl t x)) x)
    (hdl : ∀ t x, HasDerivAt (dl t) (dxv t x) x)
    (hdxv : ∀ t x, dxv t x = (K t (sf t x) - Real.sin (dl t x)) / Real.cos (dl t x))
    (hxf : ∀ t s, HasDerivAt (xf t) (Real.cos (delta t s)) s)
    (hx0 : ∀ t, xf t 0 = 0) (hxP : ∀ t, xf t (P t) = l t)
    (hGdef : ∀ t, G t = fun y => etaF t (sf t y) / Real.cos (dl t y))
    (hGcont : ∀ t, Continuous (G t)) (hGper : ∀ t, Function.Periodic (G t) (l t))
    (hetaR : ∀ t x, HasDerivAt (etaR t) (G t x - etaR t x) x)
    (hetaRper : ∀ t, Function.Periodic (etaR t) (l t))
    (htransport : ∀ t s, G t (xf t s) * Real.cos (delta t s) = etaF t s)
    -- the front velocity of the given path, in arclength
    (hlink : ∀ t u, Γ.eta t u = etaF t (P t * u))
    -- uniform bounds for the constants
    (hcW : ∀ t, JacobiNormalized.constW (P t) (l t) ≤ CW)
    (hc0 : ∀ t, JacobiNormalized.const0 (P t) l0 ≤ C0)
    (hc1 : ∀ t, JacobiNormalized.const1 (P t) (l t) l0 c ≤ C1)
    (hc2 : ∀ t, JacobiNormalized.const2 (P t) (l t) l0 c kh ≤ C2)
    -- the structural data of the rear family
    (hstart : ∀ u, XR 0 u = p'.1 u) (hfinish : ∀ u, XR Γ.T u = q'.1 u)
    (hderiv : ∀ t u, HasDerivAt (fun r => XR r u) ((etaR t (l t * u) : ℂ) * nuR t u) t)
    (hcont : ∀ u, Continuous fun t => (etaR t (l t * u) : ℂ) * nuR t u)
    (hnu : ∀ t u, ‖nuR t u‖ = 1)
    (hRbdd : ∀ t, BddAbove (Set.range fun u => |etaR t (l t * u)|)) :
    ∃ Δ : NormalPath p' q', Δ.T = Γ.T ∧
      cost Δ = PathMetricJacobi.jacobiConst CW C0 C1 C2 * cost Γ := by
  -- the per-slice estimates in the normalized parameter
  have hslice := fun t =>
    JacobiNormalized.jacobi_estimates_normalized_of_geometry (l := l t) (P := P t) (l0 := l0)
      (c := c) (kh := kh) (etaR := etaR t) (etaF := etaF t) (etaFs := etaFs t)
      (delta := delta t) (xf := xf t) (G := G t) (dl := dl t) (sf := sf t) (K := K t)
      (dxv := dxv t) hl0 (hll t) (hP t) hcpos (hetaFd t) (hFbdd t) (hF1bdd t) (hK t)
      (hdelta t) (hcos t) (hdlcos t) (hdlsin t) (hsf t) (hdl t) (hdxv t) (hxf t) (hx0 t)
      (hxP t) (hGdef t) (hGcont t) (hGper t) (hetaR t) (hetaRper t) (htransport t)
  -- rewrite the front densities in terms of the given path
  have hL1 : ∀ t, (∫ u in (0:ℝ)..1, |etaF t (P t * u)|) = ∫ u in (0:ℝ)..1, |Γ.eta t u| := by
    intro t
    exact intervalIntegral.integral_congr (fun u _ => by rw [hlink t u])
  have hsup0 : ∀ t, supNorm (fun u => etaF t (P t * u)) = supNorm (Γ.eta t) := by
    intro t
    have : (fun u => etaF t (P t * u)) = Γ.eta t := funext fun u => (hlink t u).symm
    rw [this]
  have hsup1 : ∀ t, supNorm (iteratedDeriv 1 fun u => etaF t (P t * u))
      = supNorm (iteratedDeriv 1 (Γ.eta t)) := by
    intro t
    have : (fun u => etaF t (P t * u)) = Γ.eta t := funext fun u => (hlink t u).symm
    rw [this]
  have hL1_nonneg : ∀ t, 0 ≤ ∫ u in (0:ℝ)..1, |Γ.eta t u| := fun t =>
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _)
  refine PathMetricJacobi.exists_normalPath_of_jacobi Γ hCW hC0 hC1 hC2
    (etaR := fun t u => etaR t (l t * u)) (nuR := nuR) (XR := XR)
    hstart hfinish hderiv hcont hnu ?_ ?_ ?_ ?_ ?_
  · intro t u
    exact le_supNorm (hRbdd t) u
  · intro t
    obtain ⟨h1, -, -, -⟩ := hslice t
    rw [hL1 t] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hcW t) (hL1_nonneg t))
  · intro t
    obtain ⟨-, h2, -, -⟩ := hslice t
    rw [hL1 t] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right (hc0 t) (hL1_nonneg t))
  · intro t
    obtain ⟨-, -, h3, -⟩ := hslice t
    rw [hL1 t, hsup0 t] at h3
    refine h3.trans (mul_le_mul_of_nonneg_right (hc1 t) ?_)
    have := supNorm_nonneg (Γ.eta t)
    linarith [hL1_nonneg t]
  · intro t
    obtain ⟨-, -, -, h4⟩ := hslice t
    rw [hL1 t, hsup0 t, hsup1 t] at h4
    refine h4.trans (mul_le_mul_of_nonneg_right (hc2 t) ?_)
    have h5 := supNorm_nonneg (Γ.eta t)
    have h6 := supNorm_nonneg (iteratedDeriv 1 (Γ.eta t))
    linarith [hL1_nonneg t]

/-- A check that the hypotheses of `exists_normalPath_of_selected_rears` are
not contradictory: the constant path of fronts, with vanishing steering angle,
front and rear arclength equal and vanishing normal velocities, satisfies them
all. -/
example (p p' : Data) :
    ∃ Δ : NormalPath p' p', Δ.T = (NormalPath.const p).T ∧
      cost Δ = PathMetricJacobi.jacobiConst (JacobiNormalized.constW 1 1)
        (JacobiNormalized.const0 1 1) (JacobiNormalized.const1 1 1 1 1)
        (JacobiNormalized.const2 1 1 1 1 0) * cost (NormalPath.const p) := by
  have hbdd : ∀ f : ℝ → ℝ, (∀ x, f x = 0) → BddAbove (Set.range fun x => |f x|) := by
    intro f hf
    refine ⟨0, ?_⟩
    rintro x ⟨s, rfl⟩
    simp [hf s]
  refine exists_normalPath_of_selected_rears (p' := p') (q' := p') (NormalPath.const p)
    (l0 := 1) (c := 1) (kh := 0) (P := fun _ => 1) (l := fun _ => 1)
    (etaF := fun _ _ => 0) (etaFs := fun _ _ => 0) (etaR := fun _ _ => 0)
    (delta := fun _ _ => 0) (xf := fun _ y => y) (G := fun _ _ => 0)
    (dl := fun _ _ => 0) (sf := fun _ y => y) (K := fun _ _ => 0) (dxv := fun _ _ => 0)
    (XR := fun _ u => p'.1 u) (nuR := fun _ _ => 1)
    one_pos one_pos
    (JacobiNormalized.constW_nonneg one_pos one_pos)
    (JacobiNormalized.const0_nonneg one_pos one_pos)
    (JacobiNormalized.const1_nonneg one_pos one_pos one_pos one_pos)
    (JacobiNormalized.const2_nonneg one_pos one_pos one_pos one_pos)
    (fun _ => le_refl 1) (fun _ => one_pos)
    (fun _ s => hasDerivAt_const s 0)
    (fun _ => hbdd _ (fun _ => rfl)) (fun _ => hbdd _ (fun _ => rfl))
    (fun _ _ => by norm_num)
    (fun _ => continuous_const) (fun _ _ => by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ x => by simpa using hasDerivAt_id x)
    (fun _ x => hasDerivAt_const x 0)
    (fun _ _ => by norm_num)
    (fun _ s => by simpa using hasDerivAt_id s) (fun _ => rfl) (fun _ => rfl)
    (fun _ => by funext y; norm_num)
    (fun _ => continuous_const) (fun _ => fun _ => rfl)
    (fun _ x => by simpa using hasDerivAt_const x (0:ℝ))
    (fun _ => fun _ => rfl)
    (fun _ _ => by norm_num)
    (fun _ _ => rfl)
    (fun _ => le_refl _) (fun _ => le_refl _) (fun _ => le_refl _) (fun _ => le_refl _)
    (fun _ => rfl) (fun _ => rfl)
    (fun t u => by simpa using hasDerivAt_const t (p'.1 u))
    (fun _ => by simpa using continuous_const)
    (fun _ _ => by simp)
    (fun _ => hbdd _ (fun _ => rfl))

/-- **The Lipschitz bound for the path pseudodistance.**  If every normal path
from `p` to `q` admits a family of selected rears in the sense of
`exists_normalPath_of_selected_rears`, the selected inverse is Lipschitz for
the path pseudodistance with constant `C_W + C₀ + 2C₁ + 3C₂`. -/
theorem pathDist_le_of_selected_rears {F : Data → Data} {p q : Data} {CW C0 C1 C2 : ℝ}
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h : ∀ Γ : NormalPath p q, ∃ Δ : NormalPath (F p) (F q),
      cost Δ ≤ PathMetricJacobi.jacobiConst CW C0 C1 C2 * cost Γ)
    (hne : Nonempty (NormalPath p q)) :
    pathDist (F p) (F q) ≤ PathMetricJacobi.jacobiConst CW C0 C1 C2 * pathDist p q :=
  PathMetricJacobi.pathDist_le_of_jacobi hCW hC0 hC1 hC2 h hne

end SelectedInverseLipschitz
