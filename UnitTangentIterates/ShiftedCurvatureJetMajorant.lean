import Mathlib
import UnitTangentIterates.PulseFromCurvature
import UnitTangentIterates.PaperHairpinConfig

/-!
# Relative majorants for finite shifted curvature jets

This file contains the algebraic estimate engine used after differentiating
the shifted curvature equation

`K' = A(K) (K o sigma) - K - K^3`.

It intentionally does not state a derivative identity.  Instead, corrected
order-three and order-four identities can be decomposed into sums, products,
bounded coefficient functions, and shifted lower derivatives; the lemmas
below turn that decomposition into a relative bound `|F| <= C K`.
-/

noncomputable section

open Real
open PaperHairpinConfig

namespace ShiftedCurvatureJetMajorant

/-! ### Canonical higher pulse derivatives -/

/-- The third front-arclength pulse derivative, canonically defined from the
explicit second derivative. -/
def pulseDDD (K K1 K2 x : ℝ → ℝ) : ℝ → ℝ := fun s =>
  deriv (PulseFromCurvature.pulseDD K K1 K2 x) s

/-- Expanded third pulse derivative after the rear/front arclength change. -/
def pulseDDDExpanded (K K1 K2 K3 x : ℝ → ℝ) : ℝ → ℝ := fun s =>
  let k := K (x s)
  let k1 := K1 (x s)
  let k2 := K2 (x s)
  let k3 := K3 (x s)
  let q := 1 + k ^ 2
  k3 / q ^ 3 - (13 * k * k1 * k2 + 4 * k1 ^ 3) / q ^ 4
    + 28 * k ^ 2 * k1 ^ 3 / q ^ 5

/-- Explicit relative constant for the expanded third pulse derivative. -/
def pulseThirdConstant (B D1 D2 D3 : ℝ) : ℝ :=
  D3 + 13 * B ^ 2 * D1 * D2 + 4 * B ^ 2 * D1 ^ 3
    + 28 * B ^ 4 * D1 ^ 3

theorem pulseThirdConstant_nonneg
    (hB : 0 ≤ B) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) :
    0 ≤ pulseThirdConstant B D1 D2 D3 := by
  dsimp [pulseThirdConstant]
  positivity

/-- A curvature jet through order three and a differentiable inverse
coordinate make `pulseDDD` the actual derivative of `pulseDD`. -/
theorem hasDerivAt_pulseDD_pulseDDD
    {K K1 K2 K3 x xd : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hx : ∀ s, HasDerivAt x (xd s) s) (s : ℝ) :
    HasDerivAt (PulseFromCurvature.pulseDD K K1 K2 x)
      (pulseDDD K K1 K2 x s) s := by
  have hd : DifferentiableAt ℝ (PulseFromCurvature.pulseDD K K1 K2 x) s := by
    have hxd : DifferentiableAt ℝ x s := (hx s).differentiableAt
    have hKx : DifferentiableAt ℝ (fun t => K (x t)) s :=
      ((hK (x s)).differentiableAt).comp s hxd
    have hK1x : DifferentiableAt ℝ (fun t => K1 (x t)) s :=
      ((hK1 (x s)).differentiableAt).comp s hxd
    have hK2x : DifferentiableAt ℝ (fun t => K2 (x t)) s :=
      ((hK2 (x s)).differentiableAt).comp s hxd
    have hq : DifferentiableAt ℝ (fun t => 1 + K (x t) ^ 2) s :=
      (differentiableAt_const (1 : ℝ)).add (hKx.pow 2)
    have hqpos : (0:ℝ) < 1 + K (x s) ^ 2 := by positivity
    have hsq : DifferentiableAt ℝ (fun t => Real.sqrt (1 + K (x t) ^ 2)) s :=
      ((Real.hasDerivAt_sqrt hqpos.ne').differentiableAt).comp s hq
    have hd2ne : Real.sqrt (1 + K (x s) ^ 2) * (1 + K (x s) ^ 2) ^ 2 ≠ 0 := by
      positivity
    have hd3ne : Real.sqrt (1 + K (x s) ^ 2) * (1 + K (x s) ^ 2) ^ 3 ≠ 0 := by
      positivity
    show DifferentiableAt ℝ (fun t =>
      K2 (x t) / (Real.sqrt (1 + K (x t) ^ 2) * (1 + K (x t) ^ 2) ^ 2)
        - 4 * K (x t) * K1 (x t) ^ 2 /
          (Real.sqrt (1 + K (x t) ^ 2) * (1 + K (x t) ^ 2) ^ 3)) s
    exact (hK2x.div (hsq.mul (hq.pow 2)) hd2ne).sub
      ((((differentiableAt_const (4 : ℝ)).mul hKx).mul (hK1x.pow 2)).div
        (hsq.mul (hq.pow 3)) hd3ne)
  simpa [pulseDDD] using hd.hasDerivAt

/-- The derivative of `x ↦ 1 + x²`. -/
private theorem hasDerivAt_one_add_sq (k : ℝ) :
    HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * k) k := by
  refine ((hasDerivAt_const k (1 : ℝ)).add ((hasDerivAt_id k).pow 2)).congr_deriv ?_
  norm_num

/-- The derivative of `x ↦ √(1 + x²)`. -/
private theorem hasDerivAt_sqrt_one_add_sq (k : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (k / Real.sqrt (1 + k ^ 2)) k := by
  have hpos : (0:ℝ) < 1 + k ^ 2 := by positivity
  have hs : Real.sqrt (1 + k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  refine ((Real.hasDerivAt_sqrt hpos.ne').comp k (hasDerivAt_one_add_sq k)).congr_deriv ?_
  field_simp

/-- The fourth front-arclength pulse derivative. -/
def pulseDDDD (K K1 K2 x : ℝ → ℝ) : ℝ → ℝ := fun s =>
  deriv (pulseDDD K K1 K2 x) s

/-- Differentiability of the canonical third pulse derivative identifies its
derivative with `pulseDDDD`. -/
theorem hasDerivAt_pulseDDD_pulseDDDD
    {K K1 K2 x : ℝ → ℝ}
    (h : Differentiable ℝ (pulseDDD K K1 K2 x)) (s : ℝ) :
    HasDerivAt (pulseDDD K K1 K2 x)
      (pulseDDDD K K1 K2 x s) s := by
  simpa [pulseDDDD] using (h s).hasDerivAt

/-! ### Canonical finite differentiated identities -/

/-- The exact right-hand side of the second differentiated shifted-curvature
equation. -/
def secondRhs (K K1 sigma : ℝ → ℝ) : ℝ → ℝ := fun u =>
  (3 * K u * Real.sqrt (1 + K u ^ 2) * K1 u) * K (sigma u)
    + ((1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2)) *
        (K1 (sigma u) * Real.sqrt (1 + K u ^ 2))
    - K1 u - 3 * K u ^ 2 * K1 u

/-- The canonical third-order right-hand side is the derivative of the exact
second-order expression.  Keeping it in this form prevents transcription
errors in a hand-expanded formula. -/
def thirdRhs (K K1 sigma : ℝ → ℝ) : ℝ → ℝ := fun u =>
  deriv (secondRhs K K1 sigma) u

/-- The canonical fourth-order right-hand side. -/
def fourthRhs (K K1 sigma : ℝ → ℝ) : ℝ → ℝ := fun u =>
  deriv (thirdRhs K K1 sigma) u

/-- Named coefficient fields for the normalized differentiated equation.
`v1,v2` and `a1,a2,a3` are derivatives with respect to the scalar curvature
argument, not arclength derivatives. -/
structure CoefficientJet where
  v : ℝ → ℝ
  v1 : ℝ → ℝ
  v2 : ℝ → ℝ
  a : ℝ → ℝ
  a1 : ℝ → ℝ
  a2 : ℝ → ℝ
  a3 : ℝ → ℝ

/-- The named coefficient functions form an actual derivative jet. -/
structure CoefficientJet.IsDerivativeJet (c : CoefficientJet) : Prop where
  dv : ∀ k, HasDerivAt c.v (c.v1 k) k
  dv1 : ∀ k, HasDerivAt c.v1 (c.v2 k) k
  da : ∀ k, HasDerivAt c.a (c.a1 k) k
  da1 : ∀ k, HasDerivAt c.a1 (c.a2 k) k
  da2 : ∀ k, HasDerivAt c.a2 (c.a3 k) k

/-- The completely normalized order-three expression. -/
def thirdExpanded (c : CoefficientJet) (K K1 K2 sigma : ℝ → ℝ) : ℝ → ℝ := fun u =>
  (c.a2 (K u) * K1 u ^ 2 + c.a1 (K u) * K2 u) * K (sigma u)
    + 2 * c.a1 (K u) * K1 u * K1 (sigma u) * c.v (K u)
    + c.a (K u) * K2 (sigma u) * c.v (K u) ^ 2
    + c.a (K u) * K1 (sigma u) * (c.v1 (K u) * K1 u)
    - 6 * K u * K1 u ^ 2 - (1 + 3 * K u ^ 2) * K2 u

/-- The normalized second-order expression from which `thirdExpanded` is
obtained by one structural differentiation. -/
def secondExpanded (c : CoefficientJet) (K K1 sigma : ℝ → ℝ) : ℝ → ℝ := fun u =>
  c.a1 (K u) * K1 u * K (sigma u)
    + c.a (K u) * K1 (sigma u) * c.v (K u)
    - K1 u - 3 * K u ^ 2 * K1 u

/-- The completely normalized order-four expression, obtained by
differentiating `thirdExpanded` term by term. -/
def fourthExpanded (c : CoefficientJet)
    (K K1 K2 K3 sigma : ℝ → ℝ) : ℝ → ℝ := fun u =>
  (c.a3 (K u) * K1 u ^ 3
      + 3 * c.a2 (K u) * K1 u * K2 u
      + c.a1 (K u) * K3 u) * K (sigma u)
    + (c.a2 (K u) * K1 u ^ 2 + c.a1 (K u) * K2 u) *
        K1 (sigma u) * c.v (K u)
    + 2 * (c.a2 (K u) * K1 u ^ 2 + c.a1 (K u) * K2 u) *
        K1 (sigma u) * c.v (K u)
    + 2 * c.a1 (K u) * K1 u * K2 (sigma u) * c.v (K u) ^ 2
    + 2 * c.a1 (K u) * K1 u * K1 (sigma u) *
        (c.v1 (K u) * K1 u)
    + c.a1 (K u) * K1 u * K2 (sigma u) * c.v (K u) ^ 2
    + c.a (K u) * K3 (sigma u) * c.v (K u) ^ 3
    + 2 * c.a (K u) * K2 (sigma u) * c.v (K u) *
        (c.v1 (K u) * K1 u)
    + c.a1 (K u) * K1 u * K1 (sigma u) * (c.v1 (K u) * K1 u)
    + c.a (K u) * K2 (sigma u) * c.v (K u) *
        (c.v1 (K u) * K1 u)
    + c.a (K u) * K1 (sigma u) *
        (c.v2 (K u) * K1 u ^ 2 + c.v1 (K u) * K2 u)
    - 6 * K1 u ^ 3 - 18 * K u * K1 u * K2 u
    - (1 + 3 * K u ^ 2) * K3 u

/-- The coefficient jet for `v(k)=sqrt(1+k^2)` and
`a(k)=(1+k^2)sqrt(1+k^2)`. -/
def curvatureCoefficientJet : CoefficientJet where
  v := fun k => Real.sqrt (1 + k ^ 2)
  v1 := fun k => k / Real.sqrt (1 + k ^ 2)
  v2 := fun k => 1 / (Real.sqrt (1 + k ^ 2)) ^ 3
  a := fun k => (1 + k ^ 2) * Real.sqrt (1 + k ^ 2)
  a1 := fun k => 3 * k * Real.sqrt (1 + k ^ 2)
  a2 := fun k => 3 * Real.sqrt (1 + k ^ 2)
    + 3 * k ^ 2 / Real.sqrt (1 + k ^ 2)
  a3 := fun k => 9 * k / Real.sqrt (1 + k ^ 2)
    - 3 * k ^ 3 / (Real.sqrt (1 + k ^ 2)) ^ 3

/-- The concrete square-root/amplitude coefficients form the asserted
derivative jet. -/
theorem curvatureCoefficientJet_isDerivativeJet :
    curvatureCoefficientJet.IsDerivativeJet := by
  constructor <;> intro k <;> dsimp [curvatureCoefficientJet]
  · exact hasDerivAt_sqrt_one_add_sq k
  · have hpos : (0:ℝ) < 1 + k ^ 2 := by positivity
    have hs : Real.sqrt (1 + k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hsq : Real.sqrt (1 + k ^ 2) ^ 2 = 1 + k ^ 2 := Real.sq_sqrt hpos.le
    refine ((hasDerivAt_id k).div (hasDerivAt_sqrt_one_add_sq k) hs).congr_deriv ?_
    field_simp
    simp only [id_eq]
    linear_combination hsq
  · have hpos : (0:ℝ) < 1 + k ^ 2 := by positivity
    have hs : Real.sqrt (1 + k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hsq : Real.sqrt (1 + k ^ 2) ^ 2 = 1 + k ^ 2 := Real.sq_sqrt hpos.le
    refine ((hasDerivAt_one_add_sq k).mul (hasDerivAt_sqrt_one_add_sq k)).congr_deriv ?_
    field_simp
    linear_combination (-k) * hsq
  · have hpos : (0:ℝ) < 1 + k ^ 2 := by positivity
    have hs : Real.sqrt (1 + k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hsq : Real.sqrt (1 + k ^ 2) ^ 2 = 1 + k ^ 2 := Real.sq_sqrt hpos.le
    refine (((hasDerivAt_const k (3 : ℝ)).mul (hasDerivAt_id k)).mul
      (hasDerivAt_sqrt_one_add_sq k)).congr_deriv ?_
    field_simp
    simp only [Pi.mul_apply, id_eq]
    ring
  · have hpos : (0:ℝ) < 1 + k ^ 2 := by positivity
    have hs : Real.sqrt (1 + k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hsq : Real.sqrt (1 + k ^ 2) ^ 2 = 1 + k ^ 2 := Real.sq_sqrt hpos.le
    have hquot : HasDerivAt (fun x : ℝ => 3 * x ^ 2 / Real.sqrt (1 + x ^ 2))
        ((3 * (2 * k) * Real.sqrt (1 + k ^ 2)
            - 3 * k ^ 2 * (k / Real.sqrt (1 + k ^ 2))) /
          Real.sqrt (1 + k ^ 2) ^ 2) k := by
      refine (((hasDerivAt_const k (3 : ℝ)).mul ((hasDerivAt_id k).pow 2)).div
        (hasDerivAt_sqrt_one_add_sq k) hs).congr_deriv ?_
      norm_num
    refine (((hasDerivAt_const k (3 : ℝ)).mul
      (hasDerivAt_sqrt_one_add_sq k)).add hquot).congr_deriv ?_
    field_simp
    ring

/-- Structural product/chain-rule verification of the normalized fourth-order
expression. -/
theorem hasDerivAt_thirdExpanded (c : CoefficientJet)
    (hc : c.IsDerivativeJet) {K K1 K2 K3 K4 sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3 : ∀ u, HasDerivAt K3 (K4 u) u)
    (hsigma : ∀ u, HasDerivAt sigma (c.v (K u)) u) (u : ℝ) :
    HasDerivAt (thirdExpanded c K K1 K2 sigma)
      (fourthExpanded c K K1 K2 K3 sigma u) u := by
  have hKu : HasDerivAt K (K1 u) u := hK u
  have hK1u : HasDerivAt K1 (K2 u) u := hK1 u
  have hK2u : HasDerivAt K2 (K3 u) u := hK2 u
  have haK : HasDerivAt (fun t => c.a (K t)) (c.a1 (K u) * K1 u) u :=
    (hc.da (K u)).comp u hKu
  have ha1K : HasDerivAt (fun t => c.a1 (K t)) (c.a2 (K u) * K1 u) u :=
    (hc.da1 (K u)).comp u hKu
  have ha2K : HasDerivAt (fun t => c.a2 (K t)) (c.a3 (K u) * K1 u) u :=
    (hc.da2 (K u)).comp u hKu
  have hvK : HasDerivAt (fun t => c.v (K t)) (c.v1 (K u) * K1 u) u :=
    (hc.dv (K u)).comp u hKu
  have hv1K : HasDerivAt (fun t => c.v1 (K t)) (c.v2 (K u) * K1 u) u :=
    (hc.dv1 (K u)).comp u hKu
  have hKs : HasDerivAt (fun t => K (sigma t)) (K1 (sigma u) * c.v (K u)) u :=
    (hK (sigma u)).comp u (hsigma u)
  have hK1s : HasDerivAt (fun t => K1 (sigma t)) (K2 (sigma u) * c.v (K u)) u :=
    (hK1 (sigma u)).comp u (hsigma u)
  have hK2s : HasDerivAt (fun t => K2 (sigma t)) (K3 (sigma u) * c.v (K u)) u :=
    (hK2 (sigma u)).comp u (hsigma u)
  have h1 := ((ha2K.mul (hK1u.pow 2)).add (ha1K.mul hK2u)).mul hKs
  have h2 := ((((hasDerivAt_const u (2 : ℝ)).mul ha1K).mul hK1u).mul hK1s).mul hvK
  have h3 := (haK.mul hK2s).mul (hvK.pow 2)
  have h4 := (haK.mul hK1s).mul (hv1K.mul hK1u)
  have h5 := ((hasDerivAt_const u (6 : ℝ)).mul hKu).mul (hK1u.pow 2)
  have h6 := ((hasDerivAt_const u (1 : ℝ)).add
    ((hasDerivAt_const u (3 : ℝ)).mul (hKu.pow 2))).mul hK2u
  refine ((((h1.add h2).add h3).add h4).sub h5).sub h6 |>.congr_deriv ?_
  dsimp [fourthExpanded]
  ring

/-- Structural verification of the normalized third-order expression. -/
theorem hasDerivAt_secondExpanded (c : CoefficientJet)
    (hc : c.IsDerivativeJet) {K K1 K2 sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hsigma : ∀ u, HasDerivAt sigma (c.v (K u)) u) (u : ℝ) :
    HasDerivAt (secondExpanded c K K1 sigma)
      (thirdExpanded c K K1 K2 sigma u) u := by
  have hKu : HasDerivAt K (K1 u) u := hK u
  have haK : HasDerivAt (fun t => c.a (K t)) (c.a1 (K u) * K1 u) u :=
    (hc.da (K u)).comp u hKu
  have ha1K : HasDerivAt (fun t => c.a1 (K t)) (c.a2 (K u) * K1 u) u :=
    (hc.da1 (K u)).comp u hKu
  have hvK : HasDerivAt (fun t => c.v (K t)) (c.v1 (K u) * K1 u) u :=
    (hc.dv (K u)).comp u hKu
  have hKs : HasDerivAt (fun t => K (sigma t)) (K1 (sigma u) * c.v (K u)) u :=
    (hK (sigma u)).comp u (hsigma u)
  have hK1s : HasDerivAt (fun t => K1 (sigma t)) (K2 (sigma u) * c.v (K u)) u :=
    (hK1 (sigma u)).comp u (hsigma u)
  have h1 := (ha1K.mul (hK1 u)).mul hKs
  have h2 := (haK.mul hK1s).mul hvK
  have h4 := ((hasDerivAt_const u (3 : ℝ)).mul (hKu.pow 2)).mul (hK1 u)
  refine (((h1.add h2).sub (hK1 u)).sub h4).congr_deriv ?_
  push_cast
  dsimp [thirdExpanded]
  ring

/-- The concrete normalized second-order expression is definitionally the
canonical `secondRhs`. -/
theorem secondExpanded_curvature_eq (K K1 sigma : ℝ → ℝ) :
    secondExpanded curvatureCoefficientJet K K1 sigma = secondRhs K K1 sigma := by
  funext u
  dsimp [secondExpanded, secondRhs, curvatureCoefficientJet]
  ring

/-- Once the concrete coefficient functions are certified as a derivative
jet, the normalized order-three formula equals the canonical derivative RHS. -/
theorem thirdExpanded_eq_canonical
    (hc : curvatureCoefficientJet.IsDerivativeJet)
    {K K1 K2 sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hsigma : ∀ u, HasDerivAt sigma
      (curvatureCoefficientJet.v (K u)) u) (u : ℝ) :
    thirdExpanded curvatureCoefficientJet K K1 K2 sigma u =
      thirdRhs K K1 sigma u := by
  have hd := hasDerivAt_secondExpanded curvatureCoefficientJet hc hK hK1 hsigma u
  have heq := secondExpanded_curvature_eq K K1 sigma
  rw [heq] at hd
  exact hd.deriv.symm

/-- The exact second-order equation constructs the third curvature derivative
as the normalized expression.  The concrete coefficient certificate is an
explicit parameter, so downstream work does not depend on how that certificate
is proved. -/
theorem hasDerivAt_K2_thirdExpanded
    (hc : curvatureCoefficientJet.IsDerivativeJet)
    {K K1 K2 sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hsigma : ∀ u, HasDerivAt sigma
      (curvatureCoefficientJet.v (K u)) u)
    (hsecond : ∀ u, K2 u = secondRhs K K1 sigma u) :
    ∀ u, HasDerivAt K2
      (thirdExpanded curvatureCoefficientJet K K1 K2 sigma u) u := by
  have heq : K2 = secondExpanded curvatureCoefficientJet K K1 sigma := by
    rw [secondExpanded_curvature_eq]
    exact funext hsecond
  intro u
  have h := hasDerivAt_secondExpanded curvatureCoefficientJet hc hK hK1 hsigma u
  rw [← heq] at h
  exact h

/-- The normalized order-four formula equals the canonical fourth derivative
RHS. -/
theorem fourthExpanded_eq_canonical
    (hc : curvatureCoefficientJet.IsDerivativeJet)
    {K K1 K2 K3 K4 sigma : ℝ → ℝ}
    (hK : ∀ u, HasDerivAt K (K1 u) u)
    (hK1 : ∀ u, HasDerivAt K1 (K2 u) u)
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3 : ∀ u, HasDerivAt K3 (K4 u) u)
    (hsigma : ∀ u, HasDerivAt sigma
      (curvatureCoefficientJet.v (K u)) u) (u : ℝ) :
    fourthExpanded curvatureCoefficientJet K K1 K2 K3 sigma u =
      fourthRhs K K1 sigma u := by
  have h3 : thirdExpanded curvatureCoefficientJet K K1 K2 sigma =
      thirdRhs K K1 sigma := by
    funext t
    exact thirdExpanded_eq_canonical hc hK hK1 hsigma t
  have hd := hasDerivAt_thirdExpanded curvatureCoefficientJet hc
    hK hK1 hK2 hK3 hsigma u
  rw [h3] at hd
  exact hd.deriv.symm

/-- Correct order-three identity from the second-order identity and the
derivative witness for `K2`. -/
theorem third_eq_canonical {K K1 K2 K3 sigma : ℝ → ℝ}
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hsecond : ∀ u, K2 u = secondRhs K K1 sigma u) (u : ℝ) :
    K3 u = thirdRhs K K1 sigma u := by
  have heq : K2 = secondRhs K K1 sigma := funext hsecond
  calc
    K3 u = deriv K2 u := (hK2 u).deriv.symm
    _ = deriv (secondRhs K K1 sigma) u := by rw [heq]
    _ = thirdRhs K K1 sigma u := rfl

/-- Correct order-four identity from the canonical third expression and the
derivative witness for `K3`. -/
theorem fourth_eq_canonical {K K1 K2 K3 K4 sigma : ℝ → ℝ}
    (hK2 : ∀ u, HasDerivAt K2 (K3 u) u)
    (hK3 : ∀ u, HasDerivAt K3 (K4 u) u)
    (hsecond : ∀ u, K2 u = secondRhs K K1 sigma u) (u : ℝ) :
    K4 u = fourthRhs K K1 sigma u := by
  have hthird : K3 = thirdRhs K K1 sigma := by
    funext t
    exact third_eq_canonical hK2 hsecond t
  calc
    K4 u = deriv K3 u := (hK3 u).deriv.symm
    _ = deriv (thirdRhs K K1 sigma) u := by rw [hthird]
    _ = fourthRhs K K1 sigma u := rfl

/-- `F` is bounded relative to the positive base curvature `K`. -/
def RelMajorant (K F : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ u, |F u| ≤ C * K u

/-- An ordinary uniform pointwise bound. -/
def UniformMajorant (F : ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ u, |F u| ≤ A

theorem rel_zero (K : ℝ → ℝ) : RelMajorant K (fun _ => 0) 0 := by
  intro u
  simp

theorem rel_self (hK0 : ∀ u, 0 ≤ K u) : RelMajorant K K 1 := by
  intro u
  rw [abs_of_nonneg (hK0 u), one_mul]

theorem rel_neg (h : RelMajorant K F C) : RelMajorant K (fun u => -F u) C := by
  intro u
  simpa using h u

theorem rel_add (hF : RelMajorant K F C) (hG : RelMajorant K G D) :
    RelMajorant K (fun u => F u + G u) (C + D) := by
  intro u
  calc
    |F u + G u| ≤ |F u| + |G u| := abs_add_le _ _
    _ ≤ C * K u + D * K u := add_le_add (hF u) (hG u)
    _ = (C + D) * K u := by ring

theorem rel_sub (hF : RelMajorant K F C) (hG : RelMajorant K G D) :
    RelMajorant K (fun u => F u - G u) (C + D) := by
  simpa [sub_eq_add_neg] using rel_add hF (rel_neg hG)

theorem rel_const_mul (hc : 0 ≤ c) (hF : RelMajorant K F C) :
    RelMajorant K (fun u => c * F u) (c * C) := by
  intro u
  rw [abs_mul, abs_of_nonneg hc]
  calc
    c * |F u| ≤ c * (C * K u) := mul_le_mul_of_nonneg_left (hF u) hc
    _ = (c * C) * K u := by ring

/-- Multiplication by a uniformly bounded coefficient preserves a relative
majorant. -/
theorem uniform_mul_rel (hB : UniformMajorant B A) (hA0 : 0 ≤ A)
    (hF : RelMajorant K F C) (hC0 : 0 ≤ C) (hK0 : ∀ u, 0 ≤ K u) :
    RelMajorant K (fun u => B u * F u) (A * C) := by
  intro u
  rw [abs_mul]
  calc
    |B u| * |F u| ≤ A * (C * K u) :=
      mul_le_mul (hB u) (hF u) (abs_nonneg _) hA0
    _ = (A * C) * K u := by ring

theorem uniform_mul_uniform
    (hF : UniformMajorant F A) (hG : UniformMajorant G B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    UniformMajorant (fun u => F u * G u) (A * B) := by
  intro u
  rw [abs_mul]
  exact mul_le_mul (hF u) (hG u) (abs_nonneg _) hA

theorem uniform_add_uniform
    (hF : UniformMajorant F A) (hG : UniformMajorant G B) :
    UniformMajorant (fun u => F u + G u) (A + B) := by
  intro u
  exact (abs_add_le _ _).trans (add_le_add (hF u) (hG u))

theorem uniform_const_mul
    (hc : 0 ≤ c) (hF : UniformMajorant F A) :
    UniformMajorant (fun u => c * F u) (c * A) := by
  intro u
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (hF u) hc

/-- The product of two relative quantities is relative when the base
curvature has a uniform upper bound. -/
theorem rel_mul_rel (hF : RelMajorant K F C) (hG : RelMajorant K G D)
    (hC0 : 0 ≤ C) (hD0 : 0 ≤ D) (hK0 : ∀ u, 0 ≤ K u)
    (hKA : ∀ u, K u ≤ A) (hA0 : 0 ≤ A) :
    RelMajorant K (fun u => F u * G u) (C * D * A) := by
  intro u
  rw [abs_mul]
  calc
    |F u| * |G u| ≤ (C * K u) * (D * K u) :=
      mul_le_mul (hF u) (hG u) (abs_nonneg _) (mul_nonneg hC0 (hK0 u))
    _ = (C * D) * K u * K u := by ring
    _ ≤ (C * D) * K u * A := by
      exact mul_le_mul_of_nonneg_left (hKA u)
        (mul_nonneg (mul_nonneg hC0 hD0) (hK0 u))
    _ = (C * D * A) * K u := by ring

theorem rel_mul3_rel
    (hF : RelMajorant K F C) (hG : RelMajorant K G D)
    (hH : RelMajorant K H E)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hK0 : ∀ u, 0 ≤ K u) (hKA : ∀ u, K u ≤ A) (hA : 0 ≤ A) :
    RelMajorant K (fun u => F u * G u * H u)
      ((C * D * A) * E * A) := by
  exact rel_mul_rel (rel_mul_rel hF hG hC hD hK0 hKA hA) hH
    (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hE hK0 hKA hA

/-- Harnack comparison transports a relative bound through the shift. -/
theorem rel_comp_shift {sigma : ℝ → ℝ} (hF : RelMajorant K F C) (hC0 : 0 ≤ C)
    (hshift : ∀ u, K (sigma u) ≤ Ch * K u) :
    RelMajorant K (fun u => F (sigma u)) (C * Ch) := by
  intro u
  calc
    |F (sigma u)| ≤ C * K (sigma u) := hF _
    _ ≤ C * (Ch * K u) := mul_le_mul_of_nonneg_left (hshift u) hC0
    _ = (C * Ch) * K u := by ring

/-- Powers of the base curvature reduce to one factor of `K` under a uniform
upper bound. -/
theorem rel_pow (hK0 : ∀ u, 0 ≤ K u) (hKA : ∀ u, K u ≤ A)
    (hA0 : 0 ≤ A) (n : ℕ) :
    RelMajorant K (fun u => K u ^ (n + 1)) (A ^ n) := by
  intro u
  rw [abs_of_nonneg (pow_nonneg (hK0 u) _), pow_succ]
  exact mul_le_mul (pow_le_pow_left₀ (hK0 u) (hKA u) n) le_rfl
    (hK0 u) (pow_nonneg hA0 n)

/-- A finite sum of already majorized jet terms is majorized by the sum of
their constants. -/
theorem rel_finset_sum {ι : Type*} {s : Finset ι}
    {F : ι → ℝ → ℝ} {C : ι → ℝ}
    (h : ∀ i ∈ s, RelMajorant K (F i) (C i)) :
    RelMajorant K (fun u => ∑ i ∈ s, F i u) (∑ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero K
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact rel_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Rewrite an exact finite differentiated identity and apply the structural
majorant of its right-hand side. -/
theorem rel_of_eq (heq : ∀ u, J u = R u) (hR : RelMajorant K R C) :
    RelMajorant K J C := by
  intro u
  rw [heq u]
  exact hR u

/-- The relative majorant constant may be replaced by any equal expression. -/
theorem rel_of_const_eq {K J : ℝ → ℝ} {C C' : ℝ} (h : C = C')
    (hR : RelMajorant K J C) : RelMajorant K J C' := h ▸ hR

/-! ### The finite pulse chain consumed by periodization -/

/-- The exact five-function pulse jet needed to make both the pulse and its
first derivative have `C3` periodizations. -/
structure PulseJet4 (y0 y1 y2 y3 y4 : ℝ → ℝ) : Prop where
  deriv01 : ∀ s, HasDerivAt y0 (y1 s) s
  deriv12 : ∀ s, HasDerivAt y1 (y2 s) s
  deriv23 : ∀ s, HasDerivAt y2 (y3 s) s
  deriv34 : ∀ s, HasDerivAt y3 (y4 s) s
  continuous3 : Continuous y3
  continuous4 : Continuous y4

/-- Relative bounds for the finite pulse jet, with one constant per order. -/
structure PulseJetRelative (y0 y1 y2 y3 y4 : ℝ → ℝ)
    (D0 D1 D2 D3 D4 : ℝ) : Prop where
  base_nonneg : ∀ s, 0 ≤ y0 s
  D0_nonneg : 0 ≤ D0
  D1_nonneg : 0 ≤ D1
  D2_nonneg : 0 ≤ D2
  D3_nonneg : 0 ≤ D3
  D4_nonneg : 0 ≤ D4
  bound0 : ∀ s, |y0 s| ≤ D0 * y0 s
  bound1 : ∀ s, |y1 s| ≤ D1 * y0 s
  bound2 : ∀ s, |y2 s| ≤ D2 * y0 s
  bound3 : ∀ s, |y3 s| ≤ D3 * y0 s
  bound4 : ∀ s, |y4 s| ≤ D4 * y0 s

/-- Relative pulse estimates inherit the exponential decay of the base pulse.
This is the finite replacement for the former all-orders decay package. -/
theorem pulseJet_exp_bounds
    {y0 y1 y2 y3 y4 : ℝ → ℝ} {D0 D1 D2 D3 D4 C alpha : ℝ}
    (hC0 : 0 ≤ C)
    (hrel : PulseJetRelative y0 y1 y2 y3 y4 D0 D1 D2 D3 D4)
    (hdec : ∀ s, y0 s ≤ C * Real.exp (-alpha * |s|)) :
    (∀ s, |y0 s| ≤ (D0 * C) * Real.exp (-alpha * |s|)) ∧
    (∀ s, |y1 s| ≤ (D1 * C) * Real.exp (-alpha * |s|)) ∧
    (∀ s, |y2 s| ≤ (D2 * C) * Real.exp (-alpha * |s|)) ∧
    (∀ s, |y3 s| ≤ (D3 * C) * Real.exp (-alpha * |s|)) ∧
    (∀ s, |y4 s| ≤ (D4 * C) * Real.exp (-alpha * |s|)) := by
  have step : ∀ (F : ℝ → ℝ) (D : ℝ), 0 ≤ D →
      (∀ s, |F s| ≤ D * y0 s) →
      ∀ s, |F s| ≤ (D * C) * Real.exp (-alpha * |s|) := by
    intro F D hD hb s
    calc
      |F s| ≤ D * y0 s := hb s
      _ ≤ D * (C * Real.exp (-alpha * |s|)) :=
        mul_le_mul_of_nonneg_left (hdec s) hD
      _ = (D * C) * Real.exp (-alpha * |s|) := by ring
  exact ⟨step y0 D0 hrel.D0_nonneg hrel.bound0,
    step y1 D1 hrel.D1_nonneg hrel.bound1,
    step y2 D2 hrel.D2_nonneg hrel.bound2,
    step y3 D3 hrel.D3_nonneg hrel.bound3,
    step y4 D4 hrel.D4_nonneg hrel.bound4⟩

/-- Replace the five order-dependent exponential constants by their maximum,
as required by `PeriodizedPulseSmooth`. -/
theorem pulseJet_common_exp_bound
    {y0 y1 y2 y3 y4 : ℝ → ℝ} {C0 C1 C2 C3 C4 alpha : ℝ}
    (h0 : ∀ s, |y0 s| ≤ C0 * Real.exp (-alpha * |s|))
    (h1 : ∀ s, |y1 s| ≤ C1 * Real.exp (-alpha * |s|))
    (h2 : ∀ s, |y2 s| ≤ C2 * Real.exp (-alpha * |s|))
    (h3 : ∀ s, |y3 s| ≤ C3 * Real.exp (-alpha * |s|))
    (h4 : ∀ s, |y4 s| ≤ C4 * Real.exp (-alpha * |s|)) :
    ∃ C : ℝ,
      (∀ s, |y0 s| ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |y1 s| ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |y2 s| ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |y3 s| ≤ C * Real.exp (-alpha * |s|)) ∧
      (∀ s, |y4 s| ≤ C * Real.exp (-alpha * |s|)) := by
  let C := max (max (max (max C0 C1) C2) C3) C4
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro s
    first
    | exact (h0 s).trans (mul_le_mul_of_nonneg_right
        (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _)))) (Real.exp_nonneg _))
    | exact (h1 s).trans (mul_le_mul_of_nonneg_right
        (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
          (le_trans (le_max_left _ _) (le_max_left _ _)))) (Real.exp_nonneg _))
    | exact (h2 s).trans (mul_le_mul_of_nonneg_right
        (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
        (Real.exp_nonneg _))
    | exact (h3 s).trans (mul_le_mul_of_nonneg_right
        (le_trans (le_max_right _ _) (le_max_left _ _)) (Real.exp_nonneg _))
    | exact (h4 s).trans (mul_le_mul_of_nonneg_right
        (le_max_right _ _) (Real.exp_nonneg _))

/-! ### Coefficient envelopes and explicit jet constants -/

/-- Uniform envelopes for the named coefficient jet over the actual bounded
curvature range. -/
structure CoefficientBounds (c : CoefficientJet) (K : ℝ → ℝ)
    (V V1 V2 A0 A1 A2 A3 : ℝ) : Prop where
  V_nonneg : 0 ≤ V
  V1_nonneg : 0 ≤ V1
  V2_nonneg : 0 ≤ V2
  A0_nonneg : 0 ≤ A0
  A1_nonneg : 0 ≤ A1
  A2_nonneg : 0 ≤ A2
  A3_nonneg : 0 ≤ A3
  v : ∀ u, |c.v (K u)| ≤ V
  v1 : ∀ u, |c.v1 (K u)| ≤ V1
  v2 : ∀ u, |c.v2 (K u)| ≤ V2
  a : ∀ u, |c.a (K u)| ≤ A0
  a1 : ∀ u, |c.a1 (K u)| ≤ A1
  a2 : ∀ u, |c.a2 (K u)| ≤ A2
  a3 : ∀ u, |c.a3 (K u)| ≤ A3

/-- The explicit constant obtained by applying the majorant algebra to
`thirdExpanded`. -/
def thirdConstant (B Ch D1 D2 V V1 A0 A1 A2 : ℝ) : ℝ :=
  A2 * D1 ^ 2 * Ch * B ^ 2
    + A1 * D2 * Ch * B
    + 2 * A1 * V * D1 ^ 2 * Ch * B
    + A0 * D2 * Ch * V ^ 2
    + A0 * V1 * D1 ^ 2 * Ch * B
    + 6 * D1 ^ 2 * B ^ 2
    + (1 + 3 * B ^ 2) * D2

/-- A manifestly nonnegative third-order constant. -/
theorem thirdConstant_nonneg
    (hB : 0 ≤ B) (hCh : 0 ≤ Ch) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hV : 0 ≤ V) (hV1 : 0 ≤ V1) (hA0 : 0 ≤ A0)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) :
    0 ≤ thirdConstant B Ch D1 D2 V V1 A0 A1 A2 := by
  dsimp [thirdConstant]
  positivity

/-- Final aggregation of the seven termwise bounds in `thirdExpanded`. -/
theorem rel_thirdExpanded_of_term_bounds
    {c : CoefficientJet} {K K1 K2 sigma : ℝ → ℝ}
    {C1 C2 C3 C4 C5 C6 C7 : ℝ}
    (h1 : RelMajorant K (fun u =>
      (c.a2 (K u) * K1 u ^ 2) * K (sigma u)) C1)
    (h2 : RelMajorant K (fun u =>
      (c.a1 (K u) * K2 u) * K (sigma u)) C2)
    (h3 : RelMajorant K (fun u =>
      2 * c.a1 (K u) * K1 u * K1 (sigma u) * c.v (K u)) C3)
    (h4 : RelMajorant K (fun u =>
      c.a (K u) * K2 (sigma u) * c.v (K u) ^ 2) C4)
    (h5 : RelMajorant K (fun u =>
      c.a (K u) * K1 (sigma u) * (c.v1 (K u) * K1 u)) C5)
    (h6 : RelMajorant K (fun u => 6 * K u * K1 u ^ 2) C6)
    (h7 : RelMajorant K (fun u => (1 + 3 * K u ^ 2) * K2 u) C7) :
    RelMajorant K (thirdExpanded c K K1 K2 sigma)
      (C1 + C2 + C3 + C4 + C5 + C6 + C7) := by
  have hp := rel_add (rel_add (rel_add (rel_add (rel_add h1 h2) h3) h4) h5)
    (rel_neg h6)
  have hall := rel_add hp (rel_neg h7)
  refine rel_of_eq ?_ hall
  intro u
  dsimp [thirdExpanded]
  ring

/-- Instantiate all seven order-three term bounds from coefficient envelopes,
relative lower-jet bounds, the curvature ceiling, and Harnack transport through
the shift. -/
theorem rel_thirdExpanded
    {c : CoefficientJet} {K K1 K2 sigma : ℝ → ℝ}
    {B Ch D1 D2 V V1 V2 A0 A1 A2 A3 : ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B)
    (hB : 0 ≤ B) (hCh : 0 ≤ Ch)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hshift : ∀ u, K (sigma u) ≤ Ch * K u)
    (hK1 : RelMajorant K K1 D1) (hK2 : RelMajorant K K2 D2)
    (hc : CoefficientBounds c K V V1 V2 A0 A1 A2 A3) :
    RelMajorant K (thirdExpanded c K K1 K2 sigma)
      (thirdConstant B Ch D1 D2 V V1 A0 A1 A2) := by
  have hV := hc.V_nonneg
  have hV1 := hc.V1_nonneg
  have hV2 := hc.V2_nonneg
  have hA0 := hc.A0_nonneg
  have hA1 := hc.A1_nonneg
  have hA2 := hc.A2_nonneg
  have hA3 := hc.A3_nonneg
  have hKs : RelMajorant K (fun u => K (sigma u)) Ch := by
    simpa using rel_comp_shift (rel_self hK0) zero_le_one hshift
  have hK1s : RelMajorant K (fun u => K1 (sigma u)) (D1 * Ch) :=
    rel_comp_shift hK1 hD1 hshift
  have hK2s : RelMajorant K (fun u => K2 (sigma u)) (D2 * Ch) :=
    rel_comp_shift hK2 hD2 hshift
  have hK1sq : RelMajorant K (fun u => K1 u * K1 u) (D1 * D1 * B) :=
    rel_mul_rel hK1 hK1 hD1 hD1 hK0 hKB hB
  have h1r : RelMajorant K
      (fun u => (K1 u * K1 u) * K (sigma u))
      ((D1 * D1 * B) * Ch * B) :=
    rel_mul_rel hK1sq hKs (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hCh hK0 hKB hB
  have h1 : RelMajorant K (fun u =>
      (c.a2 (K u) * K1 u ^ 2) * K (sigma u))
      (A2 * D1 ^ 2 * Ch * B ^ 2) := by
    have hu := uniform_mul_rel
      (B := fun u => c.a2 (K u)) (F := fun u => (K1 u * K1 u) * K (sigma u))
      hc.a2 hc.A2_nonneg h1r (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    refine rel_of_const_eq (C := A2 * ((D1 * D1 * B) * Ch * B)) (by ring)
      (rel_of_eq (R := fun u => c.a2 (K u) * ((K1 u * K1 u) * K (sigma u))) ?_ ?_)
    · intro u; ring
    · convert hu using 1 <;> ring
  have h2r := rel_mul_rel hK2 hKs hD2 hCh hK0 hKB hB
  have h2 : RelMajorant K (fun u =>
      (c.a1 (K u) * K2 u) * K (sigma u))
      (A1 * D2 * Ch * B) := by
    have hu := uniform_mul_rel hc.a1 hc.A1_nonneg h2r (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    refine rel_of_const_eq (C := A1 * (D2 * Ch * B)) (by ring)
      (rel_of_eq (R := fun u => c.a1 (K u) * (K2 u * K (sigma u))) ?_ ?_)
    · intro u; ring
    · convert hu using 1 <;> ring
  have h3r := rel_mul_rel hK1 hK1s hD1 (mul_nonneg hD1 hCh) hK0 hKB hB
  have hcoef3 : UniformMajorant (fun u => 2 * c.a1 (K u) * c.v (K u))
      (2 * A1 * V) := by
    intro u
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hc.a1 u) (by norm_num))
      (hc.v u) (abs_nonneg _) (mul_nonneg (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hc.A1_nonneg)
  have h3u := uniform_mul_rel hcoef3 (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) h3r (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
  have h3 : RelMajorant K (fun u =>
      2 * c.a1 (K u) * K1 u * K1 (sigma u) * c.v (K u))
      (2 * A1 * V * D1 ^ 2 * Ch * B) := by
    refine rel_of_const_eq (C := (2 * A1 * V) * (D1 * (D1 * Ch) * B)) (by ring)
      (rel_of_eq (R := fun u => (2 * c.a1 (K u) * c.v (K u)) * (K1 u * K1 (sigma u))) ?_ ?_)
    · intro u; ring
    · convert h3u using 1 <;> ring
  have hcoef4 : UniformMajorant (fun u => c.a (K u) * c.v (K u) ^ 2)
      (A0 * V ^ 2) := by
    intro u
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hc.a u) (pow_le_pow_left₀ (abs_nonneg _) (hc.v u) 2)
      (pow_nonneg (abs_nonneg _) 2) hc.A0_nonneg
  have h4u := uniform_mul_rel hcoef4 (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK2s
    (mul_nonneg hD2 hCh) hK0
  have h4 : RelMajorant K (fun u =>
      c.a (K u) * K2 (sigma u) * c.v (K u) ^ 2)
      (A0 * D2 * Ch * V ^ 2) := by
    refine rel_of_const_eq (C := (A0 * V ^ 2) * (D2 * Ch)) (by ring)
      (rel_of_eq (R := fun u => (c.a (K u) * c.v (K u) ^ 2) * K2 (sigma u)) ?_ ?_)
    · intro u; ring
    · convert h4u using 1 <;> ring
  have h5r := rel_mul_rel hK1s hK1 (mul_nonneg hD1 hCh) hD1 hK0 hKB hB
  have hcoef5 : UniformMajorant (fun u => c.a (K u) * c.v1 (K u))
      (A0 * V1) := by
    intro u
    rw [abs_mul]
    exact mul_le_mul (hc.a u) (hc.v1 u) (abs_nonneg _) hc.A0_nonneg
  have h5u := uniform_mul_rel hcoef5 (mul_nonneg hc.A0_nonneg hc.V1_nonneg)
    h5r (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
  have h5 : RelMajorant K (fun u =>
      c.a (K u) * K1 (sigma u) * (c.v1 (K u) * K1 u))
      (A0 * V1 * D1 ^ 2 * Ch * B) := by
    refine rel_of_const_eq (C := (A0 * V1) * ((D1 * Ch) * D1 * B)) (by ring)
      (rel_of_eq (R := fun u => (c.a (K u) * c.v1 (K u)) * (K1 (sigma u) * K1 u)) ?_ ?_)
    · intro u; ring
    · convert h5u using 1 <;> ring
  have h6r := rel_mul_rel (rel_self hK0) hK1sq zero_le_one (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption))
    hK0 hKB hB
  have h6 : RelMajorant K (fun u => 6 * K u * K1 u ^ 2)
      (6 * D1 ^ 2 * B ^ 2) := by
    have hu := rel_const_mul (by norm_num : (0 : ℝ) ≤ 6) h6r
    refine rel_of_const_eq (C := 6 * (1 * (D1 * D1 * B) * B)) (by ring)
      (rel_of_eq (R := fun u => 6 * (K u * (K1 u * K1 u))) ?_ ?_)
    · intro u; ring
    · convert hu using 1 <;> ring
  have hcoef7 : UniformMajorant (fun u => 1 + 3 * K u ^ 2)
      (1 + 3 * B ^ 2) := by
    intro u
    rw [abs_of_nonneg (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption))]
    nlinarith [hK0 u, hKB u]
  have h7 : RelMajorant K (fun u => (1 + 3 * K u ^ 2) * K2 u)
      ((1 + 3 * B ^ 2) * D2) :=
    uniform_mul_rel hcoef7 (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK2 hD2 hK0
  have hall := rel_thirdExpanded_of_term_bounds h1 h2 h3 h4 h5 h6 h7
  convert hall using 1 <;> simp [thirdConstant] <;> ring

/-- The explicit constant obtained term by term from `fourthExpanded`.  Terms
which have the same majorant are collected, but no cancellation is used. -/
def fourthConstant
    (B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 : ℝ) : ℝ :=
  A3 * D1 ^ 3 * Ch * B ^ 3
    + 3 * A2 * D1 * D2 * Ch * B ^ 2
    + A1 * D3 * Ch * B
    + 3 * V * D1 * Ch * B * (A2 * D1 ^ 2 * B + A1 * D2)
    + 3 * A1 * D1 * D2 * Ch * B * V ^ 2
    + 3 * A1 * V1 * D1 ^ 3 * Ch * B ^ 2
    + A0 * D3 * Ch * V ^ 3
    + 3 * A0 * V * V1 * D2 * D1 * Ch * B
    + A0 * V2 * D1 ^ 3 * Ch * B ^ 2
    + A0 * V1 * D1 * D2 * Ch * B
    + 6 * D1 ^ 3 * B ^ 2
    + 18 * D1 * D2 * B ^ 2
    + (1 + 3 * B ^ 2) * D3

/-- The thirteen groups of the fourth-order expansion, aligned term-for-term
with `fourthConstant`.  Repeated product-rule terms are collected before any
absolute-value estimate is taken. -/
def fourthTerm (c : CoefficientJet)
    (K K1 K2 K3 sigma : ℝ → ℝ) (i : Fin 13) : ℝ → ℝ := fun u =>
  match i.1 with
  | 0 => c.a3 (K u) * K1 u ^ 3 * K (sigma u)
  | 1 => 3 * c.a2 (K u) * K1 u * K2 u * K (sigma u)
  | 2 => c.a1 (K u) * K3 u * K (sigma u)
  | 3 => 3 * (c.a2 (K u) * K1 u ^ 2 + c.a1 (K u) * K2 u) *
      K1 (sigma u) * c.v (K u)
  | 4 => 3 * c.a1 (K u) * K1 u * K2 (sigma u) * c.v (K u) ^ 2
  | 5 => 3 * c.a1 (K u) * K1 u * K1 (sigma u) *
      (c.v1 (K u) * K1 u)
  | 6 => c.a (K u) * K3 (sigma u) * c.v (K u) ^ 3
  | 7 => 3 * c.a (K u) * K2 (sigma u) * c.v (K u) *
      (c.v1 (K u) * K1 u)
  | 8 => c.a (K u) * K1 (sigma u) * (c.v2 (K u) * K1 u ^ 2)
  | 9 => c.a (K u) * K1 (sigma u) * (c.v1 (K u) * K2 u)
  | 10 => -(6 * K1 u ^ 3)
  | 11 => -(18 * K u * K1 u * K2 u)
  | _ => -((1 + 3 * K u ^ 2) * K3 u)

/-- The grouped finite family is exactly the displayed fourth-order
expression. -/
theorem fourthExpanded_eq_sum (c : CoefficientJet)
    (K K1 K2 K3 sigma : ℝ → ℝ) (u : ℝ) :
    fourthExpanded c K K1 K2 K3 sigma u =
      ∑ i : Fin 13, fourthTerm c K K1 K2 K3 sigma i u := by
  simp [fourthExpanded, fourthTerm, Fin.sum_univ_succ]
  ring

/-- The thirteen constants paired with `fourthTerm`. -/
def fourthTermConstant
    (B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 : ℝ) (i : Fin 13) : ℝ :=
  match i.1 with
  | 0 => A3 * D1 ^ 3 * Ch * B ^ 3
  | 1 => 3 * A2 * D1 * D2 * Ch * B ^ 2
  | 2 => A1 * D3 * Ch * B
  | 3 => 3 * V * D1 * Ch * B * (A2 * D1 ^ 2 * B + A1 * D2)
  | 4 => 3 * A1 * D1 * D2 * Ch * B * V ^ 2
  | 5 => 3 * A1 * V1 * D1 ^ 3 * Ch * B ^ 2
  | 6 => A0 * D3 * Ch * V ^ 3
  | 7 => 3 * A0 * V * V1 * D2 * D1 * Ch * B
  | 8 => A0 * V2 * D1 ^ 3 * Ch * B ^ 2
  | 9 => A0 * V1 * D1 * D2 * Ch * B
  | 10 => 6 * D1 ^ 3 * B ^ 2
  | 11 => 18 * D1 * D2 * B ^ 2
  | _ => (1 + 3 * B ^ 2) * D3

theorem sum_fourthTermConstant
    (B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 : ℝ) :
    (∑ i : Fin 13,
      fourthTermConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 i) =
      fourthConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 := by
  simp [fourthTermConstant, fourthConstant, Fin.sum_univ_succ]
  ring

/-- Aggregate the thirteen grouped fourth-order estimates. -/
theorem rel_fourthExpanded_of_term_bounds
    {c : CoefficientJet} {K K1 K2 K3 sigma : ℝ → ℝ}
    {B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 : ℝ}
    (hterm : ∀ i : Fin 13,
      RelMajorant K (fourthTerm c K K1 K2 K3 sigma i)
        (fourthTermConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 i)) :
    RelMajorant K (fourthExpanded c K K1 K2 K3 sigma)
      (fourthConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3) := by
  have hs := rel_finset_sum (K := K) (s := Finset.univ)
    (F := fun i => fourthTerm c K K1 K2 K3 sigma i)
    (C := fun i => fourthTermConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 i)
    (fun i _ => hterm i)
  apply rel_of_eq (R := fun u => ∑ i : Fin 13,
    fourthTerm c K K1 K2 K3 sigma i u)
  · intro u
    exact fourthExpanded_eq_sum c K K1 K2 K3 sigma u
  · simpa [sum_fourthTermConstant] using hs

/-- The three coefficient-free tail terms of the fourth-order expansion. -/
theorem rel_fourth_tail_terms
    {c : CoefficientJet} {K K1 K2 K3 sigma : ℝ → ℝ}
    {B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 : ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B) (hB : 0 ≤ B)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hK1 : RelMajorant K K1 D1) (hK2 : RelMajorant K K2 D2)
    (hK3 : RelMajorant K K3 D3) :
    RelMajorant K (fourthTerm c K K1 K2 K3 sigma ⟨10, by omega⟩)
        (fourthTermConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 ⟨10, by omega⟩) ∧
    RelMajorant K (fourthTerm c K K1 K2 K3 sigma ⟨11, by omega⟩)
        (fourthTermConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 ⟨11, by omega⟩) ∧
    RelMajorant K (fourthTerm c K K1 K2 K3 sigma ⟨12, by omega⟩)
        (fourthTermConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 ⟨12, by omega⟩) := by
  have h111 := rel_mul3_rel hK1 hK1 hK1 hD1 hD1 hD1 hK0 hKB hB
  have ht10 := rel_neg (rel_const_mul (by norm_num : (0 : ℝ) ≤ 6) h111)
  have h012 := rel_mul3_rel (rel_self hK0) hK1 hK2 zero_le_one hD1 hD2 hK0 hKB hB
  have ht11 := rel_neg (rel_const_mul (by norm_num : (0 : ℝ) ≤ 18) h012)
  have hcoef : UniformMajorant (fun u => 1 + 3 * K u ^ 2) (1 + 3 * B ^ 2) := by
    intro u
    rw [abs_of_nonneg (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption))]
    have hs : K u ^ 2 ≤ B ^ 2 := by nlinarith [hK0 u, hKB u]
    nlinarith
  have ht12 := rel_neg (uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK3 hD3 hK0)
  refine ⟨?_, ?_, ?_⟩
  · convert ht10 using 1 <;>
      first
        | (unfold fourthTerm; funext u; norm_num; ring)
        | (unfold fourthTermConstant; norm_num; ring)
        | ring
  · convert ht11 using 1 <;>
      first
        | (unfold fourthTerm; funext u; norm_num; ring)
        | (unfold fourthTermConstant; norm_num; ring)
        | ring
  · convert ht12 using 1 <;>
      first
        | (unfold fourthTerm; funext u; norm_num; ring)
        | (unfold fourthTermConstant; norm_num; ring)
        | ring

/-- Coefficient/shift instantiations for fourth-order groups zero through four. -/
theorem rel_fourth_terms_zero_to_four
    {c : CoefficientJet} {K K1 K2 K3 sigma : ℝ → ℝ}
    {B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 : ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B)
    (hB : 0 ≤ B) (hCh : 0 ≤ Ch)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hshift : ∀ u, K (sigma u) ≤ Ch * K u)
    (hK1 : RelMajorant K K1 D1) (hK2 : RelMajorant K K2 D2)
    (hK3 : RelMajorant K K3 D3)
    (hc : CoefficientBounds c K V V1 V2 A0 A1 A2 A3) :
    ∀ i : Fin 13, i.1 ≤ 4 →
      RelMajorant K (fourthTerm c K K1 K2 K3 sigma i)
        (fourthTermConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 i) := by
  have hV := hc.V_nonneg
  have hV1 := hc.V1_nonneg
  have hV2 := hc.V2_nonneg
  have hA0 := hc.A0_nonneg
  have hA1 := hc.A1_nonneg
  have hA2 := hc.A2_nonneg
  have hA3 := hc.A3_nonneg
  have hKs : RelMajorant K (fun u => K (sigma u)) Ch := by
    simpa using rel_comp_shift (rel_self hK0) zero_le_one hshift
  have hK1s := rel_comp_shift hK1 hD1 hshift
  have hK2s := rel_comp_shift hK2 hD2 hshift
  have hK3s := rel_comp_shift hK3 hD3 hshift
  have hK1sq := rel_mul_rel hK1 hK1 hD1 hD1 hK0 hKB hB
  have hK1cube := rel_mul3_rel hK1 hK1 hK1 hD1 hD1 hD1 hK0 hKB hB
  have ua1 : UniformMajorant (fun u => c.a1 (K u)) A1 := hc.a1
  have ua2 : UniformMajorant (fun u => c.a2 (K u)) A2 := hc.a2
  have ua3 : UniformMajorant (fun u => c.a3 (K u)) A3 := hc.a3
  have uv : UniformMajorant (fun u => c.v (K u)) V := hc.v
  intro i hi
  interval_cases h : i.1
  · have hr := rel_mul_rel hK1cube hKs (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hCh hK0 hKB hB
    have hu := uniform_mul_rel ua3 hc.A3_nonneg hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)
  · have hr := rel_mul3_rel hK1 hK2 hKs hD1 hD2 hCh hK0 hKB hB
    have hcoef := uniform_const_mul (by norm_num : (0 : ℝ) ≤ 3) ua2
    have hu := uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)
  · have hr := rel_mul_rel hK3 hKs hD3 hCh hK0 hKB hB
    have hu := uniform_mul_rel ua1 hc.A1_nonneg hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)
  · have ha2sq := uniform_mul_rel ua2 hc.A2_nonneg hK1sq (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    have ha1k2 := uniform_mul_rel ua1 hc.A1_nonneg hK2 hD2 hK0
    have hinner := rel_add ha2sq ha1k2
    have hr := rel_mul_rel hK1s hinner (mul_nonneg hD1 hCh) (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption))
      hK0 hKB hB
    have hcoef := uniform_const_mul (by norm_num : (0 : ℝ) ≤ 3) uv
    have hu := uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    refine rel_of_const_eq (C := (3 * V) * ((D1 * Ch) *
        (A2 * (D1 * D1 * B) + A1 * D2) * B))
      (by unfold fourthTermConstant; rw [h]; ring)
      (rel_of_eq (R := fun u => (3 * c.v (K u)) *
        (K1 (sigma u) *
          (c.a2 (K u) * (K1 u * K1 u) + c.a1 (K u) * K2 u))) ?_ ?_)
    · intro u; unfold fourthTerm; rw [h]; ring
    · convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)
  · have hr := rel_mul_rel hK1 hK2s hD1 (mul_nonneg hD2 hCh) hK0 hKB hB
    have hv2 := uniform_mul_uniform uv uv hc.V_nonneg hc.V_nonneg
    have hcoef0 := uniform_mul_uniform ua1 hv2 hc.A1_nonneg (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption))
    have hcoef := uniform_const_mul (by norm_num : (0 : ℝ) ≤ 3) hcoef0
    have hu := uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    refine rel_of_const_eq (C := (3 * (A1 * (V * V))) * (D1 * (D2 * Ch) * B))
      (by unfold fourthTermConstant; rw [h]; ring)
      (rel_of_eq (R := fun u => (3 * (c.a1 (K u) * (c.v (K u) * c.v (K u)))) * (K1 u * K2 (sigma u))) ?_ ?_)
    · intro u; unfold fourthTerm; rw [h]; ring
    · convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)

/-- Coefficient/shift instantiations for fourth-order groups five through nine. -/
theorem rel_fourth_terms_five_to_nine
    {c : CoefficientJet} {K K1 K2 K3 sigma : ℝ → ℝ}
    {B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 : ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B)
    (hB : 0 ≤ B) (hCh : 0 ≤ Ch)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hshift : ∀ u, K (sigma u) ≤ Ch * K u)
    (hK1 : RelMajorant K K1 D1) (hK2 : RelMajorant K K2 D2)
    (hK3 : RelMajorant K K3 D3)
    (hc : CoefficientBounds c K V V1 V2 A0 A1 A2 A3) :
    ∀ i : Fin 13, 5 ≤ i.1 → i.1 ≤ 9 →
      RelMajorant K (fourthTerm c K K1 K2 K3 sigma i)
        (fourthTermConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 i) := by
  have hV := hc.V_nonneg
  have hV1 := hc.V1_nonneg
  have hV2 := hc.V2_nonneg
  have hA0 := hc.A0_nonneg
  have hA1 := hc.A1_nonneg
  have hA2 := hc.A2_nonneg
  have hA3 := hc.A3_nonneg
  have hK1s := rel_comp_shift hK1 hD1 hshift
  have hK2s := rel_comp_shift hK2 hD2 hshift
  have hK3s := rel_comp_shift hK3 hD3 hshift
  have hK1sq := rel_mul_rel hK1 hK1 hD1 hD1 hK0 hKB hB
  have ua0 : UniformMajorant (fun u => c.a (K u)) A0 := hc.a
  have ua1 : UniformMajorant (fun u => c.a1 (K u)) A1 := hc.a1
  have uv : UniformMajorant (fun u => c.v (K u)) V := hc.v
  have uv1 : UniformMajorant (fun u => c.v1 (K u)) V1 := hc.v1
  have uv2 : UniformMajorant (fun u => c.v2 (K u)) V2 := hc.v2
  intro i hlo hhi
  interval_cases h : i.1
  · have hr := rel_mul3_rel hK1s hK1 hK1 (mul_nonneg hD1 hCh) hD1 hD1
      hK0 hKB hB
    have hcoef0 := uniform_mul_uniform ua1 uv1 hc.A1_nonneg hc.V1_nonneg
    have hcoef := uniform_const_mul (by norm_num : (0 : ℝ) ≤ 3) hcoef0
    have hu := uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)
  · have hr := hK3s
    have hv3 := uniform_mul_uniform
      (uniform_mul_uniform uv uv hc.V_nonneg hc.V_nonneg) uv (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hc.V_nonneg
    have hcoef := uniform_mul_uniform ua0 hv3 hc.A0_nonneg (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption))
    have hu := uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hr (mul_nonneg hD3 hCh) hK0
    convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)
  · have hr := rel_mul_rel hK2s hK1 (mul_nonneg hD2 hCh) hD1 hK0 hKB hB
    have hcoef0 := uniform_mul_uniform
      (uniform_mul_uniform ua0 uv hc.A0_nonneg hc.V_nonneg) uv1
      (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hc.V1_nonneg
    have hcoef := uniform_const_mul (by norm_num : (0 : ℝ) ≤ 3) hcoef0
    have hu := uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)
  · have hr := rel_mul_rel hK1s hK1sq (mul_nonneg hD1 hCh)
      (mul_nonneg (mul_nonneg hD1 hD1) hB) hK0 hKB hB
    have hcoef := uniform_mul_uniform ua0 uv2 hc.A0_nonneg hc.V2_nonneg
    have hu := uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)
  · have hr := rel_mul_rel hK1s hK2 (mul_nonneg hD1 hCh) hD2 hK0 hKB hB
    have hcoef := uniform_mul_uniform ua0 uv1 hc.A0_nonneg hc.V1_nonneg
    have hu := uniform_mul_rel hcoef (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hr (by first | positivity | ((repeat' apply mul_nonneg) <;> assumption)) hK0
    convert hu using 1 <;>
      first
        | (unfold fourthTerm; rw [h]; funext u; ring)
        | (unfold fourthTermConstant; rw [h]; ring)
        | (unfold fourthTermConstant; rw [h]; norm_num; ring)

/-- The complete fourth-order shifted-curvature relative majorant. -/
theorem rel_fourthExpanded
    {c : CoefficientJet} {K K1 K2 K3 sigma : ℝ → ℝ}
    {B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 : ℝ}
    (hK0 : ∀ u, 0 ≤ K u) (hKB : ∀ u, K u ≤ B)
    (hB : 0 ≤ B) (hCh : 0 ≤ Ch)
    (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hshift : ∀ u, K (sigma u) ≤ Ch * K u)
    (hK1 : RelMajorant K K1 D1) (hK2 : RelMajorant K K2 D2)
    (hK3 : RelMajorant K K3 D3)
    (hc : CoefficientBounds c K V V1 V2 A0 A1 A2 A3) :
    RelMajorant K (fourthExpanded c K K1 K2 K3 sigma)
      (fourthConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3) := by
  have hV := hc.V_nonneg
  have hV1 := hc.V1_nonneg
  have hV2 := hc.V2_nonneg
  have hA0 := hc.A0_nonneg
  have hA1 := hc.A1_nonneg
  have hA2 := hc.A2_nonneg
  have hA3 := hc.A3_nonneg
  apply rel_fourthExpanded_of_term_bounds
  intro i
  by_cases h04 : i.1 ≤ 4
  · exact rel_fourth_terms_zero_to_four hK0 hKB hB hCh hD1 hD2 hD3 hshift
      hK1 hK2 hK3 hc i h04
  by_cases h59 : i.1 ≤ 9
  · exact rel_fourth_terms_five_to_nine hK0 hKB hB hCh hD1 hD2 hD3 hshift
      hK1 hK2 hK3 hc i (by omega) h59
  have htail := rel_fourth_tail_terms (c := c) (sigma := sigma) (Ch := Ch)
    (V := V) (V1 := V1) (V2 := V2) (A0 := A0) (A1 := A1) (A2 := A2) (A3 := A3)
    hK0 hKB hB hD1 hD2 hD3 hK1 hK2 hK3
  have hub : i.1 < 13 := i.isLt
  have hlb : 10 ≤ i.1 := by omega
  interval_cases h : i.1
  · have hi : i = (10 : Fin 13) := Fin.ext (by rw [h]; rfl)
    rw [hi]; exact htail.1
  · have hi : i = (11 : Fin 13) := Fin.ext (by rw [h]; rfl)
    rw [hi]; exact htail.2.1
  · have hi : i = (12 : Fin 13) := Fin.ext (by rw [h]; rfl)
    rw [hi]; exact htail.2.2

theorem fourthConstant_nonneg
    (hB : 0 ≤ B) (hCh : 0 ≤ Ch) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2)
    (hD3 : 0 ≤ D3) (hV : 0 ≤ V) (hV1 : 0 ≤ V1) (hV2 : 0 ≤ V2)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) :
    0 ≤ fourthConstant B Ch D1 D2 D3 V V1 V2 A0 A1 A2 A3 := by
  dsimp [fourthConstant]
  positivity

/-- Assemble the exact finite periodization jet from the canonical pulse
derivatives. -/
theorem pulseJet4_of_curvatureJet
    {y0 K K1 K2 x : ℝ → ℝ}
    (h01 : ∀ s, HasDerivAt y0 (PulseFromCurvature.pulseD K K1 x s) s)
    (h12 : ∀ s, HasDerivAt (PulseFromCurvature.pulseD K K1 x)
      (PulseFromCurvature.pulseDD K K1 K2 x s) s)
    (h23 : ∀ s, HasDerivAt (PulseFromCurvature.pulseDD K K1 K2 x)
      (pulseDDD K K1 K2 x s) s)
    (h34 : ∀ s, HasDerivAt (pulseDDD K K1 K2 x)
      (pulseDDDD K K1 K2 x s) s)
    (hc3 : Continuous (pulseDDD K K1 K2 x))
    (hc4 : Continuous (pulseDDDD K K1 K2 x)) :
    PulseJet4 y0 (PulseFromCurvature.pulseD K K1 x)
      (PulseFromCurvature.pulseDD K K1 K2 x)
      (pulseDDD K K1 K2 x) (pulseDDDD K K1 K2 x) :=
  ⟨h01, h12, h23, h34, hc3, hc4⟩

/-- Translation of a function on the pulse line. -/
def shift (q : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun s => f (s - q)

/-- Translating every member of a finite pulse jet preserves its derivative
chain and the required continuity. -/
theorem PulseJet4.shift {y0 y1 y2 y3 y4 : ℝ → ℝ} {q : ℝ}
    (h : PulseJet4 y0 y1 y2 y3 y4) :
    PulseJet4 (shift q y0) (shift q y1) (shift q y2) (shift q y3) (shift q y4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    simpa [shift] using (h.deriv01 (s - q)).comp s
      ((hasDerivAt_id s).sub_const q)
  · intro s
    simpa [shift] using (h.deriv12 (s - q)).comp s
      ((hasDerivAt_id s).sub_const q)
  · intro s
    simpa [shift] using (h.deriv23 (s - q)).comp s
      ((hasDerivAt_id s).sub_const q)
  · intro s
    simpa [shift] using (h.deriv34 (s - q)).comp s
      ((hasDerivAt_id s).sub_const q)
  · exact h.continuous3.comp (continuous_id.sub continuous_const)
  · exact h.continuous4.comp (continuous_id.sub continuous_const)

/-- Exponential decay is preserved by translation, with the sharp elementary
loss `exp(alpha*|q|)`. -/
theorem shift_exp_bound {f : ℝ → ℝ} {C alpha q : ℝ} (halpha : 0 ≤ alpha)
    (h : ∀ s, |f s| ≤ C * Real.exp (-alpha * |s|)) :
    ∀ s, |shift q f s| ≤
      (C * Real.exp (alpha * |q|)) * Real.exp (-alpha * |s|) := by
  intro s
  have hC : 0 ≤ C := by
    have h0 := (abs_nonneg (f 0)).trans (h 0)
    have he := Real.exp_pos (-alpha * |(0:ℝ)|)
    nlinarith
  have habs : |s| - |q| ≤ |s - q| := by
    have hadd := abs_add_le (s - q) q
    simp only [sub_add_cancel] at hadd
    linarith
  have hexp : Real.exp (-alpha * |s - q|) ≤
      Real.exp (alpha * |q|) * Real.exp (-alpha * |s|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    |shift q f s| ≤ C * Real.exp (-alpha * |s - q|) := by simpa [shift] using h (s - q)
    _ ≤ C * (Real.exp (alpha * |q|) * Real.exp (-alpha * |s|)) :=
      mul_le_mul_of_nonneg_left hexp hC
    _ = (C * Real.exp (alpha * |q|)) * Real.exp (-alpha * |s|) := by ring

/-- Translation preserves every relative pulse-jet bound with exactly the
same constants. -/
theorem PulseJetRelative.shift
    {y0 y1 y2 y3 y4 : ℝ → ℝ} {D0 D1 D2 D3 D4 q : ℝ}
    (h : PulseJetRelative y0 y1 y2 y3 y4 D0 D1 D2 D3 D4) :
    PulseJetRelative (shift q y0) (shift q y1) (shift q y2) (shift q y3) (shift q y4)
      D0 D1 D2 D3 D4 := by
  refine ⟨?_, h.D0_nonneg, h.D1_nonneg, h.D2_nonneg, h.D3_nonneg,
    h.D4_nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    simpa [shift] using h.base_nonneg (s - q)
  · intro s
    simpa [shift] using h.bound0 (s - q)
  · intro s
    simpa [shift] using h.bound1 (s - q)
  · intro s
    simpa [shift] using h.bound2 (s - q)
  · intro s
    simpa [shift] using h.bound3 (s - q)
  · intro s
    simpa [shift] using h.bound4 (s - q)

/-- A common exponential envelope for all five jet members remains common
after translation. -/
theorem shift_common_exp_bounds
    {y0 y1 y2 y3 y4 : ℝ → ℝ} {C alpha q : ℝ} (halpha : 0 ≤ alpha)
    (h0 : ∀ s, |y0 s| ≤ C * Real.exp (-alpha * |s|))
    (h1 : ∀ s, |y1 s| ≤ C * Real.exp (-alpha * |s|))
    (h2 : ∀ s, |y2 s| ≤ C * Real.exp (-alpha * |s|))
    (h3 : ∀ s, |y3 s| ≤ C * Real.exp (-alpha * |s|))
    (h4 : ∀ s, |y4 s| ≤ C * Real.exp (-alpha * |s|)) :
    let Cq := C * Real.exp (alpha * |q|)
    (∀ s, |shift q y0 s| ≤ Cq * Real.exp (-alpha * |s|)) ∧
    (∀ s, |shift q y1 s| ≤ Cq * Real.exp (-alpha * |s|)) ∧
    (∀ s, |shift q y2 s| ≤ Cq * Real.exp (-alpha * |s|)) ∧
    (∀ s, |shift q y3 s| ≤ Cq * Real.exp (-alpha * |s|)) ∧
    (∀ s, |shift q y4 s| ≤ Cq * Real.exp (-alpha * |s|)) := by
  dsimp
  exact ⟨shift_exp_bound halpha h0, shift_exp_bound halpha h1,
    shift_exp_bound halpha h2, shift_exp_bound halpha h3,
    shift_exp_bound halpha h4⟩

/-- One pulse jet and its phase translate supply the two-pulse analytic record
used by the Config threshold constructor. -/
theorem pulsePairAnalyticData_of_shift
    {y0 y1 y2 y3 y4 : ℝ → ℝ}
    {D0 D1 D2 D3 D4 alpha C CU D DU DU2 au P q : ℝ}
    (hjet : PulseJet4 y0 y1 y2 y3 y4)
    (hrel : PulseJetRelative y0 y1 y2 y3 y4 D0 D1 D2 D3 D4)
    (halpha : 0 ≤ alpha)
    (hdec0 : ∀ s, |y0 s| ≤ C * Real.exp (-alpha * |s|))
    (hdec1 : ∀ s, |y1 s| ≤ C * Real.exp (-alpha * |s|))
    (hCU : C * Real.exp (alpha * |q|) ≤ CU)
    (hD : D1 ≤ D) (hDU : D1 ≤ DU) (hDU2 : D2 ≤ DU2)
    (hstrip : ∀ u, (∑' m : ℤ, shift q y0 (u - m * P)) ≤ au) :
    PulsePairAnalyticData
      (alpha := alpha) (au := au) (C := C) (CU := CU)
      (DU := DU) (DU2 := DU2) (D := D) (P := P)
      y0 y1 (shift q y0) (shift q y1) (shift q y2) := by
  have hy1c : Continuous y1 :=
    Differentiable.continuous fun s => (hjet.deriv12 s).differentiableAt
  have hy2c : Continuous y2 :=
    Differentiable.continuous fun s => (hjet.deriv23 s).differentiableAt
  refine ⟨hrel.base_nonneg, fun s => (le_abs_self _).trans (hdec0 s),
    hjet.deriv01, hy1c, hdec1, ?_, hy1c.comp (continuous_id.sub continuous_const),
    ?_, ?_, ?_, ?_, ?_, hy2c.comp (continuous_id.sub continuous_const), ?_, hstrip⟩
  · intro s
    exact (hrel.bound1 s).trans
      (mul_le_mul_of_nonneg_right hD (hrel.base_nonneg s))
  · intro s
    simpa [shift] using hrel.base_nonneg (s - q)
  · intro s
    have hb := shift_exp_bound (q := q) halpha hdec0 s
    exact (le_abs_self _).trans (hb.trans
      (mul_le_mul_of_nonneg_right hCU (Real.exp_nonneg _)))
  · intro s
    have hb := hrel.bound1 (s - q)
    simpa [shift] using hb.trans
      (mul_le_mul_of_nonneg_right hDU (hrel.base_nonneg (s - q)))
  · exact (hjet.shift).deriv01
  · exact (hjet.shift).deriv12
  · intro s
    have hb := hrel.bound2 (s - q)
    simpa [shift] using hb.trans
      (mul_le_mul_of_nonneg_right hDU2 (hrel.base_nonneg (s - q)))

/-- Periodization commutes exactly with translation of the isolated pulse. -/
theorem periodizedPulse_shift (y : ℝ → ℝ) (P q u : ℝ) :
    ModelOrbitDefect.periodizedPulse (shift q y) P u =
      ModelOrbitDefect.periodizedPulse y P (u - q) := by
  simp only [ModelOrbitDefect.periodizedPulse, shift]
  congr 1
  funext m
  congr 1
  ring

/-- The exact model curvature commutes with a common translation of the pulse
and its derivative.  This is the cross-edge phase identity used by the
canonical configured sequence. -/
theorem modelCurvature_shift (y yd : ℝ → ℝ) (P q u : ℝ) :
    ModelOrbitDefect.modelCurvature (shift q y) (shift q yd) P u =
      ModelOrbitDefect.modelCurvature y yd P (u - q) := by
  simp only [ModelOrbitDefect.modelCurvature, shift]
  have hy : (∑' m : ℤ, y (u - m * P - q)) =
      ∑' m : ℤ, y (u - q - m * P) := by
    apply tsum_congr
    intro m
    congr 1
    ring
  have hyd : (∑' m : ℤ, yd (u - m * P - q)) =
      ∑' m : ℤ, yd (u - q - m * P) := by
    apply tsum_congr
    intro m
    congr 1
    ring
  rw [hy, hyd]

/-- Hence a uniform periodized strip for the current pulse is inherited by
its phase-translated predecessor with the same strip constant. -/
theorem previous_periodized_strip_of_current
    {y : ℝ → ℝ} {P q au : ℝ}
    (h : ∀ u, ModelOrbitDefect.periodizedPulse y P u ≤ au) :
    ∀ u, ModelOrbitDefect.periodizedPulse (shift q y) P u ≤ au := by
  intro u
  rw [periodizedPulse_shift]
  exact h (u - q)

end ShiftedCurvatureJetMajorant
