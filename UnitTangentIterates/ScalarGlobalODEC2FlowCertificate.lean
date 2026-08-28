import Mathlib

/-!
# A reusable certificate for scalar global C2 flows

This record is the constructor-independent target of smooth scalar ODE flow
theorems such as `GaugeFlowSmooth.exists_gaugeFlow_smooth_of_bounds`.
-/

noncomputable section

open Function

namespace ScalarGlobalODEC2Flow

/-- A coherent scalar flow together with its first two derivatives in the
initial parameter and the corresponding first and second variational
equations. -/
structure Certificate
    (h hx hxx : ℝ → ℝ → ℝ) (ell : ℝ)
    (Phi phi1 phi2 : ℝ → ℝ → ℝ) (K1 K2 : ℝ → ℝ) : Prop where
  initial : ∀ u, Phi 0 u = ell * u
  solves : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t
  phi1_initial : ∀ u, phi1 0 u = ell
  phi2_initial : ∀ u, phi2 0 u = 0
  phi1_variational : ∀ u t,
    HasDerivAt (fun r => phi1 r u) (hx t (Phi t u) * phi1 t u) t
  phi2_variational : ∀ u t,
    HasDerivAt (fun r => phi2 r u)
      (hxx t (Phi t u) * phi1 t u ^ 2 + hx t (Phi t u) * phi2 t u) t
  spatial_deriv : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u
  spatial_second : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u
  phi2_continuous : ∀ t, Continuous (phi2 t)
  phi1_lower : ∀ t u, 0 < K1 t → K1 t ≤ phi1 t u
  phi1_abs_upper : ∀ t u, |phi1 t u| ≤ K2 t
  phi2_abs_upper : ∀ t u, |phi2 t u| ≤ K2 t

/-- Package a smooth coherent flow.  Spatial continuity of `Phi` and `phi1`
is not an additional hypothesis: it follows from the two spatial derivative
witnesses. -/
theorem exists_certificate_of_variational_data
    {h hx hxx : ℝ → ℝ → ℝ} {ell : ℝ}
    {Phi phi1 phi2 : ℝ → ℝ → ℝ} {K1 K2 : ℝ → ℝ}
    (hinitial : ∀ u, Phi 0 u = ell * u)
    (hsolves : ∀ u t, HasDerivAt (fun r => Phi r u) (h t (Phi t u)) t)
    (hphi10 : ∀ u, phi1 0 u = ell)
    (hphi20 : ∀ u, phi2 0 u = 0)
    (hvar1 : ∀ u t,
      HasDerivAt (fun r => phi1 r u) (hx t (Phi t u) * phi1 t u) t)
    (hvar2 : ∀ u t,
      HasDerivAt (fun r => phi2 r u)
        (hxx t (Phi t u) * phi1 t u ^ 2 + hx t (Phi t u) * phi2 t u) t)
    (hspace1 : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u)
    (hspace2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u)
    (hphi2c : ∀ t, Continuous (phi2 t))
    (hlower : ∀ t u, 0 < K1 t → K1 t ≤ phi1 t u)
    (hupper1 : ∀ t u, |phi1 t u| ≤ K2 t)
    (hupper2 : ∀ t u, |phi2 t u| ≤ K2 t) :
    ∃ C : Certificate h hx hxx ell Phi phi1 phi2 K1 K2,
      (∀ t, Continuous (Phi t)) ∧
      (∀ t, Continuous (phi1 t)) := by
  let C : Certificate h hx hxx ell Phi phi1 phi2 K1 K2 :=
    { initial := hinitial
      solves := hsolves
      phi1_initial := hphi10
      phi2_initial := hphi20
      phi1_variational := hvar1
      phi2_variational := hvar2
      spatial_deriv := hspace1
      spatial_second := hspace2
      phi2_continuous := hphi2c
      phi1_lower := hlower
      phi1_abs_upper := hupper1
      phi2_abs_upper := hupper2 }
  refine ⟨C, ?_, ?_⟩
  · intro t
    exact continuous_iff_continuousAt.2 fun u => (hspace1 t u).continuousAt
  · intro t
    exact continuous_iff_continuousAt.2 fun u => (hspace2 t u).continuousAt

/-- The spatial C2 portion in the direct form consumed by gauge and normal-rate
chain-rule adapters. -/
theorem Certificate.spatialC2
    {h hx hxx : ℝ → ℝ → ℝ} {ell : ℝ}
    {Phi phi1 phi2 : ℝ → ℝ → ℝ} {K1 K2 : ℝ → ℝ}
    (C : Certificate h hx hxx ell Phi phi1 phi2 K1 K2) :
    (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
      (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
      (∀ t, Continuous (phi1 t)) ∧
      (∀ t, Continuous (phi2 t)) := by
  exact ⟨C.spatial_deriv, C.spatial_second,
    fun t => continuous_iff_continuousAt.2 fun u =>
      (C.spatial_second t u).continuousAt,
    C.phi2_continuous⟩

end ScalarGlobalODEC2Flow

