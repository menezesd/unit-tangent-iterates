import Mathlib
import UnitTangentIterates.NormalizedSelectedRearClosure
import UnitTangentIterates.ControlledJunctionVariableSpeedDistance

/-! # Selected-rear closure to strict limit regularity -/

noncomputable section

open Set

namespace SelectedRearLimitStrictnessAdapter

open NormalizedSelectedRearClosure

/-- The exact strictness/regularity output consumed by the paper capstone.
Embeddedness is intentionally not repeated: it follows independently from
the positive chord-arc constant in the closed tube. -/
structure StrictSelectedRearOutput
    (kap : ℝ) (p q : MarkedSpace.Data) (L : ℝ)
    (Theta k : ℝ → ℝ) (d : SteeringData kap) : Prop where
  canonical : q = SelectedInverseMap.selInv kap p
  curvature_pos : ∀ s, 0 < k s
  rear_C3 : ContDiff ℝ (3 : ℕ)
    (fun x => ∫ t in (0 : ℝ)..x,
      Complex.exp (((Theta t - d.delta t : ℝ) : ℂ) * Complex.I))

/-- Compose zero-pinching selected-rear identification with the exact-orbit
strictness bootstrap.  These are precisely the two analytic steps in the
paper after completeness of the summable normal-path chain. -/
@[deprecated "Use PhysicalSelectedRearStrictnessAdapter.physicalLimitStrictnessData_of_packagedRear; this normalized closure interface does not identify the physical perimeter." (since := "2026-08-24")]
theorem strictSelectedRearOutput_of_closure
    {kap c kmin dlt cR kR dR L : ℝ} {p q : MarkedSpace.Data}
    {Theta K sf k k' : ℝ → ℝ} (d : SteeringData kap)
    (hc : 0 < c) (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hp : MarkedSpace.IsTubeMember c kmin dlt p)
    (hq : MarkedSpace.IsTubeMember cR kR dR q)
    (hfront : ∀ s, HasDerivAt (MarkedSpace.ev p)
      (Complex.exp (Complex.I * (Theta s : ℂ))) s)
    (hTheta : ∀ s, HasDerivAt Theta (K s) s)
    (hsf : ∀ x, RearTrack.rearArclength d.delta (sf x) = x)
    (hperim : MarkedSpace.perim q =
      RearTrack.rearArclength d.delta (MarkedSpace.perim p))
    (hrear : ∀ x, MarkedSpace.ev q x =
      RearTrack.rearTrack (MarkedSpace.ev p) Theta d.delta (sf x))
    (hperimP : MarkedSpace.perim p = 1)
    (hL : 0 < L) (hThetaC1 : ContDiff ℝ (1 : ℕ) Theta)
    (hThetaK : ∀ s, HasDerivAt Theta (d.K s) s)
    (hkper : Function.Periodic k L) (hk : ∀ s, HasDerivAt k (k' s) s)
    (hk0 : ∀ s, 0 ≤ k s)
    (hnext : ∀ s,
      0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2))
    (hkne : ∃ s, k s ≠ 0) :
    StrictSelectedRearOutput kap p q L Theta k d := by
  have hKeq : ∀ s, K s = d.K s := fun s => (hTheta s).unique (hThetaK s)
  have hdper : Function.Periodic d.delta (MarkedSpace.perim p) := by
    rw [hperimP]
    exact d.delta_periodic
  have hsteer : ∀ s, HasDerivAt d.delta (K s - Real.sin (d.delta s)) s := by
    intro s
    rw [hKeq s]
    exact d.steering s
  have hcanonical : q = SelectedInverseMap.selInv kap p :=
    packagedRear_eq_selInv hc hkap0 hkap1 hp hq hfront hTheta
      hdper d.delta_mem hsteer hsf hperim hrear
  obtain ⟨hkpos, hrearC3⟩ := rear_regular_and_strict d hL hThetaC1 hThetaK
    hkper hk hk0 hnext hkne
  exact ⟨hcanonical, hkpos, hrearC3⟩

/-- Capstone-facing version for an exact selected-inverse pair.  Once closure
has identified the reconstructed rear with `selInv`, only the intrinsic
strictness data are needed. -/
@[deprecated "Use PhysicalSelectedRearStrictnessAdapter physical-arclength outputs." (since := "2026-08-24")]
theorem strictSelectedRearOutput_of_canonical
    {kap L : ℝ} {p q : MarkedSpace.Data} {Theta k k' : ℝ → ℝ}
    (d : SteeringData kap)
    (hcanonical : q = SelectedInverseMap.selInv kap p)
    (hL : 0 < L) (hThetaC1 : ContDiff ℝ (1 : ℕ) Theta)
    (hTheta : ∀ s, HasDerivAt Theta (d.K s) s)
    (hkper : Function.Periodic k L) (hk : ∀ s, HasDerivAt k (k' s) s)
    (hk0 : ∀ s, 0 ≤ k s)
    (hnext : ∀ s,
      0 ≤ (k s + k' s / (1 + k s ^ 2)) / Real.sqrt (1 + k s ^ 2))
    (hkne : ∃ s, k s ≠ 0) :
    StrictSelectedRearOutput kap p q L Theta k d := by
  obtain ⟨hkpos, hrearC3⟩ := rear_regular_and_strict d hL hThetaC1 hTheta
    hkper hk hk0 hnext hkne
  exact ⟨hcanonical, hkpos, hrearC3⟩

/-- The controlled-junction completeness output supplies the convergence and
closed-tube half of the paper paragraph; the selected-rear closure datum is
the only additional analytic input required for strictness. -/
theorem strict_output_with_limit
    {Q : ℕ → MarkedSpace.Data} {X p q : MarkedSpace.Data}
    {kap L : ℝ} {Theta k k' : ℝ → ℝ} (d : SteeringData kap)
    (hlim : Filter.Tendsto Q Filter.atTop (nhds X))
    (hstrict : StrictSelectedRearOutput kap p q L Theta k d) :
    Filter.Tendsto Q Filter.atTop (nhds X) ∧
      StrictSelectedRearOutput kap p q L Theta k d :=
  ⟨hlim, hstrict⟩

end SelectedRearLimitStrictnessAdapter
