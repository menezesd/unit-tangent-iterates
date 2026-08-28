import Mathlib
import UnitTangentIterates.ModelGaugeControlledFamilyChooser
import UnitTangentIterates.PeriodicDerivativeAdapters

/-!
# Nonaffine endpoint markings for selected-rear gauge stages

The time-dependent gauge coordinate used to construct a rear normal path is
not, in general, the fixed change of marking at its two endpoints.  This file
records the latter datum explicitly and turns the rear-arclength
diffeomorphism estimates into the junction certificates used by recursive
assembly.
-/

noncomputable section

open Set Function MarkedSpace

namespace PathMetric

/-- The fixed endpoint change of marking obtained by freezing the gauge flow
at its terminal time.  The fields deliberately retain the time-dependent
names `Phi`, `phi1`, and `phi2` exported by
`GaugeRearFamilyFromFront`, but every junction field below is evaluated at
the single time `Gamma.T`.  Thus this package cannot accidentally use the
moving gauge map as a spatial reparameterization of the whole path. -/
structure TerminalGaugeEndpointData
    {p q p' q' : Data} (Gamma : NormalPath p q)
    (hC2 : C2NormalPathData Gamma) (M N : ℝ) where
  Phi : ℝ → ℝ → ℝ
  phi1 : ℝ → ℝ → ℝ
  phi2 : ℝ → ℝ → ℝ
  m : ℝ
  m_pos : 0 < m
  terminal_deriv : ∀ u,
    HasDerivAt (Phi Gamma.T) (phi1 Gamma.T u) u
  terminal_first_deriv : ∀ u,
    HasDerivAt (phi1 Gamma.T) (phi2 Gamma.T u) u
  terminal_first_cont : Continuous (phi1 Gamma.T)
  terminal_second_cont : Continuous (phi2 Gamma.T)
  terminal_jacobian_lower : ∀ u, m ≤ phi1 Gamma.T u
  terminal_jacobian_upper : ∀ u, |phi1 Gamma.T u| ≤ M
  terminal_second_upper : ∀ u, |phi2 Gamma.T u| ≤ N
  terminal_zero : Phi Gamma.T 0 = 0
  terminal_one : Phi Gamma.T 1 = 1
  terminal_add_one : ∀ u, Phi Gamma.T (u + 1) = Phi Gamma.T u + 1
  /-- Identification of the initial selected-rear marking after applying the
  one fixed terminal map. -/
  start_selectedRear : ∀ u, Gamma.X 0 (Phi Gamma.T u) = p'.1 u
  /-- Identification of the terminal selected-rear marking after applying
  that same fixed map. -/
  finish_selectedRear : ∀ u, Gamma.X Gamma.T (Phi Gamma.T u) = q'.1 u
  /-- Bounds for the two chain-rule expressions exported by the terminal
  gauge frame. -/
  eta1_bdd : ∀ t, BddAbove (Set.range fun u =>
    |hC2.eta1 t (Phi Gamma.T u) * phi1 Gamma.T u|)
  eta2_bdd : ∀ t, BddAbove (Set.range fun u =>
    |hC2.eta2 t (Phi Gamma.T u) * phi1 Gamma.T u ^ 2 +
      hC2.eta1 t (Phi Gamma.T u) * phi2 Gamma.T u|)

/-- A fixed nonaffine rear-arclength marking, with exactly the endpoint and
quantitative data needed by `ReparamJunctionCertificate`. -/
structure NonaffineGaugeEndpointData
    {p q p' q' : Data} (Gamma : NormalPath p q)
    (hC2 : C2NormalPathData Gamma) (M N : ℝ) where
  phi : ℝ → ℝ
  phi1 : ℝ → ℝ
  phi2 : ℝ → ℝ
  m : ℝ
  m_pos : 0 < m
  phi_deriv : ∀ u, HasDerivAt phi (phi1 u) u
  phi1_deriv : ∀ u, HasDerivAt phi1 (phi2 u) u
  phi1_cont : Continuous phi1
  phi2_cont : Continuous phi2
  jacobian_lower : ∀ u, m ≤ phi1 u
  jacobian_upper : ∀ u, |phi1 u| ≤ M
  second_upper : ∀ u, |phi2 u| ≤ N
  phi_zero : phi 0 = 0
  phi_one : phi 1 = 1
  phi_add_one : ∀ u, phi (u + 1) = phi u + 1
  phi1_periodic : Periodic phi1 1
  phi2_periodic : Periodic phi2 1
  /-- Canonical selected-rear identification at the initial endpoint. -/
  start_selectedRear : ∀ u, Gamma.X 0 (phi u) = p'.1 u
  /-- Canonical selected-rear identification at the final endpoint. -/
  finish_selectedRear : ∀ u, Gamma.X Gamma.T (phi u) = q'.1 u
  /-- Uniform bounds exported by the terminal gauge frame.  These are stated
  for the two chain-rule expressions, so no global coordinate inverse is
  exposed downstream. -/
  eta1_bdd : ∀ t, BddAbove (Set.range fun u =>
    |hC2.eta1 t (phi u) * phi1 u|)
  eta2_bdd : ∀ t, BddAbove (Set.range fun u =>
    |hC2.eta2 t (phi u) * phi1 u ^ 2 + hC2.eta1 t (phi u) * phi2 u|)

/-- Forget the moving flow after freezing it at `Gamma.T`.  Periodicity of
the two spatial derivatives is derived from the terminal translation law,
not assumed independently. -/
def TerminalGaugeEndpointData.toNonaffine
    {p q p' q' : Data} {Gamma : NormalPath p q}
    {hC2 : C2NormalPathData Gamma} {M N : ℝ}
    (E : TerminalGaugeEndpointData (p' := p') (q' := q') Gamma hC2 M N) :
    NonaffineGaugeEndpointData (p' := p') (q' := q') Gamma hC2 M N where
  phi := E.Phi Gamma.T
  phi1 := E.phi1 Gamma.T
  phi2 := E.phi2 Gamma.T
  m := E.m
  m_pos := E.m_pos
  phi_deriv := E.terminal_deriv
  phi1_deriv := E.terminal_first_deriv
  phi1_cont := E.terminal_first_cont
  phi2_cont := E.terminal_second_cont
  jacobian_lower := E.terminal_jacobian_lower
  jacobian_upper := E.terminal_jacobian_upper
  second_upper := E.terminal_second_upper
  phi_zero := E.terminal_zero
  phi_one := E.terminal_one
  phi_add_one := E.terminal_add_one
  phi1_periodic :=
    PeriodicDerivativeAdapters.periodic_derivative_of_additive_translation
      E.terminal_add_one E.terminal_deriv
  phi2_periodic :=
    PeriodicDerivativeAdapters.periodic_derivative_of_periodic
      (PeriodicDerivativeAdapters.periodic_derivative_of_additive_translation
        E.terminal_add_one E.terminal_deriv)
      E.terminal_first_deriv
  start_selectedRear := E.start_selectedRear
  finish_selectedRear := E.finish_selectedRear
  eta1_bdd := E.eta1_bdd
  eta2_bdd := E.eta2_bdd

/-- Rear-arclength endpoint data gives the fixed nonaffine junction without
losing its sharp uniform derivative constants. -/
def NonaffineGaugeEndpointData.toJunction
    {p q p' q' : Data} {Gamma : NormalPath p q}
    {hC2 : C2NormalPathData Gamma} {M N : ℝ}
    (E : NonaffineGaugeEndpointData (p' := p') (q' := q') Gamma hC2 M N) :
    ReparamJunctionCertificate (p' := p') (q' := q') Gamma where
  phi := E.phi
  phi1 := E.phi1
  phi2 := E.phi2
  m := E.m
  M := M
  N := N
  m_pos := E.m_pos
  phi_deriv := E.phi_deriv
  phi1_deriv := E.phi1_deriv
  phi1_cont := E.phi1_cont
  phi2_cont := E.phi2_cont
  jacobian_lower := E.jacobian_lower
  jacobian_upper := E.jacobian_upper
  second_upper := E.second_upper
  phi_zero := E.phi_zero
  phi_one := E.phi_one
  phi_add_one := E.phi_add_one
  phi1_periodic := E.phi1_periodic
  phi2_periodic := E.phi2_periodic
  start := E.start_selectedRear
  finish := E.finish_selectedRear

/-- The terminal rear-arclength map and the gauge-frame spatial certificate
canonically determine the `C²` reparameterization certificate. -/
def NonaffineGaugeEndpointData.toC2Certificate
    {p q p' q' : Data} {Gamma : NormalPath p q} {hC2 : C2NormalPathData Gamma}
    {M N : ℝ}
    (E : NonaffineGaugeEndpointData (p' := p') (q' := q') Gamma hC2 M N) :
    ReparamC2Certificate Gamma hC2 E.toJunction where
  eta1 := fun t u => hC2.eta1 t (E.phi u) * E.phi1 u
  eta2 := fun t u => hC2.eta2 t (E.phi u) * E.phi1 u ^ 2 +
    hC2.eta1 t (E.phi u) * E.phi2 u
  eta_deriv := fun t u => (hC2.eta_deriv t (E.phi u)).comp u (E.phi_deriv u)
  eta1_deriv := by
    intro t u
    convert ((hC2.eta1_deriv t (E.phi u)).comp u (E.phi_deriv u)).mul
      (E.phi1_deriv u) using 1
    simp only [Function.comp_apply]
    ring
  eta1_cont := fun t => by
    have hphic : Continuous E.phi :=
      Differentiable.continuous fun u => (E.phi_deriv u).differentiableAt
    exact ((hC2.eta1_cont t).comp hphic).mul E.phi1_cont
  eta2_cont := fun t => by
    have hphic : Continuous E.phi :=
      Differentiable.continuous fun u => (E.phi_deriv u).differentiableAt
    exact (((hC2.eta2_cont t).comp hphic).mul (E.phi1_cont.pow 2)).add
      (((hC2.eta1_cont t).comp hphic).mul E.phi2_cont)
  eta1_bdd := E.eta1_bdd
  eta2_bdd := E.eta2_bdd
  eta_periodic := by
    intro t u
    show Gamma.eta t (E.phi (u + 1)) = Gamma.eta t (E.phi u)
    rw [E.phi_add_one]
    exact hC2.eta_periodic t (E.phi u)
  eta1_periodic := by
    intro t u
    show hC2.eta1 t (E.phi (u + 1)) * E.phi1 (u + 1)
        = hC2.eta1 t (E.phi u) * E.phi1 u
    rw [E.phi_add_one, hC2.eta1_periodic t, E.phi1_periodic]
  eta2_periodic := by
    intro t u
    show hC2.eta2 t (E.phi (u + 1)) * E.phi1 (u + 1) ^ 2
          + hC2.eta1 t (E.phi (u + 1)) * E.phi2 (u + 1)
        = hC2.eta2 t (E.phi u) * E.phi1 u ^ 2 + hC2.eta1 t (E.phi u) * E.phi2 u
    rw [E.phi_add_one, hC2.eta2_periodic t, E.phi1_periodic,
      hC2.eta1_periodic t, E.phi2_periodic]
  eta1_formula := fun _ _ => rfl
  eta2_formula := fun _ _ => rfl

/-- Sequence-level chooser for nonaffine selected-rear endpoint markings.
The `C²` chain-rule certificate is kept separate because it is supplied by
the gauge frame export, whereas `E` is supplied by the fixed rear-arclength
diffeomorphism. -/
def ModelRecursiveEndpointDiffeomorphisms.ofNonaffineGaugeStages
    {Q : ℕ → ℕ → Data} {P0 P1 khat G1 Cg M N : ℝ}
    (A : ModelRecursiveControlledStages Q P0 P1 khat G1 Cg)
    (E : ∀ n k, NonaffineGaugeEndpointData
      (p' := Q n k) (q' := Q n (k + 1))
      (A.stage n k).path (A.stage n k).c2 M N)
    (hP0 : 0 < P0) (hP1 : 0 ≤ P1) (hkhat : 0 ≤ khat)
    (hG1 : 0 ≤ G1) (hCg : 0 ≤ Cg) (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ModelRecursiveEndpointDiffeomorphisms A P0 (P1 * M) khat
      (G1 * M ^ 2 + P1 * N) (Cg * M ^ 2 + khat * P1 * N) :=
  ModelRecursiveEndpointDiffeomorphisms.ofBaseVariableSpeed A
    (fun n k => (E n k).toJunction) (fun n k => (E n k).toC2Certificate)
    (fun _ _ => rfl) (fun _ _ => rfl)
    hP0 hP1 hkhat hG1 hCg hM hN

end PathMetric
