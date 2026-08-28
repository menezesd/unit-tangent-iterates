import Mathlib
import UnitTangentIterates.C2NormalPathReparam
import UnitTangentIterates.InterpolationPathDist

/-!
# Exact spatial C2 remainder for the interpolation path

The interpolation gauge exports time derivatives of `Phi`, spatial
continuity, and translation-periodicity.  None of those statements gives a
spatial derivative of `Phi`.  This file therefore records, without adding an
unsound inference, the precise spatial certificate still needed to turn the
exported equality `Gamma.eta = pathEta ... Phi` into `C2NormalPathData`.
-/

noncomputable section

open Set Function MarkedSpace PathMetric

namespace InterpolationPathDist

/-- The exact spatial regularity missing from the six raw interpolation-gauge
certificates.  A proof can be supplied by a C2 dependence-on-initial-data
theorem for the gauge ODE, followed by the chain rule for `scaledEta`. -/
structure PathEtaSpatialC2Certificate
    (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (Phi : ℝ → ℝ → ℝ) where
  eta1 : ℝ → ℝ → ℝ
  eta2 : ℝ → ℝ → ℝ
  eta_deriv : ∀ t u,
    HasDerivAt (pathEta k0 k1 theta0 L Phi t) (eta1 t u) u
  eta1_deriv : ∀ t u, HasDerivAt (eta1 t) (eta2 t u) u
  eta1_cont : ∀ t, Continuous (eta1 t)
  eta2_cont : ∀ t, Continuous (eta2 t)
  eta1_bdd : ∀ t, BddAbove (range fun u => |eta1 t u|)
  eta2_bdd : ∀ t, BddAbove (range fun u => |eta2 t u|)
  eta_periodic : ∀ t, Periodic (pathEta k0 k1 theta0 L Phi t) 1
  eta1_periodic : ∀ t, Periodic (eta1 t) 1
  eta2_periodic : ∀ t, Periodic (eta2 t) 1

/-- Convert the strengthened interpolation constructor's normal-rate equality
and the exact residual spatial certificate into the generic C2 path data used
by controlled junction reparameterization. -/
def PathEtaSpatialC2Certificate.toC2NormalPathData
    {p q : MarkedSpace.Data} {Gamma : NormalPath p q}
    {k0 k1 : ℝ → ℝ} {theta0 L : ℝ} {Phi : ℝ → ℝ → ℝ}
    (C : PathEtaSpatialC2Certificate k0 k1 theta0 L Phi)
    (heta : Gamma.eta = pathEta k0 k1 theta0 L Phi) :
    C2NormalPathData Gamma where
  eta1 := C.eta1
  eta2 := C.eta2
  eta_deriv := by
    intro t u
    rw [heta]
    exact C.eta_deriv t u
  eta1_deriv := C.eta1_deriv
  eta1_cont := C.eta1_cont
  eta2_cont := C.eta2_cont
  eta1_bdd := C.eta1_bdd
  eta2_bdd := C.eta2_bdd
  eta_periodic := by
    intro t
    rw [heta]
    exact C.eta_periodic t
  eta1_periodic := C.eta1_periodic
  eta2_periodic := C.eta2_periodic

/-- Logical audit: the precise additional proposition required beyond a
normal path and its exported `eta` equality. -/
def HasInterpolationPathEtaC2
    {p q : MarkedSpace.Data} (Gamma : NormalPath p q)
    (k0 k1 : ℝ → ℝ) (theta0 L : ℝ) (Phi : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : PathEtaSpatialC2Certificate k0 k1 theta0 L Phi,
    Gamma.eta = pathEta k0 k1 theta0 L Phi

def c2NormalPathData_of_hasInterpolationPathEtaC2
    {p q : MarkedSpace.Data} {Gamma : NormalPath p q}
    {k0 k1 : ℝ → ℝ} {theta0 L : ℝ} {Phi : ℝ → ℝ → ℝ}
    (h : HasInterpolationPathEtaC2 Gamma k0 k1 theta0 L Phi) :
    C2NormalPathData Gamma :=
  h.choose.toC2NormalPathData h.choose_spec

end InterpolationPathDist

