import Mathlib
import UnitTangentIterates.GaugeRearFamilyFromFront
import UnitTangentIterates.FrameNormalSpatialC2Certificate

/-!
# C2 spatial data for the gauge path of selected rears

This is the public postprocessor for
`exists_variableSpeed_normalPath_of_rearFamily_from_front_with_eta_c2flow`.
It consumes exactly the eta, additive-translation, and existential flow
derivative fields returned by that theorem.
-/

noncomputable section

open Set Function Complex MarkedSpace PathMetric PathMetric.NormalPath

namespace GaugeRearFamilyFromFrontC2

open RearFamilyFrame RearOwnArclength RearTrack FrameNormalSpatialC2Certificate

/-- The gauge path returned by the front-to-rear constructor carries the
spatial `C²` normal-rate data required by reparameterization and completeness. -/
def c2NormalPathData_of_rearFamily_from_front_c2flow
    {a b : MarkedSpace.Data} (Gamma' : NormalPath a b)
    {Ydot : ℝ → ℝ → ℂ} {Theta delta sf Phi phi1 phi2 : ℝ → ℝ → ℝ}
    {P : ℝ → ℝ}
    (hnormal : ContDiff ℝ (2 : ℕ)
      (uncurry (frameNormal Ydot (RearOwnArclength.rearOwnAngle Theta delta sf))))
    (hperiodic : ∀ t, Function.Periodic
      (frameNormal Ydot (RearOwnArclength.rearOwnAngle Theta delta sf) t)
      (rearArclength (delta t) (P t)))
    (heta : ∀ t u, Gamma'.eta t u =
      frameNormal Ydot (RearOwnArclength.rearOwnAngle Theta delta sf) t (Phi t u))
    (htrans : ∀ t u, Phi t (u + 1) =
      Phi t u + rearArclength (delta t) (P t))
    (hphi1 : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u)
    (hphi2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u)
    (hphi1c : ∀ t, Continuous (phi1 t))
    (hphi2c : ∀ t, Continuous (phi2 t)) :
    C2NormalPathData Gamma' :=
  c2NormalPathData_of_contDiff_frameNormal Gamma' hnormal hperiodic heta
    hphi1 hphi2 hphi1c hphi2c htrans

/-- Convenient conjunction form for destructuring the result of
`exists_variableSpeed_normalPath_of_rearFamily_from_front_with_eta_c2flow`:
all original path information is retained while the spatial certificate is
attached. -/
theorem attach_c2NormalPathData
    {a b : MarkedSpace.Data} (Gamma' : NormalPath a b)
    {Ydot : ℝ → ℝ → ℂ} {Theta delta sf Phi phi1 phi2 : ℝ → ℝ → ℝ}
    {P : ℝ → ℝ} {R : Prop}
    (hR : R)
    (hnormal : ContDiff ℝ (2 : ℕ)
      (uncurry (frameNormal Ydot (RearOwnArclength.rearOwnAngle Theta delta sf))))
    (hperiodic : ∀ t, Function.Periodic
      (frameNormal Ydot (RearOwnArclength.rearOwnAngle Theta delta sf) t)
      (rearArclength (delta t) (P t)))
    (heta : ∀ t u, Gamma'.eta t u =
      frameNormal Ydot (RearOwnArclength.rearOwnAngle Theta delta sf) t (Phi t u))
    (htrans : ∀ t u, Phi t (u + 1) =
      Phi t u + rearArclength (delta t) (P t))
    (hphi1 : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u)
    (hphi2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u)
    (hphi1c : ∀ t, Continuous (phi1 t))
    (hphi2c : ∀ t, Continuous (phi2 t)) :
    R ∧ Nonempty (C2NormalPathData Gamma') :=
  ⟨hR, ⟨c2NormalPathData_of_rearFamily_from_front_c2flow Gamma' hnormal
    hperiodic heta htrans hphi1 hphi2 hphi1c hphi2c⟩⟩

/-- Existential form matching the witness package exported by
`GaugeRearFamilyFromFront.exists_variableSpeed_normalPath_of_rearFamily_from_front_with_eta_c2flow`.
It appends the spatial `C²` datum without exposing the proof-local gauge frame. -/
theorem exists_c2NormalPathData_of_rearFamily_from_front_c2flow
    {a b : MarkedSpace.Data} {Ydot : ℝ → ℝ → ℂ}
    {Theta delta sf : ℝ → ℝ → ℝ} {P : ℝ → ℝ}
    (hnormal : ContDiff ℝ (2 : ℕ)
      (uncurry (frameNormal Ydot (RearOwnArclength.rearOwnAngle Theta delta sf))))
    (hperiodic : ∀ t, Function.Periodic
      (frameNormal Ydot (RearOwnArclength.rearOwnAngle Theta delta sf) t)
      (rearArclength (delta t) (P t)))
    (hex : ∃ (Phi phi1 phi2 : ℝ → ℝ → ℝ) (Gamma' : NormalPath a b),
      (∀ t u, Gamma'.eta t u = frameNormal Ydot
        (RearOwnArclength.rearOwnAngle Theta delta sf) t (Phi t u)) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + rearArclength (delta t) (P t)) ∧
      (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
      (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
      (∀ t, Continuous (phi1 t)) ∧ (∀ t, Continuous (phi2 t))) :
    ∃ (Phi phi1 phi2 : ℝ → ℝ → ℝ) (Gamma' : NormalPath a b),
      (∀ t u, Gamma'.eta t u = frameNormal Ydot
        (RearOwnArclength.rearOwnAngle Theta delta sf) t (Phi t u)) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + rearArclength (delta t) (P t)) ∧
      (∀ t u, HasDerivAt (Phi t) (phi1 t u) u) ∧
      (∀ t u, HasDerivAt (phi1 t) (phi2 t u) u) ∧
      (∀ t, Continuous (phi1 t)) ∧ (∀ t, Continuous (phi2 t)) ∧
      Nonempty (C2NormalPathData Gamma') := by
  obtain ⟨Phi, phi1, phi2, Gamma', heta, htrans, hphi1, hphi2, hphi1c, hphi2c⟩ := hex
  refine ⟨Phi, phi1, phi2, Gamma', heta, htrans, hphi1, hphi2, hphi1c, hphi2c, ?_⟩
  exact ⟨c2NormalPathData_of_rearFamily_from_front_c2flow Gamma' hnormal hperiodic
    heta htrans hphi1 hphi2 hphi1c hphi2c⟩

end GaugeRearFamilyFromFrontC2
