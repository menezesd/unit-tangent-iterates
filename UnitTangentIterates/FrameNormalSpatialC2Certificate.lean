import Mathlib
import UnitTangentIterates.C2NormalPathReparam
import UnitTangentIterates.PeriodicDerivativeAdapters
import UnitTangentIterates.UniformFrameBounds

/-!
# Spatial C2 certificates for a marked frame-normal rate

This module keeps the analytic chain rule separate from the gauge-flow
construction.  The two derivatives of the unmarked normal rate are supplied
as explicit witnesses; the marking contributes its first two spatial
derivatives.  Periodicity of the two resulting derivatives is then recovered
from periodicity of the marked normal rate, rather than by expanding products.
-/

noncomputable section

open Set Function MarkedSpace PathMetric UniformFrameBounds

namespace FrameNormalSpatialC2Certificate

/-- Spatial `C²` data for a scalar family before it is read in a marking. -/
structure Data (normal normal1 normal2 : ℝ → ℝ → ℝ) (period : ℝ → ℝ) where
  normal_deriv : ∀ t x, HasDerivAt (normal t) (normal1 t x) x
  normal1_deriv : ∀ t x, HasDerivAt (normal1 t) (normal2 t x) x
  normal1_cont : ∀ t, Continuous (normal1 t)
  normal2_cont : ∀ t, Continuous (normal2 t)
  normal_periodic : ∀ t, Periodic (normal t) (period t)

/-- The canonical derivative witnesses supplied by a `C²` scalar family. -/
theorem of_contDiff_two
    {normal : ℝ → ℝ → ℝ} {period : ℝ → ℝ}
    (hnormal : ContDiff ℝ (2 : ℕ) (uncurry normal))
    (hperiodic : ∀ t, Periodic (normal t) (period t)) :
    Data normal (partialX normal) (partialX (partialX normal)) period := by
  have hnormal1 : ContDiff ℝ (1 : ℕ) (uncurry normal) := hnormal.of_le (by norm_num)
  have hpartial : ContDiff ℝ (1 : ℕ) (uncurry (partialX normal)) :=
    contDiff_partialX hnormal
  exact
    { normal_deriv := fun t x => hasDerivAt_partialX hnormal1 t x
      normal1_deriv := fun t x => hasDerivAt_partialX hpartial t x
      normal1_cont := fun t =>
        (hpartial.continuous.comp (continuous_const.prodMk continuous_id))
      normal2_cont := fun t =>
        ((contDiff_partialX hpartial).continuous.comp
          (continuous_const.prodMk continuous_id))
      normal_periodic := hperiodic }

/-- Chain-rule construction of the spatial data required by
`C2NormalPathData`.  Additive periodicity of the marking makes the composite
normal rate one-periodic; periodicity of its two derivatives is then obtained
by derivative uniqueness. -/
def c2NormalPathData_of_marked_frameNormal
    {p q : MarkedSpace.Data} (Gamma : NormalPath p q)
    {normal normal1 normal2 Phi phi1 phi2 : ℝ → ℝ → ℝ}
    {period : ℝ → ℝ}
    (hframe : Data normal normal1 normal2 period)
    (heta : ∀ t u, Gamma.eta t u = normal t (Phi t u))
    (hphi1 : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u)
    (hphi2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u)
    (hphi1c : ∀ t, Continuous (phi1 t))
    (hphi2c : ∀ t, Continuous (phi2 t))
    (htrans : ∀ t u, Phi t (u + 1) = Phi t u + period t) :
    C2NormalPathData Gamma := by
  let eta1 : ℝ → ℝ → ℝ := fun t u => normal1 t (Phi t u) * phi1 t u
  let eta2 : ℝ → ℝ → ℝ := fun t u =>
    normal2 t (Phi t u) * phi1 t u ^ 2 + normal1 t (Phi t u) * phi2 t u
  have hPhiC : ∀ t, Continuous (Phi t) := fun t =>
    continuous_iff_continuousAt.2 fun u => (hphi1 t u).continuousAt
  have hetaD : ∀ t u, HasDerivAt (Gamma.eta t) (eta1 t u) u := by
    intro t u
    rw [funext (heta t)]
    exact (hframe.normal_deriv t (Phi t u)).comp u (hphi1 t u)
  have heta1D : ∀ t u, HasDerivAt (eta1 t) (eta2 t u) u := by
    intro t u
    dsimp [eta1, eta2]
    convert ((hframe.normal1_deriv t (Phi t u)).comp u (hphi1 t u)).mul
      (hphi2 t u) using 1
    simp only [Function.comp_apply]
    ring
  have hetaPer : ∀ t, Periodic (Gamma.eta t) 1 := by
    intro t u
    rw [heta t (u + 1), htrans t u, hframe.normal_periodic t, ← heta t u]
  obtain ⟨heta1Per, heta2Per⟩ :=
    PeriodicDerivativeAdapters.eta_derivatives_periodic hetaPer hetaD heta1D
  have heta1Cont : ∀ t, Continuous (eta1 t) := fun t =>
    (hframe.normal1_cont t).comp (hPhiC t) |>.mul (hphi1c t)
  have heta2Cont : ∀ t, Continuous (eta2 t) := fun t =>
    (((hframe.normal2_cont t).comp (hPhiC t)).mul ((hphi1c t).pow 2)).add
      (((hframe.normal1_cont t).comp (hPhiC t)).mul (hphi2c t))
  exact
    { eta1 := eta1
      eta2 := eta2
      eta_deriv := hetaD
      eta1_deriv := heta1D
      eta1_cont := heta1Cont
      eta2_cont := heta2Cont
      eta1_bdd := fun t =>
        ArclengthInverse.bddAbove_abs_of_periodic zero_lt_one (heta1Cont t) (heta1Per t)
      eta2_bdd := fun t =>
        ArclengthInverse.bddAbove_abs_of_periodic zero_lt_one (heta2Cont t) (heta2Per t)
      eta_periodic := hetaPer
      eta1_periodic := heta1Per
      eta2_periodic := heta2Per }

/-- Final adapter in the form returned by the gauge rear-family construction:
the unmarked normal rate is `C²` and periodic on the physical rear period,
while the marking and its two spatial derivatives are supplied explicitly. -/
def c2NormalPathData_of_contDiff_frameNormal
    {p q : MarkedSpace.Data} (Gamma : NormalPath p q)
    {normal Phi phi1 phi2 : ℝ → ℝ → ℝ} {period : ℝ → ℝ}
    (hnormal : ContDiff ℝ (2 : ℕ) (uncurry normal))
    (hperiodic : ∀ t, Periodic (normal t) (period t))
    (heta : ∀ t u, Gamma.eta t u = normal t (Phi t u))
    (hphi1 : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u)
    (hphi2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u)
    (hphi1c : ∀ t, Continuous (phi1 t))
    (hphi2c : ∀ t, Continuous (phi2 t))
    (htrans : ∀ t u, Phi t (u + 1) = Phi t u + period t) :
    C2NormalPathData Gamma :=
  c2NormalPathData_of_marked_frameNormal Gamma (of_contDiff_two hnormal hperiodic)
    heta hphi1 hphi2 hphi1c hphi2c htrans

end FrameNormalSpatialC2Certificate
