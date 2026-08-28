import Mathlib
import UnitTangentIterates.InterpolationPathEtaC2Adapter
import UnitTangentIterates.PeriodicDerivativeAdapters
import UnitTangentIterates.InterpolationSecondOrder
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.InterpolationGaugeSmoothSpecialized

/-! # Spatial chain rules for the smooth interpolation normal rate -/

noncomputable section

open Set Function MarkedSpace PathMetric

namespace InterpolationPathDist

open CurvatureInterpolation InterpolationNormal InterpolationEstimate
  InterpolationSecondOrder InterpolationGauge PathMetricCircle

def smoothPathEta1 (k0 k1 : ℝ → ℝ) (theta0 L : ℝ)
    (Phi phi1 : ℝ → ℝ → ℝ) (t u : ℝ) : ℝ :=
  w t * normalVelDeriv k0 k1 theta0 L (B t) (Phi (B t) u) * phi1 (B t) u

def smoothPathEta2 (k0 k1 k0' k1' : ℝ → ℝ) (theta0 L : ℝ)
    (Phi phi1 phi2 : ℝ → ℝ → ℝ) (t u : ℝ) : ℝ :=
  w t * (normalVelSecondDeriv k0 k1 k0' k1' theta0 L (B t) (Phi (B t) u) *
      phi1 (B t) u ^ 2 +
    normalVelDeriv k0 k1 theta0 L (B t) (Phi (B t) u) * phi2 (B t) u)

/-- Joint continuity of the explicit profiled normal rate. -/
theorem continuous_uncurry_pathEta_of_jointPhi
    {k0 k1 : ℝ → ℝ} {theta0 L : ℝ} {Phi : ℝ → ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hPhi : Continuous (uncurry Phi)) :
    Continuous (uncurry (pathEta k0 k1 theta0 L Phi)) := by
  have hBu : Continuous (fun p : ℝ × ℝ => (B p.1, p.2)) :=
    (continuous_B.comp continuous_fst).prodMk continuous_snd
  have hPhiB : Continuous (fun p : ℝ × ℝ => Phi (B p.1) p.2) :=
    hPhi.comp hBu
  have harg : Continuous (fun p : ℝ × ℝ => (B p.1, Phi (B p.1) p.2)) :=
    (continuous_B.comp continuous_fst).prodMk hPhiB
  have hnv := (continuous_uncurry_normalVel (θ₀ := theta0) (L := L)
    hk0 hk1).comp harg
  simpa [pathEta, scaledEta] using (continuous_w.comp continuous_fst).mul hnv

/-- Joint continuity of the first explicit spatial normal-rate derivative. -/
theorem continuous_uncurry_smoothPathEta1
    {k0 k1 : ℝ → ℝ} {theta0 L : ℝ}
    {Phi phi1 : ℝ → ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hPhi : Continuous (uncurry Phi))
    (hphi1 : Continuous (uncurry phi1)) :
    Continuous (uncurry (smoothPathEta1 k0 k1 theta0 L Phi phi1)) := by
  have hBu : Continuous (fun p : ℝ × ℝ => (B p.1, p.2)) :=
    (continuous_B.comp continuous_fst).prodMk continuous_snd
  have hPhiB : Continuous (fun p : ℝ × ℝ => Phi (B p.1) p.2) :=
    hPhi.comp hBu
  have harg : Continuous (fun p : ℝ × ℝ => (B p.1, Phi (B p.1) p.2)) :=
    (continuous_B.comp continuous_fst).prodMk hPhiB
  have hnv := (continuous_uncurry_normalVelDeriv (θ₀ := theta0) (L := L)
    hk0 hk1).comp harg
  have hp1 : Continuous (fun p : ℝ × ℝ => phi1 (B p.1) p.2) :=
    hphi1.comp hBu
  simpa [smoothPathEta1] using
    ((continuous_w.comp continuous_fst).mul hnv).mul hp1

/-- Joint continuity of the second explicit spatial normal-rate derivative. -/
theorem continuous_uncurry_smoothPathEta2
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L : ℝ}
    {Phi phi1 phi2 : ℝ → ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0' : Continuous k0') (hk1' : Continuous k1')
    (hPhi : Continuous (uncurry Phi))
    (hphi1 : Continuous (uncurry phi1))
    (hphi2 : Continuous (uncurry phi2)) :
    Continuous (uncurry
      (smoothPathEta2 k0 k1 k0' k1' theta0 L Phi phi1 phi2)) := by
  have hBu : Continuous (fun p : ℝ × ℝ => (B p.1, p.2)) :=
    (continuous_B.comp continuous_fst).prodMk continuous_snd
  have hPhiB : Continuous (fun p : ℝ × ℝ => Phi (B p.1) p.2) :=
    hPhi.comp hBu
  have harg : Continuous (fun p : ℝ × ℝ => (B p.1, Phi (B p.1) p.2)) :=
    (continuous_B.comp continuous_fst).prodMk hPhiB
  have hnv2 := (continuous_uncurry_normalVelSecondDeriv
    (θ₀ := theta0) (L := L) hk0 hk1 hk0' hk1').comp harg
  have hnv1 := (continuous_uncurry_normalVelDeriv (θ₀ := theta0) (L := L)
    hk0 hk1).comp harg
  have hp1 : Continuous (fun p : ℝ × ℝ => phi1 (B p.1) p.2) :=
    hphi1.comp hBu
  have hp2 : Continuous (fun p : ℝ × ℝ => phi2 (B p.1) p.2) :=
    hphi2.comp hBu
  simpa [smoothPathEta2] using (continuous_w.comp continuous_fst).mul
    ((hnv2.mul (hp1.pow 2)).add (hnv1.mul hp2))

/-- Canonical first and second spatial chain rules for `pathEta`.  Continuity
and boundedness are separated as explicit analytic certificates, while all
derivative and periodicity fields are discharged here. -/
def pathEtaSpatialC2Certificate_of_smoothPhi
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L : ℝ}
    {Phi phi1 phi2 : ℝ → ℝ → ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi)
    (hd0 : ∀ s, HasDerivAt k0 (k0' s) s)
    (hd1 : ∀ s, HasDerivAt k1 (k1' s) s)
    (htrans : ∀ t u, Phi t (u + 1) = Phi t u + 2 * L)
    (hphi1 : ∀ t u, HasDerivAt (Phi t) (phi1 t u) u)
    (hphi2 : ∀ t u, HasDerivAt (phi1 t) (phi2 t u) u)
    (hphi2c : ∀ t, Continuous (phi2 t)) :
    PathEtaSpatialC2Certificate k0 k1 theta0 L Phi := by
  let eta1 := smoothPathEta1 k0 k1 theta0 L Phi phi1
  let eta2 := smoothPathEta2 k0 k1 k0' k1' theta0 L Phi phi1 phi2
  have heta : ∀ t u, HasDerivAt (pathEta k0 k1 theta0 L Phi t) (eta1 t u) u := by
    intro t u
    exact (hasDerivAt_scaledEta hk0 hk1 (w t) (B t) (Phi (B t) u)).comp u
      (hphi1 (B t) u)
  have heta1 : ∀ t u, HasDerivAt (eta1 t) (eta2 t u) u := by
    intro t u
    have hbase := (hasDerivAt_normalVelDeriv (θ₀ := theta0) (L := L)
      hk0 hk1 hd0 hd1 (B t) (Phi (B t) u)).comp u (hphi1 (B t) u)
    have h := ((hbase.const_mul (w t)).mul (hphi2 (B t) u))
    convert h using 1
    simp only [eta2, smoothPathEta2, Function.comp_apply]
    ring
  have hetaPer : ∀ t, Periodic (pathEta k0 k1 theta0 L Phi t) 1 := by
    intro t u
    simp only [pathEta]
    rw [htrans (B t) u]
    exact periodic_scaledEta hk0 hk1 hper0 hper1 htot0 htot1 (w t) (B t)
      (Phi (B t) u)
  let hderivPer :=
    PeriodicDerivativeAdapters.eta_derivatives_periodic hetaPer heta heta1
  have heta1Per := hderivPer.1
  have heta2Per := hderivPer.2
  have heta1c : ∀ t, Continuous (eta1 t) := by
    intro t
    have hPhic : Continuous (Phi (B t)) :=
      continuous_iff_continuousAt.2 fun u => (hphi1 (B t) u).continuousAt
    have hphi1c : Continuous (phi1 (B t)) :=
      continuous_iff_continuousAt.2 fun u => (hphi2 (B t) u).continuousAt
    have hbase := (continuous_uncurry_normalVelDeriv (θ₀ := theta0) (L := L) hk0 hk1).comp
      ((continuous_const : Continuous fun _ : ℝ => B t).prodMk hPhic)
    exact (continuous_const.mul hbase).mul hphi1c
  have heta2c : ∀ t, Continuous (eta2 t) := by
    intro t
    have hPhic : Continuous (Phi (B t)) :=
      continuous_iff_continuousAt.2 fun u => (hphi1 (B t) u).continuousAt
    have hphi1c : Continuous (phi1 (B t)) :=
      continuous_iff_continuousAt.2 fun u => (hphi2 (B t) u).continuousAt
    have hbase2 := (continuous_uncurry_normalVelSecondDeriv
      (θ₀ := theta0) (L := L) hk0 hk1 hk0'c hk1'c).comp
        ((continuous_const : Continuous fun _ : ℝ => B t).prodMk hPhic)
    have hbase1 := (continuous_uncurry_normalVelDeriv
      (θ₀ := theta0) (L := L) hk0 hk1).comp ((continuous_const : Continuous fun _ : ℝ => B t).prodMk hPhic)
    exact continuous_const.mul
      ((hbase2.mul (hphi1c.pow 2)).add (hbase1.mul (hphi2c (B t))))
  have heta1b : ∀ t, BddAbove (range fun u => |eta1 t u|) := fun t =>
    ArclengthInverse.bddAbove_abs_of_periodic zero_lt_one (heta1c t) (heta1Per t)
  have heta2b : ∀ t, BddAbove (range fun u => |eta2 t u|) := fun t =>
    ArclengthInverse.bddAbove_abs_of_periodic zero_lt_one (heta2c t) (heta2Per t)
  exact
    { eta1 := eta1
      eta2 := eta2
      eta_deriv := heta
      eta1_deriv := heta1
      eta1_cont := heta1c
      eta2_cont := heta2c
      eta1_bdd := heta1b
      eta2_bdd := heta2b
      eta_periodic := hetaPer
      eta1_periodic := heta1Per
      eta2_periodic := heta2Per }

/-- Smooth curvature interpolation as a normal path with its complete spatial
C2 normal-rate certificate. -/
theorem exists_normalPath_interp_with_c2
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L kstar kd dsup : ℝ}
    (hk0 : Continuous k0) (hk1 : Continuous k1)
    (hk0'c : Continuous k0') (hk1'c : Continuous k1')
    (hper0 : Periodic k0 L) (hper1 : Periodic k1 L)
    (htot0 : (∫ r in (0 : ℝ)..L, k0 r) = Real.pi)
    (htot1 : (∫ r in (0 : ℝ)..L, k1 r) = Real.pi) (hL : 0 < L)
    (hd0 : ∀ s, HasDerivAt k0 (k0' s) s)
    (hd1 : ∀ s, HasDerivAt k1 (k1' s) s)
    (hd : ∀ s, |k1 s - k0 s| ≤ dsup)
    (hkd0 : ∀ s, |k0' s| ≤ kd) (hkd1 : ∀ s, |k1' s| ≤ kd)
    (hk0nn : ∀ s, 0 ≤ k0 s) (hk1nn : ∀ s, 0 ≤ k1 s)
    (hk0le : ∀ s, k0 s ≤ kstar) (hk1le : ∀ s, k1 s ≤ kstar) :
    ∃ (Phi phi1 phi2 : ℝ → ℝ → ℝ),
      (∀ u, Phi 0 u = 2 * L * u) ∧
      (∀ t u, Phi t (u + 1) = Phi t u + 2 * L) ∧
      ∀ p q : Data,
        (∀ u, p.1 u = interpCurve k0 theta0 L (2 * L * u)) →
        (∀ u, q.1 u = interpCurve k1 theta0 L (Phi 1 u)) →
        ∃ Gamma : NormalPath p q, Gamma.T = 1 ∧
          Gamma.eta = pathEta k0 k1 theta0 L Phi ∧
          Nonempty (C2NormalPathData Gamma) ∧
          NormalPath.cost Gamma ≤ interpPathCost kstar kd dsup L (curvDist k0 k1 L) := by
  obtain ⟨Phi, phi1, phi2, hPhi0, hPhid, htrans, hphi1, hphi2,
      hPhic, hphi1c, hphi2c, hphi1bd, hphi2bd, hnormal⟩ :=
    InterpolationGauge.exists_interpolation_gauge_flow_smooth_specialized
      hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1
      hk0nn hk1nn hk0le hk1le hkd0 hkd1
  let C := pathEtaSpatialC2Certificate_of_smoothPhi (theta0 := theta0) hk0 hk1 hk0'c hk1'c
    hper0 hper1 htot0 htot1 hd0 hd1 htrans hphi1 hphi2 hphi2c
  refine ⟨Phi, phi1, phi2, hPhi0, htrans, ?_⟩
  intro p q hp hq
  obtain ⟨Gamma, hT, heta, hcost⟩ := normalPath_interp_of_gauge
    hk0 hk1 hk0'c hk1'c hper0 hper1 htot0 htot1 hL hd0 hd1 hd
    hkd0 hkd1 hk0nn hk1nn hk0le hk1le Phi hPhi0 hPhid hnormal p q hp hq
  exact ⟨Gamma, hT, heta, ⟨C.toC2NormalPathData heta⟩, hcost⟩

/-- Attach the canonical smooth-rate certificate to a normal path returned by
`normalPath_interp_of_gauge`. -/
def c2NormalPathData_of_smoothPathEta
    {p q : Data} {Gamma : NormalPath p q}
    {k0 k1 k0' k1' : ℝ → ℝ} {theta0 L : ℝ}
    {Phi phi1 phi2 : ℝ → ℝ → ℝ}
    (C : PathEtaSpatialC2Certificate k0 k1 theta0 L Phi)
    (heta : Gamma.eta = pathEta k0 k1 theta0 L Phi) :
    C2NormalPathData Gamma := C.toC2NormalPathData heta

end InterpolationPathDist
