import UnitTangentIterates.SelectedInverseFiniteRangeConstructor
import UnitTangentIterates.LocalVariableSpeedApproximatePullback

/-!
# Endpoint curvature retained from local pullback paths

Although the metric pullback theorem returns only increment bounds, its public
step-path constructor still reconstructs a variable-speed normal path at every
finite edge.  The slice frame at the initial endpoint identifies its oriented
curvature with the bounded path curvature, yielding exactly the selected-strip
upper bound needed by the finite selected-inverse range constructor.
-/

noncomputable section

open Set Function Filter Topology Complex MarkedSpace PathMetric
open PathMetric.NormalPath NormalPathC2IncrementVariableSpeed

namespace LocalPullbackEndpointCurvature

/-- The initial endpoint of a variable-speed normal path inherits its
oriented-curvature upper bound. -/
theorem start_orientedCurvature_le
    {p q : Data} {P0 P1 kh G1 Cg c kmin dlt : ℝ}
    (Gamma : NormalPath p q) (hp : IsTubeMember c kmin dlt p)
    (hGamma : IsVariableSpeedNormalPath P0 P1 kh G1 Cg Gamma)
    (u : ℝ) :
    ((starRingEnd ℂ) (p.2.1 u) * p.2.2 u).im ≤
      kh * ‖p.2.1 u‖ ^ 3 := by
  obtain ⟨g, gu, gt, gut, theta, kappa, etas, kt, hgnn, _hgub, _hguB,
      hkap, hXu, hgu, hthetau, _hgt, _hgtc, _hgtbd, _hgut, _hgutc,
      _hgutbd, _hthetat, _hetasc, _hetas, _hkappat, _hktc, _hkt⟩ := hGamma
  have hv := vel_eq_of_slice (g := g) (theta := theta) Gamma 0
    hp.hasDerivAt_curve (funext Gamma.start) (hXu 0) u
  have ha := acc_eq_of_slice (g := g) (gu := gu) (theta := theta)
    (kappa := kappa) Gamma 0 hp.hasDerivAt_curve hp.hasDerivAt_vel
    (funext Gamma.start) (hXu 0) (hgu 0) (hthetau 0) u
  let a := g 0 u
  let b := kappa 0 u
  let z := Complex.exp (Complex.I * (theta 0 u : ℂ))
  have hv' : p.2.1 u = (a : ℂ) * z := by simpa [a, z] using hv
  have ha' : p.2.2 u =
      (((gu 0 u : ℝ) : ℂ) + Complex.I * (((a ^ 2 * b : ℝ) : ℂ))) * z := by
    simpa [a, b, z] using ha
  have ha0 : 0 ≤ a := hgnn 0 u
  have hb : b ≤ kh := (le_abs_self b).trans (hkap 0 u)
  have hzNorm : ‖z‖ = 1 := by
    dsimp [z]
    rw [Complex.norm_exp]
    simp
  have hzsq : Complex.normSq z = 1 := by
    calc
      Complex.normSq z = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
      _ = 1 := by rw [hzNorm]; norm_num
  have hzconj : (starRingEnd ℂ) z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, hzsq]
    norm_num
  have him : ((starRingEnd ℂ) ((a : ℂ) * z) *
      ((((gu 0 u : ℝ) : ℂ) + Complex.I * (((a ^ 2 * b : ℝ) : ℂ))) * z)).im =
      a ^ 3 * b := by
    rw [map_mul, Complex.conj_ofReal]
    have hreassoc :
        ((a : ℂ) * (starRingEnd ℂ) z) *
            ((((gu 0 u : ℝ) : ℂ) +
              Complex.I * (((a ^ 2 * b : ℝ) : ℂ))) * z) =
          (a : ℂ) *
            (((gu 0 u : ℝ) : ℂ) +
              Complex.I * (((a ^ 2 * b : ℝ) : ℂ))) *
            ((starRingEnd ℂ) z * z) := by ring
    rw [hreassoc, hzconj]
    simp [Complex.mul_im]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  rw [hv', ha', him, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0,
    hzNorm, mul_one]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hb (pow_nonneg ha0 3))

/-- Every finite front pullback has the selected-strip curvature upper bound.
The variable-speed path witness is reconstructed with slack chosen inside the
strict local cost cap. -/
theorem pullback_front_orientedCurvature_le
    {B : Data → Data} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 kh G1 Cg c dlt Mtotal : ℝ}
    (hK : 1 ≤ K)
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 kh G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eps : ℝ, 0 < eps → ∃ Delta : NormalPath (B p) (B q),
        cost Delta ≤ K * cost Gamma + eps ∧
        IsVariableSpeedNormalPath P0 P1 kh G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eps : ℝ, 0 < eps →
      ∃ Lambda : NormalPath (Q n) (B (Q (n + 1))),
        cost Lambda ≤ d n + eps ∧
        IsVariableSpeedNormalPath P0 P1 kh G1 Cg Lambda)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback B Q n k))
    (hcap : ∀ n k, K ^ k * d (n + k) < Mtotal) :
    ∀ n k u,
      ((starRingEnd ℂ)
          ((TubePullbackLimit.pullback B Q (n + 1) k).2.1 u) *
        (TubePullbackLimit.pullback B Q (n + 1) k).2.2 u).im ≤
      kh * ‖(TubePullbackLimit.pullback B Q (n + 1) k).2.1 u‖ ^ 3 := by
  intro n k u
  let base := K ^ k * d ((n + 1) + k)
  let eps := (Mtotal - base) / 2
  have heps : 0 < eps := half_pos (sub_pos.mpr (hcap (n + 1) k))
  have hle : base + eps ≤ Mtotal := by
    dsimp [eps]
    linarith [hcap (n + 1) k]
  obtain ⟨Gamma, _hcost, hGamma⟩ :=
    PaperFaithfulLocalApproximatePullback.exists_step_path_local
      hK hmap hdefect (n + 1) k (fun m j _ => hmem m j) eps heps
        (by simpa [base] using hle)
  exact start_orientedCurvature_le Gamma (hmem (n + 1) k)
    hGamma u

/-- Local approximate transport discharges the finite curvature premise in
the selected-inverse range-orbit constructor.  Only turning-one of the actual
finite front pullbacks remains. -/
theorem selectedInverse_orbitRange_of_localTransport_and_turning
    {kh : ℝ} {Q : ℕ → Data} {X : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 G1 Cg c dlt Mtotal : ℝ}
    (hK : 1 ≤ K) (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hmap : ∀ (p q : Data) (Gamma : NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      IsVariableSpeedNormalPath P0 P1 kh G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eps : ℝ, 0 < eps →
        ∃ Delta : NormalPath (SelectedInverseMap.selInv kh p)
            (SelectedInverseMap.selInv kh q),
          cost Delta ≤ K * cost Gamma + eps ∧
          IsVariableSpeedNormalPath P0 P1 kh G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eps : ℝ, 0 < eps →
      ∃ Lambda : NormalPath (Q n)
          (SelectedInverseMap.selInv kh (Q (n + 1))),
        cost Lambda ≤ d n + eps ∧
        IsVariableSpeedNormalPath P0 P1 kh G1 Cg Lambda)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k))
    (hcap : ∀ n k, K ^ k * d (n + k) < Mtotal)
    (hXmem : ∀ n, IsTubeMember c 0 dlt (X n))
    (hXlim : ∀ n,
      Tendsto (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n)
        Filter.atTop (nhds (X n)))
    (hturn : ∀ n k, ∃ Theta Kappa : ℝ → ℝ,
      (∀ s, HasDerivAt
        (ev (TubePullbackLimit.pullback
          (SelectedInverseMap.selInv kh) Q (n + 1) k))
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (Kappa s) s) ∧
      (∀ s, Theta
          (s + perim (TubePullbackLimit.pullback
            (SelectedInverseMap.selInv kh) Q (n + 1) k)) =
        Theta s + 2 * Real.pi)) :
    ∀ n, range (ev (X (n + 1))) =
      range (UnitTangent.unitTangentMap (ev (X n))) := by
  apply SelectedInverseFiniteRangeConstructor.pullback_orbitRange_of_curvature_turning
    hc hkh0 hkh1 hmem hXmem hXlim
  · exact pullback_front_orientedCurvature_le
      hK hmap hdefect hmem hcap
  · exact hturn

end LocalPullbackEndpointCurvature
