import UnitTangentIterates.FiniteColumnPullbackPaperCapstone
import UnitTangentIterates.ConfiguredInductiveTubeBudget
import UnitTangentIterates.PhysicalRearLimitHarnackAdapter

/-!
# Configured physical sidecars for finite canonical pullback columns

The finite-column compactness theorem only controls marked increments.  This
leaf supplies its geometric sidecars from the configured inductive tube budget
and the actual finite selected-rear kinematics.  The only additional estimate
is the direct distance from a canonical pullback to its strict model front.
-/

noncomputable section

open Set Function Filter Topology MarkedSpace PathMetric
open NormalPathC2IncrementVariableSpeed

namespace FiniteColumnPullbackConfiguredSidecars

open FiniteColumnPullbackPaperCapstone
open FiniteColumnStablePhysicalComponentCompactness
open PaperFaithfulLocalApproximatePullback

/-- Integrated strictness on an actual marked tube member is exactly the
finite Harnack inequality used by the paper capstone. -/
theorem harnack_of_strictness
    {c dlt : ℝ} (hc : 0 < c) {p : Data}
    (hp : IsTubeMember c 0 dlt p)
    (D : UnconditionalAssembly.LimitStrictnessDataH p) :
    ∀ a b : ℝ, a ≤ b →
      Real.exp (a - b) *
          (UnconditionalAssembly.arcCurv p a /
            Real.sqrt (1 + UnconditionalAssembly.arcCurv p a ^ 2)) ≤
        UnconditionalAssembly.arcCurv p b /
          Real.sqrt (1 + UnconditionalAssembly.arcCurv p b ^ 2) := by
  intro a b hab
  have hcurv : ∀ s, D.k s = UnconditionalAssembly.arcCurv p s :=
    RearTrackEmbedded.curvature_eq_arcCurv hc hp
      D.curve_deriv D.angle_deriv
  have H := D.curvature_harnack a b hab
  change Real.exp (a - b) *
      (D.k a / Real.sqrt (1 + D.k a ^ 2)) ≤
    D.k b / Real.sqrt (1 + D.k b ^ 2) at H
  simpa only [hcurv a, hcurv b] using H

/-- The configured distance-to-model estimate upgrades every weak canonical
pullback to the common positive tube. -/
theorem finiteTube_of_budget
    {kh : ℝ} {Q : ℕ → Data} {C K : ℝ} {d : ℕ → ℝ}
    {c d0 dlt : ℝ} {A0 rho : ℕ → ℝ}
    (R : InductiveTubeBudget (SelectedInverseMap.selInv kh) Q C K d
      c d0 dlt A0 rho)
    (hdist : ∀ n k, dist (Q n) (grid kh Q n k) ≤
      PullbackTubeTailBudget.radius C K d n) :
    ∀ n k, IsTubeMember c 0 dlt (grid kh Q n k) := by
  intro n k
  exact R.pullback_mem_of_dist n k (hdist n k)

/-- The same positive tube is closed under a marked row limit. -/
theorem limitTube_of_budget
    {kh : ℝ} {Q : ℕ → Data} {C K : ℝ} {d : ℕ → ℝ}
    {c d0 dlt : ℝ} {A0 rho : ℕ → ℝ}
    (R : InductiveTubeBudget (SelectedInverseMap.selInv kh) Q C K d
      c d0 dlt A0 rho)
    (hdist : ∀ n k, dist (Q n) (grid kh Q n k) ≤
      PullbackTubeTailBudget.radius C K d n)
    {X : ℕ → Data}
    (hlim : ∀ n, Tendsto (grid kh Q n) atTop (nhds (X n))) :
    ∀ n, IsTubeMember c 0 dlt (X n) := by
  intro n
  exact (isClosed_tube c 0 dlt).mem_of_tendsto (hlim n)
    (Eventually.of_forall (finiteTube_of_budget R hdist n))

/-- Actual physical selected-rear kinematics identify every finite canonical
edge with the unit-tangent image of the canonical selected inverse. -/
theorem finiteRange_of_kinematics
    {kh c dlt : ℝ} {Q : ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hmem : ∀ n k, IsTubeMember c 0 dlt (grid kh Q n k))
    (finite : FinitePullbackPhysicalRearKinematics kh (grid kh Q)) :
    ∀ n k,
      range (ev (grid kh Q (n + 1) k)) =
        range (UnitTangent.unitTangentMap
          (ev (SelectedInverseMap.selInv kh (grid kh Q (n + 1) k)))) := by
  intro n k
  let K := Classical.choice (finite.stage n k)
  let S := K.toStageComponents hkh0 hkh1 hc (hmem (n + 1) k)
  simpa [grid, TubePullbackLimit.pullback_succ] using
    S.range_front_eq_unitTangent_rear

/-- Depth zero uses the configured-front strictness.  Every positive depth
uses the strictness retained by the actual selected rear at the preceding
finite edge. -/
theorem finiteHarnack_of_kinematics
    {kh c dlt : ℝ} {Q : ℕ → Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hmem : ∀ n k, IsTubeMember c 0 dlt (grid kh Q n k))
    (finite : FinitePullbackPhysicalRearKinematics kh (grid kh Q))
    (baseStrictness : ∀ n,
      UnconditionalAssembly.LimitStrictnessDataH (Q n)) :
    ∀ n k a b, a ≤ b →
      Real.exp (a - b) *
          (UnconditionalAssembly.arcCurv (grid kh Q n k) a /
            Real.sqrt (1 +
              UnconditionalAssembly.arcCurv (grid kh Q n k) a ^ 2)) ≤
        UnconditionalAssembly.arcCurv (grid kh Q n k) b /
          Real.sqrt (1 +
            UnconditionalAssembly.arcCurv (grid kh Q n k) b ^ 2) := by
  intro n k
  cases k with
  | zero =>
      simpa [grid] using
        harnack_of_strictness hc (hmem n 0) (baseStrictness n)
  | succ k =>
      let K := Classical.choice (finite.stage n k)
      let S := K.toStageComponents hkh0 hkh1 hc (hmem (n + 1) k)
      let D := S.limitStrictness hc (hmem (n + 1) k)
      exact harnack_of_strictness hc (hmem n (k + 1))
        (D.toH (fun s => (D.curvature_deriv s).differentiableAt))

/-- Stable finite-column components plus the configured physical sidecars
produce the paper capstone provider.  No global selected-inverse map estimate
or infinite physical recursion is used. -/
theorem exists_provider_of_stable_components_and_budget
    {kh : ℝ} {Q : ℕ → Data} {g : ℕ → ℕ → Data}
    {Gamma : ∀ n k, NormalPath (grid kh Q n k) (g n k)}
    {period P0 P1 khat G1 Cg defect cap : ℕ → ℕ → ℝ}
    {componentConst conversionConst : ℕ → ℝ}
    {C K : ℝ} {d : ℕ → ℝ}
    {c d0 dlt : ℝ} {A0 rho : ℕ → ℝ}
    (R : InductiveTubeBudget (SelectedInverseMap.selInv kh) Q C K d
      c d0 dlt A0 rho)
    (hdist : ∀ n k, dist (Q n) (grid kh Q n k) ≤
      PullbackTubeTailBudget.radius C K d n)
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (finite : FinitePullbackPhysicalRearKinematics kh (grid kh Q))
    (baseStrictness : ∀ n,
      UnconditionalAssembly.LimitStrictnessDataH (Q n))
    (hg : ∀ n k u, HasDerivAt (⇑(g n k).1) ((g n k).2.1 u) u)
    (hgv : ∀ n k u, HasDerivAt (⇑(g n k).2.1) ((g n k).2.2 u) u)
    (hgeom : ∀ n k, IsVariableSpeedNormalPath
      (P0 n k) (P1 n k) (khat n k) (G1 n k) (Cg n k) (Gamma n k))
    (Hcomp : ∀ n k, StablePhysicalComponents
      (Gamma n k) (period n k) (componentConst n) (defect n k))
    (hcomponent : ∀ n, 0 ≤ componentConst n)
    (hconversionConst : ∀ n, 0 ≤ conversionConst n)
    (hdefect : ∀ n k, 0 ≤ defect n k)
    (hconversion : ∀ n k,
      c2ConstVar (P0 n k) (P1 n k) (khat n k) (G1 n k) (Cg n k) ≤
        conversionConst n)
    (hcap : ∀ n k, dist (g n k) (grid kh Q n (k + 1)) ≤ cap n k)
    (hsumDefect : ∀ n, Summable (defect n))
    (hsumCap : ∀ n, Summable (cap n)) :
    Nonempty (Provider kh Q
      (componentError componentConst conversionConst defect cap) c dlt) := by
  have hmem := finiteTube_of_budget R hdist
  exact exists_provider_of_stable_components hmem hg hgv hgeom Hcomp
    hcomponent hconversionConst hdefect hconversion hcap
    hsumDefect hsumCap
    (finiteRange_of_kinematics hkh0 hkh1 R.c_pos hmem finite)
    (finiteHarnack_of_kinematics hkh0 hkh1 R.c_pos hmem finite
      baseStrictness)

end FiniteColumnPullbackConfiguredSidecars
