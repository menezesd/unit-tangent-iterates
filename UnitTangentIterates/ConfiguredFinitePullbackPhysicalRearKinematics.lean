import UnitTangentIterates.FinitePullbackPhysicalRearKinematicsConstructor
import UnitTangentIterates.ConfiguredInductiveTubeBudget
import UnitTangentIterates.TwoCapMarked

/-!
# Finite pullback kinematics from configured model turning

Turning number one propagates through an actual physical selected-rear edge.
Consequently the explicit turning of the configured two-cap fronts supplies
the formerly residual turning hypothesis at every finite pullback depth.
-/

noncomputable section

open Set Function MarkedSpace RearTrack
open UnconditionalAssembly TwoCapPairsAssembly
open NormalizedSteeringPhysicalRescaling
open PathMetric PathMetric.NormalPath

namespace ConfiguredFinitePullbackPhysicalRearKinematics

/-- The tangent-angle lift of a physical selected rear has the same full-turn
increment as the tangent-angle lift of its front. -/
theorem exists_rear_turning_of_kinematics
    {kh c dlt : ℝ} {rear front : Data}
    (hkh0 : 0 ≤ kh) (hkh1 : kh < 1) (hc : 0 < c)
    (hfront : IsTubeMember c 0 dlt front)
    (K : PhysicalRearLimitKinematics kh rear front)
    (hturn : ∃ Theta Kappa : ℝ → ℝ,
      (∀ s, HasDerivAt (ev front)
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (Kappa s) s) ∧
      (∀ s, Theta (s + perim front) = Theta s + 2 * Real.pi)) :
    ∃ Theta Kappa : ℝ → ℝ,
      (∀ s, HasDerivAt (ev rear)
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (Kappa s) s) ∧
      (∀ s, Theta (s + perim rear) = Theta s + 2 * Real.pi) := by
  let S := K.toStageComponents hkh0 hkh1 hc hfront
  let D := S.inverseData
  let F := S.rearFrenetCore
  obtain ⟨Theta, Kappa, hX, hTheta, hturn⟩ := hturn
  have hfrontTurn : ∀ s,
      thetaPhys K.steering (perim front) K.theta0 (s + perim front) =
        thetaPhys K.steering (perim front) K.theta0 s + 2 * Real.pi :=
    RearTrackEmbedded.turning_of_lift K.front_frenet hX
      (hasDerivAt_thetaPhys K.steering K.curvature_continuous) hTheta hturn
  refine ⟨F.psi, F.k, F.curve_deriv, F.angle_deriv, ?_⟩
  intro x
  change SelectedRearFrenetChain.rearPsi K.steering (perim front) K.theta0 K.sf
      (x + perim rear) =
    SelectedRearFrenetChain.rearPsi K.steering (perim front) K.theta0 K.sf x +
      2 * Real.pi
  rw [S.perimeter_eq_inverseRearPeriod]
  change thetaPhys K.steering (perim front) K.theta0
        (K.sf (x + D.rearPeriod)) -
      deltaPhys K.steering (perim front) (K.sf (x + D.rearPeriod)) =
    (thetaPhys K.steering (perim front) K.theta0 (K.sf x) -
      deltaPhys K.steering (perim front) (K.sf x)) + 2 * Real.pi
  have hshift : K.sf (x + D.rearPeriod) = K.sf x + perim front := by
    simpa [D, S] using D.sf_shift x
  rw [hshift, hfrontTurn, deltaPhys_periodic]
  ring

/-- The configured model fronts and the local approximate transport produce
the complete aligned finite physical selected-rear kinematics.  The proof is
a depth induction: configured fronts start with turning one, and each physical
selected rear carries that turning to the next depth. -/
theorem finitePullbackKinematics_of_configuredModel_and_localTransport
    {kappas : ℕ → ℝ → ℝ} {Hs eps : ℕ → ℝ}
    (model : ConfiguredModelSequence kappas Hs eps)
    {kh khat : ℝ} {Q : ℕ → Data} {d : ℕ → ℝ}
    {K P0 P1 G1 Cg c dlt Mtotal : ℝ}
    (hQmodel : ∀ n,
      perim (Q n) = 2 * Hs n ∧
      ev (Q n) = front (kappas n) model.thetaBase (Hs n))
    (hK : 1 ≤ K) (hc : 0 < c) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hkhat_le_kh : khat ≤ kh)
    (hmap : ∀ (p q : Data) (Gamma : PathMetric.NormalPath p q),
      IsTubeMember c 0 dlt p → IsTubeMember c 0 dlt q →
      NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
        P0 P1 khat G1 Cg Gamma →
      cost Gamma ≤ Mtotal →
      ∀ eta : ℝ, 0 < eta →
        ∃ Delta : PathMetric.NormalPath (SelectedInverseMap.selInv kh p)
            (SelectedInverseMap.selInv kh q),
          cost Delta ≤ K * cost Gamma + eta ∧
          NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
            P0 P1 khat G1 Cg Delta)
    (hdefect : ∀ n : ℕ, ∀ eta : ℝ, 0 < eta →
      ∃ Lambda : PathMetric.NormalPath (Q n)
          (SelectedInverseMap.selInv kh (Q (n + 1))),
        cost Lambda ≤ d n + eta ∧
        NormalPathC2IncrementVariableSpeed.IsVariableSpeedNormalPath
          P0 P1 khat G1 Cg Lambda)
    (hmem : ∀ n k, IsTubeMember c 0 dlt
      (TubePullbackLimit.pullback (SelectedInverseMap.selInv kh) Q n k))
    (hcap : ∀ n k, K ^ k * d (n + k) < Mtotal) :
    PathMetric.FinitePullbackPhysicalRearKinematics kh
      (fun n k => TubePullbackLimit.pullback
        (SelectedInverseMap.selInv kh) Q n k) := by
  let B : Data → Data := SelectedInverseMap.selInv kh
  let pull : ℕ → ℕ → Data := TubePullbackLimit.pullback B Q
  have hturn : ∀ k n, ∃ Theta Kappa : ℝ → ℝ,
      (∀ s, HasDerivAt (ev (pull n k))
        (Complex.exp (Complex.I * (Theta s : ℂ))) s) ∧
      (∀ s, HasDerivAt Theta (Kappa s) s) ∧
      (∀ s, Theta (s + perim (pull n k)) = Theta s + 2 * Real.pi) := by
    intro k
    induction k with
    | zero =>
        intro n
        refine ⟨frontAngle (kappas n) model.thetaBase, kappas n, ?_, ?_, ?_⟩
        · intro s
          change HasDerivAt (ev (Q n)) _ s
          rw [(hQmodel n).2]
          exact front_hasDerivAt (model.curvature_continuous n) s
        · exact CurvatureInterpolation.hasDerivAt_tangentAngle
            (model.curvature_continuous n)
        · intro s
          change frontAngle (kappas n) model.thetaBase
              (s + perim (Q n)) =
            frontAngle (kappas n) model.thetaBase s + 2 * Real.pi
          rw [(hQmodel n).1]
          exact TwoCapMarked.frontAngle_add_period
            (model.curvature_continuous n) (model.curvature_periodic n)
            (model.total_turning n) s
    | succ k ih =>
        intro n
        have hkin : Nonempty
            (PhysicalRearLimitKinematics kh (pull n (k + 1))
              (pull (n + 1) k)) := by
          have h :=
            FinitePullbackPhysicalRearKinematicsConstructor.exists_kinematics_selInv_of_curvature_turning
              hc hkh0 hkh1 (by simpa [pull] using hmem (n + 1) k)
              (fun u => by
                have hu := LocalPullbackEndpointCurvature.pullback_front_orientedCurvature_le
                  hK hmap hdefect hmem hcap n k u
                calc
                  ((starRingEnd ℂ) ((pull (n + 1) k).2.1 u) *
                      (pull (n + 1) k).2.2 u).im ≤
                      khat * ‖(pull (n + 1) k).2.1 u‖ ^ 3 := by
                    simpa [pull] using hu
                  _ ≤ kh * ‖(pull (n + 1) k).2.1 u‖ ^ 3 :=
                    mul_le_mul_of_nonneg_right hkhat_le_kh (by positivity))
              (ih (n + 1))
          simpa [pull, B, TubePullbackLimit.pullback_succ] using h
        exact exists_rear_turning_of_kinematics hkh0 hkh1 hc
          (by simpa [pull] using hmem (n + 1) k) hkin.some (ih (n + 1))
  refine ⟨?_⟩
  intro n k
  have h :=
    FinitePullbackPhysicalRearKinematicsConstructor.exists_kinematics_selInv_of_curvature_turning
      hc hkh0 hkh1 (by simpa [pull] using hmem (n + 1) k)
      (fun u => by
        have hu := LocalPullbackEndpointCurvature.pullback_front_orientedCurvature_le
          hK hmap hdefect hmem hcap n k u
        calc
          ((starRingEnd ℂ) ((pull (n + 1) k).2.1 u) *
              (pull (n + 1) k).2.2 u).im ≤
              khat * ‖(pull (n + 1) k).2.1 u‖ ^ 3 := by
            simpa [pull] using hu
          _ ≤ kh * ‖(pull (n + 1) k).2.1 u‖ ^ 3 :=
            mul_le_mul_of_nonneg_right hkhat_le_kh (by positivity))
      (hturn k (n + 1))
  simpa [pull, B, TubePullbackLimit.pullback_succ] using h

end ConfiguredFinitePullbackPhysicalRearKinematics
