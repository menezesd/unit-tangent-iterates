import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostTransportInput
import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam

/-!
# Canonical-recost control of the exact-successor Jacobi source

The first derivative in the canonical recost is taken in the chosen marking.
The chain rule therefore introduces the inverse marking Jacobian.  A normalized
jet bound, a rear-period floor, and `eps <= 1/4` give the uniform weakening by
the factor two used by the direct recosted successor source.
-/

noncomputable section

open Function Set RearTrack RearOwnArclength RearFamilyFrame

namespace FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostDerivativeBound

open FiniteSmoothRearFamilyMarkingAwareSource
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSuccessorFront
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorPreTransport
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorGaugeExistence
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorAutomaticBounds
  FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostTransportInput
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam

variable {p q a b : MarkedSpace.Data} {Gamma : PathMetric.NormalPath p q}
  {P0 kh khat Qmax kap eps : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}
  (W : ChosenPath Gamma A E.Phi a b)
  (S : ExactSelected A (kap := kap))
  (R : PreTransport S)

private theorem eta1_mul_identity (t u : ℝ) :
    (A.etaF t (A.sf t (E.Phi t u)) /
          Real.cos (A.delta t (A.sf t (E.Phi t u))) -
        rearNormal A t (E.Phi t u)) * W.phi1 t u =
      W.c2.eta1 t u := by
  have hchain := (A.jacobi t (E.Phi t u)).comp u (W.phi1_deriv t u)
  have hchosen : HasDerivAt (W.Delta.eta t)
      ((A.etaF t (A.sf t (E.Phi t u)) /
            Real.cos (A.delta t (A.sf t (E.Phi t u))) -
          rearNormal A t (E.Phi t u)) * W.phi1 t u) u := by
    convert hchain using 1
    · funext v
      exact W.eta_eq t v
  exact hchosen.unique (W.c2.eta_deriv t u)

private theorem abs_eta1_le_recost
    (heta0 : Continuous (Function.uncurry W.Delta.eta))
    (heta1 : Continuous (Function.uncurry W.c2.eta1))
    (heta2 : Continuous (Function.uncurry W.c2.eta2))
    (t u : ℝ) :
    |W.c2.eta1 t u| ≤
      (CanonicalNormalPathRecost.recost W.Delta W.c2 heta0 heta1 heta2).m t := by
  let D := CanonicalNormalPathRecost.recost W.Delta W.c2 heta0 heta1 heta2
  have hd : iteratedDeriv 1 (D.eta t) = W.c2.eta1 t := by
    rw [iteratedDeriv_one]
    funext v
    change deriv (W.Delta.eta t) v = W.c2.eta1 t v
    exact (W.c2.eta_deriv t v).deriv
  have hbdd : BddAbove
      (Set.range fun v => |iteratedDeriv 1 (D.eta t) v|) := by
    simpa only [hd] using W.c2.eta1_bdd t
  rw [← congrFun hd u]
  exact (MarkedTopology.le_supNorm hbdd u).trans
    (D.le_m_sup t 1 (by norm_num))

/-- The physical rear-normal spatial derivative is bounded by twice the
canonical chosen density.  The factor two is a uniform weakening of the sharp
inverse-Jacobian factor under `eps <= 1/4` and rear period at least one. -/
theorem etaDerivative_le_two_recost
    (heta0 : Continuous (Function.uncurry W.Delta.eta))
    (heta1 : Continuous (Function.uncurry W.c2.eta1))
    (heta2 : Continuous (Function.uncurry W.c2.eta2))
    (J : NormalizedJetBounds W eps)
    (heps : eps ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t)
    (hT : W.Delta.T = 1) :
    ∀ t s,
      |A.etaF t (A.sf t s) / Real.cos (A.delta t (A.sf t s)) -
          rearNormal A t s| ≤
        2 * (CanonicalNormalPathRecost.recost W.Delta W.c2
          heta0 heta1 heta2).m t := by
  let D := CanonicalNormalPathRecost.recost W.Delta W.c2 heta0 heta1 heta2
  intro t s
  have hc : Continuous (E.Phi t) := continuous_iff_continuousAt.2 fun u =>
    (W.phi1_deriv t u).continuousAt
  have hsurj : Surjective (E.Phi t) :=
    surjective_of_continuous_quasiPeriodic
      ((MarkingAwareSource.successorFrontCore A).period_pos t) hc (W.shift t)
  obtain ⟨u, hu⟩ := hsurj s
  subst s
  let z := A.etaF t (A.sf t (E.Phi t u)) /
      Real.cos (A.delta t (A.sf t (E.Phi t u))) -
        rearNormal A t (E.Phi t u)
  have hmul : |z| * W.phi1 t u ≤ D.m t := by
    have hphi : 0 < W.phi1 t u :=
      (mul_pos (A.rear_period_pos 0) (Real.exp_pos _)).trans_le
        (W.phi1_lower t u)
    rw [← abs_of_pos hphi, ← abs_mul,
      eta1_mul_identity W t u]
    exact abs_eta1_le_recost W heta0 heta1 heta2 t u
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hnormalized : 3 / 4 ≤ normalizedPsi1 W t u := by
      have hlo := (abs_le.mp (J.dpsi t ht u)).1
      dsimp [normalizedPsi1] at hlo ⊢
      linarith
    have hphi : 3 / 4 ≤ W.phi1 t u := by
      have hmulPeriod := mul_le_mul_of_nonneg_right hnormalized
        (A.rear_period_pos t).le
      have hcancel :
          normalizedPsi1 W t u * rearPeriod A t = W.phi1 t u := by
        exact div_mul_cancel₀ _ (A.rear_period_pos t).ne'
      change 3 / 4 * rearPeriod A t ≤
        normalizedPsi1 W t u * rearPeriod A t at hmulPeriod
      rw [hcancel] at hmulPeriod
      have hscale : 3 / 4 ≤ (3 / 4) * rearPeriod A t := by
        nlinarith [hperiod t]
      exact hscale.trans hmulPeriod
    nlinarith [abs_nonneg z, D.m_nonneg t]
  · have hstop : D.m t = 0 := by
      apply D.m_stop t
      intro hactive
      apply ht
      have hDT : D.T = 1 := by
        simpa [D, CanonicalNormalPathRecost.recost] using hT
      rw [hDT] at hactive
      exact ⟨hactive.1.le, hactive.2.le⟩
    rw [hstop] at hmul ⊢
    have hphi : 0 < W.phi1 t u :=
      (mul_pos (A.rear_period_pos 0) (Real.exp_pos _)).trans_le
        (W.phi1_lower t u)
    nlinarith [abs_nonneg z]

/-- Direct specialization of the generalized exact Jacobi-source bound to
twice the canonical recost density. -/
theorem raw_gS_bound_recost
    (hkap0 : 0 ≤ kap) (hkap1 : kap < 1)
    (hcurv : ∀ t s, |curvature A t s| ≤ kap)
    (heta0 : Continuous (Function.uncurry W.Delta.eta))
    (heta1 : Continuous (Function.uncurry W.c2.eta1))
    (heta2 : Continuous (Function.uncurry W.c2.eta2))
    (J : NormalizedJetBounds W eps)
    (heps : eps ≤ 1 / 4)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t)
    (hT : W.Delta.T = 1) :
    ∀ t x, |R.gS t x| ≤
      sourceConst (kh := kh) (kap := kap) *
        (2 * (CanonicalNormalPathRecost.recost W.Delta W.c2
          heta0 heta1 heta2).m t) := by
  let D := CanonicalNormalPathRecost.recost W.Delta W.c2 heta0 heta1 heta2
  apply raw_gS_bound_of_eta_le W S R hkap0 hkap1 hcurv
    (fun t => 2 * D.m t)
  · intro t
    exact mul_nonneg (by norm_num) (D.m_nonneg t)
  · intro t u
    exact (D.abs_eta_le t u).trans (by nlinarith [D.m_nonneg t])
  · intro t s
    have h := etaDerivative_le_two_recost W heta0 heta1 heta2 J heps
      hperiod hT t s
    have hdc : 1 ≤ derivativeConst (kh := kh) := by
      dsimp [derivativeConst,
        FiniteSmoothRearFamilyMarkingAwareSmoothSource.intrinsicDerivativeConst]
      have hnonneg : 0 ≤ 1 / Real.sqrt (1 - kh ^ 2) := by positivity
      linarith
    exact h.trans (by
      change 2 * D.m t ≤ derivativeConst (kh := kh) * (2 * D.m t)
      nlinarith [D.m_nonneg t])

end FiniteSmoothRearFamilyMarkingAwareExactSuccessorRecostDerivativeBound
