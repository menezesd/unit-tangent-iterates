import UnitTangentIterates.FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison

/-!
# Nonaffine fully physical history links

This module performs the marking part of one history link without asserting
that the source marking is affine.  The source and chosen `W` components are
handled by exact Jacobian changes of variables.  Only the spatial channels
pay the predecessor inverse first-jet and current first/second-jet factors.
-/

noncomputable section

open Function Set MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds
  FiniteSmoothRearFamilyMarkingAwareAppliedSource
  FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam
  FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW
  FiniteSmoothRearFamilyMarkingAwarePreGaugePhysicalW
  FiniteSmoothRearFamilyMarkingAwareSeparatedAppliedSource
  FiniteSmoothRearFamilyMarkingAwareSource
  GaugeNormalPathVariableSeparatedNonaffine
  VariableArclengthScaledJacobiTransition
  VariableArclengthScaledTimeReparamTransition

open FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison

variable {p q a b : Data} {Gamma : NormalPath p q}
  {P0 kh khat Qmax P1 m M : ℝ}
  {A : MarkingAwareSource Gamma P0 kh khat Qmax}
  {E : Applied Gamma A}

/-- The intrinsic front density attached to a genuinely nonaffine source. -/
def intrinsicFront (A : MarkingAwareSource Gamma P0 kh khat Qmax)
    (t u : ℝ) : ℝ :=
  A.etaF t (A.P t * u)

/-- A predecessor normalized jet bound gives exactly the spatial source
comparison used by the tower.  The `W` comparison is not estimated by the
reparameterization lemma: it is the exact Jacobian change of variables. -/
def sourceComparison
    (S : Nonaffine.Facts A P1 m M)
    (Fmarked : FunctionalIntegrable Gamma.eta)
    (Fintrinsic : FunctionalIntegrable (intrinsicFront A))
    {eps : ℝ} (J : SourceNormalizedJetBounds A eps) (heps : eps < 1) :
    SourceIntrinsicComparison
      (jacobianComponents A.phi1 Gamma.eta)
      (VariableArclengthScaledJacobiTransition.physicalComponents
        A.P (intrinsicFront A))
      (1 / (1 - eps)) := by
  have hden : 0 < 1 - eps := by linarith [J.eps_nonnegative]
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      FrontComparison (intrinsicFront A t) (Gamma.eta t)
        ((1 + eps) * A.P t / A.P t) 1
        (A.P t / ((1 - eps) * A.P t)) := by
    intro t ht
    have hP : 0 < A.P t := A.period_pos t
    have hmP : 0 < (1 - eps) * A.P t := mul_pos hden hP
    have hphic : Continuous (A.phi t) :=
      Differentiable.continuous fun u => (A.phi_deriv t u).differentiableAt
    have hsurj : Surjective (A.phi t) :=
      FiniteSmoothRearFamilyMarkingAwareSource.surjective_of_continuous_quasiPeriodic
        hP hphic (A.phi_shift t)
    have hmarked : (fun u => A.etaF t (A.phi t u)) = Gamma.eta t := by
      funext u
      exact (A.eta_link t u).symm
    have hbdd0 : BddAbove
        (Set.range fun u => |A.etaF t (A.phi t u)|) := by
      have heq : (fun u => |A.etaF t (A.phi t u)|) =
          fun u => |Gamma.eta t u| := congrArg (fun f u => |f u|) hmarked
      rw [heq]
      exact S.marked_bdd0 t
    have hbdd1 : BddAbove (Set.range fun u =>
        |iteratedDeriv 1 (fun v => A.etaF t (A.phi t v)) u|) := by
      have heq : (fun u =>
          |iteratedDeriv 1 (fun v => A.etaF t (A.phi t v)) u|) =
          fun u => |iteratedDeriv 1 (Gamma.eta t) u| :=
        congrArg (fun f u => |iteratedDeriv 1 f u|) hmarked
      rw [heq]
      exact S.marked_bdd1 t
    simpa only [intrinsicFront, hmarked] using
      frontComparison_of_reparam hP hmP (S.etaF_deriv t)
        (Differentiable.continuous fun x =>
          (S.etaF_deriv t x).differentiableAt)
        (A.phi_deriv t) (A.phi1_continuous t) (S.etaF_periodic t)
        (S.marking_increment t) (fun u => J.lower t ht u)
        (fun u => J.upper t ht u) hsurj hbdd0 hbdd1
  have hw :
      (VariableArclengthScaledJacobiTransition.physicalComponents
        A.P (intrinsicFront A)).w =
        (jacobianComponents A.phi1 Gamma.eta).w := by
    unfold VariableArclengthScaledJacobiTransition.physicalComponents
      VariableArclengthScaledJacobiTransition.physicalW
      jacobianComponents jacobianPhysicalW intrinsicFront
    apply intervalIntegral.integral_congr
    intro t _
    change A.P t * (∫ u in (0 : ℝ)..1,
      |A.etaF t (A.P t * u)|) =
        ∫ u in (0 : ℝ)..1, A.phi1 t u * |Gamma.eta t u|
    rw [source_jacobian_slice_eq_intrinsic S t]
    have hP : A.P t ≠ 0 := (A.period_pos t).ne'
    rw [JacobiNormalized.integral_abs_comp_mul hP (A.etaF t)]
    field_simp [hP]
  refine
    { w := hw.le
      s0 := intervalIntegral.integral_mono_on zero_le_one
        Fintrinsic.s0 Fmarked.s0 fun t ht => by
          simpa using (hslice t ht).s0
      s1 := ?_ }
  calc
    MarkedTopology.S 1 (intrinsicFront A) ≤
      ∫ t in (0 : ℝ)..1,
        (1 / (1 - eps)) * supNorm (iteratedDeriv 1 (Gamma.eta t)) :=
      intervalIntegral.integral_mono_on zero_le_one Fintrinsic.s1
        (Fmarked.s1.const_mul (1 / (1 - eps))) fun t ht => by
          have H := (hslice t ht).s1
          have hP : A.P t ≠ 0 := (A.period_pos t).ne'
          convert H using 1 <;> field_simp [hP, hden.ne']
    _ = (1 / (1 - eps)) *
        MarkedTopology.S 1 Gamma.eta := by
      unfold MarkedTopology.S
      rw [intervalIntegral.integral_const_mul]

/-- The source Jacobian components are nonnegative under a normalized jet
bound strictly below one. -/
theorem source_nonnegative
    {eps : ℝ} (J : SourceNormalizedJetBounds A eps) (heps : eps < 1) :
    (jacobianComponents A.phi1 Gamma.eta).Nonnegative := by
  have hden : 0 < 1 - eps := by linarith [J.eps_nonnegative]
  refine
    { w := ?_
      s0 := by simpa [jacobianComponents] using S_nonneg 0 Gamma.eta
      s1 := by simpa [jacobianComponents] using S_nonneg 1 Gamma.eta
      s2 := by simpa [jacobianComponents] using S_nonneg 2 Gamma.eta }
  unfold jacobianComponents jacobianPhysicalW
  exact intervalIntegral.integral_nonneg zero_le_one fun t ht =>
    intervalIntegral.integral_nonneg zero_le_one fun u _ =>
      mul_nonneg (le_of_lt (lt_of_lt_of_le
        (mul_pos hden (A.period_pos t)) (J.lower t ht u))) (abs_nonneg _)

/-- Exact `W` identity between the intrinsic selected rear and the actual
chosen marking, with no affine-source hypothesis. -/
theorem chosenPhysicalW_eq
    (W : ChosenPath Gamma A E.Phi a b)
    (S : Nonaffine.Facts A P1 m M) :
    jacobianPhysicalW W.phi1 W.Delta.eta =
      physicalW (rearPeriod A) (normalizedRearDensity A) := by
  unfold jacobianPhysicalW physicalW
  apply intervalIntegral.integral_congr
  intro t _
  change (∫ u in (0 : ℝ)..1, W.phi1 t u * |W.Delta.eta t u|) =
    rearPeriod A t * (∫ u in (0 : ℝ)..1,
      |normalizedRearDensity A t u|)
  rw [chosen_jacobian_slice_eq_intrinsic W S t]
  have hR : rearPeriod A t ≠ 0 := (A.rear_period_pos t).ne'
  change (∫ x in (0 : ℝ)..rearPeriod A t, |rearNormal A t x|) =
    rearPeriod A t * (∫ u in (0 : ℝ)..1,
      |rearNormal A t (rearPeriod A t * u)|)
  rw [JacobiNormalized.integral_abs_comp_mul hR (rearNormal A t)]
  field_simp [hR]

/-- A complete nonaffine marking adapter for one fully physical history link.

`Hraw` is the intrinsic inverse-Jacobi estimate. `Btarget` is only the
spatial time-reparameterization bound for the chosen marking; both Jacobian
`W` comparisons are supplied internally and exactly. -/
def transition
    (W : ChosenPath Gamma A E.Phi a b)
    (S : Nonaffine.Facts A P1 m M)
    (Fmarked : FunctionalIntegrable Gamma.eta)
    (Fintrinsic : FunctionalIntegrable (intrinsicFront A))
    {epsPrev epsCur C0 C1 C2 : ℝ}
    (Jprev : SourceNormalizedJetBounds A epsPrev) (hepsPrev : epsPrev < 1)
    (Jcur : NormalizedJetBounds W epsCur) (hepsCur : epsCur < 1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (Hraw : Transition
      (VariableArclengthScaledJacobiTransition.physicalComponents
        A.P (intrinsicFront A))
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (rearPeriod A) (normalizedRearDensity A)) 1 1 0 C0 C1 C2)
    (Btarget : VariableFixedReparamBounds
      (rearPeriod A) (normalizedRearDensity A) W.Delta.eta
      (1 - epsCur) (1 + epsCur) epsCur) :
    Transition (jacobianComponents A.phi1 Gamma.eta)
      (jacobianComponents W.phi1 W.Delta.eta) 1
      ((1 + epsCur) / (1 - epsPrev)) epsCur C0 C1 C2 := by
  have hinv : 1 ≤ 1 / (1 - epsPrev) := by
    have hden : 0 < 1 - epsPrev := by linarith [Jprev.eps_nonnegative]
    apply (le_div_iff₀ hden).2
    linarith [Jprev.eps_nonnegative]
  have HT : TargetMarkingComparison
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (rearPeriod A) (normalizedRearDensity A))
      (jacobianComponents W.phi1 W.Delta.eta) (1 + epsCur) epsCur :=
    targetMarkingComparison_of_timeReparamBounds
      (chosenPhysicalW_eq W S).le Btarget
  have H := transition_of_intrinsic_and_markingComparisons
    (source_nonnegative Jprev hepsPrev) hinv
    (by linarith [Jcur.eps_nonnegative]) Jcur.eps_nonnegative
    hC0 hC1 hC2 (sourceComparison S Fmarked Fintrinsic Jprev hepsPrev)
    Hraw HT
  simpa [div_eq_mul_inv] using H

/-- Specialize a nonaffine row link to the common paired tower majorant. -/
def transitionToPairedMajor
    (W : ChosenPath Gamma A E.Phi a b)
    (S : Nonaffine.Facts A P1 m M)
    (Fmarked : FunctionalIntegrable Gamma.eta)
    (Fintrinsic : FunctionalIntegrable (intrinsicFront A))
    {major : ℕ → ℝ} {j : ℕ} {epsPrev epsCur C0 C1 C2 : ℝ}
    (Jprev : SourceNormalizedJetBounds A epsPrev) (hepsPrev : epsPrev < 1)
    (Jcur : NormalizedJetBounds W epsCur) (hepsCur : epsCur < 1)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (Hraw : Transition
      (VariableArclengthScaledJacobiTransition.physicalComponents
        A.P (intrinsicFront A))
      (VariableArclengthScaledJacobiTransition.physicalComponents
        (rearPeriod A) (normalizedRearDensity A)) 1 1 0 C0 C1 C2)
    (Btarget : VariableFixedReparamBounds
      (rearPeriod A) (normalizedRearDensity A) W.Delta.eta
      (1 - epsCur) (1 + epsCur) epsCur)
    (hmajor0 : ∀ i, 0 ≤ major i)
    (hprev : epsPrev ≤ major j) (hcur : epsCur ≤ major (j + 1))
    (hadjacent : major j + major (j + 1) ≤ 1 / 4) :
    Transition (jacobianComponents A.phi1 Gamma.eta)
      (jacobianComponents W.phi1 W.Delta.eta)
      (NearIdentityDistortionBudget.invLower (pairedMajor major) j)
      (NearIdentityDistortionBudget.upper (pairedMajor major) j)
      (pairedMajor major j) C0 C1 C2 :=
  transition_to_pairedMajor (source_nonnegative Jprev hepsPrev) hC1 hC2
    Jprev.eps_nonnegative Jcur.eps_nonnegative hmajor0 hprev hcur hadjacent
    (transition W S Fmarked Fintrinsic Jprev hepsPrev Jcur hepsCur
      hC0 hC1 hC2 Hraw Btarget)

/-! ## Coordinate-correct normalized history nodes

The fixed configured ceilings apply to these components, not to the
unnormalized `jacobianComponents` above.  The latter remain useful only with
the period-dependent pre-gauge coefficients.
-/

/-- The source half of the fully physical nonaffine marking sandwich. -/
def fullyPhysicalSourceComparison
    (S : Nonaffine.Facts A P1 m M)
    (Fmarked : FunctionalIntegrable Gamma.eta)
    (Fintrinsic : FunctionalIntegrable (intrinsicFront A))
    {eps : ℝ} (J : SourceNormalizedJetBounds A eps) (heps : eps < 1)
    (hmarkedS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t)
      volume 0 1)
    (hintrinsicS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (intrinsicFront A t)) / A.P t)
      volume 0 1) :
    SourceIntrinsicComparison
      (markedPhysicalComponents A.phi1 A.P Gamma.eta)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P (intrinsicFront A))
      (1 / (1 - eps)) := by
  have hden : 0 < 1 - eps := by linarith [J.eps_nonnegative]
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      FrontComparison (intrinsicFront A t) (Gamma.eta t)
        ((1 + eps) * A.P t / A.P t) 1
        (A.P t / ((1 - eps) * A.P t)) := by
    intro t ht
    have hP : 0 < A.P t := A.period_pos t
    have hmP : 0 < (1 - eps) * A.P t := mul_pos hden hP
    have hphic : Continuous (A.phi t) :=
      Differentiable.continuous fun u => (A.phi_deriv t u).differentiableAt
    have hsurj : Surjective (A.phi t) :=
      FiniteSmoothRearFamilyMarkingAwareSource.surjective_of_continuous_quasiPeriodic
        hP hphic (A.phi_shift t)
    have hmarked : (fun u => A.etaF t (A.phi t u)) = Gamma.eta t := by
      funext u
      exact (A.eta_link t u).symm
    have hbdd0 : BddAbove
        (Set.range fun u => |A.etaF t (A.phi t u)|) := by
      have heq : (fun u => |A.etaF t (A.phi t u)|) =
          fun u => |Gamma.eta t u| := congrArg (fun f u => |f u|) hmarked
      rw [heq]
      exact S.marked_bdd0 t
    have hbdd1 : BddAbove (Set.range fun u =>
        |iteratedDeriv 1 (fun v => A.etaF t (A.phi t v)) u|) := by
      have heq : (fun u =>
          |iteratedDeriv 1 (fun v => A.etaF t (A.phi t v)) u|) =
          fun u => |iteratedDeriv 1 (Gamma.eta t) u| :=
        congrArg (fun f u => |iteratedDeriv 1 f u|) hmarked
      rw [heq]
      exact S.marked_bdd1 t
    simpa only [intrinsicFront, hmarked] using
      frontComparison_of_reparam hP hmP (S.etaF_deriv t)
        (Differentiable.continuous fun x =>
          (S.etaF_deriv t x).differentiableAt)
        (A.phi_deriv t) (A.phi1_continuous t) (S.etaF_periodic t)
        (S.marking_increment t) (fun u => J.lower t ht u)
        (fun u => J.upper t ht u) hsurj hbdd0 hbdd1
  have hw :
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P (intrinsicFront A)).w =
        (markedPhysicalComponents A.phi1 A.P Gamma.eta).w := by
    unfold FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
      VariableArclengthScaledJacobiTransition.physicalW
      markedPhysicalComponents jacobianPhysicalW intrinsicFront
    apply intervalIntegral.integral_congr
    intro t _
    change A.P t * (∫ u in (0 : ℝ)..1,
      |A.etaF t (A.P t * u)|) =
        ∫ u in (0 : ℝ)..1, A.phi1 t u * |Gamma.eta t u|
    rw [source_jacobian_slice_eq_intrinsic S t]
    have hP : A.P t ≠ 0 := (A.period_pos t).ne'
    rw [JacobiNormalized.integral_abs_comp_mul hP (A.etaF t)]
    field_simp [hP]
  refine
    { w := hw.le
      s0 := intervalIntegral.integral_mono_on zero_le_one
        Fintrinsic.s0 Fmarked.s0 fun t ht => by
          simpa using (hslice t ht).s0
      s1 := ?_ }
  calc
    (∫ t in (0 : ℝ)..1,
        supNorm (iteratedDeriv 1 (intrinsicFront A t)) / A.P t) ≤
        ∫ t in (0 : ℝ)..1, (1 / (1 - eps)) *
          (supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t) :=
      intervalIntegral.integral_mono_on zero_le_one hintrinsicS1
        (hmarkedS1.const_mul _) fun t ht => by
          have H := (hslice t ht).s1
          have hP : 0 < A.P t := A.period_pos t
          have hcoef : A.P t / ((1 - eps) * A.P t) =
              1 / (1 - eps) := by field_simp [hP.ne', hden.ne']
          rw [hcoef] at H
          have Hd := (div_le_div_iff_of_pos_right hP).2 H
          convert Hd using 1 <;> ring
    _ = (1 / (1 - eps)) *
        (∫ t in (0 : ℝ)..1,
          supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t) := by
      rw [intervalIntegral.integral_const_mul]

/-- The sharp intrinsic slice certificate needs only the geometric fields of
`Nonaffine.Facts`; it does not use an affine identity for the marked source. -/
def nonaffineSliceCertificate
    (S : Nonaffine.Facts A P1 m M) (t : ℝ) :
    GaugeGeometrySeparatedSliceCertificate.Certificate
      (fun _ u => intrinsicFront A t u) (fun _ => rearNormal A t)
      (fun _ => rearPeriod A t)
      (A.P t)
      (A.P t / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))))
      (A.P t / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))))
      (1 / Real.sqrt (1 - kh ^ 2))
      (A.P t / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))))
      (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
        1 / Real.sqrt (1 - kh ^ 2))
      (1 / (A.P t * Real.sqrt (1 - kh ^ 2) ^ 2)) := by
  simpa [intrinsicFront, rearPeriod] using
    (GaugeGeometrySeparatedSliceCertificate.certificate
      (P0 := A.P t) (P1 := A.P t) (kh := kh)
      (P := fun _ => A.P t)
      (delta := fun _ => A.delta t) (K := fun _ => A.K t)
      (etaF := fun _ => A.etaF t) (etaFs := fun _ => S.etaFs t)
      (etaR := fun _ => rearNormal A t) (sf := fun _ => A.sf t)
      (A.period_pos t) A.kh_nonnegative A.kh_lt_one
      (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => A.steering t) (fun _ => A.strip_nonnegative t)
      (fun _ => A.strip_le t) (fun _ => A.steering_periodic t)
      (fun _ => A.curvature_le t) (fun _ => S.etaF_deriv t)
      (fun _ => S.etaFs_continuous t) (fun _ => S.etaF_periodic t)
      (fun _ => A.sf_rightInverse t) (fun _ => A.jacobi t)
      (fun _ =>
        FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.rearNormal_periodic
          (A := A) t))

/-- Intrinsic fixed-ceiling Jacobi input for a nonaffine source.  The front
node is the genuine arclength density `etaF(P*u)`, so no affine statement
about `Gamma.eta` appears. -/
def intrinsicAnalyticInputOfSpatial
    (N : RearOwnFrameDrift.SpatialC2 (rearNormal A))
    (hkh : 0 < kh) (S : Nonaffine.Facts A P1 m M)
    (F : FunctionalIntegrable (intrinsicFront A)) :
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.AnalyticInput
      A.P (rearPeriod A) (intrinsicFront A) (normalizedRearDensity A)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) := by
  open FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi in
  let R := FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.normalizedRearFunctionalIntegrable
    (A := A) (E := E)
  have hPc : Continuous A.P := A.period_contDiff.continuous
  have hRc : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t => (E.frame.period_deriv t).differentiableAt
  have hPinv : Continuous (fun t => (A.P t)⁻¹) :=
    hPc.inv₀ fun t => (A.period_pos t).ne'
  have hRinv : Continuous (fun t => (rearPeriod A t)⁻¹) :=
    hRc.inv₀ fun t => (A.rear_period_pos t).ne'
  have hR2inv : Continuous (fun t => (rearPeriod A t ^ 2)⁻¹) :=
    (hRc.pow 2).inv₀ fun t => (sq_pos_of_pos (A.rear_period_pos t)).ne'
  have hfrontW : IntervalIntegrable
      (fun t => A.P t * ∫ u in (0 : ℝ)..1, |intrinsicFront A t u|)
      volume 0 1 := by
    simpa [mul_comm] using F.w.mul_continuousOn hPc.continuousOn
  have hrearW : IntervalIntegrable
      (fun t => rearPeriod A t *
        ∫ u in (0 : ℝ)..1, |normalizedRearDensity A t u|) volume 0 1 := by
    simpa [mul_comm] using R.w.mul_continuousOn hRc.continuousOn
  have hrearS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (normalizedRearDensity A t)) /
        rearPeriod A t) volume 0 1 := by
    simpa [div_eq_mul_inv] using R.s1.mul_continuousOn hRinv.continuousOn
  have hfrontS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (intrinsicFront A t)) / A.P t)
      volume 0 1 := by
    simpa [div_eq_mul_inv] using F.s1.mul_continuousOn hPinv.continuousOn
  have hrearS2 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (normalizedRearDensity A t)) /
        rearPeriod A t ^ 2) volume 0 1 := by
    simpa [div_eq_mul_inv] using R.s2.mul_continuousOn hR2inv.continuousOn
  have hroot : 0 < Real.sqrt (1 - kh ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [A.kh_nonnegative, A.kh_lt_one])
  have hc0 : 0 ≤ ceilingC0 kh := ceilingC0_nonnegative hkh A.kh_lt_one
  have hc11 : 0 ≤ 1 / Real.sqrt (1 - kh ^ 2) := one_div_nonneg.mpr hroot.le
  have hc21 : 0 ≤ 2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
      1 / Real.sqrt (1 - kh ^ 2) :=
    add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg kh))
        (pow_nonneg hroot.le 3)) hc11
  have hc22 : 0 ≤ 1 / Real.sqrt (1 - kh ^ 2) ^ 2 :=
    one_div_nonneg.mpr (sq_nonneg _)
  refine
    { frontW_integrable := hfrontW
      rearW_integrable := hrearW
      w := ?_
      rearS0_integrable := R.s0
      frontS0_integrable := F.s0
      s0 := ?_
      rearS1_integrable := hrearS1
      frontS1_integrable := hfrontS1
      s1 := ?_
      rearS2_integrable := hrearS2
      s2 := ?_ }
  · intro t _
    have H := (nonaffineSliceCertificate S t).w t
    change rearPeriod A t * (∫ u in (0 : ℝ)..1,
      |rearNormal A t (rearPeriod A t * u)|) ≤
        A.P t * ∫ u in (0 : ℝ)..1, |intrinsicFront A t u|
    have hR : rearPeriod A t ≠ 0 := (A.rear_period_pos t).ne'
    rw [JacobiNormalized.integral_abs_comp_mul hR (rearNormal A t)]
    field_simp [hR]
    simpa [rearPeriod] using H
  · intro t
    have H := (nonaffineSliceCertificate S t).s0 t
    change supNorm (fun u => rearNormal A t (rearPeriod A t * u)) ≤ _
    simp only [rearPeriod]
    rw [JacobiNormalized.supNorm_comp_mul (A.rear_period_pos t).ne'
      (rearNormal A t)]
    have hW : 0 ≤ A.P t *
        (∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) :=
      mul_nonneg (A.period_pos t).le
        (intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _)
    calc
      supNorm (rearNormal A t) ≤
          (1 / (1 - Real.exp
            (-(Real.sqrt (1 - kh ^ 2) * A.P t)))) *
            (A.P t * ∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using H
      _ ≤ ceilingC0 kh *
          (A.P t * ∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) :=
        mul_le_mul_of_nonneg_right
          (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.inverseDamping_le
            (A := A) hkh t) hW
  · intro t
    have H := (nonaffineSliceCertificate S t).separated t |>.s1
    have hRt : 0 ≤ rearPeriod A t := (A.rear_period_pos t).le
    have hW : 0 ≤ A.P t *
        (∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) :=
      mul_nonneg (A.period_pos t).le
        (intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _)
    have hS0 : 0 ≤ supNorm (intrinsicFront A t) := supNorm_nonneg _
    change supNorm (iteratedDeriv 1
      (fun u => rearNormal A t (rearPeriod A t * u))) /
        rearPeriod A t ≤ _
    simp only [rearPeriod]
    rw [JacobiNormalized.iteratedDeriv_one_comp_mul (N.deriv1 t),
      JacobiNormalized.supNorm_const_mul (by simpa [rearPeriod] using hRt),
      JacobiNormalized.supNorm_comp_mul
        (by simpa [rearPeriod] using (A.rear_period_pos t).ne') (N.xi1 t),
      mul_div_cancel_left₀ _
        (by simpa [rearPeriod] using (A.rear_period_pos t).ne')]
    have hd1 : deriv (rearNormal A t) = N.xi1 t :=
      funext fun x => (N.deriv1 t x).deriv
    rw [← hd1]
    have h0 := FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.inverseDamping_le
      (A := A) hkh t
    have h0' : 1 / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))) ≤ ceilingC1 kh :=
      h0.trans (le_max_left _ _)
    have h1 : 1 / Real.sqrt (1 - kh ^ 2) ≤ ceilingC1 kh := le_max_right _ _
    calc
      supNorm (deriv (rearNormal A t)) ≤ _ := H
      _ = (1 / (1 - Real.exp
            (-(Real.sqrt (1 - kh ^ 2) * A.P t)))) *
            (A.P t * ∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) +
          (1 / Real.sqrt (1 - kh ^ 2)) * supNorm (intrinsicFront A t) := by ring
      _ ≤ ceilingC1 kh *
            (A.P t * ∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) +
          ceilingC1 kh * supNorm (intrinsicFront A t) :=
        add_le_add (mul_le_mul_of_nonneg_right h0' hW)
          (mul_le_mul_of_nonneg_right h1 hS0)
      _ = ceilingC1 kh * (A.P t *
          (∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) +
        supNorm (intrinsicFront A t)) := by ring
  · intro t
    have H := (nonaffineSliceCertificate S t).separated t |>.s2
    have hRt2 : 0 ≤ rearPeriod A t ^ 2 := sq_nonneg _
    have hW : 0 ≤ A.P t *
        (∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) :=
      mul_nonneg (A.period_pos t).le
        (intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _)
    have hS0 : 0 ≤ supNorm (intrinsicFront A t) := supNorm_nonneg _
    have hS1 : 0 ≤ supNorm (iteratedDeriv 1 (intrinsicFront A t)) / A.P t :=
      div_nonneg (supNorm_nonneg _) (A.period_pos t).le
    change supNorm (iteratedDeriv 2
      (fun u => rearNormal A t (rearPeriod A t * u))) /
        rearPeriod A t ^ 2 ≤ _
    simp only [rearPeriod]
    rw [JacobiNormalized.iteratedDeriv_two_comp_mul (N.deriv1 t) (N.deriv2 t),
      JacobiNormalized.supNorm_const_mul (by simpa [rearPeriod] using hRt2),
      JacobiNormalized.supNorm_comp_mul
        (by simpa [rearPeriod] using (A.rear_period_pos t).ne') (N.xi2 t),
      mul_div_cancel_left₀ _ (by
        simpa [rearPeriod] using (pow_ne_zero 2 (A.rear_period_pos t).ne'))]
    have hd1 : deriv (rearNormal A t) = N.xi1 t :=
      funext fun x => (N.deriv1 t x).deriv
    have hd2 : deriv (deriv (rearNormal A t)) = N.xi2 t := by
      rw [hd1]
      exact funext fun x => (N.deriv2 t x).deriv
    rw [← hd2]
    have h0 : 1 / (1 - Real.exp
        (-(Real.sqrt (1 - kh ^ 2) * A.P t))) ≤ ceilingC2 kh :=
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalIntrinsicCeilings.inverseDamping_le
        (A := A) hkh t).trans (le_max_left _ _)
    have h21 : 2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
        1 / Real.sqrt (1 - kh ^ 2) ≤ ceilingC2 kh :=
      (le_max_left _ _).trans (le_max_right _ _)
    have h22 : 1 / Real.sqrt (1 - kh ^ 2) ^ 2 ≤ ceilingC2 kh :=
      (le_max_right _ _).trans (le_max_right _ _)
    calc
      supNorm (deriv (deriv (rearNormal A t))) ≤ _ := H
      _ = (1 / (1 - Real.exp
            (-(Real.sqrt (1 - kh ^ 2) * A.P t)))) *
            (A.P t * ∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) +
          (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
            1 / Real.sqrt (1 - kh ^ 2)) * supNorm (intrinsicFront A t) +
          (1 / Real.sqrt (1 - kh ^ 2) ^ 2) *
            (supNorm (iteratedDeriv 1 (intrinsicFront A t)) / A.P t) := by
        field_simp [(A.period_pos t).ne']
      _ ≤ ceilingC2 kh *
            (A.P t * ∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) +
          ceilingC2 kh * supNorm (intrinsicFront A t) +
          ceilingC2 kh *
            (supNorm (iteratedDeriv 1 (intrinsicFront A t)) / A.P t) :=
        add_le_add
          (add_le_add (mul_le_mul_of_nonneg_right h0 hW)
            (mul_le_mul_of_nonneg_right h21 hS0))
          (mul_le_mul_of_nonneg_right h22 hS1)
      _ = ceilingC2 kh * (A.P t *
            (∫ u in (0 : ℝ)..1, |intrinsicFront A t u|) +
          supNorm (intrinsicFront A t) +
          supNorm (iteratedDeriv 1 (intrinsicFront A t)) / A.P t) := by ring

/-- Fixed-ceiling nonaffine transition on the normalized Jacobian nodes.
This is the sound replacement for a fixed-ceiling transition on
`jacobianComponents`. -/
def fullyPhysicalTransition
    {source intrinsicFrontC intrinsicRear target : Components}
    {epsPrev epsCur C0 C1 C2 : ℝ}
    (hsource : source.Nonnegative)
    (Jprev0 : 0 ≤ epsPrev) (hepsPrev : epsPrev < 1)
    (Jcur0 : 0 ≤ epsCur)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (HS : SourceIntrinsicComparison source intrinsicFrontC (1 / (1 - epsPrev)))
    (Hraw : Transition intrinsicFrontC intrinsicRear 1 1 0 C0 C1 C2)
    (HT : TargetMarkingComparison intrinsicRear target (1 + epsCur) epsCur) :
    Transition source target 1 ((1 + epsCur) / (1 - epsPrev)) epsCur
      C0 C1 C2 := by
  have hden : 0 < 1 - epsPrev := by linarith
  have hinv : 1 ≤ 1 / (1 - epsPrev) := by
    apply (le_div_iff₀ hden).2
    linarith
  have H := transition_of_intrinsic_and_markingComparisons hsource hinv
    (by linarith) Jcur0 hC0 hC1 hC2 HS Hraw HT
  simpa [div_eq_mul_inv] using H

/-- The fixed-ceiling intrinsic input needs no affine marking hypothesis.
The source's retained frame regularity supplies the spatial derivative
certificate used by `intrinsicAnalyticInputOfSpatial`. -/
def intrinsicAnalyticInput
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (hkh : 0 < kh) (S : Nonaffine.Facts A P1 m M)
    (F : FunctionalIntegrable (intrinsicFront A)) :
    FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.AnalyticInput
      A.P (rearPeriod A) (intrinsicFront A) (normalizedRearDensity A)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) := by
  cases A.frame_regularity with
  | joint hYdot hangle =>
      exact intrinsicAnalyticInputOfSpatial (E := E)
        (RearOwnFrameDrift.SpatialC2.ofContDiff
          (RearOwnTangential.contDiff_frameNormal hYdot hangle)) hkh S F
  | spatial R =>
      exact intrinsicAnalyticInputOfSpatial (E := E) R.normal hkh S F

/-- Callback-free fixed-ceiling intrinsic transition for a nonaffine source. -/
def intrinsicTransition
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (hkh : 0 < kh) (S : Nonaffine.Facts A P1 m M)
    (F : FunctionalIntegrable (intrinsicFront A)) :
    Transition
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P (intrinsicFront A))
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (rearPeriod A)
        (normalizedRearDensity A))
      1 1 0
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) :=
  (intrinsicAnalyticInput (E := E) hkh S F).toRawBounds.toTransition

/-- The chosen time-dependent marking input only needs nonaffine rear `C²`
regularity.  The former affine hypothesis was used solely to obtain this
regularity and the intrinsic rear integrability, both of which are explicit
here. -/
def nonaffineTimeReparamInput
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (S : Nonaffine.Facts A P1 m M)
    (H : FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.AnalyticInput
      A.P (rearPeriod A) (intrinsicFront A) (normalizedRearDensity A)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh))
    {eps : ℝ} (J : NormalizedJetBounds W eps) (heps : eps < 1) :
    VariableArclengthScaledTimeReparamTransition.TimeReparamInput
      (rearPeriod A) (normalizedRearDensity A) W.Delta.eta
      (1 - eps) (1 + eps) eps := by
  let Ftarget :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource W
  have hRcont : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t => (E.frame.period_deriv t).differentiableAt
  have hsourceC2 : ∀ t, ContDiff ℝ (2 : ℕ) (normalizedRearDensity A t) := by
    intro t
    have hlin : ContDiff ℝ (2 : ℕ)
        (fun u : ℝ => rearPeriod A t * u) := contDiff_const.mul contDiff_id
    simpa only [normalizedRearDensity] using (S.rearNormal_c2 t).comp hlin
  have hsource1c : ∀ t, Continuous (deriv (normalizedRearDensity A t)) := by
    intro t
    exact (UniformFrameBounds.contDiff_deriv_of_two (hsourceC2 t)).continuous
  have hsource2c : ∀ t,
      Continuous (deriv (deriv (normalizedRearDensity A t))) := by
    intro t
    exact (UniformFrameBounds.contDiff_deriv_of_two
      (hsourceC2 t)).continuous_deriv (by norm_num)
  have hp0 : ∀ t, Periodic (normalizedRearDensity A t) 1 :=
    FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.normalizedRearDensity_periodic
      (A := A)
  have hp1 : ∀ t, Periodic (deriv (normalizedRearDensity A t)) 1 := fun t =>
    ArclengthInverse.periodic_of_hasDerivAt
      (fun u => ((hsourceC2 t).differentiable (by norm_num) u).hasDerivAt)
      (hp0 t)
  have hp2 : ∀ t, Periodic
      (deriv (deriv (normalizedRearDensity A t))) 1 := fun t =>
    ArclengthInverse.periodic_of_hasDerivAt
      (fun u => by
        have hC1 := UniformFrameBounds.contDiff_deriv_of_two (hsourceC2 t)
        exact (hC1.differentiable (by norm_num) u).hasDerivAt)
      (hp1 t)
  have htargetPhysical : IntervalIntegrable
      (fun t => rearPeriod A t *
        ∫ u in (0 : ℝ)..1, |W.Delta.eta t u|) volume 0 1 := by
    simpa [mul_comm] using
      Ftarget.w.mul_continuousOn hRcont.continuousOn
  refine
    { psi := FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi E
      psi1 := FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi1 W
      psi2 := FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi2 W
      target_eq := ?_
      source_differentiable := fun t u =>
        (hsourceC2 t).differentiable (by norm_num) u
      source_deriv_differentiable := fun t u => by
        have hC1 := UniformFrameBounds.contDiff_deriv_of_two (hsourceC2 t)
        exact hC1.differentiable (by norm_num) u
      psi_deriv := fun t u => (W.phi1_deriv t u).div_const (rearPeriod A t)
      psi1_deriv := fun t u => (W.phi2_deriv t u).div_const (rearPeriod A t)
      psi1_continuous := fun t => (W.phi1_continuous t).div_const _
      psi_zero := ?_
      psi_one := ?_
      mA_pos := by linarith
      jacobian_lower := ?_
      jacobian_upper := ?_
      second_upper := J.ddpsi
      period_nonnegative := fun t _ => (A.rear_period_pos t).le
      source_bdd0 := fun t => ArclengthInverse.bddAbove_abs_of_periodic
        one_pos (hsourceC2 t).continuous (hp0 t)
      source_bdd1 := fun t => ArclengthInverse.bddAbove_abs_of_periodic
        one_pos (hsource1c t) (hp1 t)
      source_bdd2 := fun t => ArclengthInverse.bddAbove_abs_of_periodic
        one_pos (hsource2c t) (hp2 t)
      source_functional :=
        FiniteSmoothRearFamilyMarkingAwarePreGaugeVariableTransition.normalizedRearFunctionalIntegrable
          (E := E)
      target_functional := Ftarget
      source_physicalW := H.rearW_integrable
      target_physicalW := htargetPhysical }
  · intro t u
    rw [W.eta_eq]
    unfold normalizedRearDensity
      FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi
    congr 1
    exact (mul_div_cancel₀ (E.Phi t u) (A.rear_period_pos t).ne').symm
  · intro t
    rw [FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi,
      E.base t, zero_div]
  · intro t
    have hs := W.shift t 0
    have hPhi1 : E.Phi t 1 = rearPeriod A t := by
      simpa [E.base t] using hs
    rw [FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi,
      hPhi1]
    exact div_self (A.rear_period_pos t).ne'
  · intro t ht u
    have h := (abs_le.mp (J.dpsi t ht u)).1
    unfold FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi1 at h ⊢
    linarith
  · intro t ht u
    have h := abs_le.mp (J.dpsi t ht u)
    have hpos : 0 <
        FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi1 W t u := by
      linarith
    rw [abs_of_pos hpos]
    linarith

/-- Fully physical target comparison for a nonaffine chosen marking. -/
def nonaffineChosenTargetComparison
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    (hkh : 0 < kh) (S : Nonaffine.Facts A P1 m M)
    (F : FunctionalIntegrable (intrinsicFront A))
    {eps : ℝ} (J : NormalizedJetBounds W eps) (heps : eps < 1)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t) :
    TargetMarkingComparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (rearPeriod A)
        (normalizedRearDensity A))
      (markedPhysicalComponents W.phi1 (rearPeriod A) W.Delta.eta)
      (1 + eps) eps := by
  let Hphysical := intrinsicAnalyticInput (E := E) hkh S F
  let Htime := nonaffineTimeReparamInput W S Hphysical J heps
  let Ftarget :=
    FiniteSmoothRearFamilyMarkingAwareChosenExactFunctionalFacts.ChosenPath.functionalIntegrable_of_exactSource W
  have hRcont : Continuous (rearPeriod A) :=
    Differentiable.continuous fun t => (E.frame.period_deriv t).differentiableAt
  have hRinv : Continuous (fun t => (rearPeriod A t)⁻¹) :=
    hRcont.inv₀ fun t => (A.rear_period_pos t).ne'
  have hR2inv : Continuous (fun t => (rearPeriod A t ^ 2)⁻¹) :=
    (hRcont.pow 2).inv₀ fun t => (sq_pos_of_pos (A.rear_period_pos t)).ne'
  have htargetS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (W.Delta.eta t)) / rearPeriod A t)
      volume 0 1 := by
    simpa [div_eq_mul_inv] using
      Ftarget.s1.mul_continuousOn hRinv.continuousOn
  have htargetS2 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 2 (W.Delta.eta t)) / rearPeriod A t ^ 2)
      volume 0 1 := by
    simpa [div_eq_mul_inv] using
      Ftarget.s2.mul_continuousOn hR2inv.continuousOn
  apply FiniteSmoothRearFamilyMarkingAwareFullyPhysicalTargetComparison.targetComparison_of_timeReparamInput
    Htime
  · intro t u
    change W.phi1 t u = rearPeriod A t *
      FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi1 W t u
    unfold FiniteSmoothRearFamilyMarkingAwareChosenVariableTimeReparam.normalizedPsi1
    calc
      W.phi1 t u = (rearPeriod A t / rearPeriod A t) * W.phi1 t u := by
        have hRR : rearPeriod A t / rearPeriod A t = 1 :=
          div_self (A.rear_period_pos t).ne'
        rw [hRR, one_mul]
      _ = rearPeriod A t * (W.phi1 t u / rearPeriod A t) := by ring
  · intro t _
    exact hperiod t
  · exact Hphysical.rearS1_integrable
  · exact htargetS1
  · exact Hphysical.rearS2_integrable
  · exact htargetS2

/-- The normalized source comparison with its two weighted first-spatial
integrability obligations discharged from ordinary functional integrability
and positivity of the source period. -/
def fullyPhysicalSourceComparisonOfFunctional
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M eps : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    (S : Nonaffine.Facts A P1 m M)
    (Fmarked : FunctionalIntegrable Gamma.eta)
    (Fintrinsic : FunctionalIntegrable (intrinsicFront A))
    (J : SourceNormalizedJetBounds A eps) (heps : eps < 1) :
    SourceIntrinsicComparison
      (markedPhysicalComponents A.phi1 A.P Gamma.eta)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        A.P (intrinsicFront A))
      (1 / (1 - eps)) := by
  have hPinv : Continuous (fun t => (A.P t)⁻¹) :=
    A.period_contDiff.continuous.inv₀ fun t => (A.period_pos t).ne'
  have hmarkedS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (Gamma.eta t)) / A.P t)
      volume 0 1 := by
    simpa [div_eq_mul_inv] using
      Fmarked.s1.mul_continuousOn hPinv.continuousOn
  have hintrinsicS1 : IntervalIntegrable
      (fun t => supNorm (iteratedDeriv 1 (intrinsicFront A t)) / A.P t)
      volume 0 1 := by
    simpa [div_eq_mul_inv] using
      Fintrinsic.s1.mul_continuousOn hPinv.continuousOn
  exact fullyPhysicalSourceComparison S Fmarked Fintrinsic J heps
    hmarkedS1 hintrinsicS1

/-- Transport the target comparison to the genuine recosted successor
source.  Only the three exact identities retained by direct recost recursion
are used; no equality of source records or path costs is asserted. -/
def recostTargetComparison
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    {P0' kh' khat' Qmax' : ℝ}
    {targetPath : NormalPath a b}
    (target : MarkingAwareSource targetPath P0' kh' khat' Qmax')
    (hkh : 0 < kh) (S : Nonaffine.Facts A P1 m M)
    (F : FunctionalIntegrable (intrinsicFront A))
    {eps : ℝ} (J : NormalizedJetBounds W eps) (heps : eps < 1)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t)
    (heta : targetPath.eta = W.Delta.eta)
    (hP : target.P = rearPeriod A)
    (hphi1 : target.phi1 = W.phi1) :
    TargetMarkingComparison
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.physicalComponents
        (rearPeriod A) (normalizedRearDensity A))
      (markedPhysicalComponents target.phi1 target.P targetPath.eta)
      (1 + eps) eps := by
  have H := nonaffineChosenTargetComparison W hkh S F J heps hperiod
  simpa only [heta, hP, hphi1] using H

/-- Complete normalized nonaffine row transition, typed on the genuine
recosted target path.  The only analytic data beyond the theorem-produced
source/chosen records is functional integrability of the marked and
intrinsic-front densities. -/
def recostRawTransition
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    {P0' kh' khat' Qmax' : ℝ}
    {targetPath : NormalPath a b}
    (target : MarkingAwareSource targetPath P0' kh' khat' Qmax')
    (hkh : 0 < kh) (hkh1 : kh < 1)
    (S : Nonaffine.Facts A P1 m M)
    (Fmarked : FunctionalIntegrable Gamma.eta)
    (Fintrinsic : FunctionalIntegrable (intrinsicFront A))
    {epsPrev epsCur : ℝ}
    (Jprev : SourceNormalizedJetBounds A epsPrev)
    (hepsPrev : epsPrev < 1)
    (Jcur : NormalizedJetBounds W epsCur) (hepsCur : epsCur < 1)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t)
    (heta : targetPath.eta = W.Delta.eta)
    (hP : target.P = rearPeriod A)
    (hphi1 : target.phi1 = W.phi1)
    (hsource :
      (markedPhysicalComponents A.phi1 A.P Gamma.eta).Nonnegative) :
    Transition
      (markedPhysicalComponents A.phi1 A.P Gamma.eta)
      (markedPhysicalComponents target.phi1 target.P targetPath.eta)
      1 ((1 + epsCur) / (1 - epsPrev)) epsCur
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) := by
  let HS := fullyPhysicalSourceComparisonOfFunctional S Fmarked Fintrinsic
    Jprev hepsPrev
  let Hraw := intrinsicTransition (E := E) hkh S Fintrinsic
  let HT := recostTargetComparison W target hkh S Fintrinsic Jcur hepsCur
    hperiod heta hP hphi1
  exact fullyPhysicalTransition hsource Jprev.eps_nonnegative hepsPrev
    Jcur.eps_nonnegative
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0_nonnegative
      hkh hkh1)
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1_nonnegative
      hkh hkh1)
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2_nonnegative
      hkh hkh1)
    HS Hraw HT

/-- Exact-source regularity certificate retained before the lightweight
`MarkingAwareSource` API erases time measurability of `etaF`.  This is not a
new analytic hypothesis: base and direct-recost constructors must build it
from their concrete jointly regular formulas and carry it with the reachable
state. -/
structure IntrinsicFrontFunctionalFacts
    {p q : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax : ℝ}
    (A : MarkingAwareSource Gamma P0 kh khat Qmax) : Prop where
  functional : FunctionalIntegrable (intrinsicFront A)

/-- Time-dependent rigid spatial shifts preserve all four functional
integrability channels.  No regularity of the phase in time is needed,
because every slice functional is exactly invariant. -/
def functionalIntegrable_shift
    {eta : ℝ → ℝ → ℝ} (F : FunctionalIntegrable eta)
    (phase : ℝ → ℝ) (hper : ∀ t, Periodic (eta t) 1) :
    FunctionalIntegrable (fun t u => eta t (u + phase t)) := by
  refine { w := ?_, s0 := ?_, s1 := ?_, s2 := ?_ }
  · convert F.w using 1
    funext t
    simpa using NormalGauge.integral_abs_shift
      (eta := eta t) (P := (1 : ℝ)) (a := phase t) (hper t)
  · convert F.s0 using 1
    funext t
    unfold supNorm
    exact NormalGauge.iSup_abs_shift (eta := eta t) (phase t)
  · convert F.s1 using 1
    funext t
    rw [iteratedDeriv_comp_add_const]
    unfold supNorm
    exact NormalGauge.iSup_abs_shift
      (eta := iteratedDeriv 1 (eta t)) (phase t)
  · convert F.s2 using 1
    funext t
    rw [iteratedDeriv_comp_add_const]
    unfold supNorm
    exact NormalGauge.iSup_abs_shift
      (eta := iteratedDeriv 2 (eta t)) (phase t)

/-- Paired-major form of `recostRawTransition`.  This is the exact transition
consumed by normalized nonaffine history induction. -/
def recostTransitionToPairedMajor
    {p q a b : Data} {Gamma : NormalPath p q}
    {P0 kh khat Qmax P1 m M : ℝ}
    {A : MarkingAwareSource Gamma P0 kh khat Qmax}
    {E : Applied Gamma A}
    (W : ChosenPath Gamma A E.Phi a b)
    {P0' kh' khat' Qmax' : ℝ}
    {targetPath : NormalPath a b}
    (target : MarkingAwareSource targetPath P0' kh' khat' Qmax')
    (hkh : 0 < kh) (hkh1 : kh < 1)
    (S : Nonaffine.Facts A P1 m M)
    (Fmarked : FunctionalIntegrable Gamma.eta)
    (Fintrinsic : IntrinsicFrontFunctionalFacts A)
    {epsPrev epsCur : ℝ}
    (Jprev : SourceNormalizedJetBounds A epsPrev)
    (hepsPrev : epsPrev < 1)
    (Jcur : NormalizedJetBounds W epsCur) (hepsCur : epsCur < 1)
    (hperiod : ∀ t, 1 ≤ rearPeriod A t)
    (heta : targetPath.eta = W.Delta.eta)
    (hP : target.P = rearPeriod A)
    (hphi1 : target.phi1 = W.phi1)
    (hsource :
      (markedPhysicalComponents A.phi1 A.P Gamma.eta).Nonnegative)
    {major : ℕ → ℝ} {j : ℕ}
    (hmajor0 : ∀ i, 0 ≤ major i)
    (hprev : epsPrev ≤ major j)
    (hcur : epsCur ≤ major (j + 1))
    (hadjacent : major j + major (j + 1) ≤ 1 / 4) :
    Transition
      (markedPhysicalComponents A.phi1 A.P Gamma.eta)
      (markedPhysicalComponents target.phi1 target.P targetPath.eta)
      (NearIdentityDistortionBudget.invLower
        (FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.pairedMajor major) j)
      (NearIdentityDistortionBudget.upper
        (FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.pairedMajor major) j)
      (FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.pairedMajor major j)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC0 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1 kh)
      (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2 kh) := by
  apply FiniteSmoothRearFamilyMarkingAwareNonaffinePhysicalW.transition_to_pairedMajor
    hsource
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC1_nonnegative
      hkh hkh1)
    (FiniteSmoothRearFamilyMarkingAwareFullyPhysicalJacobi.ceilingC2_nonnegative
      hkh hkh1)
    Jprev.eps_nonnegative Jcur.eps_nonnegative hmajor0 hprev hcur hadjacent
  exact recostRawTransition W target hkh hkh1 S Fmarked Fintrinsic.functional
    Jprev hepsPrev Jcur hepsCur hperiod heta hP hphi1 hsource

end FiniteSmoothRearFamilyMarkingAwareNonaffineFullyPhysicalHistoryLink
