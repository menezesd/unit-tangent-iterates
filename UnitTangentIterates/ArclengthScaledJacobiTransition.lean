import UnitTangentIterates.JacobiControlledJunctionComponents

/-!
# Arclength-scaled Jacobi components

The paper's nonexpansive component is physical arclength `L¹`, not the
unweighted average in a unit marking.  For a constant-speed representative of
perimeter `P`, it is `P * W eta 1`.  This module keeps that factor through the
raw rear step and removes it only after the configured separation gives
`1 ≤ P`.
-/

noncomputable section

open Set MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace ArclengthScaledJacobiTransition

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds

/-- Components with the physical arclength `L¹` functional. -/
def physicalComponents (P : ℝ) (eta : ℝ → ℝ → ℝ) : Components where
  w := P * W eta 1
  s0 := S 0 eta
  s1 := S 1 eta
  s2 := S 2 eta

/-- Slicewise hypotheses in the exact scale used by the paper. -/
structure AnalyticInput
    (PF PR : ℝ) (front rear : ℝ → ℝ → ℝ) (C0 C1 C2 : ℝ) : Prop where
  PF_nonnegative : 0 ≤ PF
  C0_nonnegative : 0 ≤ C0
  rearW_integrable : IntervalIntegrable
    (fun t => ∫ x in (0 : ℝ)..1, |rear t x|) volume 0 1
  frontW_integrable : IntervalIntegrable
    (fun t => ∫ s in (0 : ℝ)..1, |front t s|) volume 0 1
  W_slice : ∀ t ∈ Icc (0 : ℝ) 1,
    PR * (∫ x in (0 : ℝ)..1, |rear t x|) ≤
      PF * ∫ s in (0 : ℝ)..1, |front t s|
  rearS0_integrable : IntervalIntegrable
    (fun t => supNorm (rear t)) volume 0 1
  S0_slice : ∀ t x, |rear t x| ≤
    C0 * (PF * ∫ s in (0 : ℝ)..1, |front t s|)
  rearS1_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 1 (rear t))) volume 0 1
  frontS0_integrable : IntervalIntegrable
    (fun t => supNorm (front t)) volume 0 1
  S1_slice : ∀ t x, |iteratedDeriv 1 (rear t) x| ≤
    C1 * supNorm (front t) +
      (C1 * PF) * ∫ s in (0 : ℝ)..1, |front t s|
  rearS2_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 2 (rear t))) volume 0 1
  frontS1_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 1 (front t))) volume 0 1
  S2_slice : ∀ t x, |iteratedDeriv 2 (rear t) x| ≤
    C2 * supNorm (front t) + C2 * supNorm (iteratedDeriv 1 (front t)) +
      (C2 * PF) * ∫ s in (0 : ℝ)..1, |front t s|

/-- Supremum-form density estimates exported by a concrete gauge rear-family
stage before time integration. -/
structure DensityBounds
    (PF PR : ℝ) (front rear : ℝ → ℝ → ℝ) (C0 C1 C2 : ℝ) : Prop where
  w : ∀ t, PR * (∫ x in (0 : ℝ)..1, |rear t x|) ≤
    PF * ∫ s in (0 : ℝ)..1, |front t s|
  s0 : ∀ t, supNorm (rear t) ≤
    C0 * (PF * ∫ s in (0 : ℝ)..1, |front t s|)
  s1 : ∀ t, supNorm (iteratedDeriv 1 (rear t)) ≤
    C1 * supNorm (front t) +
      (C1 * PF) * ∫ s in (0 : ℝ)..1, |front t s|
  s2 : ∀ t, supNorm (iteratedDeriv 2 (rear t)) ≤
    C2 * supNorm (front t) + C2 * supNorm (iteratedDeriv 1 (front t)) +
      (C2 * PF) * ∫ s in (0 : ℝ)..1, |front t s|

/-- Joint `C²` continuity plus the concrete physical density estimates gives
the complete analytic input, with no separate measurability or integrability
hypotheses. -/
def AnalyticInput.of_jointC2_densityBounds
    {pf qf pr qr : Data} {frontPath : NormalPath pf qf}
    {rearPath : NormalPath pr qr} {PF PR C0 C1 C2 : ℝ}
    (frontC2 : C2NormalPathData frontPath) (rearC2 : C2NormalPathData rearPath)
    (hfront0 : Continuous (Function.uncurry frontPath.eta))
    (hfront1 : Continuous (Function.uncurry frontC2.eta1))
    (hfront2 : Continuous (Function.uncurry frontC2.eta2))
    (hrear0 : Continuous (Function.uncurry rearPath.eta))
    (hrear1 : Continuous (Function.uncurry rearC2.eta1))
    (hrear2 : Continuous (Function.uncurry rearC2.eta2))
    (hPF : 0 ≤ PF) (hC0 : 0 ≤ C0)
    (B : DensityBounds PF PR frontPath.eta rearPath.eta C0 C1 C2) :
    AnalyticInput PF PR frontPath.eta rearPath.eta C0 C1 C2 := by
  let hfront :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      frontC2 hfront0 hfront1 hfront2
  let hrear :=
    PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      rearC2 hrear0 hrear1 hrear2
  refine
    { PF_nonnegative := hPF
      C0_nonnegative := hC0
      rearW_integrable := hrear.w
      frontW_integrable := hfront.w
      W_slice := fun t _ => B.w t
      rearS0_integrable := hrear.s0
      S0_slice := ?_
      rearS1_integrable := hrear.s1
      frontS0_integrable := hfront.s0
      S1_slice := ?_
      rearS2_integrable := hrear.s2
      frontS1_integrable := hfront.s1
      S2_slice := ?_ }
  · intro t x
    exact (le_supNorm
      ⟨rearPath.m t, by rintro _ ⟨u, rfl⟩; exact rearPath.abs_eta_le t u⟩ x).trans (B.s0 t)
  · intro t x
    have hd1 : iteratedDeriv 1 (rearPath.eta t) = rearC2.eta1 t := by
      funext u
      rw [iteratedDeriv_one]
      exact (rearC2.eta_deriv t u).deriv
    exact (le_supNorm (by simpa only [hd1] using rearC2.eta1_bdd t) x).trans (B.s1 t)
  · intro t x
    have hd1 : deriv (rearPath.eta t) = rearC2.eta1 t := by
      funext u
      exact (rearC2.eta_deriv t u).deriv
    have hd2 : iteratedDeriv 2 (rearPath.eta t) = rearC2.eta2 t := by
      funext u
      simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_zero, hd1]
      exact (rearC2.eta1_deriv t u).deriv
    exact (le_supNorm (by simpa only [hd2] using rearC2.eta2_bdd t) x).trans (B.s2 t)

/-- The four integrated physical-component inequalities. -/
structure RawBounds
    (PF PR : ℝ) (front rear : ℝ → ℝ → ℝ) (C0 C1 C2 : ℝ) : Prop where
  w : (physicalComponents PR rear).w ≤ (physicalComponents PF front).w
  s0 : (physicalComponents PR rear).s0 ≤
    C0 * (physicalComponents PF front).w
  s1 : (physicalComponents PR rear).s1 ≤
    C1 * ((physicalComponents PF front).w +
      (physicalComponents PF front).s0)
  s2 : (physicalComponents PR rear).s2 ≤
    C2 * ((physicalComponents PF front).w +
      (physicalComponents PF front).s0 +
      (physicalComponents PF front).s1)

/-- Integrate the arclength-scaled slicewise estimates. -/
def AnalyticInput.toRawBounds
    {PF PR : ℝ} {front rear : ℝ → ℝ → ℝ} {C0 C1 C2 : ℝ}
    (h : AnalyticInput PF PR front rear C0 C1 C2) :
    RawBounds PF PR front rear C0 C1 C2 where
  w := by
    dsimp [physicalComponents, W]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by norm_num)
      (h.rearW_integrable.const_mul PR)
      (h.frontW_integrable.const_mul PF) h.W_slice
  s0 := by
    have hs := JacobiPathGains.S0_gain_path
      (mul_nonneg h.C0_nonnegative h.PF_nonnegative)
      h.rearS0_integrable h.frontW_integrable (by
        intro t x
        simpa [mul_assoc] using h.S0_slice t x)
    simpa [physicalComponents, mul_assoc] using hs
  s1 := by
    have hs := JacobiPathGains.S1_gain_path
      (C := C1 * PF) (c0 := C1⁻¹) h.rearS1_integrable
      h.frontS0_integrable h.frontW_integrable (by
        intro t x
        simpa only [inv_inv] using h.S1_slice t x)
    rw [inv_inv] at hs
    calc
      S 1 rear ≤ C1 * S 0 front + (C1 * PF) * W front 1 := hs
      _ = C1 * ((physicalComponents PF front).w +
          (physicalComponents PF front).s0) := by
        dsimp [physicalComponents]
        ring
  s2 := by
    have hs := JacobiPathGains.S2_gain_path
      (C := C2 * PF) (c0 := C2) (c1 := C2)
      h.rearS2_integrable h.frontS0_integrable h.frontS1_integrable
      h.frontW_integrable h.S2_slice
    calc
      S 2 rear ≤ C2 * S 0 front + C2 * S 1 front +
          (C2 * PF) * W front 1 := hs
      _ = C2 * ((physicalComponents PF front).w +
          (physicalComponents PF front).s0 +
          (physicalComponents PF front).s1) := by
        dsimp [physicalComponents]
        ring

/-- Compose an exactly nonexpansive physical Jacobi step with the actual
controlled endpoint marking.  Only the marking factor `1 / J.m` remains in
the `W` transition. -/
theorem transition_of_raw_and_junction
    {PF PR : ℝ} {front : ℝ → ℝ → ℝ} {p q p' q' : Data}
    (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma)
    {C0 C1 C2 : ℝ} (hPR : 0 ≤ PR)
    (hraw : AnalyticInput PF PR front Gamma.eta C0 C1 C2)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (reparamAtJunction Gamma hC2 J).eta) :
    Transition (physicalComponents PF front)
      (physicalComponents PR (reparamAtJunction Gamma hC2 J).eta)
      (1 / J.m) J.M J.N C0 C1 C2 := by
  let B := hraw.toRawBounds
  let A := reparamAtJunction_bounds Gamma hC2 J hsource htarget
  have hInv : 0 ≤ 1 / J.m := (one_div_pos.mpr J.m_pos).le
  have hM : 0 ≤ J.M := (abs_nonneg (J.phi1 0)).trans (J.jacobian_upper 0)
  have hN : 0 ≤ J.N := (abs_nonneg (J.phi2 0)).trans (J.second_upper 0)
  refine
    { w := ?_
      s0 := A.s0.trans B.s0
      s1 := ?_
      s2 := ?_ }
  · dsimp [physicalComponents]
    calc
      PR * W (reparamAtJunction Gamma hC2 J).eta 1 ≤
          PR * ((1 / J.m) * W Gamma.eta 1) :=
        mul_le_mul_of_nonneg_left A.w hPR
      _ = (1 / J.m) * (PR * W Gamma.eta 1) := by ring
      _ ≤ (1 / J.m) * (PF * W front 1) :=
        mul_le_mul_of_nonneg_left B.w hInv
  · exact A.s1.trans (by
      simpa [physicalComponents, mul_assoc] using
        (mul_le_mul_of_nonneg_left B.s1 hM))
  · have hfirst := mul_le_mul_of_nonneg_left B.s2 (sq_nonneg J.M)
    have hsecond := mul_le_mul_of_nonneg_left B.s1 hN
    exact A.s2.trans (by
      simpa [physicalComponents, mul_assoc] using add_le_add hfirst hsecond)

/-- Once the configured separation gives `1 ≤ P`, normalized `W` is bounded
by the physical component used in the stable induction. -/
theorem W_le_physicalW {P : ℝ} (hP : 1 ≤ P) (eta : ℝ → ℝ → ℝ) :
    W eta 1 ≤ (physicalComponents P eta).w := by
  dsimp [physicalComponents]
  have hW : 0 ≤ W eta 1 := by
    unfold W
    exact intervalIntegral.integral_nonneg zero_le_one fun t _ =>
      intervalIntegral.integral_nonneg zero_le_one fun u _ => abs_nonneg _
  calc
    W eta 1 = 1 * W eta 1 := by ring
    _ ≤ P * W eta 1 := mul_le_mul_of_nonneg_right hP hW

end ArclengthScaledJacobiTransition
