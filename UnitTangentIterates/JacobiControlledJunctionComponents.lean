import UnitTangentIterates.AnchoredJacobiStableTransition
import UnitTangentIterates.ConfiguredStableRowDefectProvider
import UnitTangentIterates.NearIdentityDistortionBudget
import UnitTangentIterates.PeriodicSupNormFunctionalIntegrable
import UnitTangentIterates.ArclengthInverse
import UnitTangentIterates.GaugeNormalPath

/-!
# Jacobi component certificates for anchored recursive stages

This module is the narrow analytic adapter into
`AnchoredJacobiStableTransition`.  It invokes the four Jacobi path-gain
lemmas separately, retains the resulting `W,S0,S1,S2` bounds, and only then
composes them with the fixed controlled-junction bounds.  Thus it never routes
through the coarse scalar `affineCost` multiplier.
-/

noncomputable section

open Set MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace JacobiControlledJunctionComponents

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds

/-- The analytic hypotheses exported by one raw gauge rear-family path.
The coefficient normalization matches `RawJacobiBounds`: the first derivative
has a common coefficient `C1`, and all three second-derivative terms have the
common coefficient `C2`. -/
structure RawJacobiAnalyticInput
    (front rear : ℝ → ℝ → ℝ) (CW C0 C1 C2 : ℝ) : Prop where
  CW_nonnegative : 0 ≤ CW
  C0_nonnegative : 0 ≤ C0
  rearW_integrable : IntervalIntegrable
    (fun t => ∫ x in (0 : ℝ)..1, |rear t x|) volume 0 1
  frontW_integrable : IntervalIntegrable
    (fun t => ∫ s in (0 : ℝ)..1, |front t s|) volume 0 1
  W_slice : ∀ t ∈ Icc (0 : ℝ) 1,
    (∫ x in (0 : ℝ)..1, |rear t x|) ≤
      CW * ∫ s in (0 : ℝ)..1, |front t s|
  rearS0_integrable : IntervalIntegrable
    (fun t => supNorm (rear t)) volume 0 1
  S0_slice : ∀ t x, |rear t x| ≤
    C0 * ∫ s in (0 : ℝ)..1, |front t s|
  rearS1_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 1 (rear t))) volume 0 1
  frontS0_integrable : IntervalIntegrable
    (fun t => supNorm (front t)) volume 0 1
  S1_slice : ∀ t x, |iteratedDeriv 1 (rear t) x| ≤
    C1 * supNorm (front t) +
      C1 * ∫ s in (0 : ℝ)..1, |front t s|
  rearS2_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 2 (rear t))) volume 0 1
  frontS1_integrable : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 1 (front t))) volume 0 1
  S2_slice : ∀ t x, |iteratedDeriv 2 (rear t) x| ≤
    C2 * supNorm (front t) + C2 * supNorm (iteratedDeriv 1 (front t)) +
      C2 * ∫ s in (0 : ℝ)..1, |front t s|

/-- Construct the analytic input from the density inequalities naturally
proved inside the long gauge-Jacobi construction.  This isolates exactly the
facts that its current existential output erases. -/
def RawJacobiAnalyticInput.of_density_bounds
    {front rear : ℝ → ℝ → ℝ} {CW C0 C1 C2 : ℝ}
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0)
    (hfront : FunctionalIntegrable front) (hrear : FunctionalIntegrable rear)
    (hW : ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ x in (0 : ℝ)..1, |rear t x|) ≤
        CW * ∫ s in (0 : ℝ)..1, |front t s|)
    (hS0 : ∀ t, supNorm (rear t) ≤
      C0 * ∫ s in (0 : ℝ)..1, |front t s|)
    (hS1 : ∀ t, supNorm (iteratedDeriv 1 (rear t)) ≤
      C1 * (supNorm (front t) +
        ∫ s in (0 : ℝ)..1, |front t s|))
    (hS2 : ∀ t, supNorm (iteratedDeriv 2 (rear t)) ≤
      C2 * supNorm (front t) + C2 * supNorm (iteratedDeriv 1 (front t)) +
        C2 * ∫ s in (0 : ℝ)..1, |front t s|)
    (hbdd0 : ∀ t, BddAbove (Set.range fun x => |rear t x|))
    (hbdd1 : ∀ t, BddAbove
      (Set.range fun x => |iteratedDeriv 1 (rear t) x|))
    (hbdd2 : ∀ t, BddAbove
      (Set.range fun x => |iteratedDeriv 2 (rear t) x|)) :
    RawJacobiAnalyticInput front rear CW C0 C1 C2 where
  CW_nonnegative := hCW
  C0_nonnegative := hC0
  rearW_integrable := hrear.w
  frontW_integrable := hfront.w
  W_slice := hW
  rearS0_integrable := hrear.s0
  S0_slice t x := (le_supNorm (hbdd0 t) x).trans (hS0 t)
  rearS1_integrable := hrear.s1
  frontS0_integrable := hfront.s0
  S1_slice t x := (le_supNorm (hbdd1 t) x).trans (by
    simpa only [mul_add, add_comm] using hS1 t)
  rearS2_integrable := hrear.s2
  frontS1_integrable := hfront.s1
  S2_slice t x := (le_supNorm (hbdd2 t) x).trans (hS2 t)

/-- No-residual producer from the joint smoothness retained by the gauge
construction.  Compact periodic suprema discharge all functional
integrability and boundedness fields. -/
def RawJacobiAnalyticInput.of_jointC2_density_bounds
    {pf qf pr qr : Data} {frontPath : NormalPath pf qf}
    {rearPath : NormalPath pr qr} {CW C0 C1 C2 : ℝ}
    (frontC2 : C2NormalPathData frontPath) (rearC2 : C2NormalPathData rearPath)
    (hfront0 : Continuous (Function.uncurry frontPath.eta))
    (hfront1 : Continuous (Function.uncurry frontC2.eta1))
    (hfront2 : Continuous (Function.uncurry frontC2.eta2))
    (hrear0 : Continuous (Function.uncurry rearPath.eta))
    (hrear1 : Continuous (Function.uncurry rearC2.eta1))
    (hrear2 : Continuous (Function.uncurry rearC2.eta2))
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0)
    (hW : ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ x in (0 : ℝ)..1, |rearPath.eta t x|) ≤
        CW * ∫ s in (0 : ℝ)..1, |frontPath.eta t s|)
    (hS0 : ∀ t, supNorm (rearPath.eta t) ≤
      C0 * ∫ s in (0 : ℝ)..1, |frontPath.eta t s|)
    (hS1 : ∀ t, supNorm (iteratedDeriv 1 (rearPath.eta t)) ≤
      C1 * (supNorm (frontPath.eta t) +
        ∫ s in (0 : ℝ)..1, |frontPath.eta t s|))
    (hS2 : ∀ t, supNorm (iteratedDeriv 2 (rearPath.eta t)) ≤
      C2 * supNorm (frontPath.eta t) +
        C2 * supNorm (iteratedDeriv 1 (frontPath.eta t)) +
        C2 * ∫ s in (0 : ℝ)..1, |frontPath.eta t s|) :
    RawJacobiAnalyticInput frontPath.eta rearPath.eta CW C0 C1 C2 := by
  apply of_density_bounds hCW hC0
    (PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      frontC2 hfront0 hfront1 hfront2)
    (PeriodicSupNormFunctionalIntegrable.functionalIntegrable_of_jointC2
      rearC2 hrear0 hrear1 hrear2)
    hW hS0 hS1 hS2
  · intro t
    exact ArclengthInverse.bddAbove_abs_of_periodic one_pos
      (hrear0.comp (continuous_const.prodMk continuous_id))
      (rearC2.eta_periodic t)
  · intro t
    have hd1 : deriv (rearPath.eta t) = rearC2.eta1 t :=
      funext fun u => (rearC2.eta_deriv t u).deriv
    simpa only [iteratedDeriv_one, hd1] using rearC2.eta1_bdd t
  · intro t
    have hd1 : deriv (rearPath.eta t) = rearC2.eta1 t :=
      funext fun u => (rearC2.eta_deriv t u).deriv
    have hd2 : deriv (rearC2.eta1 t) = rearC2.eta2 t :=
      funext fun u => (rearC2.eta1_deriv t u).deriv
    simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_zero, hd1, hd2]
    exact rearC2.eta2_bdd t

/-- Direct adapter from the four estimates retained by the gauge-normal-path
constructor.  Joint `C²` continuity supplies all integrability and boundedness
facts, so this introduces no analytic residual. -/
def RawJacobiAnalyticInput.of_flowedDensityBounds
    {pf qf pr qr : Data} {frontPath : NormalPath pf qf}
    {rearPath : NormalPath pr qr} {CW C0 C1 C2 : ℝ}
    (frontC2 : C2NormalPathData frontPath) (rearC2 : C2NormalPathData rearPath)
    (hfront0 : Continuous (Function.uncurry frontPath.eta))
    (hfront1 : Continuous (Function.uncurry frontC2.eta1))
    (hfront2 : Continuous (Function.uncurry frontC2.eta2))
    (hrear0 : Continuous (Function.uncurry rearPath.eta))
    (hrear1 : Continuous (Function.uncurry rearC2.eta1))
    (hrear2 : Continuous (Function.uncurry rearC2.eta2))
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0)
    (B : GaugeNormalPath.FlowedDensityBounds
      frontPath.eta rearPath.eta CW C0 C1 C2) :
    RawJacobiAnalyticInput frontPath.eta rearPath.eta CW C0 C1 C2 := by
  apply of_jointC2_density_bounds frontC2 rearC2
    hfront0 hfront1 hfront2 hrear0 hrear1 hrear2 hCW hC0
  · exact fun t _ => B.w t
  · exact B.s0
  · intro t
    simpa only [add_comm] using B.s1 t
  · intro t
    simpa only [mul_add, add_assoc, add_comm, add_left_comm] using B.s2 t

/-- Componentwise raw Jacobi estimates with the honest gauge `W` coefficient
retained. -/
structure ScaledRawJacobiBounds
    (front rear : ℝ → ℝ → ℝ) (CW C0 C1 C2 : ℝ) : Prop where
  w : W rear 1 ≤ CW * W front 1
  s0 : S 0 rear ≤ C0 * W front 1
  s1 : S 1 rear ≤ C1 * (W front 1 + S 0 front)
  s2 : S 2 rear ≤ C2 * (W front 1 + S 0 front + S 1 front)

/-- Invoke all four `JacobiPathGains` theorems and retain their components in
exactly the structure consumed by the stable transition theorem. -/
def RawJacobiAnalyticInput.toScaledRawJacobiBounds
    {front rear : ℝ → ℝ → ℝ} {CW C0 C1 C2 : ℝ}
    (h : RawJacobiAnalyticInput front rear CW C0 C1 C2) :
    ScaledRawJacobiBounds front rear CW C0 C1 C2 where
  w := by
    unfold W
    calc
      (∫ t in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |rear t x|) ≤
          ∫ t in (0 : ℝ)..1,
            CW * ∫ s in (0 : ℝ)..1, |front t s| :=
        intervalIntegral.integral_mono_on (by norm_num) h.rearW_integrable
          (h.frontW_integrable.const_mul CW) h.W_slice
      _ = CW * ∫ t in (0 : ℝ)..1,
          ∫ s in (0 : ℝ)..1, |front t s| := by
        rw [intervalIntegral.integral_const_mul]
  s0 := JacobiPathGains.S0_gain_path h.C0_nonnegative
    h.rearS0_integrable h.frontW_integrable h.S0_slice
  s1 := by
    have hs := JacobiPathGains.S1_gain_path
      (C := C1) (c0 := C1⁻¹) h.rearS1_integrable
      h.frontS0_integrable h.frontW_integrable (by
        intro t x
        simpa only [inv_inv] using h.S1_slice t x)
    calc
      S 1 rear ≤ C1 * S 0 front + C1 * W front 1 := by
        simpa only [inv_inv] using hs
      _ = C1 * (W front 1 + S 0 front) := by ring
  s2 := by
    have hs := JacobiPathGains.S2_gain_path
      (C := C2) (c0 := C2) (c1 := C2) h.rearS2_integrable
      h.frontS0_integrable h.frontS1_integrable h.frontW_integrable h.S2_slice
    calc
      S 2 rear ≤ C2 * S 0 front + C2 * S 1 front + C2 * W front 1 := hs
      _ = C2 * (W front 1 + S 0 front + S 1 front) := by ring

/-- The original nonexpansive component package is recovered exactly when
the retained `W` coefficient is one. -/
def RawJacobiAnalyticInput.toRawJacobiBounds
    {front rear : ℝ → ℝ → ℝ} {C0 C1 C2 : ℝ}
    (h : RawJacobiAnalyticInput front rear 1 C0 C1 C2) :
    RawJacobiBounds front rear C0 C1 C2 where
  w := by simpa using h.toScaledRawJacobiBounds.w
  s0 := h.toScaledRawJacobiBounds.s0
  s1 := h.toScaledRawJacobiBounds.s1
  s2 := h.toScaledRawJacobiBounds.s2

/-- A raw Jacobi stage followed by its actual controlled endpoint junction,
with no aggregate-cost erasure. -/
theorem transition_of_rawJacobi_and_junction
    {front : ℝ → ℝ → ℝ} {p q p' q' : Data}
    (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma)
    {C0 C1 C2 : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2c : 0 ≤ C2)
    (hfront : (components front).Nonnegative)
    (hraw : RawJacobiAnalyticInput front Gamma.eta 1 C0 C1 C2)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (reparamAtJunction Gamma hC2 J).eta) :
    Transition (components front)
      (components (reparamAtJunction Gamma hC2 J).eta)
      (1 / J.m) J.M J.N C0 C1 C2 := by
  exact transition_of_rawJacobi_and_fixedReparam J.m_pos
    (le_trans (abs_nonneg _) (J.jacobian_upper 0))
    (le_trans (abs_nonneg _) (J.second_upper 0))
    hC0 hC1 hC2c hfront hraw.toRawJacobiBounds
    (reparamAtJunction_bounds Gamma hC2 J hsource htarget)

/-- Honest gauge-scaled version of the anchored transition.  The spatial
junction contributes `1 / J.m`, while the gauge path contributes `CW`; their
product is retained rather than silently replaced by one. -/
theorem transition_of_scaledRawJacobi_and_junction
    {front : ℝ → ℝ → ℝ} {p q p' q' : Data}
    (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma)
    {CW C0 C1 C2 : ℝ}
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2c : 0 ≤ C2)
    (hfront : (components front).Nonnegative)
    (hraw : RawJacobiAnalyticInput front Gamma.eta CW C0 C1 C2)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (reparamAtJunction Gamma hC2 J).eta) :
    Transition (components front)
      (components (reparamAtJunction Gamma hC2 J).eta)
      (CW / J.m) J.M J.N C0 C1 C2 := by
  let B := hraw.toScaledRawJacobiBounds
  let A := reparamAtJunction_bounds Gamma hC2 J hsource htarget
  have hInv : 0 ≤ 1 / J.m := (one_div_pos.mpr J.m_pos).le
  have hM : 0 ≤ J.M := (abs_nonneg (J.phi1 0)).trans (J.jacobian_upper 0)
  have hN : 0 ≤ J.N := (abs_nonneg (J.phi2 0)).trans (J.second_upper 0)
  refine
    { w := A.w.trans ?_
      s0 := A.s0.trans B.s0
      s1 := A.s1.trans ?_
      s2 := A.s2.trans ?_ }
  · calc
      1 / J.m * W Gamma.eta 1 ≤ 1 / J.m * (CW * W front 1) :=
        mul_le_mul_of_nonneg_left B.w hInv
      _ = CW / J.m * W front 1 := by ring
  · simpa [components, mul_assoc] using
      (mul_le_mul_of_nonneg_left B.s1 hM)
  · have hfirst := mul_le_mul_of_nonneg_left B.s2 (sq_nonneg J.M)
    have hsecond := mul_le_mul_of_nonneg_left B.s1 hN
    simpa [components, mul_assoc] using add_le_add hfirst hsecond

/-- The paper-faithful depth-uniform multiplier applied to the honest stable
row defect `d_(n+k)`. -/
def stableError (D : ConstructedConfiguredSequenceWeighted.Data)
    (Aw AM AN C0 C1 C2 : ℝ) (n k : ℕ) : ℝ :=
  stableConst Aw AM AN C0 C1 C2 *
    ConfiguredStableRowDefectProvider.error D n k

 theorem stableConst_nonnegative (Aw AM AN C0 C1 C2 : ℝ) :
    0 ≤ stableConst Aw AM AN C0 C1 C2 := by
  exact (Real.exp_pos Aw).le.trans (le_max_left _ _)

/-- A single depth-independent triangular constant preserves rowwise
summability.  This is the defect provider expected by recursive choice after
`depth_uniform_components` has been applied to each propagated increment. -/
def stableProvider (D : ConstructedConfiguredSequenceWeighted.Data)
    (Aw AM AN C0 C1 C2 : ℝ) :
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RowDefectProvider
      (stableError D Aw AM AN C0 C1 C2) where
  nonnegative n k := mul_nonneg (stableConst_nonnegative Aw AM AN C0 C1 C2)
    ((ConfiguredStableRowDefectProvider.provider D).nonnegative n k)
  summable n := ((ConfiguredStableRowDefectProvider.provider D).summable n).mul_left
    (stableConst Aw AM AN C0 C1 C2)

/-- Specialization of the depth-uniform shadow lemma to a single summable
near-identity jet error.  This is the form to be instantiated from the direct
gauge-flow estimates `|dpsi-1|, |ddpsi| <= eps`. -/
theorem depth_uniform_of_nearIdentity
    {V : ℕ → Components} {eps : ℕ → ℝ}
    {E C0 C1 C2 d : ℝ}
    (heps0 : ∀ k, 0 ≤ eps k) (hepsHalf : ∀ k, eps k ≤ 1 / 2)
    (heps : Summable eps) (htsum : (∑' k, eps k) ≤ E)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hd : 0 ≤ d)
    (hV : ∀ k, (V k).Nonnegative)
    (hinit : (V 0).w ≤ d ∧ (V 0).s0 ≤ d ∧
      (V 0).s1 ≤ d ∧ (V 0).s2 ≤ d)
    (hstep : ∀ k, Transition (V k) (V (k + 1))
      (NearIdentityDistortionBudget.invLower eps k)
      (NearIdentityDistortionBudget.upper eps k) (eps k) C0 C1 C2) :
    ∀ k,
      (V k).w ≤ stableConst (2 * E) E E C0 C1 C2 * d ∧
      (V k).s0 ≤ stableConst (2 * E) E E C0 C1 C2 * d ∧
      (V k).s1 ≤ stableConst (2 * E) E E C0 C1 C2 * d ∧
      (V k).s2 ≤ stableConst (2 * E) E E C0 C1 C2 * d :=
  depth_uniform_components
    (NearIdentityDistortionBudget.budget heps0 hepsHalf heps htsum)
    hC0 hC1 hC2 hd hV hinit hstep

def nearIdentityStableError (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) (n k : ℕ) : ℝ :=
  stableError D (2 * E) E E C0 C1 C2 n k

/-- The recursive-choice defect provider obtained after direct near-identity
jet control. -/
def nearIdentityStableProvider (D : ConstructedConfiguredSequenceWeighted.Data)
    (E C0 C1 C2 : ℝ) :
    TriangularMarkedRecursiveChoiceVariableTerminalConstructor.RowDefectProvider
      (nearIdentityStableError D E C0 C1 C2) :=
  stableProvider D (2 * E) E E C0 C1 C2

end JacobiControlledJunctionComponents
