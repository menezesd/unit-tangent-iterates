import UnitTangentIterates.ArclengthScaledJacobiTransition

/-!
# Variable-arclength-scaled Jacobi transitions

For a family whose physical perimeter is `P t`, the physical `L1` component is

`integral t in 0..1, P t * integral u in 0..1, |eta t u|`.

Keeping `P` inside the time integral is essential when the slices have
different perimeters.  This file supplies the exact selected-inverse
nonexpansiveness theorem in that scale and packages it in the component form
used by the stable triangular induction.
-/

noncomputable section

open Set Function MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace VariableArclengthScaledJacobiTransition

open AnchoredJacobiStableTransition
  ControlledJunctionPathFunctionalBounds

/-- Physical `L1` of a unit-period marking with time-dependent perimeter. -/
def physicalW (P : ℝ → ℝ) (eta : ℝ → ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, P t * ∫ u in (0 : ℝ)..1, |eta t u|

/-- Stable components with the exact variable-perimeter physical `L1` entry. -/
def physicalComponents (P : ℝ → ℝ) (eta : ℝ → ℝ → ℝ) : Components where
  w := physicalW P eta
  s0 := S 0 eta
  s1 := S 1 eta
  s2 := S 2 eta

theorem physicalW_nonnegative
    {P : ℝ → ℝ} (hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t)
    (eta : ℝ → ℝ → ℝ) :
    0 ≤ physicalW P eta := by
  unfold physicalW
  exact intervalIntegral.integral_nonneg zero_le_one fun t ht ↦
    mul_nonneg (hP t ht)
      (intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ abs_nonneg _)

theorem physicalComponents_nonnegative
    {P : ℝ → ℝ} (hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t)
    (eta : ℝ → ℝ → ℝ) :
    (physicalComponents P eta).Nonnegative := by
  exact
    { w := by simpa [physicalComponents] using physicalW_nonnegative hP eta
      s0 := by simpa [physicalComponents] using S_nonneg 0 eta
      s1 := by simpa [physicalComponents] using S_nonneg 1 eta
      s2 := by simpa [physicalComponents] using S_nonneg 2 eta }

/-- An affine arclength normalization of a physical density. -/
def affineNormalize (P : ℝ → ℝ) (eta : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t u ↦ eta t (P t * u)

/-- Exact slicewise physical `L1` contraction.  This is the change from the
front arclength `s` to the rear arclength `x`, followed by the inverse Jacobi
operator.  Both normalized periods are restored, so the coefficient is
exactly one even when the two periods vary with `t`. -/
theorem affineNormalize_slice_nonexpansive
    {PF PR : ℝ → ℝ} {etaF etaR delta xf G : ℝ → ℝ → ℝ}
    (hPF : ∀ t, 0 < PF t) (hPR : ∀ t, 0 < PR t)
    (hG : ∀ t, Continuous (G t))
    (hGper : ∀ t, Periodic (G t) (PR t))
    (hetaR : ∀ t x, HasDerivAt (etaR t) (G t x - etaR t x) x)
    (hetaRper : ∀ t, Periodic (etaR t) (PR t))
    (hx : ∀ t s, HasDerivAt (xf t) (Real.cos (delta t s)) s)
    (hdelta : ∀ t, Continuous (delta t))
    (hx0 : ∀ t, xf t 0 = 0) (hxP : ∀ t, xf t (PF t) = PR t)
    (hcos : ∀ t s, 0 < Real.cos (delta t s))
    (htransport : ∀ t s,
      G t (xf t s) * Real.cos (delta t s) = etaF t s)
    (t : ℝ) :
    PR t * (∫ u in (0 : ℝ)..1, |affineNormalize PR etaR t u|) ≤
      PF t * ∫ u in (0 : ℝ)..1, |affineNormalize PF etaF t u| := by
  have H := JacobiAssembly.W_estimate (l := PR t) (P := PF t)
    (etaR := etaR t) (etaF := etaF t) (G := G t)
    (delta := delta t) (xf := xf t)
    (hPR t) (hG t) (hGper t) (hetaR t) (hetaRper t)
    (hx t) (hdelta t) (hx0 t) (hxP t) (hcos t) (htransport t)
  rw [show affineNormalize PR etaR t = fun u ↦ etaR t (PR t * u) from rfl,
    show affineNormalize PF etaF t = fun u ↦ etaF t (PF t * u) from rfl,
    JacobiNormalized.integral_abs_comp_mul (hPR t).ne' (etaR t),
    JacobiNormalized.integral_abs_comp_mul (hPF t).ne' (etaF t)]
  calc
    PR t * ((PR t)⁻¹ * ∫ x in (0 : ℝ)..PR t, |etaR t x|) =
        ∫ x in (0 : ℝ)..PR t, |etaR t x| := by
          field_simp [(hPR t).ne']
    _ ≤ ∫ s in (0 : ℝ)..PF t, |etaF t s| := H
    _ = PF t * ((PF t)⁻¹ * ∫ s in (0 : ℝ)..PF t, |etaF t s|) := by
          field_simp [(hPF t).ne']

/-- The time-integrated exact physical `L1` contraction. -/
theorem physicalW_nonexpansive_of_slice
    {PF PR : ℝ → ℝ} {front rear : ℝ → ℝ → ℝ}
    (hR : IntervalIntegrable
      (fun t ↦ PR t * ∫ u in (0 : ℝ)..1, |rear t u|) volume 0 1)
    (hF : IntervalIntegrable
      (fun t ↦ PF t * ∫ u in (0 : ℝ)..1, |front t u|) volume 0 1)
    (hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      PR t * (∫ u in (0 : ℝ)..1, |rear t u|) ≤
        PF t * ∫ u in (0 : ℝ)..1, |front t u|) :
    physicalW PR rear ≤ physicalW PF front := by
  exact intervalIntegral.integral_mono_on zero_le_one hR hF hslice

/-- Slicewise data in the exact variable-period physical scale. -/
structure AnalyticInput
    (PF PR : ℝ → ℝ) (front rear : ℝ → ℝ → ℝ)
    (C0 C1 C2 : ℝ) : Prop where
  frontPhysicalW_integrable : IntervalIntegrable
    (fun t ↦ PF t * ∫ u in (0 : ℝ)..1, |front t u|) volume 0 1
  rearPhysicalW_integrable : IntervalIntegrable
    (fun t ↦ PR t * ∫ u in (0 : ℝ)..1, |rear t u|) volume 0 1
  W_slice : ∀ t ∈ Icc (0 : ℝ) 1,
    PR t * (∫ u in (0 : ℝ)..1, |rear t u|) ≤
      PF t * ∫ u in (0 : ℝ)..1, |front t u|
  rearS0_integrable : IntervalIntegrable
    (fun t ↦ supNorm (rear t)) volume 0 1
  S0_slice : ∀ t, supNorm (rear t) ≤
    C0 * (PF t * ∫ u in (0 : ℝ)..1, |front t u|)
  rearS1_integrable : IntervalIntegrable
    (fun t ↦ supNorm (iteratedDeriv 1 (rear t))) volume 0 1
  frontS0_integrable : IntervalIntegrable
    (fun t ↦ supNorm (front t)) volume 0 1
  S1_slice : ∀ t, supNorm (iteratedDeriv 1 (rear t)) ≤
    C1 * (supNorm (front t) +
      PF t * ∫ u in (0 : ℝ)..1, |front t u|)
  rearS2_integrable : IntervalIntegrable
    (fun t ↦ supNorm (iteratedDeriv 2 (rear t))) volume 0 1
  frontS1_integrable : IntervalIntegrable
    (fun t ↦ supNorm (iteratedDeriv 1 (front t))) volume 0 1
  S2_slice : ∀ t, supNorm (iteratedDeriv 2 (rear t)) ≤
    C2 * (supNorm (front t) + supNorm (iteratedDeriv 1 (front t)) +
      PF t * ∫ u in (0 : ℝ)..1, |front t u|)

/-- Integrated raw estimates in variable-perimeter components. -/
structure RawBounds
    (PF PR : ℝ → ℝ) (front rear : ℝ → ℝ → ℝ)
    (C0 C1 C2 : ℝ) : Prop where
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

def AnalyticInput.toRawBounds
    {PF PR : ℝ → ℝ} {front rear : ℝ → ℝ → ℝ}
    {C0 C1 C2 : ℝ} (H : AnalyticInput PF PR front rear C0 C1 C2) :
    RawBounds PF PR front rear C0 C1 C2 where
  w := by
    simpa [physicalComponents] using physicalW_nonexpansive_of_slice
      H.rearPhysicalW_integrable H.frontPhysicalW_integrable H.W_slice
  s0 := by
    unfold physicalComponents S physicalW
    calc
      (∫ t in (0 : ℝ)..1, supNorm (rear t)) ≤
          ∫ t in (0 : ℝ)..1,
            C0 * (PF t * ∫ u in (0 : ℝ)..1, |front t u|) :=
        intervalIntegral.integral_mono_on zero_le_one H.rearS0_integrable
          (H.frontPhysicalW_integrable.const_mul C0) fun t _ ↦ H.S0_slice t
      _ = C0 * ∫ t in (0 : ℝ)..1,
          PF t * ∫ u in (0 : ℝ)..1, |front t u| := by
        rw [intervalIntegral.integral_const_mul]
  s1 := by
    unfold physicalComponents S physicalW
    have hRhs : IntervalIntegrable
        (fun t ↦ C1 * (supNorm (front t) +
          PF t * ∫ u in (0 : ℝ)..1, |front t u|)) volume 0 1 :=
      (H.frontS0_integrable.add H.frontPhysicalW_integrable).const_mul C1
    calc
      (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 1 (rear t))) ≤
          ∫ t in (0 : ℝ)..1, C1 * (supNorm (front t) +
            PF t * ∫ u in (0 : ℝ)..1, |front t u|) :=
        intervalIntegral.integral_mono_on zero_le_one H.rearS1_integrable hRhs
          fun t _ ↦ H.S1_slice t
      _ = C1 * ((∫ t in (0 : ℝ)..1,
            PF t * ∫ u in (0 : ℝ)..1, |front t u|) +
          ∫ t in (0 : ℝ)..1, supNorm (front t)) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add H.frontS0_integrable
            H.frontPhysicalW_integrable]
        ring
  s2 := by
    unfold physicalComponents S physicalW
    have hRhs : IntervalIntegrable
        (fun t ↦ C2 * (supNorm (front t) +
          supNorm (iteratedDeriv 1 (front t)) +
          PF t * ∫ u in (0 : ℝ)..1, |front t u|)) volume 0 1 :=
      ((H.frontS0_integrable.add H.frontS1_integrable).add
        H.frontPhysicalW_integrable).const_mul C2
    calc
      (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 2 (rear t))) ≤
          ∫ t in (0 : ℝ)..1, C2 * (supNorm (front t) +
            supNorm (iteratedDeriv 1 (front t)) +
            PF t * ∫ u in (0 : ℝ)..1, |front t u|) :=
        intervalIntegral.integral_mono_on zero_le_one H.rearS2_integrable hRhs
          fun t _ ↦ H.S2_slice t
      _ = C2 * ((∫ t in (0 : ℝ)..1,
            PF t * ∫ u in (0 : ℝ)..1, |front t u|) +
          (∫ t in (0 : ℝ)..1, supNorm (front t)) +
          ∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 1 (front t))) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add
            (H.frontS0_integrable.add H.frontS1_integrable)
            H.frontPhysicalW_integrable,
          intervalIntegral.integral_add H.frontS0_integrable
            H.frontS1_integrable]
        ring

/-- Raw exact estimates are an identity-junction stable transition. -/
def RawBounds.toTransition
    {PF PR : ℝ → ℝ} {front rear : ℝ → ℝ → ℝ}
    {C0 C1 C2 : ℝ} (H : RawBounds PF PR front rear C0 C1 C2) :
    Transition (physicalComponents PF front) (physicalComponents PR rear)
      1 1 0 C0 C1 C2 where
  w := by simpa using H.w
  s0 := H.s0
  s1 := by simpa using H.s1
  s2 := by simpa using H.s2

/-- If every slice perimeter is at least one, normalized `W` is bounded by
the variable physical component. -/
theorem W_le_physicalW
    {P : ℝ → ℝ} {eta : ℝ → ℝ → ℝ}
    (hW : IntervalIntegrable
      (fun t ↦ ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1)
    (hPW : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, 1 ≤ P t) :
    W eta 1 ≤ physicalW P eta := by
  unfold W physicalW
  exact intervalIntegral.integral_mono_on zero_le_one hW hPW fun t ht ↦ by
    have hI : 0 ≤ ∫ u in (0 : ℝ)..1, |eta t u| :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ ↦ abs_nonneg _
    simpa using mul_le_mul_of_nonneg_right (hP t ht) hI

/-! ## Controlled fixed spatial junctions -/

/-- The four independent junction estimates with the variable physical `L1`
component retained exactly. -/
structure VariableFixedReparamBounds
    (P : ℝ → ℝ) (eta eta' : ℝ → ℝ → ℝ)
    (mA MA NA : ℝ) : Prop where
  w : physicalW P eta' ≤ (1 / mA) * physicalW P eta
  s0 : S 0 eta' ≤ S 0 eta
  s1 : S 1 eta' ≤ MA * S 1 eta
  s2 : S 2 eta' ≤ MA ^ 2 * S 2 eta + NA * S 1 eta

/-- A fixed spatial reparametrization has the same `mA⁻¹` distortion for
variable physical `L1`: the nonnegative perimeter weight is pointwise in time
and therefore passes through the slicewise change of variables. -/
theorem physicalW_comp_le
    {p q : Data} (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    {P : ℝ → ℝ} (hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t)
    {phi phi1 : ℝ → ℝ} {mA : ℝ}
    (hmA : 0 < mA) (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1c : Continuous phi1) (hlow : ∀ u, mA ≤ phi1 u)
    (hphi0 : phi 0 = 0) (hphi1v : phi 1 = 1)
    (hsource : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) volume 0 1)
    (htarget : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t (phi u)|) volume 0 1) :
    physicalW P (fun t u ↦ Gamma.eta t (phi u)) ≤
      (1 / mA) * physicalW P Gamma.eta := by
  unfold physicalW
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t (phi u)|) ≤
        (1 / mA) *
          (P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by
    intro t ht
    have H := PathFunctionalsReparam.integral_abs_comp_le
      (m := mA) (a := 0) (b := 1) (eta := Gamma.eta t)
      (phi := phi) (phi1 := phi1) hmA zero_le_one
      (continuous_iff_continuousAt.2 fun u ↦
        (hC2.eta_deriv t u).continuousAt)
      hphi1 hphi1c hlow
    have H' : (∫ u in (0 : ℝ)..1, |Gamma.eta t (phi u)|) ≤
        (1 / mA) * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := by
      simpa [hphi0, hphi1v] using H
    calc
      P t * (∫ u in (0 : ℝ)..1, |Gamma.eta t (phi u)|) ≤
          P t * ((1 / mA) *
            ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
        mul_le_mul_of_nonneg_left H' (hP t ht)
      _ = (1 / mA) *
          (P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) := by ring
  calc
    (∫ t in (0 : ℝ)..1,
        P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t (phi u)|) ≤
      ∫ t in (0 : ℝ)..1, (1 / mA) *
        (P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
      intervalIntegral.integral_mono_on zero_le_one htarget
        (hsource.const_mul _) hslice
    _ = (1 / mA) *
        ∫ t in (0 : ℝ)..1,
          P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := by
      rw [intervalIntegral.integral_const_mul]

/-- Variable-physical component bounds for the fixed diffeomorphism stored in
a junction certificate. -/
theorem reparamAtJunction_bounds
    {p q p' q' : Data} (Gamma : NormalPath p q)
    (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma)
    {P : ℝ → ℝ} (hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (reparamAtJunction Gamma hC2 J).eta)
    (hsourceW : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) volume 0 1)
    (htargetW : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1,
        |(reparamAtJunction Gamma hC2 J).eta t u|) volume 0 1) :
    VariableFixedReparamBounds P Gamma.eta
      (reparamAtJunction Gamma hC2 J).eta J.m J.M J.N := by
  have B := ControlledJunctionPathFunctionalBounds.reparamAtJunction_bounds
    Gamma hC2 J hsource htarget
  refine
    { w := ?_
      s0 := B.s0
      s1 := B.s1
      s2 := B.s2 }
  simpa [reparamAtJunction, NormalPath.reparamSpace] using
    physicalW_comp_le Gamma hC2 hP J.m_pos J.phi_deriv J.phi1_cont
      J.jacobian_lower J.phi_zero J.phi_one hsourceW (by
        simpa [reparamAtJunction, NormalPath.reparamSpace] using htargetW)

/-- Compose an exact variable-arclength Jacobi step with its controlled
terminal marking.  This is the triangular transition consumed by the stable
component induction. -/
theorem transition_of_raw_and_junction
    {p q p' q' : Data} (Gamma : NormalPath p q)
    (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma)
    {PF P : ℝ → ℝ} {front : ℝ → ℝ → ℝ}
    {C0 C1 C2 : ℝ}
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ P t)
    (H : RawBounds PF P front Gamma.eta C0 C1 C2)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (reparamAtJunction Gamma hC2 J).eta)
    (hsourceW : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) volume 0 1)
    (htargetW : IntervalIntegrable
      (fun t ↦ P t * ∫ u in (0 : ℝ)..1,
        |(reparamAtJunction Gamma hC2 J).eta t u|) volume 0 1) :
    Transition (physicalComponents PF front)
      (physicalComponents P (reparamAtJunction Gamma hC2 J).eta)
      (1 / J.m) J.M J.N C0 C1 C2 := by
  let B := reparamAtJunction_bounds Gamma hC2 J hP hsource htarget
    hsourceW htargetW
  have hinv : 0 ≤ 1 / J.m := (one_div_pos.mpr J.m_pos).le
  have hM : 0 ≤ J.M :=
    (abs_nonneg (J.phi1 0)).trans (J.jacobian_upper 0)
  have hN : 0 ≤ J.N :=
    (abs_nonneg (J.phi2 0)).trans (J.second_upper 0)
  refine
    { w := ?_
      s0 := B.s0.trans H.s0
      s1 := ?_
      s2 := ?_ }
  · calc
      (physicalComponents P (reparamAtJunction Gamma hC2 J).eta).w ≤
          (1 / J.m) * (physicalComponents P Gamma.eta).w := B.w
      _ ≤ (1 / J.m) * (physicalComponents PF front).w :=
        mul_le_mul_of_nonneg_left H.w hinv
  · exact B.s1.trans (by
      simpa [physicalComponents, mul_assoc] using
        mul_le_mul_of_nonneg_left H.s1 hM)
  · have hfirst := mul_le_mul_of_nonneg_left H.s2 (sq_nonneg J.M)
    have hsecond := mul_le_mul_of_nonneg_left H.s1 hN
    exact B.s2.trans (by
      simpa [physicalComponents, mul_assoc] using add_le_add hfirst hsecond)

end VariableArclengthScaledJacobiTransition
