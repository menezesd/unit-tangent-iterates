import UnitTangentIterates.GaugeNormalPathVariableSeparated

/-! Separated density transport through a nonaffine marking. -/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric

namespace GaugeNormalPathVariableSeparatedNonaffine

open UniformFrameBounds GaugeNormalPath GaugeNormalPathSeparated

/-- The three inverse functional estimates needed to replace an affine front
parameter by an arbitrary marked parameter.  They are deliberately separated:
the selected-rear Jacobi estimate depends on the front only through `W`, `S0`,
and `S1`. -/
structure FrontComparison (intrinsic marked : ℝ → ℝ) (BW B0 B1 : ℝ) : Prop where
  w : (∫ u in (0 : ℝ)..1, |intrinsic u|) ≤
    BW * ∫ u in (0 : ℝ)..1, |marked u|
  s0 : supNorm intrinsic ≤ B0 * supNorm marked
  s1 : supNorm (iteratedDeriv 1 intrinsic) ≤
    B1 * supNorm (iteratedDeriv 1 marked)

def frontComparison_mono
    {intrinsic marked : ℝ → ℝ} {BW B0 B1 BW' B0' B1' : ℝ}
    (H : FrontComparison intrinsic marked BW B0 B1)
    (hW : BW ≤ BW') (h0 : B0 ≤ B0') (h1 : B1 ≤ B1') :
    FrontComparison intrinsic marked BW' B0' B1' where
  w := H.w.trans (mul_le_mul_of_nonneg_right hW
    (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)))
  s0 := H.s0.trans (mul_le_mul_of_nonneg_right h0 (supNorm_nonneg _))
  s1 := H.s1.trans (mul_le_mul_of_nonneg_right h1 (supNorm_nonneg _))

/-- The inverse functional comparison supplied by a positive nonaffine
reparametrization of one period.  The upper first-jet bound controls `W`,
surjectivity controls `S0`, and the lower first-jet bound controls `S1`. -/
theorem frontComparison_of_reparam
    {eta eta1 phi phi1 : ℝ → ℝ} {P m M : ℝ}
    (hP : 0 < P) (hm : 0 < m)
    (heta1 : ∀ x, HasDerivAt eta (eta1 x) x) (hetac : Continuous eta)
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u) (hphi1c : Continuous phi1)
    (hetaPer : Periodic eta P) (hphiP : phi 1 - phi 0 = P)
    (hlow : ∀ u, m ≤ phi1 u) (hupp : ∀ u, phi1 u ≤ M)
    (hsurj : Surjective phi)
    (hbdd0 : BddAbove (Set.range fun u => |eta (phi u)|))
    (hbdd1 : BddAbove
      (Set.range fun u => |iteratedDeriv 1 (fun v => eta (phi v)) u|)) :
    FrontComparison (fun u => eta (P * u)) (fun u => eta (phi u))
      (M / P) 1 (P / m) := by
  have hphid : Differentiable ℝ phi := fun u => (hphi1 u).differentiableAt
  have hphic : Continuous phi := hphid.continuous
  have hmarkedc : Continuous fun u => |eta (phi u)| :=
    (hetac.comp hphic).abs
  have hchange : (∫ u in (0 : ℝ)..1, phi1 u * |eta (phi u)|) =
      ∫ x in (0 : ℝ)..P, |eta x| := by
    have h := intervalIntegral.integral_comp_smul_deriv
      (a := (0 : ℝ)) (b := 1) (f := phi) (f' := phi1) (g := fun x => |eta x|)
      (fun u _ => hphi1 u) hphi1c.continuousOn hetac.abs
    have hend : phi 1 = phi 0 + P := by linarith
    calc
      (∫ u in (0 : ℝ)..1, phi1 u * |eta (phi u)|) =
          ∫ x in phi 0..phi 1, |eta x| := by
            simpa [smul_eq_mul] using h
      _ = ∫ x in phi 0..phi 0 + P, |eta x| := by rw [hend]
      _ = ∫ x in (0 : ℝ)..P, |eta x| := by
        have hperabs : Periodic (fun x ↦ |eta x|) P := fun x ↦ by
          change |eta (x + P)| = |eta x|
          rw [hetaPer x]
        simpa using (hperabs.intervalIntegral_add_eq (phi 0) 0)
  have hchangeUpper : (∫ x in (0 : ℝ)..P, |eta x|) ≤
      M * ∫ u in (0 : ℝ)..1, |eta (phi u)| := by
    rw [← hchange, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on zero_le_one
      ((hphi1c.mul hmarkedc).intervalIntegrable _ _)
      ((continuous_const.mul hmarkedc).intervalIntegrable _ _) ?_
    intro u _
    exact mul_le_mul_of_nonneg_right (hupp u) (abs_nonneg _)
  have hAffine : (∫ x in (0 : ℝ)..P, |eta x|) =
      P * ∫ u in (0 : ℝ)..1, |eta (P * u)| := by
    rw [JacobiNormalized.integral_abs_comp_mul hP.ne' eta]
    field_simp
  have hderivMarked : iteratedDeriv 1 (fun u => eta (phi u)) =
      fun u => eta1 (phi u) * phi1 u := by
    rw [iteratedDeriv_one]
    exact PathFunctionalsReparam.deriv_comp_eq heta1 hphi1
  have hderivAffine : iteratedDeriv 1 (fun u => eta (P * u)) =
      fun u => eta1 (P * u) * P := by
    rw [iteratedDeriv_one]
    funext u
    simpa [Function.comp_def] using
      ((heta1 (P * u)).comp u ((hasDerivAt_const u P).mul (hasDerivAt_id u))).deriv
  refine { w := ?_, s0 := ?_, s1 := ?_ }
  · rw [hAffine] at hchangeUpper
    have hWnonneg : 0 ≤ ∫ u in (0 : ℝ)..1, |eta (phi u)| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hP).2
    simpa [mul_comm] using hchangeUpper
  · simp only [one_mul]
    refine Real.iSup_le (fun u => ?_) (supNorm_nonneg _)
    obtain ⟨v, hv⟩ := hsurj (P * u)
    dsimp
    rw [← hv]
    exact le_supNorm hbdd0 v
  · rw [hderivAffine]
    refine Real.iSup_le (fun u => ?_)
      (mul_nonneg (div_nonneg hP.le hm.le) (supNorm_nonneg _))
    obtain ⟨v, hv⟩ := hsurj (P * u)
    have hpoint : |eta1 (phi v) * phi1 v| ≤
        supNorm (iteratedDeriv 1 fun z => eta (phi z)) := by
      calc
        |eta1 (phi v) * phi1 v| =
            |iteratedDeriv 1 (fun z => eta (phi z)) v| := by rw [hderivMarked]
        _ ≤ supNorm (iteratedDeriv 1 fun z => eta (phi z)) := le_supNorm hbdd1 v
    have hphi1pos : 0 < phi1 v := hm.trans_le (hlow v)
    have heta1le : |eta1 (P * u)| ≤
        supNorm (iteratedDeriv 1 fun z => eta (phi z)) / m := by
      rw [← hv, le_div_iff₀ hm]
      calc
        |eta1 (phi v)| * m ≤ |eta1 (phi v)| * phi1 v :=
          mul_le_mul_of_nonneg_left (hlow v) (abs_nonneg _)
        _ = |eta1 (phi v) * phi1 v| := by
          rw [abs_mul, abs_of_pos hphi1pos]
        _ ≤ supNorm (iteratedDeriv 1 fun z => eta (phi z)) := hpoint
    rw [abs_mul, abs_of_pos hP]
    calc
      |eta1 (P * u)| * P ≤
          (supNorm (iteratedDeriv 1 fun z => eta (phi z)) / m) * P :=
        mul_le_mul_of_nonneg_right heta1le hP.le
      _ = (P / m) * supNorm (iteratedDeriv 1 fun z => eta (phi z)) := by ring

/-- A nonaffine front comparison rescales the separated arclength estimates,
after which the existing variable-period gauge theorem gives the four marked
`W/S0/S1/S2` density gains. -/
theorem flowedBounds_of_frontComparison
    {p q : Data} (Gamma : NormalPath p q) (D : GaugeFrameData)
    {Phi : ℝ → ℝ → ℝ} {Qf Qf' : ℝ → ℝ}
    (hQpos : ∀ t, 0 < Qf t) (hQd : ∀ t, HasDerivAt Qf (Qf' t) t)
    (hvper : ∀ t, Periodic (D.v t) (Qf t))
    (hxiqp : ∀ t x, D.xi t (x + Qf t) = D.xi t x - Qf' t * D.v t x)
    (hPhid : ∀ u t, HasDerivAt (fun r => Phi r u)
      (GaugeRate.gaugeRate D.xi D.v t (Phi t u)) t)
    (hPhi0 : ∀ u, Phi 0 u = Qf 0 * u)
    {etaR front : ℝ → ℝ → ℝ}
    (hetaC2 : ∀ t, ContDiff ℝ (2 : ℕ) (etaR t))
    (hetaper : ∀ t, Periodic (etaR t) (Qf t))
    (hrest : ∀ t ∉ Ioo (0 : ℝ) Gamma.T, etaR t = fun _ => 0)
    {CW C0 A10 A11 A20 A21 A22 BW B0 B1 : ℝ}
    (hCW : 0 ≤ CW) (hC0 : 0 ≤ C0)
    (hA10 : 0 ≤ A10) (hA11 : 0 ≤ A11)
    (hA20 : 0 ≤ A20) (hA21 : 0 ≤ A21) (hA22 : 0 ≤ A22)
    (hBW : 0 ≤ BW) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hfront : ∀ t ∈ Ioo (0 : ℝ) Gamma.T,
      FrontComparison (front t) (Gamma.eta t) BW B0 B1)
    (hW : ∀ t ∈ Ioo (0 : ℝ) Gamma.T,
      (∫ x in (0 : ℝ)..Qf t, |etaR t x|) ≤
        CW * ∫ u in (0 : ℝ)..1, |front t u|)
    (hS0 : ∀ t ∈ Ioo (0 : ℝ) Gamma.T,
      supNorm (etaR t) ≤ C0 * ∫ u in (0 : ℝ)..1, |front t u|)
    (hsep : ∀ t ∈ Ioo (0 : ℝ) Gamma.T,
      JacobiArclengthSeparated.Bounds (front t) (etaR t)
        A10 A11 A20 A21 A22) :
    FlowedBounds Gamma.eta (fun t u => etaR t (Phi t u))
      (gaugeCW (CW * BW) D.rateLip Gamma.T (Qf 0)) (C0 * BW)
      (flowFirst (A10 * BW) D.rateLip Gamma.T (Qf 0))
      (flowFirst (A11 * B0) D.rateLip Gamma.T (Qf 0))
      (flowSecond (A20 * BW) D.rateLip Gamma.T (Qf 0) +
        flowDrift (A10 * BW) D.rateLip D.rateBound2 Gamma.T (Qf 0))
      (flowSecond (A21 * B0) D.rateLip Gamma.T (Qf 0) +
        flowDrift (A11 * B0) D.rateLip D.rateBound2 Gamma.T (Qf 0))
      (flowSecond (A22 * B1) D.rateLip Gamma.T (Qf 0)) := by
  apply GaugeNormalPathVariableSeparated.flowedBounds Gamma D hQpos hQd hvper hxiqp
    hPhid hPhi0 hetaC2 hetaper hrest
    (mul_nonneg hCW hBW) (mul_nonneg hC0 hBW)
    (mul_nonneg hA10 hBW) (mul_nonneg hA11 hB0)
    (mul_nonneg hA20 hBW) (mul_nonneg hA21 hB0) (mul_nonneg hA22 hB1)
  · intro t ht
    calc
      (∫ x in (0 : ℝ)..Qf t, |etaR t x|) ≤
          CW * ∫ u in (0 : ℝ)..1, |front t u| := hW t ht
      _ ≤ CW * (BW * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
        mul_le_mul_of_nonneg_left (hfront t ht).w hCW
      _ = (CW * BW) * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := by ring
  · intro t ht
    calc
      supNorm (etaR t) ≤ C0 * ∫ u in (0 : ℝ)..1, |front t u| := hS0 t ht
      _ ≤ C0 * (BW * ∫ u in (0 : ℝ)..1, |Gamma.eta t u|) :=
        mul_le_mul_of_nonneg_left (hfront t ht).w hC0
      _ = (C0 * BW) * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := by ring
  · intro t ht
    let W := ∫ u in (0 : ℝ)..1, |Gamma.eta t u|
    let S0 := supNorm (Gamma.eta t)
    let S1 := supNorm (iteratedDeriv 1 (Gamma.eta t))
    have hw : 0 ≤ W := intervalIntegral.integral_nonneg zero_le_one
      (fun _ _ => abs_nonneg _)
    have hs0 : 0 ≤ S0 := supNorm_nonneg _
    have hs1 : 0 ≤ S1 := supNorm_nonneg _
    refine { s1 := (hsep t ht).s1.trans ?_, s2 := (hsep t ht).s2.trans ?_ }
    · calc
        A10 * (∫ u in (0 : ℝ)..1, |front t u|) + A11 * supNorm (front t) ≤
            A10 * (BW * W) + A11 * (B0 * S0) :=
          add_le_add (mul_le_mul_of_nonneg_left (hfront t ht).w hA10)
            (mul_le_mul_of_nonneg_left (hfront t ht).s0 hA11)
        _ = (A10 * BW) * W + (A11 * B0) * S0 := by ring
    · calc
        A20 * (∫ u in (0 : ℝ)..1, |front t u|) + A21 * supNorm (front t) +
            A22 * supNorm (iteratedDeriv 1 (front t)) ≤
          A20 * (BW * W) + A21 * (B0 * S0) + A22 * (B1 * S1) :=
            add_le_add
              (add_le_add (mul_le_mul_of_nonneg_left (hfront t ht).w hA20)
                (mul_le_mul_of_nonneg_left (hfront t ht).s0 hA21))
              (mul_le_mul_of_nonneg_left (hfront t ht).s1 hA22)
        _ = (A20 * BW) * W + (A21 * B0) * S0 + (A22 * B1) * S1 := by ring

end GaugeNormalPathVariableSeparatedNonaffine
