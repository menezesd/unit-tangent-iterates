import UnitTangentIterates.GaugeGeometryPathVariable
import UnitTangentIterates.JacobiArclengthSeparated

/-! The separated inverse-Jacobi slice estimates used internally by the
variable-period gauge geometry theorem, exported without path erasure. -/

noncomputable section

open Set Function MeasureTheory MarkedSpace MarkedTopology PathMetric
  RearTrack ArclengthInverse

namespace GaugeGeometrySeparatedSliceCertificate

open UniformFrameBounds GaugeNormalPath GaugeJacobiAssemblyVariable
  JacobiArclength JacobiArclengthUniform SelectedInversePathGeometry
  SelectedRearArclengthEstimates PathMetricJacobi

structure Certificate
    (front rear : ℝ → ℝ → ℝ) (Qf : ℝ → ℝ)
    (CW C0 C10 C11 C20 C21 C22 : ℝ) : Prop where
  w : ∀ t, (∫ x in (0 : ℝ)..Qf t, |rear t x|) ≤
    CW * ∫ u in (0 : ℝ)..1, |front t u|
  s0 : ∀ t, supNorm (rear t) ≤
    C0 * ∫ u in (0 : ℝ)..1, |front t u|
  separated : ∀ t, JacobiArclengthSeparated.Bounds (front t) (rear t)
    C10 C11 C20 C21 C22

theorem certificate
    {P0 P1 kh : ℝ} {P : ℝ → ℝ}
    {delta K etaF etaFs etaR sf : ℝ → ℝ → ℝ}
    (hP0 : 0 < P0) (hkh0 : 0 ≤ kh) (hkh1 : kh < 1)
    (hPl : ∀ t, P0 ≤ P t) (hPu : ∀ t, P t ≤ P1)
    (hsteer : ∀ t s, HasDerivAt (delta t)
      (K t s - Real.sin (delta t s)) s)
    (hstrip0 : ∀ t s, 0 ≤ delta t s)
    (hstrip1 : ∀ t s, delta t s ≤ Real.arcsin kh)
    (hdper : ∀ t, Periodic (delta t) (P t))
    (hK : ∀ t s, |K t s| ≤ kh)
    (hetaFd : ∀ t s, HasDerivAt (etaF t) (etaFs t s) s)
    (hetaFsc : ∀ t, Continuous (etaFs t))
    (hetaFper : ∀ t, Periodic (etaF t) (P t))
    (hsfinv : ∀ t x, rearArclength (delta t) (sf t x) = x)
    (hetaR : ∀ t x, HasDerivAt (etaR t)
      (etaF t (sf t x) / Real.cos (delta t (sf t x)) - etaR t x) x)
    (hetaRper : ∀ t, Periodic (etaR t) (rearArclength (delta t) (P t))) :
    Certificate (fun t u => etaF t (P t * u)) etaR
      (fun t => rearArclength (delta t) (P t))
      P1
      (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))))
      (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))))
      (1 / Real.sqrt (1 - kh ^ 2))
      (P1 / (1 - Real.exp (-(Real.sqrt (1 - kh ^ 2) * P0))))
      (2 * kh ^ 2 / Real.sqrt (1 - kh ^ 2) ^ 3 +
        1 / Real.sqrt (1 - kh ^ 2))
      (1 / (P0 * Real.sqrt (1 - kh ^ 2) ^ 2)) := by
  set c : ℝ := Real.sqrt (1 - kh ^ 2) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact Real.sqrt_pos.mpr (by nlinarith)
  let l : ℝ → ℝ := fun t => rearArclength (delta t) (P t)
  have hPpos : ∀ t, 0 < P t := fun t => lt_of_lt_of_le hP0 (hPl t)
  have hdeltac : ∀ t, Continuous (delta t) := fun t =>
    Differentiable.continuous fun s => (hsteer t s).differentiableAt
  have hcos : ∀ t s, c ≤ Real.cos (delta t s) := fun t s =>
    Shadowing.cos_ge_of_mem_strip (hstrip0 t s) (hstrip1 t s)
  have hcospos : ∀ t s, 0 < Real.cos (delta t s) := fun t s =>
    lt_of_lt_of_le hcpos (hcos t s)
  have hcosne : ∀ t s, Real.cos (delta t s) ≠ 0 := fun t s => ne_of_gt (hcospos t s)
  have hsin : ∀ t s, |Real.sin (delta t s)| ≤ kh := fun t s =>
    abs_sin_le_of_mem_strip hkh0 hkh1.le (hstrip0 t s) (hstrip1 t s)
  have hxfd : ∀ t s, HasDerivAt (rearArclength (delta t))
      (Real.cos (delta t s)) s := fun t s => hasDerivAt_rearArclength (hdeltac t) s
  have hmono : ∀ t, StrictMono (rearArclength (delta t)) := fun t =>
    strictMono_of_deriv_ge hcpos (hxfd t) (hcos t)
  have hsfleft : ∀ t s, sf t (rearArclength (delta t) s) = s := fun t s =>
    leftInverse_of_rightInverse (hmono t).injective (hsfinv t) s
  have hsfc : ∀ t, Continuous (sf t) := fun t =>
    continuous_of_rightInverse hcpos (hxfd t) (hcos t) (hsfinv t)
  have hsfd : ∀ t x, HasDerivAt (sf t)
      (1 / Real.cos (delta t (sf t x))) x := fun t x =>
    hasDerivAt_of_rightInverse hcpos (hxfd t) (hcos t) (hsfinv t) x
  have hsfshift : ∀ t y, sf t (y + l t) = sf t y + P t := fun t y =>
    rightInverse_add_of_shift (hmono t).injective
      (fun s => rearArclength_add_period (hdeltac t) (hdper t) s) (hsfinv t) y
  have hlge : ∀ t, c * P0 ≤ l t := by
    intro t
    have h1 : c * P t ≤ l t := rearArclength_ge (hdeltac t) (hcos t) (hPpos t).le
    have h2 : c * P0 ≤ c * P t := by nlinarith [hPl t]
    linarith
  set dl : ℝ → ℝ → ℝ := fun t x => delta t (sf t x) with hdldef
  set dxv : ℝ → ℝ → ℝ := fun t x =>
    (K t (sf t x) - Real.sin (delta t (sf t x))) /
      Real.cos (delta t (sf t x)) with hdxvdef
  have hdld : ∀ t x, HasDerivAt (dl t) (dxv t x) x := by
    intro t x
    have h := (hsteer t (sf t x)).comp x (hsfd t x)
    refine h.congr_deriv ?_
    simp only [hdxvdef]
    field_simp
  set G : ℝ → ℝ → ℝ := fun t y => etaF t (sf t y) / Real.cos (dl t y)
  have hetaFc : ∀ t, Continuous (etaF t) := fun t =>
    Differentiable.continuous fun s => (hetaFd t s).differentiableAt
  have hGc : ∀ t, Continuous (G t) := by
    intro t
    exact Continuous.div ((hetaFc t).comp (hsfc t))
      (Real.continuous_cos.comp ((hdeltac t).comp (hsfc t)))
      (fun y => hcosne t (sf t y))
  have hGper : ∀ t, Periodic (G t) (l t) := by
    intro t y
    simp only [G, dl, hsfshift t y]
    rw [hetaFper t (sf t y), hdper t (sf t y)]
  have htransport : ∀ t s,
      G t (rearArclength (delta t) s) * Real.cos (delta t s) = etaF t s := by
    intro t s
    simp only [G, dl, hsfleft t s]
    field_simp [hcosne t s]
  have hetaFsper : ∀ t, Periodic (etaFs t) (P t) := fun t =>
    periodic_of_hasDerivAt (hetaFd t) (hetaFper t)
  have hFbdd : ∀ t, BddAbove (Set.range fun s => |etaF t s|) := fun t =>
    bddAbove_abs_of_periodic (hPpos t) (hetaFc t) (hetaFper t)
  have hF1bdd : ∀ t, BddAbove (Set.range fun s => |etaFs t s|) := fun t =>
    bddAbove_abs_of_periodic (hPpos t) (hetaFsc t) (hetaFsper t)
  have hraw : ∀ t,
      (∫ x in (0 : ℝ)..l t, |etaR t x|) ≤ ∫ s in (0 : ℝ)..P t, |etaF t s| ∧
      (∀ x, |etaR t x| ≤ (1 - Real.exp (-(c * P0)))⁻¹ *
        ∫ s in (0 : ℝ)..P t, |etaF t s|) ∧
      (∀ x, |deriv (etaR t) x| ≤ supNorm (etaF t) / c +
        (1 - Real.exp (-(c * P0)))⁻¹ * ∫ s in (0 : ℝ)..P t, |etaF t s|) ∧
      (∀ x, |deriv (deriv (etaR t)) x| ≤
        supNorm (etaFs t) / c ^ 2 + 2 * kh ^ 2 * supNorm (etaF t) / c ^ 3 +
          (supNorm (etaF t) / c + (1 - Real.exp (-(c * P0)))⁻¹ *
            ∫ s in (0 : ℝ)..P t, |etaF t s|)) := by
    intro t
    exact JacobiAssembly.jacobi_estimates (l := l t) (P := P t) (l0 := c * P0)
      (c := c) (kh := kh) (SF0 := supNorm (etaF t)) (SF1 := supNorm (etaFs t))
      (etaR := etaR t) (etaF := etaF t) (G := G t) (delta := delta t)
      (xf := rearArclength (delta t)) (etaFs := etaFs t) (dl := dl t) (sf := sf t)
      (K := K t) (dxv := dxv t) (by positivity) (hlge t) hcpos (hetaFd t)
      (fun s => le_supNorm (hFbdd t) s) (fun s => le_supNorm (hF1bdd t) s) (hK t)
      (hdeltac t) (hcospos t) (fun x => hcos t (sf t x)) (fun x => hsin t (sf t x))
      (hsfd t) (hdld t) (fun _ => rfl) (hxfd t) (by simp [rearArclength]) rfl rfl
      (hGc t) (hGper t) (fun x => hetaR t x) (hetaRper t) (htransport t)
  have hn0 : ∀ t, supNorm (etaF t) ≤ supNorm (fun u => etaF t (P t * u)) := by
    intro t
    exact le_of_eq (JacobiNormalized.supNorm_comp_mul (ne_of_gt (hPpos t)) (etaF t)).symm
  have hn1 : ∀ t, P t * supNorm (etaFs t) ≤
      supNorm (iteratedDeriv 1 (fun u => etaF t (P t * u))) := by
    intro t
    rw [JacobiNormalized.iteratedDeriv_one_comp_mul (hetaFd t),
      JacobiNormalized.supNorm_const_mul (hPpos t).le,
      JacobiNormalized.supNorm_comp_mul (ne_of_gt (hPpos t)) (etaFs t)]
  have hsepAll : ∀ t, JacobiArclengthSeparated.Bounds
      (fun u => etaF t (P t * u)) (etaR t)
      (P1 / (1 - Real.exp (-(c * P0)))) (1 / c)
      (P1 / (1 - Real.exp (-(c * P0))))
      (2 * kh ^ 2 / c ^ 3 + 1 / c) (1 / (P0 * c ^ 2)) := by
    intro t
    have hR1 : ∀ x, HasDerivAt (etaR t) (deriv (etaR t) x) x := fun x => by
      rw [(hetaR t x).deriv]
      exact hetaR t x
    have hR2 : ∀ x, HasDerivAt (deriv (etaR t)) (deriv (deriv (etaR t)) x) x := fun x => by
      have hcos0 : Real.cos (dl t x) ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le hcpos (hcos t (sf t x)))
      have h := JacobiAssembly.etaR_second_hasDerivAt (etaR := etaR t) (etaF := etaF t)
        (G := G t) (dl := dl t) (sf := sf t) (etaFs := etaFs t (sf t x))
        (dxv := dxv t x) (fun y => hetaR t y) rfl hcos0 (hsfd t x) (hdld t x)
        (hetaFd t (sf t x))
      rw [h.deriv]
      exact h
    exact JacobiArclengthSeparated.uniform
      (JacobiArclengthSeparated.bounds (l := l t) (P := P t) (l0 := c * P0)
        (c := c) (kh := kh) (SF0 := supNorm (etaF t)) (SF1 := supNorm (etaFs t))
        (etaF := etaF t) (etaR1 := deriv (etaR t)) (etaR2 := deriv (deriv (etaR t)))
        (hPpos t) (mul_pos hcpos hP0) hcpos hR1 hR2
        (hraw t).2.2.1 (hraw t).2.2.2 (hn0 t) (hn1 t))
      hP0 (mul_pos hcpos hP0) hcpos (hPl t) (hPu t)
  refine { w := ?_, s0 := ?_, separated := hsepAll }
  · intro t
    have hchange : (∫ s in (0 : ℝ)..P t, |etaF t s|) =
        P t * ∫ u in (0 : ℝ)..1, |etaF t (P t * u)| := by
      rw [JacobiNormalized.integral_abs_comp_mul (hPpos t).ne' (etaF t)]
      field_simp [(hPpos t).ne']
    have hI : 0 ≤ ∫ u in (0 : ℝ)..1, |etaF t (P t * u)| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    calc
      (∫ x in (0 : ℝ)..l t, |etaR t x|) ≤
          ∫ s in (0 : ℝ)..P t, |etaF t s| := (hraw t).1
      _ = P t * ∫ u in (0 : ℝ)..1, |etaF t (P t * u)| := hchange
      _ ≤ P1 * ∫ u in (0 : ℝ)..1, |etaF t (P t * u)| :=
        mul_le_mul_of_nonneg_right (hPu t) hI
  · intro t
    refine supNorm_le_of_forall fun x => (hraw t).2.1 x |>.trans ?_
    have hden : 0 < 1 - Real.exp (-(c * P0)) :=
      JacobiNormalized.one_sub_exp_pos (mul_pos hcpos hP0)
    have hchange : (∫ s in (0 : ℝ)..P t, |etaF t s|) =
        P t * ∫ u in (0 : ℝ)..1, |etaF t (P t * u)| := by
      rw [JacobiNormalized.integral_abs_comp_mul (hPpos t).ne' (etaF t)]
      field_simp [(hPpos t).ne']
    have hI : 0 ≤ ∫ u in (0 : ℝ)..1, |etaF t (P t * u)| :=
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
    rw [hchange]
    have hcoef : (1 - Real.exp (-(c * P0)))⁻¹ * P t ≤
        P1 / (1 - Real.exp (-(c * P0))) := by
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (hPu t) hden.le
    nlinarith

end GaugeGeometrySeparatedSliceCertificate
