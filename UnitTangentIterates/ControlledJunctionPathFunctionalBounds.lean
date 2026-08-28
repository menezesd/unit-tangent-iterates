import UnitTangentIterates.C2NormalPathJunctionAdapter

/-!
# Separate path-functional bounds for controlled spatial junctions

`NormalPath.reparamSpace` uses one aggregate density multiplier because a
`NormalPath` stores only a single cost density.  The invariant-tube argument
instead needs the four path functionals separately.  This module retains their
sharp fixed-spatial-reparametrization dependencies:

* `W` grows by at most `mA⁻¹`;
* `S0` does not grow;
* `S1` grows by at most `MA`;
* `S2` is bounded by `MA² * S2 + NA * S1`.

No multiplication of all four estimates by `reparamCostConst` occurs.
-/

noncomputable section

open Set Function MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace ControlledJunctionPathFunctionalBounds

/-- Time-integrability of the four densities used by `W,S0,S1,S2`.  This is
kept explicit because `NormalPath` only records continuity of its aggregate
majorant, not measurability of each supremum-valued density. -/
structure FunctionalIntegrable (eta : ℝ → ℝ → ℝ) : Prop where
  w : IntervalIntegrable
    (fun t => ∫ u in (0 : ℝ)..1, |eta t u|) volume 0 1
  s0 : IntervalIntegrable (fun t => supNorm (eta t)) volume 0 1
  s1 : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 1 (eta t))) volume 0 1
  s2 : IntervalIntegrable
    (fun t => supNorm (iteratedDeriv 2 (eta t))) volume 0 1

/-- The four independent distortions of a fixed spatial reparametrization. -/
structure FixedReparamBounds
    (eta eta' : ℝ → ℝ → ℝ) (mA MA NA : ℝ) : Prop where
  w : W eta' 1 ≤ (1 / mA) * W eta 1
  s0 : S 0 eta' ≤ S 0 eta
  s1 : S 1 eta' ≤ MA * S 1 eta
  s2 : S 2 eta' ≤ MA ^ 2 * S 2 eta + NA * S 1 eta

theorem W_comp_le
    {p q : Data} (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    {phi phi1 : ℝ → ℝ} {mA : ℝ}
    (hmA : 0 < mA) (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1c : Continuous phi1) (hlow : ∀ u, mA ≤ phi1 u)
    (hphi0 : phi 0 = 0) (hphi1v : phi 1 = 1)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (fun t u => Gamma.eta t (phi u))) :
    W (fun t u => Gamma.eta t (phi u)) 1 ≤ (1 / mA) * W Gamma.eta 1 := by
  unfold W
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ u in (0 : ℝ)..1, |Gamma.eta t (phi u)|) ≤
        (1 / mA) * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := by
    intro t _
    have h := PathFunctionalsReparam.integral_abs_comp_le
      (m := mA) (a := 0) (b := 1) (eta := Gamma.eta t)
      (phi := phi) (phi1 := phi1) hmA zero_le_one
      (continuous_iff_continuousAt.2 fun u => (hC2.eta_deriv t u).continuousAt)
      hphi1 hphi1c hlow
    simpa [hphi0, hphi1v] using h
  calc
    (∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, |Gamma.eta t (phi u)|) ≤
        ∫ t in (0 : ℝ)..1,
          (1 / mA) * ∫ u in (0 : ℝ)..1, |Gamma.eta t u| :=
      intervalIntegral.integral_mono_on (by norm_num) htarget.w
        (hsource.w.const_mul _) hslice
    _ = (1 / mA) *
        ∫ t in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, |Gamma.eta t u| := by
      rw [intervalIntegral.integral_const_mul]

theorem S0_comp_le
    {p q : Data} (Gamma : NormalPath p q)
    {phi : ℝ → ℝ}
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (fun t u => Gamma.eta t (phi u))) :
    S 0 (fun t u => Gamma.eta t (phi u)) ≤ S 0 Gamma.eta := by
  rw [S_zero, S_zero]
  apply intervalIntegral.integral_mono_on (by norm_num) htarget.s0 hsource.s0
  intro t _
  exact PathFunctionalsReparam.supNorm_comp_le
    ⟨Gamma.m t, by rintro _ ⟨u, rfl⟩; exact Gamma.abs_eta_le t u⟩ phi

theorem S1_comp_le
    {p q : Data} (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    {phi phi1 : ℝ → ℝ} {MA : ℝ}
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hMA : ∀ u, |phi1 u| ≤ MA)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (fun t u => Gamma.eta t (phi u))) :
    S 1 (fun t u => Gamma.eta t (phi u)) ≤ MA * S 1 Gamma.eta := by
  unfold S
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      supNorm (iteratedDeriv 1 (fun u => Gamma.eta t (phi u))) ≤
        MA * supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
    intro t _
    have h := PathFunctionalsReparam.supNorm_iteratedDeriv_one_comp_le
      (hC2.eta_deriv t) hphi1 (hC2.eta1_bdd t) hMA
    have heq : supNorm (hC2.eta1 t) =
        supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
      congr 1
      funext u
      rw [iteratedDeriv_one]
      exact (hC2.eta_deriv t u).deriv.symm
    calc
      supNorm (iteratedDeriv 1 (fun u => Gamma.eta t (phi u))) ≤
          supNorm (hC2.eta1 t) * MA := h
      _ = MA * supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
        rw [heq]
        ring
  calc
    (∫ t in (0 : ℝ)..1,
        supNorm (iteratedDeriv 1 (fun u => Gamma.eta t (phi u)))) ≤
      ∫ t in (0 : ℝ)..1,
        MA * supNorm (iteratedDeriv 1 (Gamma.eta t)) :=
      intervalIntegral.integral_mono_on (by norm_num) htarget.s1
        (hsource.s1.const_mul _) hslice
    _ = MA * ∫ t in (0 : ℝ)..1,
        supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
      rw [intervalIntegral.integral_const_mul]

theorem S2_comp_le
    {p q : Data} (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    {phi phi1 phi2 : ℝ → ℝ} {MA NA : ℝ}
    (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi2 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hMA : ∀ u, |phi1 u| ≤ MA) (hNA : ∀ u, |phi2 u| ≤ NA)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (fun t u => Gamma.eta t (phi u))) :
    S 2 (fun t u => Gamma.eta t (phi u)) ≤
      MA ^ 2 * S 2 Gamma.eta + NA * S 1 Gamma.eta := by
  change
    (∫ t in (0 : ℝ)..1,
      supNorm (iteratedDeriv 2 (fun u => Gamma.eta t (phi u)))) ≤
        MA ^ 2 *
          (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 2 (Gamma.eta t))) +
        NA * (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 1 (Gamma.eta t)))
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      supNorm (iteratedDeriv 2 (fun u => Gamma.eta t (phi u))) ≤
        MA ^ 2 * supNorm (iteratedDeriv 2 (Gamma.eta t)) +
          NA * supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
    intro t _
    have h := PathFunctionalsReparam.supNorm_iteratedDeriv_two_comp_le
      (hC2.eta_deriv t) (hC2.eta1_deriv t) hphi1 hphi2
      (hC2.eta1_bdd t) (hC2.eta2_bdd t) hMA hNA
    have heq1 : supNorm (hC2.eta1 t) =
        supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
      congr 1
      funext u
      rw [iteratedDeriv_one]
      exact (hC2.eta_deriv t u).deriv.symm
    have heq2 : supNorm (hC2.eta2 t) =
        supNorm (iteratedDeriv 2 (Gamma.eta t)) := by
      congr 1
      funext u
      simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_zero]
      rw [show deriv (Gamma.eta t) = hC2.eta1 t from
        funext fun z => (hC2.eta_deriv t z).deriv]
      exact (hC2.eta1_deriv t u).deriv.symm
    calc
      supNorm (iteratedDeriv 2 (fun u => Gamma.eta t (phi u))) ≤
          supNorm (hC2.eta2 t) * MA ^ 2 +
            supNorm (hC2.eta1 t) * NA := h
      _ = MA ^ 2 * supNorm (iteratedDeriv 2 (Gamma.eta t)) +
          NA * supNorm (iteratedDeriv 1 (Gamma.eta t)) := by
        rw [heq1, heq2]
        ring
  have hrhs : IntervalIntegrable (fun t =>
      MA ^ 2 * supNorm (iteratedDeriv 2 (Gamma.eta t)) +
        NA * supNorm (iteratedDeriv 1 (Gamma.eta t))) volume 0 1 :=
    (hsource.s2.const_mul _).add (hsource.s1.const_mul _)
  calc
    (∫ t in (0 : ℝ)..1,
        supNorm (iteratedDeriv 2 (fun u => Gamma.eta t (phi u)))) ≤
      ∫ t in (0 : ℝ)..1,
        (MA ^ 2 * supNorm (iteratedDeriv 2 (Gamma.eta t)) +
          NA * supNorm (iteratedDeriv 1 (Gamma.eta t))) :=
      intervalIntegral.integral_mono_on (by norm_num) htarget.s2 hrhs hslice
    _ = MA ^ 2 *
          (∫ t in (0 : ℝ)..1, supNorm (iteratedDeriv 2 (Gamma.eta t))) +
        NA * (∫ t in (0 : ℝ)..1,
          supNorm (iteratedDeriv 1 (Gamma.eta t))) := by
      rw [intervalIntegral.integral_add (hsource.s2.const_mul _)
        (hsource.s1.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- Bundled componentwise estimate for an arbitrary fixed spatial
reparametrization. -/
theorem fixedReparamBounds
    {p q : Data} (Gamma : NormalPath p q) (hC2 : C2NormalPathData Gamma)
    {phi phi1 phi2 : ℝ → ℝ} {mA MA NA : ℝ}
    (hmA : 0 < mA) (hphi1 : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi2 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hphi1c : Continuous phi1) (hlow : ∀ u, mA ≤ phi1 u)
    (hMA : ∀ u, |phi1 u| ≤ MA) (hNA : ∀ u, |phi2 u| ≤ NA)
    (hphi0 : phi 0 = 0) (hphi1v : phi 1 = 1)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (fun t u => Gamma.eta t (phi u))) :
    FixedReparamBounds Gamma.eta (fun t u => Gamma.eta t (phi u)) mA MA NA :=
  ⟨W_comp_le Gamma hC2 hmA hphi1 hphi1c hlow hphi0 hphi1v hsource htarget,
    S0_comp_le Gamma hsource htarget,
    S1_comp_le Gamma hC2 hphi1 hMA hsource htarget,
    S2_comp_le Gamma hC2 hphi1 hphi2 hMA hNA hsource htarget⟩

/-- The same estimates specialized to the fixed diffeomorphism stored in a
controlled junction certificate. -/
theorem reparamAtJunction_bounds
    {p q p' q' : Data} (Gamma : NormalPath p q)
    (hC2 : C2NormalPathData Gamma)
    (J : ReparamJunctionCertificate (p' := p') (q' := q') Gamma)
    (hsource : FunctionalIntegrable Gamma.eta)
    (htarget : FunctionalIntegrable (reparamAtJunction Gamma hC2 J).eta) :
    FixedReparamBounds Gamma.eta (reparamAtJunction Gamma hC2 J).eta
      J.m J.M J.N := by
  simpa [reparamAtJunction, NormalPath.reparamSpace] using
    fixedReparamBounds Gamma hC2 J.m_pos J.phi_deriv J.phi1_deriv
      J.phi1_cont J.jacobian_lower J.jacobian_upper J.second_upper
      J.phi_zero J.phi_one hsource (by
        simpa [reparamAtJunction, NormalPath.reparamSpace] using htarget)

end ControlledJunctionPathFunctionalBounds
