import UnitTangentIterates.ControlledJunctionPathFunctionalBounds
import Mathlib.Topology.Order.Compact

/-!
# Functional integrability from joint continuity and periodicity

For a jointly continuous unit-periodic family, its global `supNorm` is the
maximum on `[0,1]`.  Compact maximum continuity therefore makes the `S0,S1,S2`
densities continuous in time.  The `W` density is handled by continuity of a
parametric interval integral.
-/

noncomputable section

open Set MeasureTheory MarkedTopology MarkedSpace PathMetric

namespace PeriodicSupNormFunctionalIntegrable

open ControlledJunctionPathFunctionalBounds

 theorem supNorm_eq_sSup_Icc
    {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (hper : Function.Periodic f P) :
    supNorm f = sSup ((fun u => |f u|) '' Icc 0 P) := by
  unfold supNorm
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, hu, hux⟩ := hper.exists_mem_Ico₀ hP x
    exact ⟨u, Ico_subset_Icc_self hu, by
      change |f u| = |f x|
      rw [hux]⟩
  · rintro ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩

 theorem continuous_supNorm_of_joint_continuous_periodic
    {f : ℝ → ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hcont : Continuous (Function.uncurry f))
    (hper : ∀ t, Function.Periodic (f t) P) :
    Continuous (fun t => supNorm (f t)) := by
  simp_rw [supNorm_eq_sSup_Icc hP (hper _)]
  exact isCompact_Icc.continuous_sSup (f := fun t u => |f t u|) hcont.abs

theorem continuous_L1_density_of_joint_continuous
    {f : ℝ → ℝ → ℝ} (hcont : Continuous (Function.uncurry f)) :
    Continuous (fun t => ∫ u in (0 : ℝ)..1, |f t u|) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun t u => |f t u|) hcont.abs 0 1

/-- Continuity of all four path-functional densities.  This is the
continuity-level companion of `FunctionalIntegrable`, useful when a path is
recosted by the canonical sum of its component densities. -/
structure FunctionalContinuous (eta : ℝ → ℝ → ℝ) : Prop where
  w : Continuous (fun t => ∫ u in (0 : ℝ)..1, |eta t u|)
  s0 : Continuous (fun t => supNorm (eta t))
  s1 : Continuous (fun t => supNorm (iteratedDeriv 1 (eta t)))
  s2 : Continuous (fun t => supNorm (iteratedDeriv 2 (eta t)))

/-- Joint continuity of a `C²` normal rate gives continuity, not merely
integrability, of its `W,S0,S1,S2` densities. -/
def functionalContinuous_of_jointC2
    {p q : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) :
    FunctionalContinuous Gamma.eta := by
  have hd1' : ∀ t, deriv (Gamma.eta t) = hC2.eta1 t := by
    intro t
    funext u
    exact (hC2.eta_deriv t u).deriv
  have hd1 : ∀ t, iteratedDeriv 1 (Gamma.eta t) = hC2.eta1 t := by
    intro t
    rw [iteratedDeriv_one, hd1' t]
  have hd2 : ∀ t, iteratedDeriv 2 (Gamma.eta t) = hC2.eta2 t := by
    intro t
    funext u
    simp only [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_zero]
    rw [hd1' t]
    exact (hC2.eta1_deriv t u).deriv
  refine
    { w := continuous_L1_density_of_joint_continuous heta
      s0 := continuous_supNorm_of_joint_continuous_periodic one_pos heta
        hC2.eta_periodic
      s1 := ?_
      s2 := ?_ }
  · simpa only [hd1] using
      continuous_supNorm_of_joint_continuous_periodic one_pos heta1
        hC2.eta1_periodic
  · simpa only [hd2] using
      continuous_supNorm_of_joint_continuous_periodic one_pos heta2
        hC2.eta2_periodic

/-- Joint continuity upgrades `C2NormalPathData` to the four time-integrability
facts required by the componentwise path functionals. -/
def functionalIntegrable_of_jointC2
    {p q : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2)) :
    FunctionalIntegrable Gamma.eta := by
  let h := functionalContinuous_of_jointC2 hC2 heta heta1 heta2
  refine
    { w := h.w.intervalIntegrable 0 1
      s0 := h.s0.intervalIntegrable 0 1
      s1 := h.s1.intervalIntegrable 0 1
      s2 := h.s2.intervalIntegrable 0 1 }

/-- A fixed `C²` spatial reparametrization preserves functional
integrability when the source rate and its two spatial derivatives are jointly
continuous.  This removes the last explicit integrability callback from the
configured controlled-junction transition. -/
def functionalIntegrable_comp_of_jointC2
    {p q : Data} {Gamma : NormalPath p q} (hC2 : C2NormalPathData Gamma)
    (heta : Continuous (Function.uncurry Gamma.eta))
    (heta1 : Continuous (Function.uncurry hC2.eta1))
    (heta2 : Continuous (Function.uncurry hC2.eta2))
    {phi phi1 phi2 : ℝ → ℝ}
    (hphi : ∀ u, HasDerivAt phi (phi1 u) u)
    (hphi1 : ∀ u, HasDerivAt phi1 (phi2 u) u)
    (hphi1c : Continuous phi1) (hphi2c : Continuous phi2)
    (hphi_add : ∀ u, phi (u + 1) = phi u + 1)
    (hphi1per : Function.Periodic phi1 1)
    (hphi2per : Function.Periodic phi2 1) :
    FunctionalIntegrable (fun t u => Gamma.eta t (phi u)) := by
  have hphic : Continuous phi :=
    Differentiable.continuous fun u => (hphi u).differentiableAt
  let eta0 : ℝ → ℝ → ℝ := fun t u => Gamma.eta t (phi u)
  let eta1' : ℝ → ℝ → ℝ := fun t u => hC2.eta1 t (phi u) * phi1 u
  let eta2' : ℝ → ℝ → ℝ := fun t u =>
    hC2.eta2 t (phi u) * phi1 u ^ 2 + hC2.eta1 t (phi u) * phi2 u
  have hpair : Continuous (fun z : ℝ × ℝ => (z.1, phi z.2)) :=
    continuous_fst.prodMk (hphic.comp continuous_snd)
  have hc0 : Continuous (Function.uncurry eta0) := by
    simpa only [eta0, Function.uncurry_apply_pair] using heta.comp hpair
  have hc1 : Continuous (Function.uncurry eta1') := by
    exact (heta1.comp hpair).mul (hphi1c.comp continuous_snd)
  have hc2 : Continuous (Function.uncurry eta2') := by
    exact ((heta2.comp hpair).mul ((hphi1c.comp continuous_snd).pow 2)).add
      ((heta1.comp hpair).mul (hphi2c.comp continuous_snd))
  have hp0 : ∀ t, Function.Periodic (eta0 t) 1 := by
    intro t u
    dsimp [eta0]
    rw [hphi_add, hC2.eta_periodic t]
  have hp1 : ∀ t, Function.Periodic (eta1' t) 1 := by
    intro t u
    dsimp [eta1']
    rw [hphi_add, hC2.eta1_periodic t, hphi1per]
  have hp2 : ∀ t, Function.Periodic (eta2' t) 1 := by
    intro t u
    dsimp [eta2']
    rw [hphi_add, hC2.eta2_periodic t, hphi1per,
      hC2.eta1_periodic t, hphi2per]
  have hderiv1 : ∀ t, deriv (eta0 t) = eta1' t := by
    intro t
    funext u
    exact ((hC2.eta_deriv t (phi u)).comp u (hphi u)).deriv
  have hd1 : ∀ t, iteratedDeriv 1 (eta0 t) = eta1' t := by
    intro t
    rw [iteratedDeriv_one, hderiv1 t]
  have hd2 : ∀ t, iteratedDeriv 2 (eta0 t) = eta2' t := by
    intro t
    funext u
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, hd1 t]
    have h := ((hC2.eta1_deriv t (phi u)).comp u (hphi u)).mul (hphi1 u)
    convert h.deriv using 1 <;> simp [eta1', eta2', Function.comp_apply] <;> ring
  refine
    { w := (continuous_L1_density_of_joint_continuous hc0).intervalIntegrable 0 1
      s0 := (continuous_supNorm_of_joint_continuous_periodic one_pos hc0 hp0).intervalIntegrable 0 1
      s1 := ?_
      s2 := ?_ }
  · simpa only [eta0, hd1] using
      (continuous_supNorm_of_joint_continuous_periodic one_pos hc1 hp1).intervalIntegrable 0 1
  · simpa only [eta0, hd2] using
      (continuous_supNorm_of_joint_continuous_periodic one_pos hc2 hp2).intervalIntegrable 0 1

end PeriodicSupNormFunctionalIntegrable
