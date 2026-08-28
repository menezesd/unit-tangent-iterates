import Mathlib
import UnitTangentIterates.ConstructedProfileInterior
import UnitTangentIterates.InteriorRelativeDischarge
import UnitTangentIterates.HairpinTailsInterior
import UnitTangentIterates.HairpinMassInterior
import UnitTangentIterates.PeriodizationFiniteDerivativeChain
import UnitTangentIterates.PeriodizationPositiveMixedCertificate

/-!
# All finite periodization orders for the constructed hairpin pulse

The constructed interior profile already supplies every finite smoothness order
of its front-arclength pulse and an exponential order-zero tail.  The only
all-order input not presently derived from the translator equation is the
relative-derivative induction step recorded by
`RelativeDerivativeRecurrence`.  From that one step this file constructs
relative and exponential bounds at every finite order and applies the positive
mixed-periodization machinery at an arbitrary requested pair `(r,q)`.
-/

noncomputable section

open Set Real HairpinRelative
open scoped ContDiff

namespace ConstructedPeriodizationAllOrders

open PeriodizationFiniteDerivativeChain
open PeriodizationPositiveMixedCertificate

/-! ### A quantitative Faà di Bruno closure

The paper's all-order argument repeatedly uses the following elementary
consequence of Faà di Bruno: an outer jet which is pointwise `O(w)` after a
change of variables, composed with a map whose positive-order jets are
uniformly bounded, is still `O(w)`.  Stating it with `IsBigO` lets the finite
sum and finite product bookkeeping be handled by the standard asymptotics
calculus rather than by choosing a separate numerical majorant for every
ordered partition. -/

theorem iteratedDeriv_comp_isBigO
    {g f w : ℝ → ℝ} {l : Filter ℝ} (hg : ContDiff ℝ ∞ g)
    (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (houter : ∀ j ≤ n,
      (fun x => iteratedDeriv j g (f x)) =O[l] w)
    (hinner : ∀ j, 0 < j → j ≤ n →
      iteratedDeriv j f =O[l] (fun _ => (1 : ℝ))) :
    iteratedDeriv n (g ∘ f) =O[l] w := by
  have hformula : iteratedDeriv n (g ∘ f) = fun x =>
      ∑ c : OrderedFinpartition n,
        iteratedDeriv c.length g (f x) *
          ∏ j, iteratedDeriv (c.partSize j) f x := by
    funext x
    exact iteratedDeriv_comp_eq_sum_orderedFinpartition
      hg.contDiffAt hf.contDiffAt
        (show (n : WithTop ℕ∞) ≤ ∞ from mod_cast le_top)
  rw [hformula]
  apply Asymptotics.IsBigO.sum
  intro c _
  have ho := houter c.length c.length_le
  have hi : (fun x => ∏ j, iteratedDeriv (c.partSize j) f x)
      =O[l] (fun _ => (1 : ℝ)) := by
    simpa using Asymptotics.IsBigO.finsetProd (s := Finset.univ) fun j _ =>
      hinner (c.partSize j) (c.partSize_pos j) (c.partSize_le j)
  simpa only [Pi.one_apply, mul_one] using ho.mul hi

/-- Quantitative Leibniz closure in the same form: if every jet of the first
factor through order `n` is `O(w)` and every jet of the second is uniformly
bounded, then the `n`-th jet of their product is `O(w)`. -/
theorem iteratedDeriv_mul_isBigO
    {a b w : ℝ → ℝ} {l : Filter ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (n : ℕ)
    (haO : ∀ j ≤ n, iteratedDeriv j a =O[l] w)
    (hbO : ∀ j ≤ n,
      iteratedDeriv j b =O[l] (fun _ => (1 : ℝ))) :
    iteratedDeriv n (fun x => a x * b x) =O[l] w := by
  have hformula : iteratedDeriv n (fun x => a x * b x) = fun x =>
      ∑ i ∈ Finset.range (n + 1),
        n.choose i * iteratedDeriv i a x * iteratedDeriv (n - i) b x := by
    funext x
    simpa using iteratedDeriv_mul
      (ha.contDiffAt.of_le (show (n : WithTop ℕ∞) ≤ ∞ from mod_cast le_top))
      (hb.contDiffAt.of_le (show (n : WithTop ℕ∞) ≤ ∞ from mod_cast le_top))
  rw [hformula]
  apply Asymptotics.IsBigO.sum
  intro i hi
  have hin : i ≤ n := by simpa using Finset.mem_range.mp hi
  have hni : n - i ≤ n := Nat.sub_le n i
  have hp := (haO i hin).mul (hbO (n - i) hni)
  simpa only [Pi.one_apply, mul_one, mul_assoc] using
    hp.const_mul_left (n.choose i : ℝ)

/-- A continuous scalar function of a uniformly bounded real state is
uniformly bounded.  This is the compact-range step used for every derivative
of the smooth coefficient functions in the curvature equation. -/
theorem continuous_comp_isBigO_one_of_isBigO_one
    {phi K : ℝ → ℝ} (hphi : Continuous phi)
    (hK : K =O[Filter.principal Set.univ] (fun _ => (1 : ℝ))) :
    (fun x => phi (K x)) =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := by
  rw [Asymptotics.isBigO_principal] at hK ⊢
  obtain ⟨C, hC⟩ := hK
  let R := |C|
  have hKr : ∀ x, K x ∈ Set.Icc (-R) R := by
    intro x
    have hx := hC x (Set.mem_univ x)
    simp only [norm_eq_abs, norm_one, mul_one] at hx
    have hx' : |K x| ≤ R := le_trans hx (le_abs_self C)
    exact ⟨(neg_le_of_abs_le hx'), (le_of_abs_le hx')⟩
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hphi.continuousOn
  refine ⟨|B|, fun x _ => ?_⟩
  simp only [norm_eq_abs, norm_one, mul_one]
  exact le_trans (hB (K x) (hKr x)) (le_abs_self B)

/-- A smooth function composed with a state whose positive-order jets through
`n` are uniformly bounded has a uniformly bounded `n`-th derivative. -/
theorem iteratedDeriv_comp_isBigO_one
    {g K : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hK : ContDiff ℝ ∞ K)
    (n : ℕ)
    (hKjets : ∀ j ≤ n,
      iteratedDeriv j K =O[Filter.principal Set.univ] (fun _ => (1 : ℝ))) :
    iteratedDeriv n (g ∘ K) =O[Filter.principal Set.univ]
      (fun _ => (1 : ℝ)) := by
  apply iteratedDeriv_comp_isBigO hg hK n
  · intro j hj
    apply continuous_comp_isBigO_one_of_isBigO_one
      (hg.continuous_iteratedDeriv j
        (show (j : WithTop ℕ∞) ≤ ∞ from mod_cast le_top))
    simpa only [iteratedDeriv_zero] using hKjets 0 (Nat.zero_le n)
  · intro j hjpos hj
    exact hKjets j hj

/-- The simultaneous all-order induction used in the paper for the intrinsic
curvature equation.  The hypotheses separate the exact evolution and speed
identities from the two order-zero estimates (`K = O(1)` and
`K ∘ sigma = O(K)`).  All higher estimates are consequences. -/
theorem intrinsic_relative_jets_of_shifted_evolution
    {K sigma amp speed : ℝ → ℝ}
    (hKc : ContDiff ℝ ∞ K) (hsc : ContDiff ℝ ∞ sigma)
    (hac : ContDiff ℝ ∞ amp) (hvc : ContDiff ℝ ∞ speed)
    (hKbounded : K =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)))
    (hshift : (K ∘ sigma) =O[Filter.principal Set.univ] K)
    (hspeed : deriv sigma = speed ∘ K)
    (hevol : deriv K = fun u => amp (K u) * K (sigma u) - K u - K u ^ 3) :
    ∀ n : ℕ,
      (∀ j ≤ n, iteratedDeriv j K =O[Filter.principal Set.univ] K) ∧
      (∀ j, 0 < j → j ≤ n →
        iteratedDeriv j sigma =O[Filter.principal Set.univ]
          (fun _ => (1 : ℝ))) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro j hj
        have : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        simpa only [iteratedDeriv_zero] using
          (Asymptotics.isBigO_refl K (Filter.principal Set.univ))
      · intro j hj hj0
        omega
  | succ n ih =>
      rcases ih with ⟨hKrel, hsbd⟩
      have hKbd : ∀ j ≤ n,
          iteratedDeriv j K =O[Filter.principal Set.univ]
            (fun _ => (1 : ℝ)) := fun j hj => (hKrel j hj).trans hKbounded
      have hsnext : iteratedDeriv (n + 1) sigma
          =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := by
        have hv := iteratedDeriv_comp_isBigO_one hvc hKc n hKbd
        rw [iteratedDeriv_succ', hspeed]
        exact hv
      have hsall : ∀ j, 0 < j → j ≤ n + 1 →
          iteratedDeriv j sigma =O[Filter.principal Set.univ]
            (fun _ => (1 : ℝ)) := by
        intro j hj hjn
        rcases lt_or_eq_of_le hjn with hjlt | rfl
        · exact hsbd j hj (Nat.lt_succ_iff.mp hjlt)
        · exact hsnext
      have hKshiftJets : ∀ j ≤ n,
          (fun u => iteratedDeriv j K (sigma u))
            =O[Filter.principal Set.univ] K := by
        intro j hj
        have ht : Filter.Tendsto sigma (Filter.principal Set.univ)
            (Filter.principal Set.univ) := by simp
        exact ((hKrel j hj).comp_tendsto ht).trans hshift
      have hKcomp : ContDiff ℝ ∞ (K ∘ sigma) := hKc.comp hsc
      have hKshiftDeriv : ∀ j ≤ n,
          iteratedDeriv j (K ∘ sigma)
            =O[Filter.principal Set.univ] K := by
        intro j hj
        exact iteratedDeriv_comp_isBigO hKc hsc j
          (fun k hk => hKshiftJets k (le_trans hk hj))
          (fun k hkpos hk => hsbd k hkpos (le_trans hk hj))
      have hampComp : ContDiff ℝ ∞ (amp ∘ K) := hac.comp hKc
      have hampJets : ∀ j ≤ n, iteratedDeriv j (amp ∘ K)
          =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := by
        intro j hj
        exact iteratedDeriv_comp_isBigO_one hac hKc j
          (fun k hk => hKbd k (le_trans hk hj))
      have hmain : iteratedDeriv n
          (fun u => amp (K u) * K (sigma u))
            =O[Filter.principal Set.univ] K := by
        have h := iteratedDeriv_mul_isBigO hKcomp hampComp n
          hKshiftDeriv hampJets
        simpa only [Function.comp_apply, mul_comm] using h
      have hsqc : ContDiff ℝ ∞ (fun u => K u ^ 2) := hKc.pow 2
      have hsqJets : ∀ j ≤ n, iteratedDeriv j (fun u => K u ^ 2)
          =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := by
        intro j hj
        have hpow : ContDiff ℝ ∞ (fun z : ℝ => z ^ 2) := contDiff_id.pow 2
        simpa only [Function.comp_apply] using
          (iteratedDeriv_comp_isBigO_one hpow hKc j
            (fun k hk => hKbd k (le_trans hk hj)))
      have hcube : iteratedDeriv n (fun u => K u ^ 3)
          =O[Filter.principal Set.univ] K := by
        have h := iteratedDeriv_mul_isBigO hKc hsqc n hKrel hsqJets
        simpa only [pow_succ', pow_two] using h
      have hnext : iteratedDeriv (n + 1) K
          =O[Filter.principal Set.univ] K := by
        rw [iteratedDeriv_succ', hevol]
        have hmainc : ContDiff ℝ ∞ (fun u => amp (K u) * K (sigma u)) := by
          simpa only [Function.comp_apply] using hampComp.mul hKcomp
        have hcubec : ContDiff ℝ ∞ (fun u => K u ^ 3) := hKc.pow 3
        have hnle : (n : WithTop ℕ∞) ≤ ∞ := by
          exact_mod_cast le_top
        have hformula :
            iteratedDeriv n (fun u => amp (K u) * K (sigma u) - K u - K u ^ 3) =
              fun u => iteratedDeriv n (fun v => amp (K v) * K (sigma v)) u -
                iteratedDeriv n K u - iteratedDeriv n (fun v => K v ^ 3) u := by
          funext u
          change iteratedDeriv n
              (((fun v => amp (K v) * K (sigma v)) - K) - (fun v => K v ^ 3)) u = _
          calc
            _ = iteratedDeriv n
                  ((fun v => amp (K v) * K (sigma v)) - K) u -
                iteratedDeriv n (fun v => K v ^ 3) u :=
              iteratedDeriv_sub ((hmainc.sub hKc).contDiffAt.of_le hnle)
                (hcubec.contDiffAt.of_le hnle)
            _ = _ := by
              rw [iteratedDeriv_sub (hmainc.contDiffAt.of_le hnle)
                (hKc.contDiffAt.of_le hnle)]
        rw [hformula]
        exact (hmain.sub (hKrel n le_rfl)).sub hcube
      constructor
      · intro j hj
        rcases lt_or_eq_of_le hj with hjlt | rfl
        · exact hKrel j (Nat.lt_succ_iff.mp hjlt)
        · exact hnext
      · exact hsall

/-! ### Specialization to the localized translator phase -/

/-- The right inverse stored in `InteriorPhaseData` is also a left inverse,
because front arclength has everywhere positive derivative. -/
theorem pulseState_frontArclength
    {f theta x g gp : ℝ → ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi)) (u : ℝ) :
    x (frontArclength f theta u) = u := by
  have hkc : Continuous fun v => curvField f (theta v) :=
    continuous_curv_along_theta hf d.profile_pos d.angle_mem d.angle_deriv
  have hd := HairpinTailsInterior.hasDerivAt_frontArclength_of_comp hkc
  have hmono : StrictMono (frontArclength f theta) := by
    refine strictMono_of_deriv_pos fun v => ?_
    rw [(hd v).deriv]
    positivity
  apply hmono.injective
  exact d.inverse_value (frontArclength f theta u)

/-- The exact phase relation at an arbitrary rear arclength. -/
theorem theta_shifted_frontArclength_eq
    {f theta x g gp : ℝ → ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi)) (u : ℝ) :
    theta (frontArclength f theta u +
      Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))) =
      g (theta u) := by
  simpa [pulseState_frontArclength d hf u] using
    CanonicalTranslatorLocalPhase.theta_phase_eq d d.x_zero
      (frontArclength f theta u)

/-- Localized curvature-at-image identity.  This is the interior-only version
of `HairpinFrontCurvature.curvField_next`. -/
theorem curvField_next_of_interior
    {f theta x g gp : ℝ → ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi) :
    curvField f (g t) = gp t * pulseField f t := by
  have hdelta : g t - t ∈ Ioo 0 (Real.pi / 2) := by
    rw [d.shift t ht]
    exact ⟨Real.arctan_pos.mpr (curvField_pos_interior d.profile_pos ht),
      Real.arctan_lt_pi_div_two _⟩
  have hcos : 0 < Real.cos (g t - t) := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hdelta.1, Real.pi_pos], hdelta.2⟩
  have htan : Real.tan (g t - t) = curvField f t := by
    rw [d.shift t ht, Real.tan_arctan]
  have hrel : Real.sin t * Real.cos (g t - t) =
      f t * Real.sin (g t - t) := by
    rw [Real.tan_eq_sin_div_cos, curvField,
      div_eq_div_iff hcos.ne' (d.profile_pos t ht).ne'] at htan
    linarith
  set delta := g t - t with hdeltaDef
  have hg : g t = t + delta := by rw [hdeltaDef]; ring
  have hsin : Real.sin (g t) =
      (f t + Real.cos t) * Real.sin delta := by
    rw [hg, Real.sin_add]
    nlinarith [hrel]
  have himg := d.image_mem t ht
  have hfg : f (g t) ≠ 0 := (d.profile_pos _ himg).ne'
  rw [curvField, hsin, ← d.translator_identity t ht,
    HairpinFrontCurvature.pulseField_eq_sin_delta d.shift ht, ← hdeltaDef]
  field_simp

/-- The localized phase data imply the exact shifted intrinsic curvature
evolution used by the all-order induction. -/
theorem intrinsic_shifted_evolution_of_interior
    {f theta x g gp : ℝ → ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi)) :
    let K : ℝ → ℝ := fun u => curvField f (theta u)
    let tau : ℝ → ℝ := fun u => frontArclength f theta u +
      Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))
    deriv K = fun u =>
      (1 + K u ^ 2) * Real.sqrt (1 + K u ^ 2) * K (tau u) - K u - K u ^ 3 := by
  dsimp only
  let K : ℝ → ℝ := fun u => curvField f (theta u)
  let tau : ℝ → ℝ := fun u => frontArclength f theta u +
    Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))
  have hfpos := d.profile_pos
  obtain ⟨hthC, -, -⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have htheta : ContDiff ℝ ∞ theta := contDiff_infty.mpr hthC
  have hKc : ContDiff ℝ ∞ K := by
    exact HairpinInteriorRegularity.contDiff_comp_of_mapsTo
      (HairpinInteriorRegularity.contDiffOn_curvField hf hfpos) htheta d.angle_mem
  have hKderiv : ∀ u, HasDerivAt K (deriv K u) u := fun u =>
    ((hKc.differentiable (by simp)) u).hasDerivAt
  have hkc : Continuous K := hKc.continuous
  have htau : ∀ u, HasDerivAt tau (Real.sqrt (1 + K u ^ 2)) u := by
    intro u
    simpa [tau, K] using
      (HairpinTailsInterior.hasDerivAt_frontArclength_of_comp hkc u).const_add
        (Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2)))
  have htranslated : ∀ u,
      deriv (fun r => Real.arctan (K r)) u / deriv tau u +
          Real.sin (Real.arctan (K u)) = K (tau u) := by
    intro u
    have hgd : HasDerivAt (fun r => g (theta r) - theta r)
        (gp (theta u) * K u - K u) u := by
      exact ((d.translator_deriv _ (d.angle_mem u)).comp u (d.angle_deriv u)).sub
        (d.angle_deriv u)
    have heq : (fun r => Real.arctan (K r)) = fun r => g (theta r) - theta r := by
      funext r
      exact (d.shift _ (d.angle_mem r)).symm
    have hdatan : deriv (fun r => Real.arctan (K r)) u =
        gp (theta u) * K u - K u := by
      rw [heq]
      exact hgd.deriv
    rw [hdatan, (htau u).deriv,
      ← HairpinRelative.pulseField_eq_sin_arctan]
    calc
      (gp (theta u) * K u - K u) / Real.sqrt (1 + K u ^ 2) +
          pulseField f (theta u) = gp (theta u) * pulseField f (theta u) := by
        rw [pulseField]
        field_simp [ne_of_gt (sqrt_one_add_sq_pos (K u))]
        ring
      _ = curvField f (g (theta u)) :=
        (curvField_next_of_interior d (d.angle_mem u)).symm
      _ = K (tau u) := by
        change curvField f (g (theta u)) = curvField f
          (theta (frontArclength f theta u +
            Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))))
        rw [theta_shifted_frontArclength_eq d hf u]
  funext u
  exact HairpinPulse.curvature_deriv_eq_of_translator hKderiv htau htranslated u

/-- Every intrinsic curvature jet of the localized translator is relatively
bounded.  All constants are existentially encoded by `IsBigO`; no endpoint
extension of the angle profile is used. -/
theorem intrinsic_all_orders_of_interior
    {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hlow : ∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M) :
    ∀ n : ℕ, iteratedDeriv n (fun u => curvField f (theta u))
      =O[Filter.principal Set.univ] (fun u => curvField f (theta u)) := by
  let K : ℝ → ℝ := fun u => curvField f (theta u)
  let s0 := Hairpin.hairpinArclength f (Real.pi / 2) (g (Real.pi / 2))
  let tau : ℝ → ℝ := fun u => frontArclength f theta u + s0
  let speed : ℝ → ℝ := fun z => Real.sqrt (1 + z ^ 2)
  let amp : ℝ → ℝ := fun z => (1 + z ^ 2) * Real.sqrt (1 + z ^ 2)
  obtain ⟨hthC, -, -⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf d.profile_pos
      d.angle_mem d.angle_deriv d.state_deriv
  have htheta : ContDiff ℝ ∞ theta := contDiff_infty.mpr hthC
  have hKc : ContDiff ℝ ∞ K :=
    HairpinInteriorRegularity.contDiff_comp_of_mapsTo
      (HairpinInteriorRegularity.contDiffOn_curvField hf d.profile_pos)
      htheta d.angle_mem
  have hspeedc : ContDiff ℝ ∞ speed := by
    apply (contDiff_const.add (contDiff_id.pow 2)).sqrt
    intro z
    positivity
  have hampc : ContDiff ℝ ∞ amp := by
    exact (contDiff_const.add (contDiff_id.pow 2)).mul hspeedc
  have hkc : Continuous K := hKc.continuous
  have hfrontD : ∀ u, HasDerivAt (frontArclength f theta) (speed (K u)) u := by
    intro u
    simpa [speed, K] using
      HairpinTailsInterior.hasDerivAt_frontArclength_of_comp hkc u
  have hspeedK : ContDiff ℝ ∞ (speed ∘ K) := hspeedc.comp hKc
  have hfrontc : ContDiff ℝ ∞ (frontArclength f theta) := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun u => (hfrontD u).differentiableAt, ?_⟩
    have heq : deriv (frontArclength f theta) = speed ∘ K := by
      funext u
      exact (hfrontD u).deriv
    rw [heq]
    exact hspeedK
  have htauc : ContDiff ℝ ∞ tau := by
    exact hfrontc.add contDiff_const
  have htauD : deriv tau = speed ∘ K := by
    funext u
    have h := (hfrontD u).const_add s0
    simpa [tau] using h.deriv
  have hApos : 0 < A := by
    have hk0 : 0 < K 0 := curvField_pos_interior d.profile_pos (d.angle_mem 0)
    have hd0 : K 0 ≤ A := by simpa [K] using hdecay 0
    linarith
  have hKle : ∀ u, K u ≤ A := by
    intro u
    have he : Real.exp (-|u| / M) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg u)) hM.le
    calc
      K u ≤ A * Real.exp (-|u| / M) := hdecay u
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left he hApos.le
      _ = A := mul_one A
  have hKpos : ∀ u, 0 < K u := fun u =>
    curvField_pos_interior d.profile_pos (d.angle_mem u)
  have hKbounded : K =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := by
    rw [Asymptotics.isBigO_principal]
    refine ⟨A, fun u _ => ?_⟩
    simp only [norm_eq_abs, norm_one, mul_one, abs_of_pos (hKpos u)]
    exact hKle u
  have hharnack := harnack_shift_of_interior (s0 := s0) hm hmA hf d.profile_pos
    hlow hupp d.angle_mem d.angle_deriv d.inverse_value hdecay hM
  let Ch := (Am / m) * Real.exp ((|s0| + A ^ 2 * M / 2) / m)
  have hCh : 0 ≤ Ch := by
    have hAm : 0 < Am := lt_of_lt_of_le hm hmA
    dsimp [Ch]
    positivity
  have hshift : (K ∘ tau) =O[Filter.principal Set.univ] K := by
    rw [Asymptotics.isBigO_principal]
    refine ⟨Ch, fun u _ => ?_⟩
    simp only [Function.comp_apply, norm_eq_abs, abs_of_pos (hKpos (tau u)),
      abs_of_pos (hKpos u)]
    have h := hharnack (frontArclength f theta u)
    rw [pulseState_frontArclength d hf u] at h
    simpa [K, tau, s0, Ch] using h
  have hevol : deriv K = fun u => amp (K u) * K (tau u) - K u - K u ^ 3 := by
    simpa [K, tau, s0, amp] using intrinsic_shifted_evolution_of_interior d hf
  intro n
  exact (intrinsic_relative_jets_of_shifted_evolution hKc htauc hampc hspeedc
    hKbounded hshift htauD hevol n).1 n le_rfl

/-- Bounded jets of an inverse reparametrization whose speed is a smooth
function of a bounded state with relative jets. -/
theorem inverse_jets_of_relative_state
    {K x invSpeed : ℝ → ℝ}
    (hKc : ContDiff ℝ ∞ K) (hxc : ContDiff ℝ ∞ x)
    (hvc : ContDiff ℝ ∞ invSpeed)
    (hKbounded : K =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)))
    (hKrel : ∀ n, iteratedDeriv n K =O[Filter.principal Set.univ] K)
    (hxderiv : deriv x = invSpeed ∘ (K ∘ x)) :
    ∀ n j, 0 < j → j ≤ n →
      iteratedDeriv j x =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := by
  have htend : Filter.Tendsto x (Filter.principal Set.univ)
      (Filter.principal Set.univ) := by simp
  have hKxbounded : (K ∘ x) =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) :=
    hKbounded.comp_tendsto htend
  intro n
  induction n with
  | zero =>
      intro j hj hj0
      omega
  | succ n ih =>
      have hKxOuter : ∀ j ≤ n,
          (fun s => iteratedDeriv j K (x s))
            =O[Filter.principal Set.univ] (K ∘ x) := by
        intro j hj
        exact (hKrel j).comp_tendsto htend
      have hKxRel : ∀ j ≤ n, iteratedDeriv j (K ∘ x)
          =O[Filter.principal Set.univ] (K ∘ x) := by
        intro j hj
        exact iteratedDeriv_comp_isBigO hKc hxc j
          (fun k hk => hKxOuter k (le_trans hk hj))
          (fun k hkpos hk => ih k hkpos (le_trans hk hj))
      have hKxBd : ∀ j ≤ n, iteratedDeriv j (K ∘ x)
          =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := fun j hj =>
        (hKxRel j hj).trans hKxbounded
      have hnext : iteratedDeriv (n + 1) x
          =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := by
        rw [iteratedDeriv_succ', hxderiv]
        exact iteratedDeriv_comp_isBigO_one hvc (hKc.comp hxc) n hKxBd
      intro j hj hjn
      rcases lt_or_eq_of_le hjn with hjlt | rfl
      · exact ih j hj (Nat.lt_succ_iff.mp hjlt)
      · exact hnext

/-- Relative jets transfer through the inverse front reparametrization to the
normalized steering pulse `K(x)/sqrt(1+K(x)^2)`. -/
theorem normalized_inverse_pulse_relative_jets
    {K x : ℝ → ℝ} {B : ℝ}
    (hKc : ContDiff ℝ ∞ K) (hxc : ContDiff ℝ ∞ x)
    (hKpos : ∀ u, 0 < K u) (hB0 : 0 ≤ B) (hKB : ∀ u, K u ≤ B)
    (hKrel : ∀ n, iteratedDeriv n K =O[Filter.principal Set.univ] K)
    (hxderiv : deriv x =
      (fun z => 1 / Real.sqrt (1 + z ^ 2)) ∘ (K ∘ x)) :
    ∀ n, iteratedDeriv n
        (fun s => K (x s) / Real.sqrt (1 + K (x s) ^ 2))
      =O[Filter.principal Set.univ]
        (fun s => K (x s) / Real.sqrt (1 + K (x s) ^ 2)) := by
  let invSpeed : ℝ → ℝ := fun z => 1 / Real.sqrt (1 + z ^ 2)
  have hivc : ContDiff ℝ ∞ invSpeed := by
    apply contDiff_const.div
      ((contDiff_const.add (contDiff_id.pow 2)).sqrt fun z => by positivity)
    intro z
    positivity
  have hKbounded : K =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := by
    rw [Asymptotics.isBigO_principal]
    refine ⟨B, fun u _ => ?_⟩
    simp only [norm_eq_abs, norm_one, mul_one, abs_of_pos (hKpos u)]
    exact hKB u
  have hxjets := inverse_jets_of_relative_state hKc hxc hivc hKbounded hKrel
    (by simpa [invSpeed] using hxderiv)
  have htend : Filter.Tendsto x (Filter.principal Set.univ)
      (Filter.principal Set.univ) := by simp
  have hKxOuter : ∀ j,
      (fun s => iteratedDeriv j K (x s))
        =O[Filter.principal Set.univ] (K ∘ x) := fun j =>
    (hKrel j).comp_tendsto htend
  have hKxRel : ∀ n, iteratedDeriv n (K ∘ x)
      =O[Filter.principal Set.univ] (K ∘ x) := by
    intro n
    exact iteratedDeriv_comp_isBigO hKc hxc n
      (fun j _ => hKxOuter j) (fun j hj hjn => hxjets n j hj hjn)
  have hKxbounded : (K ∘ x) =O[Filter.principal Set.univ]
      (fun _ => (1 : ℝ)) := hKbounded.comp_tendsto htend
  have hKxBd : ∀ n, iteratedDeriv n (K ∘ x)
      =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := fun n =>
    (hKxRel n).trans hKxbounded
  have hinvJets : ∀ n, iteratedDeriv n (invSpeed ∘ (K ∘ x))
      =O[Filter.principal Set.univ] (fun _ => (1 : ℝ)) := fun n =>
    iteratedDeriv_comp_isBigO_one hivc (hKc.comp hxc) n
      (fun j _ => hKxBd j)
  have hpulseComp : (K ∘ x) =O[Filter.principal Set.univ]
      (fun s => K (x s) / Real.sqrt (1 + K (x s) ^ 2)) := by
    rw [Asymptotics.isBigO_principal]
    refine ⟨Real.sqrt (1 + B ^ 2), fun s _ => ?_⟩
    simp only [Function.comp_apply, norm_eq_abs, abs_of_pos (hKpos (x s)),
      abs_of_pos (div_pos (hKpos (x s)) (sqrt_one_add_sq_pos _))]
    have hs : Real.sqrt (1 + K (x s) ^ 2) ≤ Real.sqrt (1 + B ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [hKB (x s), (hKpos (x s)).le]
    rw [div_eq_mul_inv]
    have hsp : 0 < Real.sqrt (1 + K (x s) ^ 2) := sqrt_one_add_sq_pos _
    calc
      K (x s) = Real.sqrt (1 + K (x s) ^ 2) *
          (K (x s) * (Real.sqrt (1 + K (x s) ^ 2))⁻¹) := by field_simp
      _ ≤ Real.sqrt (1 + B ^ 2) *
          (K (x s) * (Real.sqrt (1 + K (x s) ^ 2))⁻¹) := by
            exact mul_le_mul_of_nonneg_right hs (mul_nonneg (hKpos _).le (inv_nonneg.mpr hsp.le))
  intro n
  have hprod := iteratedDeriv_mul_isBigO (hKc.comp hxc)
    (hivc.comp (hKc.comp hxc)) n (fun j _ => hKxRel j) (fun j _ => hinvJets j)
  have hrelPulse := hprod.trans hpulseComp
  simpa [invSpeed, Function.comp_apply, div_eq_mul_inv] using hrelPulse

/-- Every front-arclength pulse jet of the localized translator is relatively
bounded. -/
theorem pulse_all_orders_of_interior
    {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hlow : ∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M) :
    ∀ n, iteratedDeriv n (fun s => pulseField f (theta (x s)))
      =O[Filter.principal Set.univ] (fun s => pulseField f (theta (x s))) := by
  let K : ℝ → ℝ := fun u => curvField f (theta u)
  obtain ⟨hthC, hwC, -⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf d.profile_pos
      d.angle_mem d.angle_deriv d.state_deriv
  have htheta : ContDiff ℝ ∞ theta := contDiff_infty.mpr hthC
  have hwc : ContDiff ℝ ∞ (fun s => theta (x s)) := contDiff_infty.mpr hwC
  have hKc : ContDiff ℝ ∞ K :=
    HairpinInteriorRegularity.contDiff_comp_of_mapsTo
      (HairpinInteriorRegularity.contDiffOn_curvField hf d.profile_pos)
      htheta d.angle_mem
  have hKpos : ∀ u, 0 < K u := fun u =>
    curvField_pos_interior d.profile_pos (d.angle_mem u)
  have hApos : 0 < A := by
    have hd0 : K 0 ≤ A := by simpa [K] using hdecay 0
    linarith [hKpos 0]
  have hKB : ∀ u, K u ≤ A := by
    intro u
    have he : Real.exp (-|u| / M) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg u)) hM.le
    exact le_trans (hdecay u) (by simpa using mul_le_mul_of_nonneg_left he hApos.le)
  have hKrel : ∀ n, iteratedDeriv n K
      =O[Filter.principal Set.univ] K := by
    simpa [K] using intrinsic_all_orders_of_interior d hm hmA hf hlow hupp
      hdecay hM
  have hkc : Continuous K := hKc.continuous
  have hKxc : ContDiff ℝ ∞ (K ∘ x) := by
    simpa [K, Function.comp_apply] using
      HairpinInteriorRegularity.contDiff_comp_of_mapsTo
        (HairpinInteriorRegularity.contDiffOn_curvField hf d.profile_pos)
        hwc (fun s => d.angle_mem (x s))
  have hfrontD : ∀ u, HasDerivAt (frontArclength f theta)
      (Real.sqrt (1 + K u ^ 2)) u := by
    intro u
    simpa [K] using HairpinTailsInterior.hasDerivAt_frontArclength_of_comp hkc u
  have hxD : ∀ s, HasDerivAt x
      (1 / Real.sqrt (1 + K (x s) ^ 2)) s := by
    apply ArclengthInverse.hasDerivAt_of_rightInverse (c := 1) one_pos hfrontD
    · intro u
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + K u ^ 2 by
        nlinarith [sq_nonneg (K u)])
      simpa using h
    · exact d.inverse_value
  have hxderiv : deriv x =
      (fun z => 1 / Real.sqrt (1 + z ^ 2)) ∘ (K ∘ x) := by
    funext s
    exact (hxD s).deriv
  have hinvc : ContDiff ℝ ∞ (fun z : ℝ => 1 / Real.sqrt (1 + z ^ 2)) := by
    apply contDiff_const.div
      ((contDiff_const.add (contDiff_id.pow 2)).sqrt fun z => by positivity)
    intro z
    positivity
  have hxc : ContDiff ℝ ∞ x := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun s => (hxD s).differentiableAt, ?_⟩
    rw [hxderiv]
    exact hinvc.comp hKxc
  intro n
  have h := normalized_inverse_pulse_relative_jets hKc hxc hKpos hApos.le hKB
    hKrel hxderiv n
  simpa [pulseField, K, Function.comp_apply] using h

/-- The front-arclength steering pulse associated with interior coordinates. -/
def pulse (f theta x : ℝ → ℝ) : ℝ → ℝ :=
  fun s => pulseField f (theta (x s))

/-- The single missing all-order recurrence.  It is deliberately an induction
step rather than an assumed family of all-order estimates: differentiating the
translator identity at general order should instantiate this interface. -/
structure RelativeDerivativeRecurrence (y : ℝ → ℝ) : Prop where
  next : ∀ (n : ℕ) (D : ℝ), 0 ≤ D →
    (∀ s, |iteratedDeriv n y s| ≤ D * y s) →
    ∃ E : ℝ, 0 ≤ E ∧ ∀ s, |iteratedDeriv (n + 1) y s| ≤ E * y s

/-- The recurrence expected specifically from the constructed translator
profile.  Proving this proposition is the remaining analytic recurrence lemma;
all later all-order periodization statements are derived below. -/
def InteriorRecurrenceProvider : Prop :=
  ∀ {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ},
    CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp →
    0 < m → m ≤ Am →
    ContDiffOn ℝ ∞ f (Ioo 0 Real.pi) →
    (∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t) →
    (∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am) →
    (∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) →
    0 < M →
    (∀ z ∈ Ioo (0 : ℝ) Real.pi, ∃ u, theta u = z) →
    RelativeDerivativeRecurrence (pulse f theta x)

/-- Coefficient form of the missing translator induction.  The open-domain
flow identity gives `y⁽ⁿ⁾ = y · Lₙ`; this is the exact additional statement
needed to control `Lₙ₊₁` near the two noncompact ends of `(0,π)`. -/
def InteriorCoefficientRecurrenceProvider : Prop :=
  ∀ {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ},
    CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp →
    0 < m → m ≤ Am →
    ContDiffOn ℝ ∞ f (Ioo 0 Real.pi) →
    (∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t) →
    (∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am) →
    (∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M)) →
    0 < M →
    (∀ z ∈ Ioo (0 : ℝ) Real.pi, ∃ u, theta u = z) →
    ∀ (n : ℕ) (D : ℝ), 0 ≤ D →
      (∀ t ∈ Ioo (0 : ℝ) Real.pi,
        |RelativeDerivatives.coeff (pulseField f) n t| ≤ D) →
      ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ioo (0 : ℝ) Real.pi,
        |RelativeDerivatives.coeff (pulseField f) (n + 1) t| ≤ E

/-- The translator evolution and inverse-front transfer discharge the
coefficient recurrence at every order. -/
theorem interiorCoefficientRecurrenceProvider : InteriorCoefficientRecurrenceProvider := by
  intro f theta x g gp m Am A M d hm hmA hf hlow hupp hdecay hM hsurj
    n D hD hcoeff
  have hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  have hO := pulse_all_orders_of_interior d hm hmA hf hlow hupp hdecay hM (n + 1)
  rw [Asymptotics.isBigO_principal] at hO
  obtain ⟨C, hC⟩ := hO
  have hrel : ∀ s,
      |iteratedDeriv (n + 1) (fun r => pulseField f (theta (x r))) s| ≤
        |C| * pulseField f (theta (x s)) := by
    intro s
    have hy : 0 < pulseField f (theta (x s)) := by
      rw [pulseField]
      exact div_pos (curvField_pos_interior hfpos (d.angle_mem (x s)))
        (sqrt_one_add_sq_pos _)
    have h := hC s (Set.mem_univ s)
    simp only [norm_eq_abs, abs_of_pos hy] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (le_abs_self C) hy.le)
  refine ⟨|C|, abs_nonneg C, ?_⟩
  exact abs_coeff_pulse_le_of_flow hf hfpos d.angle_mem d.angle_deriv
    d.inverse_value hsurj d.state_deriv hrel

/-- The coefficient recurrence implies the relative-derivative recurrence by
the open-domain autonomous-flow identity and surjectivity of the pulse state. -/
theorem interiorRecurrenceProvider_of_coefficientRecurrence
    (R : InteriorCoefficientRecurrenceProvider) : InteriorRecurrenceProvider := by
  intro f theta x g gp m Am A M d hm hmA hf hlow hupp hdecay hM hsurj
  have hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  refine ⟨?_⟩
  intro n D hD hrel
  have hcoeff : ∀ t ∈ Ioo (0 : ℝ) Real.pi,
      |RelativeDerivatives.coeff (pulseField f) n t| ≤ D :=
    abs_coeff_pulse_le_of_flow hf hfpos d.angle_mem d.angle_deriv d.inverse_value
      hsurj d.state_deriv (by simpa [pulse] using hrel)
  obtain ⟨E, hE, hcoeffNext⟩ :=
    R d hm hmA hf hlow hupp hdecay hM hsurj n D hD hcoeff
  refine ⟨E, hE, ?_⟩
  simpa [pulse] using
    (abs_iteratedDeriv_pulse_le_of_coeff_bound hf hfpos
      (fun s => d.angle_mem (x s)) d.state_deriv hcoeffNext)

/-- The constructed translator recurrence, with no external analytic input. -/
theorem interiorRecurrenceProvider : InteriorRecurrenceProvider :=
  interiorRecurrenceProvider_of_coefficientRecurrence
    interiorCoefficientRecurrenceProvider

/-- The present hand-derived translator identities supply the coefficient
recurrence exactly while `n < 4`.  Extending this statement to arbitrary `n`
is the remaining Faà di Bruno/Bell-polynomial induction. -/
theorem exists_coefficient_succ_bound_of_lt_four
    {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hlow : ∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hM : 0 < M)
    (hsurj : ∀ z ∈ Ioo (0 : ℝ) Real.pi, ∃ u, theta u = z)
    (n : ℕ) (hn : n < 4) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ioo (0 : ℝ) Real.pi,
      |RelativeDerivatives.coeff (pulseField f) (n + 1) t| ≤ E := by
  obtain ⟨relativeConst, hnonneg, hrel⟩ :=
    hrelj_of_interior d hm hmA hf hlow hupp hdecay hM hsurj
  refine ⟨relativeConst (n + 1), hnonneg (n + 1), ?_⟩
  apply abs_coeff_pulse_le_of_flow hf
    (fun t ht => lt_of_lt_of_le hm (hlow t ht)) d.angle_mem d.angle_deriv
    d.inverse_value hsurj d.state_deriv
  exact hrel (n + 1) (by omega)

/-- Starting with `|y| ≤ y`, the recurrence produces a relative constant at
every requested finite order. -/
theorem RelativeDerivativeRecurrence.exists_relative_bounds
    {y : ℝ → ℝ} (R : RelativeDerivativeRecurrence y)
    (hy0 : ∀ s, 0 ≤ y s) :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧
      ∀ n s, |iteratedDeriv n y s| ≤ D n * y s := by
  have hex : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧
      ∀ s, |iteratedDeriv n y s| ≤ D * y s := by
    intro n
    induction n with
    | zero =>
        refine ⟨1, zero_le_one, ?_⟩
        intro s
        simp [iteratedDeriv_zero, abs_of_nonneg (hy0 s)]
    | succ n ih =>
        obtain ⟨D, hD0, hD⟩ := ih
        simpa [Nat.succ_eq_add_one] using R.next n D hD0 hD
  let D : ℕ → ℝ := fun n => Classical.choose (hex n)
  refine ⟨D, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (hex n)).1
  · intro n s
    exact (Classical.choose_spec (hex n)).2 s

/-- Every-finite-order smoothness gives the compatible derivative chain used by
the mixed translated summands. -/
theorem derivativeChain_iteratedDeriv {y : ℝ → ℝ}
    (hyC : ∀ n : ℕ, ContDiff ℝ (n : ℕ) y) :
    DerivativeChain (fun n => iteratedDeriv n y) := by
  refine ⟨?_⟩
  intro n s
  simpa using hasDerivAt_iteratedDeriv
    (hyC (n + 2)) (by omega : n < n + 2) s

/-- Interior hairpin data, an order-zero curvature tail, and the one recurrence
step yield exponential bounds at all orders and hence the exact TeX mixed-sum
certificate at any finite `(r,q)`. -/
theorem exists_certificate_of_interior_recurrence
    {f theta x g gp : ℝ → ℝ} {m Am A M : ℝ}
    (d : CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp)
    (hm : 0 < m) (hmA : m ≤ Am)
    (hf : ContDiffOn ℝ ∞ f (Ioo 0 Real.pi))
    (hlow : ∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t)
    (hupp : ∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am)
    (hdecay : ∀ u, curvField f (theta u) ≤ A * Real.exp (-|u| / M))
    (hA : 0 ≤ A) (hM : 0 < M)
    (R : RelativeDerivativeRecurrence (pulse f theta x))
    (r q : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      (∀ n s, |iteratedDeriv n (pulse f theta x) s| ≤
        C n * Real.exp (-(M⁻¹) * |s|)) ∧
      PositiveMixedDerivativeCertificate
        (fun n => iteratedDeriv n (pulse f theta x)) r q := by
  have hfpos : ∀ t ∈ Ioo (0 : ℝ) Real.pi, 0 < f t := fun t ht =>
    lt_of_lt_of_le hm (hlow t ht)
  obtain ⟨-, -, hyC⟩ :=
    HairpinInteriorRegularity.contDiff_nat_hairpin_coordinates hf hfpos
      d.angle_mem d.angle_deriv d.state_deriv
  have hy0 : ∀ s, 0 ≤ pulse f theta x s := by
    intro s
    exact pulseField_nonneg_interior hfpos (d.angle_mem (x s))
  obtain ⟨D, hD0, hD⟩ := R.exists_relative_bounds hy0
  have hkc : Continuous (fun u => curvField f (theta u)) :=
    continuous_curv_along_theta hf hfpos d.angle_mem d.angle_deriv
  have hknn : ∀ u, 0 ≤ curvField f (theta u) := fun u =>
    (curvField_pos_interior hfpos (d.angle_mem u)).le
  have hyle : ∀ u, pulseField f (theta u) ≤ curvField f (theta u) := fun u =>
    HairpinMassInterior.pulseField_le_curvField_at (hknn u)
  have hypulse : ∀ s, pulse f theta x s ≤
      (A * Real.exp (A ^ 2 / 2)) * Real.exp (-|s| / M) := by
    intro s
    exact HairpinTailsInterior.pulse_decay_of_comp hkc hknn hyle hdecay hA hM
      d.inverse_value s
  let C : ℕ → ℝ := fun n => D n * (A * Real.exp (A ^ 2 / 2))
  have hC0 : ∀ n, 0 ≤ C n := by
    intro n
    exact mul_nonneg (hD0 n) (mul_nonneg hA (Real.exp_pos _).le)
  have hb : ∀ n s, |iteratedDeriv n (pulse f theta x) s| ≤
      C n * Real.exp (-(M⁻¹) * |s|) := by
    intro n s
    have h := HairpinTailsInterior.abs_iteratedDeriv_pulse_decay_of_relative
      (f := f) (w := fun s => theta (x s)) (M := M)
      hypulse (hD0 n) (hD n) s
    simpa [pulse, C, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hz : DerivativeChain (fun n => iteratedDeriv n (pulse f theta x)) :=
    derivativeChain_iteratedDeriv hyC
  have halpha : 0 < M⁻¹ := inv_pos.mpr hM
  exact ⟨C, hC0, hb,
    (PeriodizationPositiveMixedCertificate.exists_certificate_of_exp
      hz halpha hb) r q⟩

/-- Arbitrary finite mixed orders for the profile actually constructed from
`eps`.  Every profile, coordinate, smoothness, and exponential-tail hypothesis
is produced internally.  The sole remaining input is
`InteriorRecurrenceProvider`, the general-order differentiated translator
recurrence. -/
theorem exists_constructed_certificate
    (R : InteriorRecurrenceProvider) {eps : ℝ}
    (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) (r q : ℕ) :
    ∃ (f g gp theta x : ℝ → ℝ) (m Am : ℝ) (C : ℕ → ℝ),
      eps⁻¹ - eps ≤ m ∧ 0 < m ∧ m ≤ Am ∧
      (∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t) ∧
      (∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am) ∧
      ContDiffOn ℝ ∞ f (Ioo 0 Real.pi) ∧
      StrictMono theta ∧
      (∀ z ∈ Ioo (0 : ℝ) Real.pi, ∃ u, theta u = z) ∧
      (∀ u, curvField f (theta u) ≤
        (2 / m) * Real.exp (-|u| / Am)) ∧
      CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp ∧
      (∀ n, 0 ≤ C n) ∧
      (∀ n s, |iteratedDeriv n (pulse f theta x) s| ≤
        C n * Real.exp (-(Am⁻¹) * |s|)) ∧
      PositiveMixedDerivativeCertificate
        (fun n => iteratedDeriv n (pulse f theta x)) r q := by
  obtain ⟨f, g, gp, theta, x, m, Am, hmbar, hm, hmA, hlow, hupp, hf,
    htheta, hsurj, hdecay, d⟩ := exists_interiorPhaseData_of_eps heps heps10
  have hAm : 0 < Am := lt_of_lt_of_le hm hmA
  have hA : 0 ≤ 2 / m := by positivity
  have hrec := R d hm hmA hf hlow hupp hdecay hAm hsurj
  obtain ⟨C, hC0, hb, hcert⟩ := exists_certificate_of_interior_recurrence
    d hm hmA hf hlow hupp hdecay hA hAm hrec r q
  exact ⟨f, g, gp, theta, x, m, Am, C, hmbar, hm, hmA, hlow, hupp, hf,
    htheta, hsurj, hdecay, d, hC0, hb, hcert⟩

/-- Arbitrary finite mixed orders for the actually constructed epsilon-profile,
with the translator recurrence discharged internally. -/
theorem exists_constructed_certificate_unconditional {eps : ℝ}
    (heps : 0 < eps) (heps10 : eps ≤ 1 / 10) (r q : ℕ) :
    ∃ (f g gp theta x : ℝ → ℝ) (m Am : ℝ) (C : ℕ → ℝ),
      eps⁻¹ - eps ≤ m ∧ 0 < m ∧ m ≤ Am ∧
      (∀ t ∈ Ioo (0 : ℝ) Real.pi, m ≤ f t) ∧
      (∀ t ∈ Ioo (0 : ℝ) Real.pi, f t ≤ Am) ∧
      ContDiffOn ℝ ∞ f (Ioo 0 Real.pi) ∧
      StrictMono theta ∧
      (∀ z ∈ Ioo (0 : ℝ) Real.pi, ∃ u, theta u = z) ∧
      (∀ u, curvField f (theta u) ≤
        (2 / m) * Real.exp (-|u| / Am)) ∧
      CanonicalTranslatorLocalPhase.InteriorPhaseData f theta x g gp ∧
      (∀ n, 0 ≤ C n) ∧
      (∀ n s, |iteratedDeriv n (pulse f theta x) s| ≤
        C n * Real.exp (-(Am⁻¹) * |s|)) ∧
      PositiveMixedDerivativeCertificate
        (fun n => iteratedDeriv n (pulse f theta x)) r q :=
  exists_constructed_certificate interiorRecurrenceProvider heps heps10 r q

end ConstructedPeriodizationAllOrders
