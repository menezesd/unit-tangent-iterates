module

public import UnitTangentIterates.ShadowChain
public import UnitTangentIterates.ShadowRearCurve

/-!
# The selected inverse on normalized ovals: qualitative properties

A normalized oval `(L, f)` is *admissible* with curvature bound `κ` (`Ovals.AdmOval`) if
`L > 0`, `f` is continuous and `1`-periodic with `0 ≤ f ≤ κ`, and `∫₀¹ L f = π`.

For admissible `(L, f)` with `κ < 1` we show that the selected inverse `(rearL L f, rearF L f)`
is again a normalized oval with positive, Lipschitz curvature (`Ovals.rear_facts`,
`Ovals.rearF_lipschitz`), and we translate it back to arclength
(`Ovals.rear_arclength`), which identifies the rear curve (`Ovals.rearCurve_eq_curveOfCurvature`)
and bounds its width.
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-- Admissible normalized ovals. -/
def AdmOval (κ L : ℝ) (f : ℝ → ℝ) : Prop :=
  0 < L ∧ Continuous f ∧ Function.Periodic f 1 ∧ (∀ σ, 0 ≤ f σ ∧ f σ ≤ κ) ∧
    ∫ σ in (0 : ℝ)..1, L * f σ = π

lemma AdmOval.mono {κ κ' L : ℝ} {f : ℝ → ℝ} (h : AdmOval κ L f) (hκ : κ ≤ κ') :
    AdmOval κ' L f :=
  ⟨h.1, h.2.1, h.2.2.1, fun σ => ⟨(h.2.2.2.1 σ).1, (h.2.2.2.1 σ).2.trans hκ⟩, h.2.2.2.2⟩

/-- A normalized oval is represented by its own data `(L f, L)` of period `1`. -/
lemma represents_self {L : ℝ} {f : ℝ → ℝ} (hL : 0 < L) :
    Represents 1 (fun σ => L * f σ) (fun _ => L) L f := by
  refine ⟨by simp, id, fun u => ?_, fun u => rfl, fun u => rfl⟩
  simpa [div_self hL.ne'] using hasDerivAt_id u

/-- Properties of a represented curvature function. -/
lemma Represents.f_props {p L : ℝ} {a g f : ℝ → ℝ} (h : Represents p a g L f) (hp : 0 < p)
    (ha : Continuous a) (hg : Continuous g) (hap : Function.Periodic a p)
    (hgp : Function.Periodic g p) (hg0 : ∀ u, 0 < g u) :
    Continuous f ∧ Function.Periodic f 1 ∧ ∫ σ in (0 : ℝ)..1, L * f σ = ∫ u in (0 : ℝ)..p, a u := by
  have hL := h.L_pos hp hg hg0
  obtain ⟨-, s, hs, hsp, hsa⟩ := h
  obtain ⟨G, hG1, hG2, hGc⟩ := Represents.exists_inverse hp hg hgp hg0 hL hs
  have hfG : ∀ y, f y = a (G y) / g (G y) := fun y => by
    have := hsa (G y)
    rw [hG1] at this
    rw [eq_div_iff (hg0 _).ne', this]; ring
  have hfc : Continuous f := by
    rw [show f = fun y => a (G y) / g (G y) from funext hfG]
    exact (ha.comp hGc).div (hg.comp hGc) fun y => (hg0 _).ne'
  have hfp : Function.Periodic f 1 := fun y => by
    have : y + 1 = s (G y + p) := by rw [hsp, hG1]
    rw [this, hfG, hfG y, hG2, hap, hgp]
  refine ⟨hfc, hfp, ?_⟩
  have e : ∀ u, a u = ((fun σ => L * f σ) ∘ s) u * (g u / L) := fun u => by
    simp only [Function.comp, hsa u]; field_simp
  have hF : Function.Periodic (fun σ => L * f σ) 1 := fun σ => by
    show L * f (σ + 1) = L * f σ; rw [hfp σ]
  have key := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := p) (f := s)
    (f' := fun u => g u / L) (g := fun σ => L * f σ) (fun u _ => hs u)
    ((hg.div_const L).continuousOn) (continuous_const.mul hfc)
  rw [show s p = s 0 + 1 by simpa using hsp 0, hF.intervalIntegral_add_eq (s 0) 0,
    zero_add] at key
  rw [← key]
  exact intervalIntegral.integral_congr fun u _ => (e u).symm

section rear

variable {κ L : ℝ} {f : ℝ → ℝ}

/-- The steering angle of an admissible normalized oval. -/
lemma rδ_spec (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    Function.Periodic (rδ L f) 1 ∧
      (∀ σ, HasDerivAt (rδ L f) (L * f σ - L * Real.sin (rδ L f σ)) σ) ∧
      ∀ σ, rδ L f σ ∈ Set.Icc 0 (Real.arcsin κ) :=
  steerAngle_spec (p := 1) (κ := κ) (a := fun σ => L * f σ) (b := fun _ => L) one_pos hκ0 hκ1
    (continuous_const.mul hA.2.1) continuous_const
    (fun σ => by show L * f (σ + 1) = L * f σ; rw [hA.2.2.1 σ])
    (fun _ => rfl) (fun _ => hA.1) (fun σ => mul_nonneg hA.1.le (hA.2.2.2.1 σ).1)
    (fun σ => by rw [mul_comm κ]; exact mul_le_mul_of_nonneg_left (hA.2.2.2.1 σ).2 hA.1.le)

/-- The selected rear turns by `π`. -/
lemma rear_turn (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    ∫ σ in (0 : ℝ)..1, L * Real.sin (rδ L f σ) = π := by
  obtain ⟨hδp, hδd, -⟩ := rδ_spec hA hκ0 hκ1
  have hδc : Continuous (rδ L f) := continuous_iff_continuousAt.2 fun σ => (hδd σ).continuousAt
  have hfc : Continuous fun σ => L * f σ := continuous_const.mul hA.2.1
  have hsL : Continuous fun σ => L * Real.sin (rδ L f σ) :=
    continuous_const.mul (Real.continuous_sin.comp hδc)
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hδd σ)
    ((hfc.sub hsL).intervalIntegrable 0 1)
  rw [show rδ L f 1 = rδ L f 0 by simpa using hδp 0, sub_self,
    intervalIntegral.integral_sub (hfc.intervalIntegrable _ _) (hsL.intervalIntegrable _ _),
    hA.2.2.2.2] at h1
  linarith

/-- The rear data `(L sin δ̃, L cos δ̃)` represent the selected inverse. -/
lemma represents_rearOv (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    Represents 1 (fun σ => L * Real.sin (rδ L f σ)) (fun σ => L * Real.cos (rδ L f σ))
      (rearL L f) (rearF L f) :=
  (represents_rear (p := 1) (κ := κ) one_pos hκ0 hκ1 (continuous_const.mul hA.2.1)
    continuous_const (fun σ => by show L * f (σ + 1) = L * f σ; rw [hA.2.2.1 σ])
    (fun _ => rfl) (fun _ => hA.1)
    (fun σ => mul_nonneg hA.1.le (hA.2.2.2.1 σ).1)
    (fun σ => by rw [mul_comm κ]; exact mul_le_mul_of_nonneg_left (hA.2.2.2.1 σ).2 hA.1.le) (represents_self hA.1)).2

/-- The selected rear in arclength: `δ(s) = δ̃(s / L)` is the arclength steering angle of the
front curvature `K(s) = f(s / L)`, the rear arclength is `x(s) = rearL · S(s / L)`, and the rear
curvature `k(y) = rearF(y / rearL)` satisfies `k(x(s)) = tan δ(s)`. -/
theorem rear_arclength (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    let K := fun s => f (s / L)
    let δ := fun s => rδ L f (s / L)
    let k := fun y => rearF L f (y / rearL L f)
    Continuous K ∧ Function.Periodic K L ∧ (∫ r in (0 : ℝ)..L, K r = π) ∧
    (∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s) ∧ Function.Periodic δ L ∧
    (∀ s, δ s ∈ Set.Icc 0 (Real.arcsin κ)) ∧ (∀ s, 0 < δ s) ∧
    Continuous k ∧ Function.Periodic k (rearL L f) ∧ (∫ r in (0 : ℝ)..rearL L f, k r = π) ∧
    (∫ r in (0 : ℝ)..L, Real.cos (δ r)) = rearL L f ∧ 0 < rearL L f ∧
    ∀ s, k (∫ r in (0 : ℝ)..s, Real.cos (δ r)) = Real.tan (δ s) := by
  intro K δ k
  obtain ⟨hL, hfc, hfp, hfb, hfi⟩ := hA
  obtain ⟨hδp, hδd, hδb⟩ := rδ_spec ⟨hL, hfc, hfp, hfb, hfi⟩ hκ0 hκ1
  have hR := represents_rearOv ⟨hL, hfc, hfp, hfb, hfi⟩ hκ0 hκ1
  have hδc : Continuous (rδ L f) := continuous_iff_continuousAt.2 fun σ => (hδd σ).continuousAt
  have hA2 := arcsin_lt_pi_div_two hκ1
  have hcos : ∀ σ, 0 < Real.cos (rδ L f σ) := fun σ => Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(hδb σ).1, Real.pi_pos], (hδb σ).2.trans_lt hA2⟩
  have hcL : Continuous fun σ => L * Real.cos (rδ L f σ) :=
    continuous_const.mul (Real.continuous_cos.comp hδc)
  have hsL : Continuous fun σ => L * Real.sin (rδ L f σ) :=
    continuous_const.mul (Real.continuous_sin.comp hδc)
  obtain ⟨hRc, hRp, hRi⟩ := hR.f_props one_pos hsL hcL (fun σ => by simp only [hδp σ])
    (fun σ => by simp only [hδp σ]) fun σ => mul_pos hL (hcos σ)
  have hRL : 0 < rearL L f := integral_pos_of_periodic one_pos hcL fun σ => mul_pos hL (hcos σ)
  -- change of variables `s = L σ`
  have hscale : ∀ {h : ℝ → ℝ}, Continuous h → ∀ c, 0 < c →
      ∫ r in (0 : ℝ)..c, h (r / c) = c * ∫ σ in (0 : ℝ)..1, h σ := fun {h} hh c hc => by
    have := intervalIntegral.integral_comp_div (a := 0) (b := c) h hc.ne'
    rw [this, zero_div, div_self hc.ne', smul_eq_mul]
  have hδd' : ∀ s, HasDerivAt δ (K s - Real.sin (δ s)) s := fun s => by
    have := (hδd (s / L)).comp s ((hasDerivAt_id s).div_const L)
    convert this using 1
    simp only [K, δ]; field_simp
  have hδp' : Function.Periodic δ L := fun s => by
    simp only [δ]; rw [add_div, div_self hL.ne', hδp]
  have hKp : Function.Periodic K L := fun s => by
    simp only [K]; rw [add_div, div_self hL.ne', hfp]
  have hKi : ∫ r in (0 : ℝ)..L, K r = π := by
    simp only [K]; rw [hscale hfc L hL, ← hfi, intervalIntegral.integral_const_mul]
  -- rear arclength
  have hx : ∀ s, ∫ r in (0 : ℝ)..s, Real.cos (δ r) =
      rearL L f * normArc 1 (fun σ => L * Real.cos (rδ L f σ)) (s / L) := fun s => by
    unfold normArc
    rw [show (∫ v in (0 : ℝ)..1, L * Real.cos (rδ L f v)) = rearL L f from rfl,
      mul_div_cancel₀ _ hRL.ne', intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_div (a := 0) (b := s)
      (fun σ => Real.cos (rδ L f σ)) hL.ne'
    simp only [δ]
    rw [this, zero_div, smul_eq_mul]
  refine ⟨hfc.comp (continuous_id.div_const L), hKp, hKi, hδd', hδp', fun s => hδb _,
    fun s => ?_, hRc.comp (continuous_id.div_const _), fun y => ?_, ?_, ?_, hRL, fun s => ?_⟩
  · -- positivity of the steering angle
    refine steering_pos hL (hfc.comp (continuous_id.div_const L)) hKp
      (fun s => (hfb _).1) (lt_of_lt_of_eq Real.pi_pos hKi.symm) hδp' hδd' (fun s => (hδb _).1) s
  · simp only [k]; rw [add_div, div_self hRL.ne', hRp]
  · simp only [k]; rw [hscale hRc _ hRL, ← intervalIntegral.integral_const_mul, hRi]
    exact rear_turn ⟨hL, hfc, hfp, hfb, hfi⟩ hκ0 hκ1
  · rw [hx L, div_self hL.ne']
    unfold normArc
    rw [div_self (show (∫ v in (0 : ℝ)..1, L * Real.cos (rδ L f v)) ≠ 0 from hRL.ne'), mul_one]
  · simp only [k]
    rw [hx s, mul_div_cancel_left₀ _ hRL.ne']
    simp only [rearF, normF, invFun_normArc one_pos hcL fun σ => mul_pos hL (hcos σ), δ]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hL.ne']

/-- **Qualitative properties of the selected inverse** on admissible normalized ovals. -/
theorem rear_facts (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    0 < rearL L f ∧ rearL L f ≤ L ∧ π / Real.tan (Real.arcsin κ) ≤ rearL L f ∧
      Continuous (rearF L f) ∧ Function.Periodic (rearF L f) 1 ∧ (∀ y, 0 < rearF L f y) ∧
      ∫ y in (0 : ℝ)..1, rearL L f * rearF L f y = π := by
  obtain ⟨hKc, hKp, hKi, hδd, hδp, hδb, hδpos, hkc, hkp, hki, hxL, hRL, hkx⟩ :=
    rear_arclength hA hκ0 hκ1
  obtain ⟨hL, hfc, hfp, hfb, hfi⟩ := hA
  obtain ⟨hδp1, hδd1, hδb1⟩ := rδ_spec ⟨hL, hfc, hfp, hfb, hfi⟩ hκ0 hκ1
  have hR := represents_rearOv ⟨hL, hfc, hfp, hfb, hfi⟩ hκ0 hκ1
  have hδc : Continuous (rδ L f) := continuous_iff_continuousAt.2 fun σ => (hδd1 σ).continuousAt
  have hA2 := arcsin_lt_pi_div_two hκ1
  have hcos : ∀ σ, 0 < Real.cos (rδ L f σ) := fun σ => Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(hδb1 σ).1, Real.pi_pos], (hδb1 σ).2.trans_lt hA2⟩
  have hcL : Continuous fun σ => L * Real.cos (rδ L f σ) :=
    continuous_const.mul (Real.continuous_cos.comp hδc)
  have hsL : Continuous fun σ => L * Real.sin (rδ L f σ) :=
    continuous_const.mul (Real.continuous_sin.comp hδc)
  obtain ⟨hRc, hRp, hRi⟩ := hR.f_props one_pos hsL hcL (fun σ => by simp only [hδp1 σ])
    (fun σ => by simp only [hδp1 σ]) fun σ => mul_pos hL (hcos σ)
  -- the turning of the rear
  have hturn : ∫ σ in (0 : ℝ)..1, L * Real.sin (rδ L f σ) = π := by
    exact rear_turn ⟨hL, hfc, hfp, hfb, hfi⟩ hκ0 hκ1
  refine ⟨hRL, ?_, ?_, hRc, hRp, fun y => ?_, hRi.trans hturn⟩
  · calc rearL L f ≤ ∫ σ in (0 : ℝ)..1, L := intervalIntegral.integral_mono_on zero_le_one
          (hcL.intervalIntegrable _ _) intervalIntegrable_const fun σ _ =>
            mul_le_of_le_one_right hL.le (Real.cos_le_one _)
      _ = L := by simp
  · have htan := PathData.tan_arcsin_pos (show 0 < κ by
      by_contra h
      push_neg at h
      have hκ : κ = 0 := le_antisymm h hκ0
      have : ∫ σ in (0 : ℝ)..1, L * f σ = 0 := by
        rw [show (fun σ => L * f σ) = fun _ => 0 from funext fun σ => by
          have := hfb σ; rw [hκ] at this; simp [le_antisymm this.2 this.1]]
        simp
      rw [hfi] at this; exact Real.pi_ne_zero this) hκ1
    rw [div_le_iff₀ htan, ← hturn, show rearL L f = ∫ σ in (0 : ℝ)..1, L * Real.cos (rδ L f σ)
      from rfl, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_mono_on zero_le_one (hsL.intervalIntegrable _ _)
      ((hcL.mul continuous_const).intervalIntegrable _ _) fun σ _ => ?_
    have htle : Real.tan (rδ L f σ) ≤ Real.tan (Real.arcsin κ) :=
      Real.strictMonoOn_tan.monotoneOn
        ⟨by linarith [(hδb1 σ).1, Real.pi_pos], (hδb1 σ).2.trans_lt hA2⟩
        ⟨by linarith [Real.arcsin_nonneg.2 hκ0, Real.pi_pos], hA2⟩ (hδb1 σ).2
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (hcos σ)] at htle
    nlinarith
  · -- positivity: `rearF (y) = k (rearL y) = tan δ (s) > 0`
    have hk := hkx
    obtain ⟨m, hm, hmc⟩ := exists_pos_lower_bound_of_periodic hL
      (Real.continuous_cos.comp (continuous_iff_continuousAt.2 fun s => (hδd s).continuousAt))
      (fun s => by show Real.cos (rδ L f ((s + L) / L)) = Real.cos (rδ L f (s / L)); rw [add_div, div_self hL.ne', hδp1]) fun s => Real.cos_pos_of_mem_Ioo
        ⟨by linarith [(hδb s).1, Real.pi_pos], (hδb s).2.trans_lt hA2⟩
    have hxd : ∀ s, HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, Real.cos (rδ L f (r / L)))
        (Real.cos (rδ L f (s / L))) s := fun s => by
      have hc : Continuous fun r => Real.cos (rδ L f (r / L)) :=
        Real.continuous_cos.comp (hδc.comp (continuous_id.div_const L))
      exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
    obtain ⟨G, hG1, -, -⟩ := exists_inverse_of_deriv_ge hm hxd hmc
    have := hk (G (rearL L f * y))
    simp only at this
    rw [hG1, mul_div_cancel_left₀ _ hRL.ne'] at this
    rw [this]
    have hp := hδpos (G (rearL L f * y))
    have hb := hδb (G (rearL L f * y))
    exact Real.tan_pos_of_pos_of_lt_pi_div_two hp (hb.2.trans_lt hA2)

/-- The selected inverse of an admissible oval is admissible, with any curvature bound `κ'`
that its curvature satisfies. -/
theorem adm_rear (hA : AdmOval κ L f) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {κ' : ℝ}
    (hκ' : ∀ y, rearF L f y ≤ κ') : AdmOval κ' (rearL L f) (rearF L f) := by
  obtain ⟨h1, -, -, h4, h5, h6, h7⟩ := rear_facts hA hκ0 hκ1
  exact ⟨h1, h4, h5, fun y => ⟨(h6 y).le, hκ' y⟩, h7⟩

end rear

end Ovals

end
