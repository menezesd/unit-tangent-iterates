module

public import UnitTangentIterates.ShadowRep
public import UnitTangentIterates.ShadowInterp
public import UnitTangentIterates.ModelChain

/-!
# Invariant neighbourhoods (proof of Theorem 6.4, first part)

Given a model chain, let `Λ_m` be the interpolation path from `Q_m` to `A_m` and consider the
iterated rear paths `𝓑^i Λ_m` (`Ovals.piece`).  By induction on `i` we show that, as long as the
total defect is small (`∑ e_n ≤ η`, `Ovals.etaC`), all these paths are defined and valid, with
curvature at most `κ̂ = (1 + κ₀)/2`, with normal velocities bounded by multiples of `e_m`, and
with steering angles controlled by `arctan κ₀ + G ∑ e_l` (`Ovals.piece_inv`).  The paths are
glued through the normalized ovals they represent at times `0` and `1`.

Consequently every backward iterate `𝓑^k A_{n+k}` of the models has curvature at most `κ̂`
and half-perimeter within `κ̂ K₁ η` of `L n` (`Ovals.chain_bounds`).
-/

@[expose] public section

namespace Ovals

open Real Filter Topology

/-! ### Generic facts -/

namespace PathData

variable {P : PathData} {κ m : ℝ}

lemma Valid.mono (hP : P.Valid κ m) {κ' : ℝ} (h : κ ≤ κ') : P.Valid κ' m := by
  refine { hP with a_le := ?_ }
  intro t u
  exact (hP.a_le t u).trans (mul_le_mul_of_nonneg_right h (hP.g_pos t u).le)

lemma Bounded.mono {w s₀ s₁ w' s₀' s₁' : ℝ} (h : P.Bounded w s₀ s₁) (hw : w ≤ w')
    (h₀ : s₀ ≤ s₀') (h₁ : s₁ ≤ s₁') : P.Bounded w' s₀' s₁' :=
  ⟨fun t => (h.1 t).trans hw, fun t u => (h.2.1 t u).trans h₀,
    fun t u => (h.2.2 t u).trans h₁⟩

end PathData

/-- The selected inverse on normalized ovals, as a self-map. -/
noncomputable def rearOv (X : ℝ × (ℝ → ℝ)) : ℝ × (ℝ → ℝ) := (rearL X.1 X.2, rearF X.1 X.2)

namespace PathData

variable {P : PathData} {κ m : ℝ}

/-- At every time, the rear data represent the selected inverse of what the data represent. -/
lemma Valid.represents_rear_at (hP : P.Valid κ m) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (t : ℝ)
    {X : ℝ × (ℝ → ℝ)} (h : Represents P.p (P.a t) (P.g t) X.1 X.2) :
    Represents P.p (P.rear.a t) (P.rear.g t) (rearOv X).1 (rearOv X).2 :=
  (represents_rear hP.p_pos hκ0 hκ1 (hP.a_cont t) (hP.g_cont t) (hP.a_per t) (hP.g_per t)
    (hP.g_pos t) (hP.a_nonneg t) (hP.a_le t) h).2

/-- The rear data at time `t` depend only on the data at time `t`. -/
lemma rear_congr {t t' : ℝ} (ha : P.a t = P.a t') (hg : P.g t = P.g t') :
    P.rear.a t = P.rear.a t' ∧ P.rear.g t = P.rear.g t' := by
  have hδ : P.δ t = P.δ t' := by simp only [PathData.δ, ha, hg]
  refine ⟨funext fun u => ?_, funext fun u => ?_⟩ <;>
    simp only [PathData.rear, hδ, show P.g t u = P.g t' u from congrFun hg u]

end PathData

/-- Curvature bounds on data give bounds on the normalized curvature they represent. -/
lemma Represents.f_le {p L c : ℝ} {a g f : ℝ → ℝ} (h : Represents p a g L f) (hp : 0 < p)
    (hg : Continuous g) (hgp : Function.Periodic g p) (hg0 : ∀ u, 0 < g u)
    (hle : ∀ u, a u ≤ c * g u) (σ : ℝ) : f σ ≤ c := by
  have hL := h.L_pos hp hg hg0
  obtain ⟨-, s, hs, -, ha⟩ := h
  obtain ⟨G, hG, -, -⟩ := Represents.exists_inverse hp hg hgp hg0 hL hs
  have h1 := hle (G σ)
  rw [ha, hG] at h1
  have := hg0 (G σ)
  by_contra hc
  push_neg at hc
  nlinarith

/-- If `g sin δ ≤ c g cos δ` with `g > 0` and `|δ| < π/2`, then `tan δ ≤ c`. -/
lemma tan_le_of_sin_le {g d c : ℝ} (hg : 0 < g) (hcos : 0 < Real.cos d)
    (h : g * Real.sin d ≤ c * (g * Real.cos d)) : Real.tan d ≤ c := by
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos]
  nlinarith

lemma sin_le_of_tan_le {g d c : ℝ} (hg : 0 < g) (hcos : 0 < Real.cos d)
    (h : Real.tan d ≤ c) : g * Real.sin d ≤ c * (g * Real.cos d) := by
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos] at h
  nlinarith

lemma le_of_tan_le_tan {d θ : ℝ} (hd : -(π / 2) < d) (hd2 : d < π / 2) (hθ : -(π / 2) < θ)
    (hθ2 : θ < π / 2) (h : Real.tan d ≤ Real.tan θ) : d ≤ θ :=
  (Real.strictMonoOn_tan.le_iff_le ⟨hd, hd2⟩ ⟨hθ, hθ2⟩).1 h

/-! ### Constants (depending only on `κ₀`) -/

/-- The curvature bound `κ̂ = (1 + κ₀)/2` maintained along all paths. -/
noncomputable def khat (κ₀ : ℝ) : ℝ := (1 + κ₀) / 2

/-- `cos A` with `A = arcsin κ̂`. -/
noncomputable def cAc (κ₀ : ℝ) : ℝ := Real.cos (Real.arcsin (khat κ₀))

/-- The constant of the interpolation estimates. -/
noncomputable def K1c : ℝ := 2 * Cσ + 1

/-- The bound for `∂ₛη` along iterated rears. -/
noncomputable def Mc (κ₀ : ℝ) : ℝ := K1c * (1 + PathData.C₀ (khat κ₀)) * (1 + 1 / cAc κ₀)

/-- The growth rate of the steering angle per unit defect. -/
noncomputable def Gc (κ₀ : ℝ) : ℝ :=
  PathData.C₀ (khat κ₀) * K1c + K1c * (1 + PathData.C₀ (khat κ₀)) + Mc κ₀

/-- The smallness threshold `η*` of Theorem 6.4. -/
noncomputable def etaC (κ₀ : ℝ) : ℝ := (Real.arctan (khat κ₀) - Real.arctan κ₀) / (Gc κ₀ + 1)

section constants

variable {κ₀ : ℝ}

lemma khat_pos (hκ₀ : 0 < κ₀) : 0 < khat κ₀ := by unfold khat; linarith
lemma khat_lt_one (hκ₀1 : κ₀ < 1) : khat κ₀ < 1 := by unfold khat; linarith
lemma lt_khat (hκ₀1 : κ₀ < 1) : κ₀ < khat κ₀ := by unfold khat; linarith

lemma cAc_pos (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1) : 0 < cAc κ₀ := Real.cos_pos_of_mem_Ioo
  ⟨by linarith [Real.arcsin_nonneg.2 (khat_pos hκ₀).le, Real.pi_pos],
    arcsin_lt_pi_div_two (khat_lt_one hκ₀1)⟩

lemma K1c_pos : 0 < K1c := by unfold K1c; linarith [Cσ_nonneg]

lemma C0_pos (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1) : 0 < PathData.C₀ (khat κ₀) :=
  PathData.C₀_pos (khat_pos hκ₀) (khat_lt_one hκ₀1)

lemma Mc_pos (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1) : 0 < Mc κ₀ := by
  have := C0_pos hκ₀ hκ₀1; have := cAc_pos hκ₀ hκ₀1; have := K1c_pos
  unfold Mc; positivity

lemma Gc_pos (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1) : 0 < Gc κ₀ := by
  have := C0_pos hκ₀ hκ₀1; have := Mc_pos hκ₀ hκ₀1; have := K1c_pos
  unfold Gc; positivity

lemma etaC_pos (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1) : 0 < etaC κ₀ := by
  have := Gc_pos hκ₀ hκ₀1
  have : Real.arctan κ₀ < Real.arctan (khat κ₀) := Real.arctan_strictMono (lt_khat hκ₀1)
  unfold etaC; apply div_pos <;> linarith

lemma Gc_mul_etaC_lt (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1) :
    Gc κ₀ * etaC κ₀ < Real.arctan (khat κ₀) - Real.arctan κ₀ := by
  have hG := Gc_pos hκ₀ hκ₀1
  have : Real.arctan κ₀ < Real.arctan (khat κ₀) := Real.arctan_strictMono (lt_khat hκ₀1)
  unfold etaC
  rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
  nlinarith

end constants

/-! ### The iterated rear paths of a model chain -/

/-- The model rear `A_m`, as a normalized oval with arclength origin at `x₀ m`. -/
noncomputable def modelO (L : ℕ → ℝ) (KA : ℕ → ℝ → ℝ) (x₀ : ℕ → ℝ) (m : ℕ) : ℝ × (ℝ → ℝ) :=
  (L m, fun σ => KA m (x₀ m + L m * σ))

/-- The path `𝓑^i Λ_m`, where `Λ_m` interpolates from `Q_m` to `A_m`. -/
noncomputable def piece (L : ℕ → ℝ) (KQ KA : ℕ → ℝ → ℝ) (i m : ℕ) : PathData :=
  PathData.rear^[i] (interpPath (KQ m) (KA m) (L m))

/-- The invariant satisfied by the paths `𝓑^i Λ_m`. -/
structure PieceInv (P : PathData) (κh mm w s₀ s₁ θ Lm : ℝ) (X₁ : ℝ × (ℝ → ℝ)) : Prop where
  valid : P.Valid κh mm
  bounded : P.Bounded w s₀ s₁
  curv : ∀ t u, P.a t u ≤ Real.tan θ * P.g t u
  const1 : ∀ t, 1 ≤ t → P.a t = P.a 1 ∧ P.g t = P.g 1
  const0 : ∀ t, t ≤ 0 → P.a t = P.a 0 ∧ P.g t = P.g 0
  period : P.p = Lm
  rep1 : Represents Lm (P.a 1) (P.g 1) X₁.1 X₁.2

section chain

variable {κ₀ : ℝ} {L : ℕ → ℝ} {KQ KA δ : ℕ → ℝ → ℝ} {x₀ : ℕ → ℝ}
  (hM : ModelChain κ₀ L KQ KA δ x₀) (hκ₀ : 0 < κ₀) (hκ₀1 : κ₀ < 1)

/-- The steering-angle bound for `𝓑^i Λ_m`. -/
noncomputable def theta (κ₀ : ℝ) (L : ℕ → ℝ) (KQ KA : ℕ → ℝ → ℝ) (i m : ℕ) : ℝ :=
  Real.arctan κ₀ + Gc κ₀ * ∑ l ∈ Finset.Ioc (m - i) m, chainDefect L KQ KA l

lemma theta_succ (i m : ℕ) (him : i + 1 ≤ m) :
    theta κ₀ L KQ KA (i + 1) m = theta κ₀ L KQ KA i (m - 1) + Gc κ₀ * chainDefect L KQ KA m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold theta
  rw [show m' + 1 - (i + 1) = m' - i by omega, show m' + 1 - 1 = m' by omega,
    Finset.sum_Ioc_succ_top (by omega)]
  ring

include hM

lemma chainDefect_nonneg (n : ℕ) : 0 ≤ chainDefect L KQ KA n := by
  unfold chainDefect
  exact mul_nonneg (sq_nonneg _) (intervalIntegral.integral_nonneg (hM.L_pos n).le
    fun _ _ => abs_nonneg _)

/-- The interpolation path is valid. -/
lemma interp_valid (m : ℕ) : (interpPath (KQ m) (KA m) (L m)).Valid κ₀ 1 :=
  interpPath_valid (hM.KQ_cont m) (hM.KA_cont m) (hM.KQ_periodic m) (hM.KA_periodic m)
    (hM.KQ_integral m) (hM.KA_integral m) (hM.L_pos m)
    (fun r => ⟨(hM.KQ_pos m r).le, hM.KQ_le m r⟩) (fun r => ⟨(hM.KA_pos m r).le, hM.KA_le m r⟩)

/-- The interpolation path is bounded by `K₁ e_m`. -/
lemma interp_bounded (hκ₀1 : κ₀ < 1) (m : ℕ) :
    (interpPath (KQ m) (KA m) (L m)).Bounded (K1c * chainDefect L KQ KA m)
      (K1c * chainDefect L KQ KA m) (K1c * chainDefect L KQ KA m) := by
  have hB := interpPath_bounded (κs := κ₀) (hM.KQ_cont m) (hM.KA_cont m) (hM.KQ_periodic m)
    (hM.KA_periodic m) (hM.KQ_integral m) (hM.KA_integral m) (hM.L_pos m)
    (fun r => ⟨(hM.KQ_pos m r).le, hM.KQ_le m r⟩) (fun r => ⟨(hM.KA_pos m r).le, hM.KA_le m r⟩)
  have hL := (hM.L_pos m).le
  have hκ0 : 0 ≤ κ₀ := (hM.KQ_pos m 0).le.trans (hM.KQ_le m 0)
  set ε := ∫ u in (0 : ℝ)..L m, |KA m u - KQ m u|
  have hε0 : 0 ≤ ε := intervalIntegral.integral_nonneg hL fun _ _ => abs_nonneg _
  have he : chainDefect L KQ KA m = (1 + L m) ^ 2 * ε := by
    unfold chainDefect
    congr 1
    exact intervalIntegral.integral_congr fun u _ => abs_sub_comm _ _
  have hC := Cσ_nonneg
  have hX : 0 ≤ (1 + L m) ^ 2 * ε := mul_nonneg (sq_nonneg _) hε0
  rw [he]
  refine hB.mono ?_ ?_ ?_
  · have : L m * (3 / 2 * L m) ≤ 3 / 2 * (1 + L m) ^ 2 := by nlinarith
    calc L m * (Cσ * (3 / 2 * L m * ε)) = Cσ * (L m * (3 / 2 * L m)) * ε := by ring
      _ ≤ Cσ * (3 / 2 * (1 + L m) ^ 2) * ε := by gcongr
      _ ≤ K1c * ((1 + L m) ^ 2 * ε) := by unfold K1c; nlinarith [mul_nonneg hC hX]
  · have : 3 / 2 * L m ≤ 3 / 2 * (1 + L m) ^ 2 := by nlinarith
    calc Cσ * (3 / 2 * L m * ε) = Cσ * (3 / 2 * L m) * ε := by ring
      _ ≤ Cσ * (3 / 2 * (1 + L m) ^ 2) * ε := by gcongr
      _ ≤ K1c * ((1 + L m) ^ 2 * ε) := by unfold K1c; nlinarith [mul_nonneg hC hX]
  · have : 1 + 3 / 2 * κ₀ * L m ≤ 3 / 2 * (1 + L m) ^ 2 := by nlinarith
    calc Cσ * ((1 + 3 / 2 * κ₀ * L m) * ε) = Cσ * (1 + 3 / 2 * κ₀ * L m) * ε := by ring
      _ ≤ Cσ * (3 / 2 * (1 + L m) ^ 2) * ε := by gcongr
      _ ≤ K1c * ((1 + L m) ^ 2 * ε) := by unfold K1c; nlinarith [mul_nonneg hC hX]

/-- The model rear `A_m` is represented by the end of the interpolation path. -/
lemma rep_modelO (m : ℕ) :
    Represents (L m) (KA m) (fun _ => 1) (modelO L KA x₀ m).1 (modelO L KA x₀ m).2 :=
  represents_arclength (hM.L_pos m) (x₀ m)

/-- The selected rear of `Q_{m+1}`, in the arclength of `Q_{m+1}`, represents `A_m`. -/
lemma rep_rear_model (hκ₀1 : κ₀ < 1) (m : ℕ) :
    Represents (L (m + 1))
      (fun u => 1 * Real.sin (steerAngle (L (m + 1)) (KQ (m + 1)) (fun _ => 1) u))
      (fun u => 1 * Real.cos (steerAngle (L (m + 1)) (KQ (m + 1)) (fun _ => 1) u))
      (modelO L KA x₀ m).1 (modelO L KA x₀ m).2 := by
  have hκ0 : 0 ≤ κ₀ := (hM.KQ_pos 0 0).le.trans (hM.KQ_le 0 0)
  have hL := hM.L_pos (m + 1)
  have hδc : Continuous (δ m) := continuous_iff_continuousAt.2 fun s =>
    (hM.steer_deriv m s).continuousAt
  obtain ⟨A, hA, hAb⟩ := exists_lt_pi_div_two_of_periodic hL hδc (hM.steer_periodic m)
    fun s => (hM.steer_mem m s).2
  have heq : steerAngle (L (m + 1)) (KQ (m + 1)) (fun _ => 1) = δ m :=
    steerAngle_eq hL hκ0 hκ₀1 (hM.KQ_cont _) continuous_const (hM.KQ_periodic _) (fun _ => rfl)
      (fun _ => one_pos) (fun s => (hM.KQ_pos _ s).le) (fun s => by simpa using hM.KQ_le _ s) hA
      (hM.steer_periodic m) (fun s => by simpa using hM.steer_deriv m s)
      (fun s => ⟨(hM.steer_mem m s).1.le, hAb s⟩)
  rw [heq]
  have hc : Continuous fun u => Real.cos (δ m u) := Real.continuous_cos.comp hδc
  have hcp : Function.Periodic (fun u => Real.cos (δ m u)) (L (m + 1)) := fun u => by
    simp only [hM.steer_periodic m u]
  have hcos : ∀ u, 0 < Real.cos (δ m u) := fun u => Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(hM.steer_mem m u).1, Real.pi_pos], (hM.steer_mem m u).2⟩
  have hLm := hM.L_pos m
  refine ⟨by simpa using hM.rear_length m, fun u => (∫ r in (0 : ℝ)..u, Real.cos (δ m r)) / L m,
    fun u => ?_, fun u => ?_, fun u => ?_⟩
  · have := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).div_const (L m)
    simpa [modelO] using this
  · simp only
    rw [integral_add_period hc hcp, hM.rear_length m, add_div, div_self hLm.ne']
  · simp only [modelO, one_mul]
    rw [mul_div_cancel₀ _ hLm.ne', hM.rear_curv m u, Real.tan_eq_sin_div_cos]
    field_simp [(hcos u).ne']

variable (hs : Summable (chainDefect L KQ KA)) (hη : ∑' n, chainDefect L KQ KA n ≤ etaC κ₀)
include hκ₀ hκ₀1 hs hη

lemma theta_bounds (i m : ℕ) :
    Real.arctan κ₀ ≤ theta κ₀ L KQ KA i m ∧ theta κ₀ L KQ KA i m < Real.arctan (khat κ₀) := by
  have hG := Gc_pos hκ₀ hκ₀1
  have h0 : 0 ≤ ∑ l ∈ Finset.Ioc (m - i) m, chainDefect L KQ KA l :=
    Finset.sum_nonneg fun l _ => chainDefect_nonneg hM l
  have h1 : ∑ l ∈ Finset.Ioc (m - i) m, chainDefect L KQ KA l ≤ etaC κ₀ :=
    (hs.sum_le_tsum _ fun l _ => chainDefect_nonneg hM l).trans hη
  have h2 := Gc_mul_etaC_lt hκ₀ hκ₀1
  unfold theta
  constructor
  · nlinarith
  · nlinarith

/-- **The invariant neighbourhoods (Theorem 6.4, invariance step).** -/
theorem piece_inv (i : ℕ) : ∀ m, i ≤ m →
    PieceInv (piece L KQ KA i m) (khat κ₀) (cAc κ₀ ^ i) (K1c * chainDefect L KQ KA m)
      (K1c * (1 + PathData.C₀ (khat κ₀)) * chainDefect L KQ KA m)
      (Mc κ₀ * chainDefect L KQ KA m) (theta κ₀ L KQ KA i m) (L m)
      (rearOv^[i] (modelO L KA x₀ m)) ∧
    (1 ≤ i → Represents (L m) ((piece L KQ KA i m).a 0) ((piece L KQ KA i m).g 0)
      (rearOv^[i - 1] (modelO L KA x₀ (m - 1))).1 (rearOv^[i - 1] (modelO L KA x₀ (m - 1))).2) := by
  have hkh0 := khat_pos hκ₀
  have hkh1 := khat_lt_one hκ₀1
  have hC0 := C0_pos hκ₀ hκ₀1
  have hcA := cAc_pos hκ₀ hκ₀1
  have hK1 := K1c_pos
  have hA2 := arcsin_lt_pi_div_two hkh1
  induction i with
  | zero =>
    intro m _
    have hpz : piece L KQ KA 0 m = interpPath (KQ m) (KA m) (L m) := rfl
    have hV := interp_valid hM m
    have he := chainDefect_nonneg hM m
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩, fun h => absurd h (by omega)⟩
    · rw [hpz, pow_zero]; exact hV.mono (lt_khat hκ₀1).le
    · rw [hpz]
      refine (interp_bounded hM hκ₀1 m).mono le_rfl ?_ ?_
      · have := mul_nonneg (mul_nonneg hK1.le hC0.le) he
        nlinarith
      · unfold Mc
        have h1 : 1 ≤ 1 + 1 / cAc κ₀ := by have := one_div_pos.2 hcA; linarith
        have h2 : K1c ≤ K1c * (1 + PathData.C₀ (khat κ₀)) * (1 + 1 / cAc κ₀) := by
          have h3 : K1c ≤ K1c * (1 + PathData.C₀ (khat κ₀)) := by nlinarith
          calc K1c ≤ K1c * (1 + PathData.C₀ (khat κ₀)) := h3
            _ ≤ _ := le_mul_of_one_le_right (by positivity) h1
        nlinarith
    · intro t u
      have : theta κ₀ L KQ KA 0 m = Real.arctan κ₀ := by simp [theta]
      rw [this, Real.tan_arctan, hpz]
      exact hV.a_le t u
    · intro t ht
      exact ⟨funext fun s => by rw [hpz, interpPath_a_of_one_le ht, interpPath_a_of_one_le le_rfl],
        rfl⟩
    · intro t ht
      exact ⟨funext fun s => by rw [hpz, interpPath_a_of_nonpos ht, interpPath_a_of_nonpos le_rfl],
        rfl⟩
    · have ha1 : (piece L KQ KA 0 m).a 1 = KA m := funext fun s => by
        rw [hpz, interpPath_a_of_one_le le_rfl]
      rw [ha1, Function.iterate_zero, id]
      exact rep_modelO hM m
  | succ i ih =>
    intro m him
    obtain ⟨hP, hP0⟩ := ih m (by omega)
    obtain ⟨hQ, -⟩ := ih (m - 1) (by omega)
    set P := piece L KQ KA i m with hPdef
    set Q := piece L KQ KA i (m - 1) with hQdef
    have hsucc : piece L KQ KA (i + 1) m = P.rear := Function.iterate_succ_apply' _ _ _
    rw [hsucc]
    have hV := hP.valid
    have hδs := hV.δ_spec hkh0.le hkh1
    have hRB := hV.rear_bounds hkh0 hkh1 hP.bounded
    have he := chainDefect_nonneg hM m
    -- the rear data at time `0` represent `𝓑^i A_{m-1}`
    have hrep0 : Represents (L m) (P.rear.a 0) (P.rear.g 0)
        (rearOv^[i] (modelO L KA x₀ (m - 1))).1 (rearOv^[i] (modelO L KA x₀ (m - 1))).2 := by
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have ha0 : P.a 0 = KQ (m' + 1) := funext fun s => by
          rw [hPdef]; exact interpPath_a_of_nonpos le_rfl s
        have hg0 : P.g 0 = fun _ => 1 := rfl
        have hp : P.p = L (m' + 1) := rfl
        have e1 : P.rear.a 0 = fun u => 1 * Real.sin
            (steerAngle (L (m' + 1)) (KQ (m' + 1)) (fun _ => 1) u) := by
          funext u; simp only [PathData.rear, PathData.δ, ha0, hg0, hp]
        have e2 : P.rear.g 0 = fun u => 1 * Real.cos
            (steerAngle (L (m' + 1)) (KQ (m' + 1)) (fun _ => 1) u) := by
          funext u; simp only [PathData.rear, PathData.δ, ha0, hg0, hp]
        rw [e1, e2]
        simpa using rep_rear_model hM hκ₀1 m'
      · have h1 := hP0 hi
        rw [← hP.period] at h1
        have h2 := hV.represents_rear_at hkh0.le hkh1 0 h1
        rw [hP.period] at h2
        have e : rearOv (rearOv^[i - 1] (modelO L KA x₀ (m - 1))) =
            rearOv^[i] (modelO L KA x₀ (m - 1)) := by
          rw [show rearOv^[i] = rearOv^[(i - 1) + 1] by rw [Nat.sub_add_cancel hi],
            Function.iterate_succ_apply']
        rwa [e] at h2
    -- the curvature at time `0`, from the end of the previous piece at level `m - 1`
    have hQV := hQ.valid
    have hcurv0 : ∀ u, P.rear.a 0 u ≤ Real.tan (theta κ₀ L KQ KA i (m - 1)) * P.rear.g 0 u := by
      have hQrep := hQ.rep1
      have hQp := hQ.period
      refine Represents.curv_le_transfer hQrep hrep0 (hQp ▸ hQV.p_pos) (hQV.g_cont 1)
        (hQp ▸ hQV.g_per 1) (hQV.g_pos 1) (fun u => ?_) (hQ.curv 1)
      exact mul_pos (hV.g_pos 0 u) (hV.cos_δ_pos hkh0.le hkh1 0 u)
    obtain ⟨hθ0, hθ1⟩ := theta_bounds hM hκ₀ hκ₀1 hs hη i (m - 1)
    obtain ⟨hθ0', hθ1'⟩ := theta_bounds hM hκ₀ hκ₀1 hs hη (i + 1) m
    have hat0 := Real.arctan_nonneg.2 hκ₀.le
    have hatk := Real.arctan_lt_pi_div_two (khat κ₀)
    have hδ0 : ∀ u, P.δ 0 u ≤ theta κ₀ L KQ KA i (m - 1) := fun u => by
      have h1 := tan_le_of_sin_le (hV.g_pos 0 u) (hV.cos_δ_pos hkh0.le hkh1 0 u) (hcurv0 u)
      exact le_of_tan_le_tan (by linarith [((hδs 0).2.2 u).1, Real.pi_pos])
        (((hδs 0).2.2 u).2.trans_lt hA2) (by linarith [Real.pi_pos]) (by linarith) h1
    -- growth of the steering angle along the path
    have hc : ∀ t u, |P.rear.η t u| + |P.η t u| + |deriv (P.η t) u / P.g t u| ≤
        Gc κ₀ * chainDefect L KQ KA m := fun t u => by
      have h1 := hRB.2.1 t u
      have h2 := hP.bounded.2.1 t u
      have h3 := hP.bounded.2.2 t u
      unfold Gc
      nlinarith
    have hθs := theta_succ (κ₀ := κ₀) (L := L) (KQ := KQ) (KA := KA) i m him
    have hδ : ∀ t u, P.δ t u ≤ theta κ₀ L KQ KA (i + 1) m := by
      have hG := Gc_pos hκ₀ hκ₀1
      have hGe : 0 ≤ Gc κ₀ * chainDefect L KQ KA m := by positivity
      have h01 : ∀ t, 0 ≤ t → t ≤ 1 → ∀ u, P.δ t u ≤ theta κ₀ L KQ KA (i + 1) m :=
        fun t ht0 ht1 u => by
          have := hV.rear_δ_growth hkh0.le hkh1 hc ht0 hδ0 u
          rw [hθs]; nlinarith
      intro t u
      rcases le_or_gt t 0 with ht | ht
      · have : P.δ t = P.δ 0 := by
          simp only [PathData.δ, (hP.const0 t ht).1, (hP.const0 t ht).2]
        rw [this]; exact h01 0 le_rfl zero_le_one u
      rcases le_or_gt t 1 with ht' | ht'
      · exact h01 t ht.le ht' u
      · have : P.δ t = P.δ 1 := by
          simp only [PathData.δ, (hP.const1 t ht'.le).1, (hP.const1 t ht'.le).2]
        rw [this]; exact h01 1 zero_le_one le_rfl u
    have htanδ : ∀ t u, Real.tan (P.δ t u) ≤ Real.tan (theta κ₀ L KQ KA (i + 1) m) := fun t u =>
      Real.strictMonoOn_tan.monotoneOn
        ⟨by linarith [((hδs t).2.2 u).1, Real.pi_pos], ((hδs t).2.2 u).2.trans_lt hA2⟩
        ⟨by linarith [Real.pi_pos], by linarith⟩ (hδ t u)
    have htanθ : Real.tan (theta κ₀ L KQ KA (i + 1) m) ≤ khat κ₀ := by
      rw [← Real.tan_arctan (khat κ₀)]
      exact Real.strictMonoOn_tan.monotoneOn ⟨by linarith [Real.pi_pos], by linarith⟩
        ⟨by linarith [Real.pi_pos], hatk⟩ hθ1'.le
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hP.period, ?_⟩, fun _ => by simpa using hrep0⟩
    · rw [pow_succ]
      exact hV.rear hkh0.le hkh1 fun t u => (htanδ t u).trans htanθ
    · refine hRB.mono le_rfl (by nlinarith) ?_
      unfold Mc
      have h1 : PathData.C₀ (khat κ₀) * K1c * chainDefect L KQ KA m ≤
          K1c * (1 + PathData.C₀ (khat κ₀)) * chainDefect L KQ KA m := by nlinarith
      have h2 : K1c * (1 + PathData.C₀ (khat κ₀)) * chainDefect L KQ KA m /
          Real.cos (Real.arcsin (khat κ₀)) = K1c * (1 + PathData.C₀ (khat κ₀)) *
          (1 / cAc κ₀) * chainDefect L KQ KA m := by unfold cAc; ring
      rw [h2]
      nlinarith
    · intro t u
      exact sin_le_of_tan_le (hV.g_pos t u) (hV.cos_δ_pos hkh0.le hkh1 t u) (htanδ t u)
    · intro t ht
      exact PathData.rear_congr (hP.const1 t ht).1 (hP.const1 t ht).2
    · intro t ht
      exact PathData.rear_congr (hP.const0 t ht).1 (hP.const0 t ht).2
    · have h1 := hP.rep1
      rw [← hP.period] at h1
      have h2 := hV.represents_rear_at hkh0.le hkh1 1 h1
      rw [hP.period, ← Function.iterate_succ_apply' rearOv i] at h2
      exact h2

/-- **Uniform bounds on the backward iterates of the models.**  Every backward iterate
`𝓑^k A_{n+k}` has normalized curvature at most `κ̂` and half-perimeter within
`κ̂ K₁ ∑_{n < l ≤ n+k} e_l` of `L n`. -/
theorem chain_bounds (n k : ℕ) :
    (∀ σ, (rearOv^[k] (modelO L KA x₀ (n + k))).2 σ ≤ khat κ₀) ∧
      |(rearOv^[k] (modelO L KA x₀ (n + k))).1 - L n| ≤
        khat κ₀ * K1c * ∑ l ∈ Finset.Ioc n (n + k), chainDefect L KQ KA l := by
  have hkh0 := khat_pos hκ₀
  have hatk := Real.arctan_lt_pi_div_two (khat κ₀)
  refine ⟨fun σ => ?_, ?_⟩
  · obtain ⟨hP, -⟩ := piece_inv hM hκ₀ hκ₀1 hs hη k (n + k) (by omega)
    obtain ⟨hθ0, hθ1⟩ := theta_bounds hM hκ₀ hκ₀1 hs hη k (n + k)
    have hat0 := Real.arctan_nonneg.2 hκ₀.le
    have htanθ : Real.tan (theta κ₀ L KQ KA k (n + k)) ≤ khat κ₀ := by
      rw [← Real.tan_arctan (khat κ₀)]
      exact Real.strictMonoOn_tan.monotoneOn ⟨by linarith [Real.pi_pos], by linarith⟩
        ⟨by linarith [Real.pi_pos], hatk⟩ hθ1.le
    have hV := hP.valid
    have hp := hP.period
    exact (hP.rep1.f_le (hp ▸ hV.p_pos) (hV.g_cont 1) (hp ▸ hV.g_per 1) (hV.g_pos 1)
      (hP.curv 1) σ).trans htanθ
  · induction k with
    | zero => simp [modelO]
    | succ k ih =>
      obtain ⟨hP, hP0⟩ := piece_inv hM hκ₀ hκ₀1 hs hη (k + 1) (n + (k + 1)) (by omega)
      have h0 := hP0 (by omega)
      simp only [show n + (k + 1) - 1 = n + k by omega, show k + 1 - 1 = k by omega] at h0
      have h1 := hP.rep1
      have hV := hP.valid
      have hch := hV.perimeter_change hkh0.le hP.bounded.1 zero_le_one
      rw [hP.period, h0.1, h1.1] at hch
      rw [show n + (k + 1) = n + k + 1 by omega, Finset.sum_Ioc_succ_top (by omega : n ≤ n + k)]
      rw [show n + (k + 1) = n + k + 1 by omega] at hch
      have := K1c_pos
      calc |(rearOv^[k + 1] (modelO L KA x₀ (n + k + 1))).1 - L n|
          ≤ |(rearOv^[k + 1] (modelO L KA x₀ (n + k + 1))).1 -
              (rearOv^[k] (modelO L KA x₀ (n + k))).1| +
            |(rearOv^[k] (modelO L KA x₀ (n + k))).1 - L n| := abs_sub_le _ _ _
        _ ≤ khat κ₀ * (K1c * chainDefect L KQ KA (n + k + 1)) * (1 - 0) +
            khat κ₀ * K1c * ∑ l ∈ Finset.Ioc n (n + k), chainDefect L KQ KA l := add_le_add hch ih
        _ = _ := by ring

end chain

end Ovals

end
