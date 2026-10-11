import Mathlib

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Set Filter Topology

namespace LogBMPilotProbe

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

structure IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop where
  isCompact : IsCompact K
  convex : Convex ℝ K
  interior_nonempty : (interior K).Nonempty

def OriginSymmetric {n : ℕ} (K : Set (Space n)) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def supportFn {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  sSup ((fun x => ⟪x, u⟫_ℝ) '' K)

def wulffBody {n : ℕ} (f : Space n → ℝ) : Set (Space n) :=
  {x | ∀ u : Space n, ‖u‖ = 1 → ⟪x, u⟫_ℝ ≤ f u}

def logCombination {n : ℕ} (K L : Set (Space n)) (t : ℝ) : Set (Space n) :=
  wulffBody (fun u => supportFn K u ^ (1 - t) * supportFn L u ^ t)

/-- 件 B0: 高斯衰减极限 (x^k·e^{-a x²} → 0 at +∞). -/
theorem gauss_tendsto_zero {k : ℕ} {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-(a * x ^ 2))) atTop (𝓝 0) := by
  have hx : Tendsto (fun x : ℝ => (1 / 2) * x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) (tendsto_id (x := atTop))
  have hv : Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hx).congr ?_
    intro x
    exact congr_arg Real.exp (by ring)
  have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha k).tendsto_zero_of_tendsto hv
  refine h.congr' (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.rpow_natCast, neg_mul]

/-- 件 B1: 半线二阶矩 (∫₀^∞ x²e^{-a x²} = (1/2a)∫₀^∞ e^{-a x²}, 分部积分真证). -/
theorem gauss_moment_half₂ {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(a * x ^ 2))
      = (1 / (2 * a)) * ∫ x in Ioi (0:ℝ), Real.exp (-(a * x ^ 2)) := by
  have hE : ∀ x : ℝ, HasDerivAt (fun y => Real.exp (-(a * y ^ 2)))
      ((-a * 2 * x) * Real.exp (-(a * x ^ 2))) x := by
    intro x
    have hg : HasDerivAt (fun y => -(a * y ^ 2)) (-(a * 2 * x)) x := by
      have hbase : HasDerivAt (fun y => (-a) * y ^ 2) ((-a) * (2 * x)) x := by
        simpa using HasDerivAt.const_mul (-a) (hasDerivAt_pow 2 x)
      rw [show (fun y => -(a * y ^ 2)) = (fun y => (-a) * y ^ 2) from by funext y; ring]
      exact HasDerivAt.congr_deriv hbase (by ring)
    have hcomp : HasDerivAt (Real.exp ∘ (fun y => -(a * y ^ 2)))
        (Real.exp (-(a * x ^ 2)) * (-(a * 2 * x))) x :=
      HasDerivAt.comp x (Real.hasDerivAt_exp (-(a * x ^ 2))) hg
    refine HasDerivAt.congr_of_eventuallyEq hcomp
      (Filter.Eventually.of_forall fun y => rfl) |>.congr_deriv (by ring)
  have hvde : ∀ x ∈ Ioi (0:ℝ),
      HasDerivAt (fun y => -(1 / (2 * a)) * Real.exp (-(a * y ^ 2)))
        (x * Real.exp (-(a * x ^ 2))) x := by
    intro x _
    refine HasDerivAt.congr_deriv ((hE x).const_mul (-(1 / (2 * a)))) ?_
    field_simp
  have hzero : Tendsto (fun y : ℝ => y * (-(1 / (2 * a)) * Real.exp (-(a * y ^ 2))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt
        (fun y : ℝ => y * (-(1 / (2 * a)) * Real.exp (-(a * y ^ 2)))) 0 := by fun_prop
    have ht := hc.tendsto
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, zero_mul, Real.exp_zero,
      neg_zero] at ht
    exact tendsto_nhdsWithin_of_tendsto_nhds ht
  have hinfty : Tendsto (fun y : ℝ => y * (-(1 / (2 * a)) * Real.exp (-(a * y ^ 2))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (-(1 / (2 * a))) * (y * Real.exp (-(a * y ^ 2))))
        atTop (𝓝 0) := by
      simpa using (gauss_tendsto_zero (k := 1) ha).const_mul (-(1 / (2 * a)))
    exact h1.congr' (Filter.Eventually.of_forall fun y => by ring)
  have huv' : IntegrableOn ((fun y : ℝ => y) *
      (fun y : ℝ => y * Real.exp (-(a * y ^ 2)))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := a) (s := 2) ha (by norm_num)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    rw [Real.rpow_two, neg_mul]
    ring
  have hIoi1 : IntegrableOn ((fun _ : ℝ => (1:ℝ)) *
      (fun y : ℝ => -(1 / (2 * a)) * Real.exp (-(a * y ^ 2)))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := a) (s := 0) ha (by norm_num)
    have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(a * x ^ 2))) (Ioi 0) := by
      refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
      simp only
      rw [Real.rpow_zero, one_mul, neg_mul]
    have h3 : IntegrableOn (fun x : ℝ => -(1 / (2 * a)) * Real.exp (-(a * x ^ 2)))
        (Ioi 0) := h2.const_mul (-(1 / (2 * a)))
    refine h3.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp [Pi.mul_apply]
  have hibp' : ∫ x in Ioi (0:ℝ), x * (x * Real.exp (-(a * x ^ 2)))
      = (0:ℝ) - 0 - ∫ x in Ioi (0:ℝ), 1 * (-(1 / (2 * a)) * Real.exp (-(a * x ^ 2))) :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (u := fun y : ℝ => y) (u' := fun _ : ℝ => 1)
      (v := fun y : ℝ => -(1 / (2 * a)) * Real.exp (-(a * y ^ 2)))
      (v' := fun y : ℝ => y * Real.exp (-(a * y ^ 2)))
      (fun x _ => hasDerivAt_id x) hvde huv' hIoi1 hzero hinfty
  calc ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(a * x ^ 2))
      = ∫ x in Ioi (0:ℝ), x * (x * Real.exp (-(a * x ^ 2))) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
        ring
    _ = (0:ℝ) - 0 - ∫ x in Ioi (0:ℝ), 1 * (-(1 / (2 * a)) * Real.exp (-(a * x ^ 2))) := hibp'
    _ = (1 / (2 * a)) * ∫ x in Ioi (0:ℝ), Real.exp (-(a * x ^ 2)) := by
        rw [sub_zero, zero_sub, integral_const_mul, integral_const_mul]
        ring




/-- 件 B2a: 幂×高斯密度半线可积 (参数化·形态收敛件). -/
theorem gauss_pow_integrable {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(a * x ^ 2))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := a) (s := ((k:ℕ):ℝ)) ha
    (by linarith [Nat.cast_nonneg (α := ℝ) (n := k)])
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, neg_mul]

/-- 件 B2: 半线四阶矩 (∫₀^∞ x⁴e^{-a x²} = (3/2a)∫₀^∞ x²e^{-a x²}, 分部积分真证). -/
theorem gauss_moment_half₄ {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0:ℝ), x ^ 4 * Real.exp (-(a * x ^ 2))
      = (3 / (2 * a)) * ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(a * x ^ 2)) := by
  have hE : ∀ x : ℝ, HasDerivAt (fun y => Real.exp (-(a * y ^ 2)))
      ((-a * 2 * x) * Real.exp (-(a * x ^ 2))) x := by
    intro x
    have hg : HasDerivAt (fun y => -(a * y ^ 2)) (-(a * 2 * x)) x := by
      have hbase : HasDerivAt (fun y => (-a) * y ^ 2) ((-a) * (2 * x)) x := by
        simpa using HasDerivAt.const_mul (-a) (hasDerivAt_pow 2 x)
      rw [show (fun y => -(a * y ^ 2)) = (fun y => (-a) * y ^ 2) from by funext y; ring]
      exact HasDerivAt.congr_deriv hbase (by ring)
    have hcomp : HasDerivAt (Real.exp ∘ (fun y => -(a * y ^ 2)))
        (Real.exp (-(a * x ^ 2)) * (-(a * 2 * x))) x :=
      HasDerivAt.comp x (Real.hasDerivAt_exp (-(a * x ^ 2))) hg
    refine HasDerivAt.congr_of_eventuallyEq hcomp
      (Filter.Eventually.of_forall fun y => rfl) |>.congr_deriv (by ring)
  have hvde : ∀ x ∈ Ioi (0:ℝ),
      HasDerivAt (fun y => -(1 / (2 * a)) * Real.exp (-(a * y ^ 2)))
        (x * Real.exp (-(a * x ^ 2))) x := by
    intro x _
    refine HasDerivAt.congr_deriv ((hE x).const_mul (-(1 / (2 * a)))) ?_
    field_simp
  have hzero : Tendsto (fun y : ℝ => y ^ 3 * (-(1 / (2 * a)) * Real.exp (-(a * y ^ 2))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt
        (fun y : ℝ => y ^ 3 * (-(1 / (2 * a)) * Real.exp (-(a * y ^ 2)))) 0 := by fun_prop
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    simpa using hc.tendsto
  have hinfty : Tendsto (fun y : ℝ => y ^ 3 * (-(1 / (2 * a)) * Real.exp (-(a * y ^ 2))))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (-(1 / (2 * a))) * (y ^ 3 * Real.exp (-(a * y ^ 2))))
        atTop (𝓝 0) := by
      simpa using (gauss_tendsto_zero (k := 3) ha).const_mul (-(1 / (2 * a)))
    exact h1.congr' (Filter.Eventually.of_forall fun y => by ring)
  have huv' : IntegrableOn ((fun y : ℝ => y ^ 3) *
      (fun y : ℝ => y * Real.exp (-(a * y ^ 2)))) (Ioi 0) := by
    refine (gauss_pow_integrable ha 4).congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    ring
  have hu'v : IntegrableOn ((fun y : ℝ => 3 * y ^ 2) *
      (fun y : ℝ => -(1 / (2 * a)) * Real.exp (-(a * y ^ 2)))) (Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ =>
        -(3 / (2 * a)) * (x ^ 2 * Real.exp (-(a * x ^ 2)))) (Ioi 0) :=
      (gauss_pow_integrable ha 2).const_mul (-(3 / (2 * a)))
    refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show -(3 / (2 * a)) * (x ^ 2 * Real.exp (-(a * x ^ 2)))
        = (3 * x ^ 2) * (-(1 / (2 * a)) * Real.exp (-(a * x ^ 2)))
    ring
  have hibp' : ∫ x in Ioi (0:ℝ), x ^ 3 * (x * Real.exp (-(a * x ^ 2)))
      = (0:ℝ) - 0 - ∫ x in Ioi (0:ℝ), (3 * x ^ 2) *
        (-(1 / (2 * a)) * Real.exp (-(a * x ^ 2))) :=
    integral_Ioi_mul_deriv_eq_deriv_mul
      (u := fun y : ℝ => y ^ 3) (u' := fun y : ℝ => 3 * y ^ 2)
      (v := fun y : ℝ => -(1 / (2 * a)) * Real.exp (-(a * y ^ 2)))
      (v' := fun y : ℝ => y * Real.exp (-(a * y ^ 2)))
      (fun x _ => (hasDerivAt_pow 3 x)) hvde huv' hu'v hzero hinfty
  calc ∫ x in Ioi (0:ℝ), x ^ 4 * Real.exp (-(a * x ^ 2))
      = ∫ x in Ioi (0:ℝ), x ^ 3 * (x * Real.exp (-(a * x ^ 2))) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
        ring
    _ = (0:ℝ) - 0 - ∫ x in Ioi (0:ℝ), (3 * x ^ 2) *
          (-(1 / (2 * a)) * Real.exp (-(a * x ^ 2))) := hibp'
    _ = (3 / (2 * a)) * ∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(a * x ^ 2)) := by
        have hcongr : (∫ x in Ioi (0:ℝ), (3 * x ^ 2)
            * (-(1 / (2 * a)) * Real.exp (-(a * x ^ 2))))
            = (3 * -(1 / (2 * a))) * ∫ x in Ioi (0:ℝ),
              x ^ 2 * Real.exp (-(a * x ^ 2)) := by
          refine setIntegral_congr_fun
            (f := fun x : ℝ => (3 * x ^ 2) * (-(1 / (2 * a)) * Real.exp (-(a * x ^ 2))))
            (g := fun x : ℝ => (3 * -(1 / (2 * a))) *
              (x ^ 2 * Real.exp (-(a * x ^ 2))))
            measurableSet_Ioi (fun x _ => ?_) |>.trans ?_
          · ring
          · rw [integral_const_mul]
        rw [sub_zero, zero_sub, hcongr]
        ring


/-- 一维板语言 (半线实例化·单方向 q=2 核). -/
def boardDensity (a : ℝ) (x : ℝ) : ℝ := Real.exp (-(a * x ^ 2))

def boardMean (a : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∫ x in Ioi (0:ℝ), F x * boardDensity a x) / ∫ x in Ioi (0:ℝ), boardDensity a x

def boardVar (a : ℝ) (F : ℝ → ℝ) : ℝ :=
  boardMean a (fun x => (F x - boardMean a F) ^ 2)

def boardPsi (h : ℝ) (x : ℝ) : ℝ := (x / h) ^ 2

/-- 件 B3: 均值线性 (标量倍). -/
theorem boardMean_const_mul (a : ℝ) (c : ℝ) (F : ℝ → ℝ) :
    boardMean a (fun x => c * F x) = c * boardMean a F := by
  unfold boardMean
  have hcongr : (∫ x in Ioi (0:ℝ), c * F x * boardDensity a x)
      = c * (∫ x in Ioi (0:ℝ), F x * boardDensity a x) := by
    refine setIntegral_congr_fun
      (f := fun x : ℝ => c * F x * boardDensity a x)
      (g := fun x : ℝ => c * (F x * boardDensity a x))
      measurableSet_Ioi (fun x _ => mul_assoc c (F x) (boardDensity a x)) |>.trans ?_
    rw [integral_const_mul]
  rw [hcongr]
  field_simp

/-- 件 B4: 方差齐次 (Var(c·F) = c²·Var(F)). -/
theorem boardVar_const_mul (a : ℝ) (c : ℝ) (F : ℝ → ℝ) :
    boardVar a (fun x => c * F x) = c ^ 2 * boardVar a F := by
  have hinner : boardMean a (fun x => c * F x) = c * boardMean a F :=
    boardMean_const_mul a c F
  unfold boardVar
  rw [hinner]
  have hG : boardMean a (fun x => (c * F x - c * boardMean a F) ^ 2)
      = (∫ x in Ioi (0:ℝ), (c * F x - c * boardMean a F) ^ 2 * boardDensity a x)
        / (∫ x in Ioi (0:ℝ), boardDensity a x) := rfl
  have hH : boardMean a (fun x => (F x - boardMean a F) ^ 2)
      = (∫ x in Ioi (0:ℝ), (F x - boardMean a F) ^ 2 * boardDensity a x)
        / (∫ x in Ioi (0:ℝ), boardDensity a x) := rfl
  rw [hG, hH]
  have hnum : (∫ x in Ioi (0:ℝ), (c * F x - c * boardMean a F) ^ 2 * boardDensity a x)
      = c ^ 2 * (∫ x in Ioi (0:ℝ), (F x - boardMean a F) ^ 2 * boardDensity a x) := by
    refine setIntegral_congr_fun
      (f := fun x : ℝ => (c * F x - c * boardMean a F) ^ 2 * boardDensity a x)
      (g := fun x : ℝ => c ^ 2 * ((F x - boardMean a F) ^ 2 * boardDensity a x))
      measurableSet_Ioi (fun x _ => ?_) |>.trans ?_
    · simp only
      rw [← mul_sub, mul_pow]
      ring
    · rw [integral_const_mul]
  rw [hnum]
  field_simp



/-- ★件 B5: 一维板方差特例主定理 (路线 B 主目标).
  var_a(b·ψ) ≤ b²·mean_a(ψ), a = ε/2 + 1/h², ψ = (x/h)² —— SoftVarianceStatement
  (正文 Prop 2.1, 式 2.2) 的单方向 q=2 实例: Var_μ(∑bᵢψᵢ) ≤ ∑bᵢ²E_μψᵢ 的一和项. -/
theorem slabVariance_half {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) (b : ℝ) :
    boardVar (ε / 2 + 1 / h ^ 2) (fun x => b * boardPsi h x)
      ≤ b ^ 2 * boardMean (ε / 2 + 1 / h ^ 2) (boardPsi h) := by
  set a := ε / 2 + 1 / h ^ 2 with hadef
  have hapos : 0 < a := add_pos (by linarith) (div_pos one_pos (pow_pos hh 2))
  have hM2 := gauss_moment_half₂ hapos
  have hM4 := gauss_moment_half₄ hapos
  have hZne' : (∫ x in Ioi (0:ℝ), boardDensity a x) ≠ 0 := by
    have h2 : (∫ x in Ioi (0:ℝ), boardDensity a x)
        = ∫ x in Ioi (0:ℝ), Real.exp (-a * x ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      show boardDensity a x = Real.exp (-a * x ^ 2)
      rw [show boardDensity a x = Real.exp (-(a * x ^ 2)) from rfl, neg_mul]
    rw [h2, integral_gaussian_Ioi]
    exact ne_of_gt (div_pos (Real.sqrt_pos.mpr (div_pos Real.pi_pos hapos)) two_pos)
  have hZne : (∫ x in Ioi (0:ℝ), Real.exp (-(a * x ^ 2))) ≠ 0 := by
    have h2 : (∫ x in Ioi (0:ℝ), Real.exp (-(a * x ^ 2)))
        = ∫ x in Ioi (0:ℝ), Real.exp (-a * x ^ 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      rw [neg_mul]
    rw [h2, integral_gaussian_Ioi]
    exact ne_of_gt (div_pos (Real.sqrt_pos.mpr (div_pos Real.pi_pos hapos)) two_pos)
  have hI2 := gauss_pow_integrable hapos 2
  have hI4 := gauss_pow_integrable hapos 4
  have hI0 : IntegrableOn (fun x : ℝ => boardDensity a x) (Ioi 0) := by
    have hbase := gauss_pow_integrable hapos 0
    refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show x ^ 0 * Real.exp (-(a * x ^ 2)) = boardDensity a x
    simp only [pow_zero, one_mul]
    rfl
  have hm : boardMean a (boardPsi h) = 1 / (2 * a * h ^ 2) := by
    unfold boardMean boardPsi boardDensity
    have hcongr : (∫ x in Ioi (0:ℝ), (x / h) ^ 2 * Real.exp (-(a * x ^ 2)))
        = (1 / h ^ 2) * (∫ x in Ioi (0:ℝ), x ^ 2 * Real.exp (-(a * x ^ 2))) := by
      refine setIntegral_congr_fun
        (f := fun x : ℝ => (x / h) ^ 2 * Real.exp (-(a * x ^ 2)))
        (g := fun x : ℝ => (1 / h ^ 2) * (x ^ 2 * Real.exp (-(a * x ^ 2))))
        measurableSet_Ioi (fun x _ => ?_) |>.trans ?_
      · ring
      · rw [integral_const_mul]
    rw [hcongr, hM2]
    field_simp [hZne]
  have hm2 : boardMean a (fun x => boardPsi h x ^ 2)
      = 3 / (4 * a ^ 2 * h ^ 4) := by
    unfold boardMean boardPsi boardDensity
    have hcongr : (∫ x in Ioi (0:ℝ), ((x / h) ^ 2) ^ 2 * Real.exp (-(a * x ^ 2)))
        = (1 / h ^ 4) * (∫ x in Ioi (0:ℝ), x ^ 4 * Real.exp (-(a * x ^ 2))) := by
      refine setIntegral_congr_fun
        (f := fun x : ℝ => ((x / h) ^ 2) ^ 2 * Real.exp (-(a * x ^ 2)))
        (g := fun x : ℝ => (1 / h ^ 4) * (x ^ 4 * Real.exp (-(a * x ^ 2))))
        measurableSet_Ioi (fun x _ => ?_) |>.trans ?_
      · ring
      · rw [integral_const_mul]
    rw [hcongr, hM4, hM2]
    field_simp [hZne']
    norm_num
  -- hvar: Var_a(ψ) = 1/(2a²h⁴) —— hint = ∫((ψ-c)²)ρ 数值化后除以 Z
  have hvar : boardVar a (boardPsi h) = 1 / (2 * a ^ 2 * h ^ 4) := by
    have hI2' : IntegrableOn (fun x : ℝ => boardPsi h x ^ 2 * boardDensity a x) (Ioi 0) := by
      have hbase : IntegrableOn (fun x : ℝ =>
          (1 / h ^ 4) * (x ^ 4 * Real.exp (-(a * x ^ 2)))) (Ioi 0) :=
        (gauss_pow_integrable hapos 4).const_mul (1 / h ^ 4)
      refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
      show (1 / h ^ 4) * (x ^ 4 * Real.exp (-(a * x ^ 2)))
          = ((x / h) ^ 2) ^ 2 * Real.exp (-(a * x ^ 2))
      field_simp
    have hI1' : IntegrableOn (fun x : ℝ => boardPsi h x * boardDensity a x) (Ioi 0) := by
      have hbase : IntegrableOn (fun x : ℝ =>
          (1 / h ^ 2) * (x ^ 2 * Real.exp (-(a * x ^ 2)))) (Ioi 0) :=
        (gauss_pow_integrable hapos 2).const_mul (1 / h ^ 2)
      refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
      show (1 / h ^ 2) * (x ^ 2 * Real.exp (-(a * x ^ 2)))
          = (x / h) ^ 2 * Real.exp (-(a * x ^ 2))
      field_simp
    have hpt : ∀ x : ℝ, ((x / h) ^ 2 - 1 / (2 * a * h ^ 2)) ^ 2 * boardDensity a x
        = boardPsi h x ^ 2 * boardDensity a x
          + ((1 / (2 * a * h ^ 2)) ^ 2 * boardDensity a x
          - (1 / (a * h ^ 2)) * (boardPsi h x * boardDensity a x)) := fun x => by
      unfold boardPsi boardDensity
      rw [div_pow, div_pow]
      field_simp
      ring
    have hi1 : (∫ x in Ioi (0:ℝ), boardPsi h x * boardDensity a x)
        = (1 / (2 * a * h ^ 2)) * (∫ x in Ioi (0:ℝ), boardDensity a x) := by
      rw [← hm]
      unfold boardMean
      field_simp [hZne']
    have hi2 : (∫ x in Ioi (0:ℝ), boardPsi h x ^ 2 * boardDensity a x)
        = (3 / (4 * a ^ 2 * h ^ 4)) * (∫ x in Ioi (0:ℝ), boardDensity a x) := by
      rw [← hm2]
      unfold boardMean
      field_simp [hZne']
    have hBint : IntegrableOn (fun x : ℝ => (1 / (a * h ^ 2)) *
        (boardPsi h x * boardDensity a x)) (Ioi 0) := hI1'.const_mul (1 / (a * h ^ 2))
    have hC : IntegrableOn (fun x : ℝ => (1 / (2 * a * h ^ 2)) ^ 2 *
        boardDensity a x) (Ioi 0) := hI0.const_mul ((1 / (2 * a * h ^ 2)) ^ 2)
    have hCB : IntegrableOn (fun x : ℝ => (1 / (2 * a * h ^ 2)) ^ 2 *
        boardDensity a x
        - (1 / (a * h ^ 2)) * (boardPsi h x * boardDensity a x)) (Ioi 0) :=
      hC.sub hBint
    have hint : (∫ x in Ioi (0:ℝ), ((x / h) ^ 2 - 1 / (2 * a * h ^ 2)) ^ 2
        * boardDensity a x)
        = (1 / (2 * a ^ 2 * h ^ 4)) * (∫ x in Ioi (0:ℝ), boardDensity a x) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x) |>.trans ?_
      rw [integral_add hI2' hCB, integral_sub hC hBint,
        integral_const_mul, integral_const_mul, hi2, hi1]
      field_simp [hapos.ne', hh.ne']
      ring
    unfold boardVar
    rw [hm]
    unfold boardMean boardPsi
    rw [hint]
    field_simp [hZne']
  -- 数值判定: var = 1/(2a²h⁴) ≤ mean = 1/(2ah²) ⟸ ah² ≥ 1 (a = ε/2+1/h²)
  rw [boardVar_const_mul a b (boardPsi h), hvar, hm]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg b)
  have h2ne : h ^ 2 ≠ 0 := pow_ne_zero 2 hh.ne'
  have hge : (1:ℝ) / h ^ 2 ≤ a := by linarith
  have hmul : (1:ℝ) / h ^ 2 * h ^ 2 ≤ a * h ^ 2 :=
    mul_le_mul_of_nonneg_right hge (pow_nonneg (le_of_lt hh) 2)
  have hmul2 : (1:ℝ) / h ^ 2 * h ^ 2 = 1 := by
    field_simp [h2ne]
  have hah1 : (1:ℝ) ≤ a * h ^ 2 := by linarith
  have hP : (0:ℝ) < 2 * a * h ^ 2 :=
    mul_pos (mul_pos two_pos hapos) (pow_pos hh 2)
  have hQ : (0:ℝ) < 2 * a ^ 2 * h ^ 4 :=
    mul_pos (mul_pos two_pos (pow_pos hapos 2)) (pow_pos hh 4)
  refine (one_div_le_one_div hQ hP).mpr ?_
  nlinarith [hah1]

/-! ## B3 段: 全线化 + ℝ² 单方向特例 —— SoftVarianceStatement (主件 L20144) 的
n=2·κ=单方向·q=2 最小退化打样. 路线: ①偶性桥接全线化(F1-F4) ②Fubini 因子分解+垂直因子约掉(F5-F7)
③主不等式组装(F8). -/

/-- F1: 偶函数全线积分 = 2×半线积分. -/
theorem integral_even_eq_two_mul_Ioi {f : ℝ → ℝ}
    (hf : Integrable f volume) (heven : ∀ x, f (-x) = f x) :
    ∫ x : ℝ, f x = 2 * ∫ x in Ioi (0:ℝ), f x := by
  have hemb := (Homeomorph.neg ℝ).measurableEmbedding
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hzero : ∫ x in {(0:ℝ)}, f x = 0 := by
    apply setIntegral_measure_zero
    exact Real.volume_singleton (a := (0:ℝ))
  have hIci : ∫ x in Ici (0:ℝ), f x = ∫ x in Ioi (0:ℝ), f x := by
    have hu : Ici (0:ℝ) = Ioi (0:ℝ) ∪ {(0:ℝ)} := by
      ext x
      simp only [mem_Ici, mem_union, mem_Ioi, mem_singleton_iff, le_iff_lt_or_eq, eq_comm]
    have hd : Disjoint (Ioi (0:ℝ)) {(0:ℝ)} := by
      rw [Set.disjoint_left]
      intro a ha ht
      simp only [mem_Ioi, mem_singleton_iff] at ha ht
      linarith
    rw [hu, setIntegral_union hd (measurableSet_singleton 0)
        (hf.integrableOn.mono_set (s := Ioi (0:ℝ)) (t := (univ : Set ℝ))
          (by exact subset_univ _))
        (integrableOn_singleton (f := f) (x := (0:ℝ))
          (hx := by rw [Real.volume_singleton]; simp)), hzero]
    ring
  rw [← integral_add_compl measurableSet_Ici hf, Set.compl_Ici, hIci]
  have hpre : Iio (0:ℝ) = (fun x : ℝ => -x) ⁻¹' Ioi (0:ℝ) := by
    ext x
    simp [mem_Iio, mem_Ioi]
  rw [hpre]
  have hc : ∫ x in (fun x : ℝ => -x) ⁻¹' Ioi (0:ℝ), f x
      = ∫ x in (fun x : ℝ => -x) ⁻¹' Ioi (0:ℝ), f (-x) :=
    setIntegral_congr_fun (measurableSet_Ioi.preimage hemb.measurable)
      (fun x _ => (heven x).symm)
  rw [hc, MeasurePreserving.setIntegral_preimage_emb hmp hemb f (Ioi (0:ℝ))]
  ring

/-- F1b: 偶函数半线可积 → 全线可积. -/
theorem integrable_even_of_Ioi {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioi (0:ℝ))) (heven : ∀ x, f (-x) = f x) :
    Integrable f volume := by
  have hemb := (Homeomorph.neg ℝ).measurableEmbedding
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0:ℝ), integrableOn_union]
  refine ⟨?_, (integrableOn_Ici_iff_integrableOn_Ioi (f := f) (b := (0:ℝ))
    (by simp)).mpr hi⟩
  have hpre : Iio (0:ℝ) = (fun x : ℝ => -x) ⁻¹' Ioi (0:ℝ) := by
    ext x
    simp [mem_Iio, mem_Ioi]
  rw [hpre]
  have h2 := (hmp.integrableOn_comp_preimage hemb).mpr hi
  exact h2.congr_fun (fun x _ => heven x) (measurableSet_Ioi.preimage hemb.measurable)

/-- F1c: 偶函数×板密度全线积分 = 2×半线. -/
theorem integral_even_density_eq_two_mul {a : ℝ} {g : ℝ → ℝ}
    (hi : IntegrableOn (fun x => g x * boardDensity a x) (Ioi (0:ℝ)))
    (heven : ∀ x, g (-x) = g x) :
    ∫ x : ℝ, g x * boardDensity a x
      = 2 * ∫ x in Ioi (0:ℝ), g x * boardDensity a x := by
  have he : ∀ x, g (-x) * Real.exp (-(a * (-x) ^ 2)) = g x * Real.exp (-(a * x ^ 2)) := by
    intro x
    rw [heven, neg_sq]
  have hic : IntegrableOn (fun x => g x * Real.exp (-(a * x ^ 2))) (Ioi (0:ℝ)) := by
    refine hi.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show g x * boardDensity a x = g x * Real.exp (-(a * x ^ 2))
    rfl
  exact integral_even_eq_two_mul_Ioi (integrable_even_of_Ioi hic he) he

/-! ### F2: 全线板语言 -/

/-- 全线高斯积分 (neg_mul 口径桥 + Mathlib 现成件). -/
theorem integral_boardDensity_full {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, boardDensity a x = Real.sqrt (Real.pi / a) := by
  have h2 : (∫ x : ℝ, boardDensity a x) = ∫ x : ℝ, Real.exp (-a * x ^ 2) := by
    simp only [boardDensity, neg_mul]
  rw [h2, integral_gaussian a]

/-- 全线密度积分非零. -/
theorem boardDensity_full_ne_zero {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, boardDensity a x) ≠ 0 := by
  rw [integral_boardDensity_full ha]
  exact ne_of_gt (Real.sqrt_pos.mpr (div_pos Real.pi_pos ha))

/-- 全线均值 (板语言·全线版). -/
def boardMeanF (a : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, F x * boardDensity a x) / ∫ x : ℝ, boardDensity a x

/-- 全线方差 (板语言·全线版). -/
def boardVarF (a : ℝ) (F : ℝ → ℝ) : ℝ :=
  boardMeanF a (fun x => (F x - boardMeanF a F) ^ 2)

/-- 可积性三件套: (g - c)²ρ 可积 ← g²ρ 可积 × gρ 可积. -/
theorem integrable_sq_sub_const {a : ℝ} (ha : 0 < a) (c : ℝ) (g : ℝ → ℝ)
    (hg2 : IntegrableOn (fun x => g x ^ 2 * boardDensity a x) (Ioi (0:ℝ)))
    (hg1 : IntegrableOn (fun x => g x * boardDensity a x) (Ioi (0:ℝ))) :
    IntegrableOn (fun x => (g x - c) ^ 2 * boardDensity a x) (Ioi (0:ℝ)) := by
  have hC : IntegrableOn (fun x : ℝ => boardDensity a x) (Ioi (0:ℝ)) := by
    refine (gauss_pow_integrable ha 0).congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp [boardDensity]
  have hcomb : IntegrableOn (fun x => g x ^ 2 * boardDensity a x
      - (2 * c * (g x * boardDensity a x) - c ^ 2 * boardDensity a x)) (Ioi (0:ℝ)) :=
    hg2.sub ((hg1.const_mul (2 * c)).sub (hC.const_mul (c ^ 2)))
  refine hcomb.congr_fun (fun x _ => ?_) measurableSet_Ioi
  ring

/-- 分母 2 倍件 (g=1 特化). -/
theorem integral_boardDensity_eq_two_mul {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, boardDensity a x) = 2 * ∫ x in Ioi (0:ℝ), boardDensity a x := by
  have hic : IntegrableOn (fun x : ℝ => (1:ℝ) * boardDensity a x) (Ioi (0:ℝ)) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq ha (s := 0) (by norm_num)).congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    simp [boardDensity]
  simpa only [one_mul] using integral_even_density_eq_two_mul hic (fun x => rfl)

/-- F3a: 全线均值 = 半线均值 (偶函数桥). -/
theorem boardMeanF_eq {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hi : IntegrableOn (fun x => g x * boardDensity a x) (Ioi (0:ℝ)))
    (heven : ∀ x, g (-x) = g x) :
    boardMeanF a g = boardMean a g := by
  unfold boardMeanF boardMean
  have h2 : (∫ x : ℝ, boardDensity a x) ≠ 0 := boardDensity_full_ne_zero ha
  rw [integral_even_density_eq_two_mul hi heven, integral_boardDensity_eq_two_mul ha]
  field_simp [h2]

/-- F3b: 全线方差 = 半线方差 (偶函数桥). -/
theorem boardVarF_eq {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ}
    (hg2 : IntegrableOn (fun x => g x ^ 2 * boardDensity a x) (Ioi (0:ℝ)))
    (hgi : IntegrableOn (fun x => g x * boardDensity a x) (Ioi (0:ℝ)))
    (heven : ∀ x, g (-x) = g x) :
    boardVarF a g = boardVar a g := by
  unfold boardVarF boardVar
  rw [boardMeanF_eq ha hgi heven]
  exact boardMeanF_eq ha
    (integrable_sq_sub_const ha (boardMean a g) g hg2 hgi)
    (fun x => by rw [heven])

/-! ### F4: 全线主定理 (B2 主定理的全线版·薄组装) -/

theorem slabVariance_full {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) (b : ℝ) :
    boardVarF (ε / 2 + 1 / h ^ 2) (fun x => b * boardPsi h x)
      ≤ b ^ 2 * boardMeanF (ε / 2 + 1 / h ^ 2) (boardPsi h) := by
  set a := ε / 2 + 1 / h ^ 2 with hadef
  have hapos : 0 < a := add_pos (by linarith) (div_pos one_pos (pow_pos hh 2))
  have hψeven : ∀ x : ℝ, boardPsi h (-x) = boardPsi h x := fun x => by
    show (-x / h) ^ 2 = (x / h) ^ 2
    rw [div_pow, div_pow, neg_sq]
  have hev1 : ∀ x : ℝ, b * boardPsi h (-x) = b * boardPsi h x := fun x => by
    rw [hψeven]
  have hb1 : IntegrableOn (fun x : ℝ => b / h ^ 2 * (x ^ 2 * Real.exp (-(a * x ^ 2))))
      (Ioi (0:ℝ)) := (gauss_pow_integrable hapos 2).const_mul (b / h ^ 2)
  have hgi : IntegrableOn (fun x => b * boardPsi h x * boardDensity a x) (Ioi (0:ℝ)) := by
    refine hb1.congr_fun (fun x _ => ?_) measurableSet_Ioi
    unfold boardPsi boardDensity
    field_simp
  have hb2 : IntegrableOn (fun x : ℝ => b ^ 2 / h ^ 4 * (x ^ 4 * Real.exp (-(a * x ^ 2))))
      (Ioi (0:ℝ)) := (gauss_pow_integrable hapos 4).const_mul (b ^ 2 / h ^ 4)
  have hg2 : IntegrableOn (fun x => (b * boardPsi h x) ^ 2 * boardDensity a x) (Ioi (0:ℝ)) := by
    refine hb2.congr_fun (fun x _ => ?_) measurableSet_Ioi
    unfold boardPsi boardDensity
    field_simp
  have hp1 : IntegrableOn (fun x : ℝ => 1 / h ^ 2 * (x ^ 2 * Real.exp (-(a * x ^ 2))))
      (Ioi (0:ℝ)) := (gauss_pow_integrable hapos 2).const_mul (1 / h ^ 2)
  have hgiψ : IntegrableOn (fun x => boardPsi h x * boardDensity a x) (Ioi (0:ℝ)) := by
    refine hp1.congr_fun (fun x _ => ?_) measurableSet_Ioi
    unfold boardPsi boardDensity
    field_simp
  rw [boardVarF_eq hapos hg2 hgi hev1, boardMeanF_eq hapos hgiψ hψeven]
  exact slabVariance_half hε hh b

/-! ### F5-F7: ℝ² 单方向特例 (Fubini 因子分解·垂直因子约掉) -/

/-- F5: ℝ² 单方向板密度 (坐标版·板方向=第一坐标轴·q=2).
    ρ₂(x,y) = exp(-(ε/2+1/h²)x²)·exp(-(ε/2)y²) —— 主件密度 exp(-ε|x|²/2-(x/h)²) 的因子重排. -/
def slabDensity2 (ε h : ℝ) (p : ℝ × ℝ) : ℝ :=
  boardDensity (ε / 2 + 1 / h ^ 2) p.1 * boardDensity (ε / 2) p.2

/-- ℝ² 全空间均值. -/
def mean2 (ε h : ℝ) (F : ℝ × ℝ → ℝ) : ℝ :=
  (∫ p : ℝ × ℝ, F p * slabDensity2 ε h p ∂Measure.prod volume volume)
    / ∫ p : ℝ × ℝ, slabDensity2 ε h p ∂Measure.prod volume volume

/-- ℝ² 全空间方差. -/
def var2 (ε h : ℝ) (F : ℝ × ℝ → ℝ) : ℝ :=
  mean2 ε h (fun p => (F p - mean2 ε h F) ^ 2)

/-- F6: 因子分解 (垂直方向高斯因子分离·Fubini 一步). -/
theorem integral_prod_slab {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) {g : ℝ → ℝ}
    (hi : IntegrableOn (fun x => g x * boardDensity (ε / 2 + 1 / h ^ 2) x) (Ioi (0:ℝ)))
    (heven : ∀ x, g (-x) = g x) :
    ∫ p : ℝ × ℝ, g p.1 * slabDensity2 ε h p ∂Measure.prod volume volume
      = (∫ x : ℝ, g x * boardDensity (ε / 2 + 1 / h ^ 2) x) * Real.sqrt (Real.pi / (ε / 2)) := by
  have hfun :
      (fun p : ℝ × ℝ => g p.1 * slabDensity2 ε h p)
        = (fun p : ℝ × ℝ =>
            (g p.1 * boardDensity (ε / 2 + 1 / h ^ 2) p.1) * boardDensity (ε / 2) p.2) := by
    funext p
    show g p.1 * (boardDensity (ε / 2 + 1 / h ^ 2) p.1 * boardDensity (ε / 2) p.2) = _
    rw [mul_assoc]
  have hapos : 0 < ε / 2 + 1 / h ^ 2 :=
    add_pos (by linarith) (div_pos one_pos (pow_pos hh 2))
  rw [hfun,
    integral_prod_mul (L := ℝ)
      (f := fun x => g x * boardDensity (ε / 2 + 1 / h ^ 2) x)
      (g := fun y => boardDensity (ε / 2) y),
    integral_boardDensity_full (a := ε / 2) (by linarith)]

/-- 分母专用: ℝ² 板密度全线积分. -/
theorem integral_slabDensity2 {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) :
    (∫ p : ℝ × ℝ, slabDensity2 ε h p ∂Measure.prod volume volume)
      = (∫ x : ℝ, boardDensity (ε / 2 + 1 / h ^ 2) x) * Real.sqrt (Real.pi / (ε / 2)) := by
  have hapos : 0 < ε / 2 + 1 / h ^ 2 :=
    add_pos (by linarith) (div_pos one_pos (pow_pos hh 2))
  have hic1 : IntegrableOn
      (fun x : ℝ => (1:ℝ) * boardDensity (ε / 2 + 1 / h ^ 2) x) (Ioi (0:ℝ)) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq hapos (s := 0) (by norm_num)).congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    show x ^ 0 * Real.exp (-(ε / 2 + 1 / h ^ 2) * x ^ 2)
      = (1:ℝ) * boardDensity (ε / 2 + 1 / h ^ 2) x
    simp [boardDensity]
    ring
  have hfun :
      (fun p : ℝ × ℝ => slabDensity2 ε h p)
        = (fun p : ℝ × ℝ =>
            ((fun _ : ℝ => (1:ℝ)) p.1) * slabDensity2 ε h p) := by
    funext p
    show boardDensity (ε / 2 + 1 / h ^ 2) p.1 * boardDensity (ε / 2) p.2
      = 1 * (boardDensity (ε / 2 + 1 / h ^ 2) p.1 * boardDensity (ε / 2) p.2)
    rw [one_mul]
  rw [hfun,
    integral_prod_slab hε hh hic1 (fun x => rfl)]
  simp only [one_mul]

/-- F7a: mean2 约化到一维全线均值 (垂直因子完全约掉). -/
theorem mean2_eq {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) {g : ℝ → ℝ}
    (hi : IntegrableOn (fun x => g x * boardDensity (ε / 2 + 1 / h ^ 2) x) (Ioi (0:ℝ)))
    (heven : ∀ x, g (-x) = g x) :
    mean2 ε h (fun p => g p.1) = boardMeanF (ε / 2 + 1 / h ^ 2) g := by
  have hapos : 0 < ε / 2 + 1 / h ^ 2 :=
    add_pos (by linarith) (div_pos one_pos (pow_pos hh 2))
  unfold mean2 boardMeanF
  rw [integral_prod_slab hε hh hi heven, integral_slabDensity2 hε hh]
  have hC : Real.sqrt (Real.pi / (ε / 2)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (div_pos Real.pi_pos (by linarith)))
  field_simp [hC]

/-- F7b: var2 约化到一维全线方差. -/
theorem var2_eq {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) {g : ℝ → ℝ}
    (hg2 : IntegrableOn (fun x => g x ^ 2 * boardDensity (ε / 2 + 1 / h ^ 2) x) (Ioi (0:ℝ)))
    (hgi : IntegrableOn (fun x => g x * boardDensity (ε / 2 + 1 / h ^ 2) x) (Ioi (0:ℝ)))
    (heven : ∀ x, g (-x) = g x) :
    var2 ε h (fun p => g p.1) = boardVarF (ε / 2 + 1 / h ^ 2) g := by
  have hapos : 0 < ε / 2 + 1 / h ^ 2 :=
    add_pos (by linarith) (div_pos one_pos (pow_pos hh 2))
  unfold var2 boardVarF
  rw [mean2_eq hε hh hgi heven]
  exact mean2_eq hε hh
    (integrable_sq_sub_const hapos (boardMeanF (ε / 2 + 1 / h ^ 2) g) g hg2 hgi)
    (fun x => by rw [heven])

/-! ### F8: softVariance 打样主定理 (n=2·κ=单方向·q=2 特例)
对接主件 SoftVarianceStatement (BrunnMinkowski.lean L20144) 的最小退化:
κ = 单方向·q = 2·板方向取第一坐标轴 (坐标版)·b 为任意权重.
语言级映射 (假设版·202 先例): 主件 MvPolynomial 特征 → 直接函数形态·
SlabPartition.variance/mean → var2/mean2. -/

theorem softVariance_pilot {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) (b : ℝ) :
    var2 ε h (fun p => b * boardPsi h p.1)
      ≤ b ^ 2 * mean2 ε h (fun p => boardPsi h p.1) := by
  have hapos : 0 < ε / 2 + 1 / h ^ 2 :=
    add_pos (by linarith) (div_pos one_pos (pow_pos hh 2))
  have hψeven : ∀ x : ℝ, boardPsi h (-x) = boardPsi h x := fun x => by
    show (-x / h) ^ 2 = (x / h) ^ 2
    rw [div_pow, div_pow, neg_sq]
  have hev1 : ∀ x : ℝ, b * boardPsi h (-x) = b * boardPsi h x := fun x => by
    rw [hψeven]
  have hp1 : IntegrableOn
      (fun x : ℝ => 1 / h ^ 2 * (x ^ 2 * Real.exp (-((ε / 2 + 1 / h ^ 2) * x ^ 2))))
      (Ioi (0:ℝ)) := (gauss_pow_integrable hapos 2).const_mul (1 / h ^ 2)
  have hgi : IntegrableOn
      (fun x => boardPsi h x * boardDensity (ε / 2 + 1 / h ^ 2) x) (Ioi (0:ℝ)) := by
    refine hp1.congr_fun (fun x _ => ?_) measurableSet_Ioi
    unfold boardPsi boardDensity
    field_simp
  have hp2 : IntegrableOn
      (fun x : ℝ => b ^ 2 / h ^ 4 * (x ^ 4 * Real.exp (-((ε / 2 + 1 / h ^ 2) * x ^ 2))))
      (Ioi (0:ℝ)) := (gauss_pow_integrable hapos 4).const_mul (b ^ 2 / h ^ 4)
  have hg2 : IntegrableOn
      (fun x => (b * boardPsi h x) ^ 2 * boardDensity (ε / 2 + 1 / h ^ 2) x)
      (Ioi (0:ℝ)) := by
    refine hp2.congr_fun (fun x _ => ?_) measurableSet_Ioi
    unfold boardPsi boardDensity
    field_simp
  have hbase : IntegrableOn
      (fun x : ℝ => b * (boardPsi h x * boardDensity (ε / 2 + 1 / h ^ 2) x)) (Ioi (0:ℝ)) :=
    hgi.const_mul b
  have hgi1 : IntegrableOn
      (fun x => b * boardPsi h x * boardDensity (ε / 2 + 1 / h ^ 2) x) (Ioi (0:ℝ)) := by
    refine hbase.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show b * (boardPsi h x * boardDensity (ε / 2 + 1 / h ^ 2) x)
      = b * boardPsi h x * boardDensity (ε / 2 + 1 / h ^ 2) x
    rw [mul_assoc]
  have hvi : IntegrableOn
      (fun x => (b * boardPsi h x - boardMeanF (ε / 2 + 1 / h ^ 2) (fun x => b * boardPsi h x)) ^ 2
        * boardDensity (ε / 2 + 1 / h ^ 2) x) (Ioi (0:ℝ)) :=
    integrable_sq_sub_const hapos
      (boardMeanF (ε / 2 + 1 / h ^ 2) (fun x => b * boardPsi h x))
      (fun x => b * boardPsi h x) hg2 hgi1
  have hmain := slabVariance_full hε hh b
  rw [var2_eq hε hh hg2 hgi1 hev1]
  refine hmain.trans ?_
  rw [mean2_eq hε hh hgi hψeven]
