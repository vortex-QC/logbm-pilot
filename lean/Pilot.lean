/-
# 对数 Brunn-Minkowski 打样板 · 路线 A 骨架复现件 (2026-10-10)
对应: papers/OpenAI数学仓库_091对数BM_立项_v0.1.md §五 (主人钉 A 路线·开)
复现对象 (独立·零 import): openai_math/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean (24490 行)

复现件 (路线 A): 件 1 支撑可达 / 件 2 原点内点 / 件 3 正支撑 /
  件 5-7 最近点·投影特征·分离单位向量 (对偶重建主链) /
  件 8 wulff_reconstructs (锚-1 重建定理) / 件 9 端点件无条件版 (假设解除) /
  件 10-16 n=1 情形件: 一维对数 BM 等式 main_dimension_one 独立复现
  (方向基础·单位向量二点刻划·偶 wulff 区间形态·乘积测度盒子路线·体积件·主等式).
路线注记: n=1 件走 PiLp.volume_preserving_ofLp + Measure.pi_pi (乘积测度盒子),
  与主件 oneEquiv ≃ₗᵢ ℝ 测度等距路线不同源.
边界: 路线 B (softVariance 特例件) 候下轮.
-/
import Mathlib

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Set Filter Topology

namespace LogBMPilot

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

/-! ### 件 1: 支撑可达 -/

theorem support_attained {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K) (u : Space n) :
    ∃ x ∈ K, IsMaxOn (fun y : Space n => ⟪y, u⟫_ℝ) K x ∧ ⟪x, u⟫_ℝ = supportFn K u := by
  have hKne : K.Nonempty := hK.interior_nonempty.mono interior_subset
  have hf : ContinuousOn (fun x : Space n => ⟪x, u⟫_ℝ) K :=
    (isBoundedBilinearMap_inner.continuous.comp
      (continuous_id.prodMk continuous_const)).comp_continuousOn continuousOn_id
  obtain ⟨x, hx, hmax⟩ := hK.isCompact.exists_isMaxOn hKne hf
  exact ⟨x, hx, hmax, Eq.symm ((hmax.isLUB hx).csSup_eq (Set.image_nonempty.mpr hKne))⟩

/-! ### 件 2: 原点在内点 -/

theorem interior_symmetric {n : ℕ} {K : Set (Space n)} (hs : OriginSymmetric K)
    {x : Space n} (hx : x ∈ interior K) : -x ∈ interior K := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  refine mem_interior.mpr ⟨Metric.ball (-x) ε, fun w hw => (hs w).mpr ?_,
    Metric.isOpen_ball, Metric.mem_ball_self hεpos⟩
  have hw' : ‖w + x‖ < ε := by
    have hd := Metric.mem_ball.mp hw
    rw [dist_eq_norm, sub_neg_eq_add] at hd
    exact hd
  refine interior_subset (hε ?_)
  rw [Metric.mem_ball, dist_eq_norm]
  have heq : -w - x = -(w + x) := by rw [sub_eq_add_neg, neg_add]
  rw [heq, norm_neg]
  exact hw'

theorem zero_mem_interior {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (hs : OriginSymmetric K) : (0 : Space n) ∈ interior K := by
  obtain ⟨y, hy⟩ := hK.interior_nonempty
  rw [← midpoint_self_neg (R := ℝ) y]
  exact (hK.convex.interior).midpoint_mem hy (interior_symmetric hs hy)

/-! ### 件 3: 正支撑 -/

theorem positive_support {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (hs : OriginSymmetric K) {u : Space n} (hu : u ≠ 0) : 0 < supportFn K u := by
  have h0 : (0 : Space n) ∈ interior K := zero_mem_interior hK hs
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp isOpen_interior 0 h0
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  obtain ⟨x₀, hx₀, hx₀max, hx₀eq⟩ := support_attained hK u
  have hmaxle : ∀ y ∈ K, ⟪y, u⟫_ℝ ≤ ⟪x₀, u⟫_ℝ := by
    rw [isMaxOn_iff] at hx₀max
    exact hx₀max
  have hw : (ε / 2 / ‖u‖) • u ∈ K := by
    refine interior_subset (hε ?_)
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / 2 / ‖u‖)]
    have h2 : (ε / 2 / ‖u‖) * ‖u‖ = ε / 2 := by field_simp
    rw [h2]
    linarith
  have hin : ⟪(ε / 2 / ‖u‖) • u, u⟫_ℝ ≤ supportFn K u := by
    rw [← hx₀eq]
    exact hmaxle _ hw
  have hval : ⟪(ε / 2 / ‖u‖) • u, u⟫_ℝ = ε / 2 * ‖u‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
    field_simp
  have hv2 : 0 < ⟪(ε / 2 / ‖u‖) • u, u⟫_ℝ := by
    rw [hval]
    exact mul_pos (by positivity) (norm_pos_iff.mpr hu)
  exact lt_of_lt_of_le hv2 hin

/-! ### 件 5: 最近点 -/

theorem nearest_point {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    {x : Space n} (hx : x ∉ K) :
    ∃ p ∈ K, ∀ y ∈ K, ‖x - p‖ ≤ ‖x - y‖ := by
  have hKne : K.Nonempty := hK.interior_nonempty.mono interior_subset
  have hf : ContinuousOn (fun y : Space n => ‖x - y‖) K :=
    (continuous_const.sub continuous_id).norm.comp_continuousOn continuousOn_id
  obtain ⟨p, hpK, hpmin⟩ := hK.isCompact.exists_isMinOn hKne hf
  exact ⟨p, hpK, isMinOn_iff.mp hpmin⟩

/-! ### 件 6: 投影特征 (norm² 路线) -/

theorem projection_property {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    {x p : Space n} (hpK : p ∈ K)
    (hpmin : ∀ y ∈ K, ‖x - p‖ ≤ ‖x - y‖) (y : Space n) (hy : y ∈ K) :
    ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  by_cases hyc : y = p
  · subst y
    simp
  · by_contra hneg0
    push_neg at hneg0
    set c := ⟪y - p, x - p⟫_ℝ with hc
    have hc2 : ⟪x - p, y - p⟫_ℝ = c := by
      rw [real_inner_comm (y - p) (x - p)]
    have hDpos : 0 < ‖y - p‖ * ‖y - p‖ :=
      mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyc)) (norm_pos_iff.mpr (sub_ne_zero.mpr hyc))
    set t := min 1 (c / (‖y - p‖ * ‖y - p‖)) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_min (by norm_num) (by positivity), min_le_left _ _⟩
    have hyt : AffineMap.lineMap p y t ∈ K := hK.convex.lineMap_mem hpK hy ht1
    have hform : x - AffineMap.lineMap p y t = (x - p) - t • (y - p) := by
      rw [AffineMap.lineMap_apply_module]
      module
    have hmin2 : ‖x - p‖ ^ 2 ≤ ‖x - AffineMap.lineMap p y t‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hpmin _ hyt) 2
    have hexp : ‖x - AffineMap.lineMap p y t‖ ^ 2
        = ‖x - p‖ ^ 2 - 2 * t * c + t * t * (‖y - p‖ * ‖y - p‖) := by
      rw [hform, norm_sub_sq_real, real_inner_smul_right, hc2,
        pow_two ‖t • (y - p)‖]
      have hnsq : ‖t • (y - p)‖ * ‖t • (y - p)‖
          = t * t * (‖y - p‖ * ‖y - p‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ t)]
        ring
      rw [hnsq]
      ring
    rw [hexp] at hmin2
    have hlin : 2 * t * c ≤ t * t * (‖y - p‖ * ‖y - p‖) := by linarith
    have h6 : 2 * c ≤ t * (‖y - p‖ * ‖y - p‖) := by nlinarith [hlin, ht0]
    have h7 : t * (‖y - p‖ * ‖y - p‖) ≤ c :=
      (le_div_iff₀ hDpos).mp (min_le_right _ _)
    linarith

/-! ### 件 7: 分离单位向量 -/

theorem support_le_of_forall {n : ℕ} {K : Set (Space n)} (hKne : K.Nonempty)
    {p u : Space n} (h : ∀ y ∈ K, ⟪y, u⟫_ℝ ≤ ⟪p, u⟫_ℝ) : supportFn K u ≤ ⟪p, u⟫_ℝ := by
  unfold supportFn
  exact csSup_le (Set.image_nonempty.mpr hKne) fun z hz => by
    obtain ⟨y, hy, rfl⟩ := hz
    exact h y hy

theorem separating_unit {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    {x : Space n} (hx : x ∉ K) :
    ∃ u : Space n, ‖u‖ = 1 ∧ supportFn K u < ⟪x, u⟫_ℝ := by
  obtain ⟨p, hpK, hpmin⟩ := nearest_point hK hx
  have hxp : x - p ≠ 0 := sub_ne_zero.mpr (fun h => hx (by rw [h]; exact hpK))
  have hd0 : ‖x - p‖ ≠ 0 := norm_ne_zero_iff.mpr hxp
  have hpxupos : 0 < ‖x - p‖ := norm_pos_iff.mpr hxp
  have hcoef : 0 < (‖x - p‖)⁻¹ := inv_pos.mpr hpxupos
  have hstep : ∀ y ∈ K, ⟪y, (‖x - p‖)⁻¹ • (x - p)⟫_ℝ ≤ ⟪p, (‖x - p‖)⁻¹ • (x - p)⟫_ℝ := by
    intro y hy
    have hproj := projection_property hK hpK hpmin y hy
    have e1 : ⟪y, (‖x - p‖)⁻¹ • (x - p)⟫_ℝ
        = ⟪p + (y - p), (‖x - p‖)⁻¹ • (x - p)⟫_ℝ := by
      congr 1
      abel
    have h2 : ⟪y, (‖x - p‖)⁻¹ • (x - p)⟫_ℝ
        = (‖x - p‖)⁻¹ * (⟪p, x - p⟫_ℝ + ⟪y - p, x - p⟫_ℝ) := by
      rw [e1, real_inner_smul_right, inner_add_left]
    rw [h2, mul_add, real_inner_smul_right]
    have hpos := mul_nonpos_of_nonneg_of_nonpos hcoef.le hproj
    linarith
  have hsup := support_le_of_forall (hK.interior_nonempty.mono interior_subset) hstep
  refine ⟨(‖x - p‖)⁻¹ • (x - p), ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpxupos),
      inv_mul_cancel₀ hd0]
  · have h1 : ⟪x - p, (‖x - p‖)⁻¹ • (x - p)⟫_ℝ = ‖x - p‖ := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
      field_simp
    have h2 : ⟪x, (‖x - p‖)⁻¹ • (x - p)⟫_ℝ
        = ⟪p, (‖x - p‖)⁻¹ • (x - p)⟫_ℝ + ⟪x - p, (‖x - p‖)⁻¹ • (x - p)⟫_ℝ := by
      rw [← inner_add_left]
      congr 1
      abel
    rw [h2, h1]
    exact lt_add_of_le_of_pos hsup hpxupos

/-! ### 件 8: 重建定理 (锚-1 构造性实例的定理化) -/

/-- 重建定理: 凸体由自身支撑函数圈定 —— wulff∘support = id.
    锚-1 "由后果反定义" 的定理级形态 (路线 A 主目标件). -/
theorem wulff_reconstructs {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K) :
    ∀ x : Space n, x ∈ K ↔ ∀ u : Space n, ‖u‖ = 1 → ⟪x, u⟫_ℝ ≤ supportFn K u := by
  intro x
  constructor
  · intro hx u hu
    obtain ⟨x₀, hx₀, hx₀max, hx₀eq⟩ := support_attained hK u
    rw [isMaxOn_iff] at hx₀max
    rw [← hx₀eq]
    exact hx₀max x hx
  · intro hx
    by_contra hnot
    obtain ⟨u, hu, hlt⟩ := separating_unit hK hnot
    exact (hx u hu).not_gt hlt

/-! ### 件 10-16: n=1 情形件 (一维对数 BM 等式·独立复现) -/

/-- 件 10a: 一维单位方向 (Mathlib single 定义·独立于主件 oneEquiv 路线). -/
def oneDirection : Space 1 := EuclideanSpace.single (0 : Fin 1) 1

theorem oneDirection_norm : ‖(oneDirection : Space 1)‖ = 1 := by
  simp [oneDirection, PiLp.norm_single]

theorem oneDirection_ne_zero : (oneDirection : Space 1) ≠ 0 := by
  have h := oneDirection_norm
  intro hz
  rw [hz] at h
  simp at h

theorem inner_oneDirection (x : Space 1) : ⟪oneDirection, x⟫_ℝ = x.ofLp 0 := by
  rw [oneDirection, EuclideanSpace.inner_single_left]
  simp

/-- 件 10b: 一维元素由 0 分量 single 显化 (Fin 1 Subsingleton). -/
theorem eq_single_zero (u : Space 1) :
    u = EuclideanSpace.single (0 : Fin 1) (u.ofLp 0) := by
  rw [WithLp.ext_iff 2]
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp

/-- 件 10c: 内积自配对 = 0 分量平方 (一维). -/
theorem inner_self_eq_sq (u : Space 1) : ⟪u, u⟫_ℝ = (u.ofLp 0) ^ 2 := by
  conv_lhs => rw [eq_single_zero u]
  rw [EuclideanSpace.inner_single_left]
  simp [pow_two]

/-- 件 11: 一维单位向量二点刻划. -/
theorem unit_eq_or_neg {u : Space 1} (hu : ‖u‖ = 1) :
    u = oneDirection ∨ u = -oneDirection := by
  have h1 : (u.ofLp 0) ^ 2 = 1 := by
    rw [← inner_self_eq_sq, real_inner_self_eq_norm_mul_norm, hu, mul_one]
  rcases sq_eq_one_iff.mp h1 with h | h
  · left
    rw [eq_single_zero u, h, oneDirection]
  · right
    rw [eq_single_zero u, h]
    have hneg : (-oneDirection : Space 1) = EuclideanSpace.single (0 : Fin 1) (-1) := by
      rw [oneDirection, WithLp.ext_iff 2]
      funext g
      simp [PiLp.single_apply, apply_ite]
    rw [hneg]

/-- 件 12: 偶函数 wulff 体的一维形态 (区间预像). -/
theorem wulff_one_eq {f : Space 1 → ℝ} (heven : ∀ u : Space 1, f (-u) = f u) :
    wulffBody f = (WithLp.ofLp (p := 2) (V := Fin 1 → ℝ)) ⁻¹'
      {g : Fin 1 → ℝ | g 0 ∈ Icc (-(f oneDirection)) (f oneDirection)} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, wulffBody]
  have hxa : ⟪x, oneDirection⟫_ℝ = x.ofLp 0 := by
    rw [real_inner_comm, inner_oneDirection]
  constructor
  · intro hx
    have h1 := hx oneDirection oneDirection_norm
    have h2 := hx (-oneDirection) (by rw [norm_neg]; exact oneDirection_norm)
    rw [heven oneDirection] at h2
    rw [inner_neg_right, hxa] at h2
    rw [hxa] at h1
    have h2' : -f oneDirection ≤ x.ofLp 0 := by linarith
    exact Set.mem_Icc.mpr ⟨h2', h1⟩
  · intro hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hneg, hpos⟩ := hx
    intro u hu
    rcases unit_eq_or_neg hu with h | h
    · rw [h, hxa]
      exact hpos
    · rw [h, inner_neg_right, hxa, heven oneDirection]
      linarith

/-- 件 13: 一维 wulff 体体积 (乘积测度盒子路线·独立于主件 oneEquiv 测度等距路线). -/
theorem volume_wulff_one {f : Space 1 → ℝ} (heven : ∀ u : Space 1, f (-u) = f u) :
    volume (wulffBody f) = ENNReal.ofReal (2 * f oneDirection) := by
  rw [wulff_one_eq heven]
  have hmp := PiLp.volume_preserving_ofLp (ι := Fin 1)
  have hmeas : MeasurableSet {g : Fin 1 → ℝ | g 0 ∈ Icc (-(f oneDirection)) (f oneDirection)} :=
    measurableSet_Icc.preimage (measurable_pi_apply 0)
  rw [hmp.measure_preimage hmeas.nullMeasurableSet]
  have hvol : (volume : Measure (Fin 1 → ℝ))
      = Measure.pi (fun _ : Fin 1 => (volume : Measure ℝ)) := rfl
  have hseteq : {g : Fin 1 → ℝ | g 0 ∈ Icc (-(f oneDirection)) (f oneDirection)}
      = univ.pi (fun _ => Icc (-(f oneDirection)) (f oneDirection)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_pi]
    exact ⟨fun h i _ => by rw [Subsingleton.elim i 0]; exact h,
      fun h => h 0 (Set.mem_univ 0)⟩
  rw [hvol, hseteq, Measure.pi_pi]
  simp [Real.volume_Icc, sub_neg_eq_add]
  rw [show (f oneDirection + f oneDirection : ℝ) = 2 * f oneDirection from by ring,
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-! ### 件 9: 对数组合端点件 (假设解除·无条件版) -/

/-- 端点件 t=0: 对数组合退化为 K (只需 K 凸体; L 任意). -/
theorem logCombination_zero {n : ℕ} {K L : Set (Space n)} (hK : IsConvexBody K) :
    logCombination K L 0 = K := by
  unfold logCombination wulffBody
  simp only [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
  ext x
  exact (wulff_reconstructs hK x).symm

/-- 端点件 t=1: 对数组合退化为 L (只需 L 凸体; K 任意). -/
theorem logCombination_one {n : ℕ} {K L : Set (Space n)} (hL : IsConvexBody L) :
    logCombination K L 1 = L := by
  unfold logCombination wulffBody
  simp only [sub_self, Real.rpow_zero, Real.rpow_one, one_mul]
  ext x
  exact (wulff_reconstructs hL x).symm

/-! ### 件 14-16: n=1 主等式 (一维对数 BM = 等式情形) -/

/-- 件 14: 支撑函数偶性 (任意维·对称凸体). -/
theorem support_even {n : ℕ} {K : Set (Space n)} (hK : IsConvexBody K)
    (hs : OriginSymmetric K) (u : Space n) :
    supportFn K (-u) = supportFn K u := by
  obtain ⟨x₀, hx₀K, hx₀max, hx₀eq⟩ := support_attained hK (-u)
  obtain ⟨x₁, hx₁K, hx₁max, hx₁eq⟩ := support_attained hK u
  have hn₀ : (-x₀ : Space n) ∈ K := (hs x₀).mp hx₀K
  have hn₁ : (-x₁ : Space n) ∈ K := (hs x₁).mp hx₁K
  rw [isMaxOn_iff] at hx₀max hx₁max
  have hval1 : ⟪(-x₀ : Space n), u⟫_ℝ = supportFn K (-u) := by
    rw [inner_neg_left, ← inner_neg_right, hx₀eq]
  have hval2 : ⟪(-x₁ : Space n), -u⟫_ℝ = supportFn K u := by
    rw [inner_neg_left, inner_neg_right, hx₁eq, neg_neg]
  have hle1 : supportFn K (-u) ≤ supportFn K u := by
    have h : supportFn K u ≥ ⟪(-x₀ : Space n), u⟫_ℝ := by
      rw [← hx₁eq]; exact hx₁max _ hn₀
    rw [hval1] at h; exact h
  have hle2 : supportFn K u ≤ supportFn K (-u) := by
    have h : supportFn K (-u) ≥ ⟪(-x₁ : Space n), -u⟫_ℝ := by
      rw [← hx₀eq]; exact hx₀max _ hn₁
    rw [hval2] at h; exact h
  exact le_antisymm hle1 hle2

/-- 件 15: 对称凸体的一维体积 = 2×单位方向支撑 (件 8 重建定理直接复用). -/
theorem volume_symmetric_one {K : Set (Space 1)} (hK : IsConvexBody K)
    (hs : OriginSymmetric K) :
    volume K = ENNReal.ofReal (2 * supportFn K oneDirection) := by
  have hKw : K = wulffBody (supportFn K) := by
    ext x
    exact wulff_reconstructs hK x
  calc volume K = volume (wulffBody (supportFn K)) := congrArg volume hKw
    _ = ENNReal.ofReal (2 * supportFn K oneDirection) :=
        volume_wulff_one (support_even hK hs)

/-- ★件 16: n=1 情形件——一维对数 BM 等式 (独立复现·乘积测度路线). -/
theorem main_dimension_one {K L : Set (Space 1)}
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hsK : OriginSymmetric K) (hsL : OriginSymmetric L)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (logCombination K L t) = volume K ^ (1 - t) * volume L ^ t := by
  have hapos : 0 ≤ supportFn K oneDirection :=
    (positive_support hK hsK oneDirection_ne_zero).le
  have hbpos : 0 ≤ supportFn L oneDirection :=
    (positive_support hL hsL oneDirection_ne_zero).le
  have h2a : 0 ≤ 2 * supportFn K oneDirection := by linarith
  have h2b : 0 ≤ 2 * supportFn L oneDirection := by linarith
  have hp1 : 0 ≤ (2 * supportFn K oneDirection) ^ (1 - t) :=
    Real.rpow_nonneg h2a (1 - t)
  have hp2 : 0 ≤ (2 * supportFn L oneDirection) ^ t := Real.rpow_nonneg h2b t
  have heven : ∀ u : Space 1,
      (fun w => supportFn K w ^ (1 - t) * supportFn L w ^ t) (-u)
        = (fun w => supportFn K w ^ (1 - t) * supportFn L w ^ t) u := by
    intro u
    simp only
    rw [support_even hK hsK u, support_even hL hsL u]
  unfold logCombination
  rw [volume_wulff_one heven, volume_symmetric_one hK hsK,
    volume_symmetric_one hL hsL,
    ENNReal.ofReal_rpow_of_nonneg h2a (sub_nonneg.mpr ht1),
    ENNReal.ofReal_rpow_of_nonneg h2b ht0,
    ← ENNReal.ofReal_mul hp1]
  congr 1
  calc 2 * (supportFn K oneDirection ^ (1 - t)
        * supportFn L oneDirection ^ t)
      = (2 ^ (1 - t) * 2 ^ t)
          * (supportFn K oneDirection ^ (1 - t)
            * supportFn L oneDirection ^ t) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), sub_add_cancel, Real.rpow_one]
    _ = (2 * supportFn K oneDirection) ^ (1 - t)
          * (2 * supportFn L oneDirection) ^ t := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hapos,
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hbpos]
        ring

