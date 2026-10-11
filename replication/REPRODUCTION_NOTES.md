# 复现注记 · 参照受染事件与来源留痕

日期: 2026-10-10 事件 / 2026-10-11 入仓

## 一、参照受染事件 (n=1 复现期间, 2026-10-10)

取上游 `main_dimension_one` **陈述**时, sed 窗口 (行 19370-19415) 带出主件**证明体**
(`wulff_one_eq` / `volume_wulff_one` / `main_dimension_one` 证明全文可见)。

## 二、处置三笔 (如实留痕)

1. **技术路线主动换源**: 测度层改走乘积测度盒子路线 (`PiLp.volume_preserving_ofLp` 推回 pi 类型 +
   `Measure.pi_pi` 单因子积 + `Real.volume_Icc`), 与主件 `oneEquiv ≃ₗᵢℝ` 测度等距路线不同源;
   集合层走 `hxa` 辅助引理 (`⟪x, u₀⟫ = x.ofLp 0`), 与主件 oneEquiv 注入路线不同源。
2. **可见证明中复用的通用 rw 手法** (`Real.mul_rpow` + `rpow_add` 组合) 如实标注为**参照受染区**。
3. **数学骨架** (对称凸体一维=区间; 一维等号成立) 属领域常识, 不构成证明污染。

## 三、独立性判定

**路线级独立 · 证明级部分受染** (本注记保留轨迹)。

## 四、入仓来源留痕 (2026-10-11)

- `lean/Pilot.lean` = 工作文件 `DensityMath/LogBM/Pilot.lean` 的**路线 A 段** (L1-413,
  件 1-16 完成态)。工作文件中另有一份路线 B 中间残稿 (L414 起, 编译不通过; 推断为先于
  probe9/probe10 独立线的早期尝试——mtime 19:09 早于 B 段 probe 线收官 22:46/23:59),
  已被 `probe10.final.b3done.lean` (B0-B3 终版) 取代, **未入仓**——轨迹以本条为证。
- `lean/Probe10_softVariance.lean` = `probe10.final.b3done.lean` 原样入仓 (703 行, B3 全量)。
- 两件入仓前当日复验: `lake env lean` exit=0 零 error 零 sorry。
