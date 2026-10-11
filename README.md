# logbm-pilot · 对数 Brunn-Minkowski 打样复现件

**Pilot independent replication of two minimal slices of the log-Brunn–Minkowski (BLYZ) proof formalization. Lean 4 + Mathlib, zero sorry.**

## 内容 (Contents)

| 文件 | 内容 |
|---|---|
| `lean/Pilot.lean` | 路线 A 骨架复现件 (413 行): 支撑可达/原点内点/正支撑/最近点·投影特征·分离单位向量对偶链/wulff_reconstructs 重建定理/端点件无条件版 + n=1 情形件 10-16——一维对数 BM 等式 `volume (logCombination K L t) = volume K^(1-t) × volume L^t` 独立复现 (乘积测度盒子路线, 与上游 oneEquiv ≃ₗᵢℝ 测度等距路线**不同源**) |
| `lean/Probe10_softVariance.lean` | 路线 B 全量 (703 行): softVariance 陈述的最小退化实例 (n=2, κ=单方向, q=2)——`slabVariance_half` → `slabVariance_full` → `softVariance_pilot` 端到端 |
| `replication/REPRODUCTION_NOTES.md` | 独立性判定 + 参照受染事件档注记 (路线级独立·证明级部分受染·三笔处置留痕) |

## 上游 (Upstream, external read-only)

对数 Brunn–Minkowski 猜想 (Böröczky–Lutwak–Yang–Zhang 公开难题) 完整证明的 Lean 形式化 companion (24,490 行 / 1,500 定理 / 零 sorry)。本包 = 对其两个最小切片的**独立打样复验** (pilot), 非重新形式化。

## 验证 (Verification)

- 2026-10-11 复验: `lake env lean` 两件 exit=0, 零 error, 零 sorry;
- 主定理 `#print axioms` = `[propext, Classical.choice, Quot.sound]` 标准三件套 (无 sorryAx, 无附加公理);
- 全库 build 8736 jobs 绿 (2026-10-10, 随录)。

## 状态 (Status)

Companion package (候发布轮, Zenodo record pending)。零新增物理宣称。
License: Code MIT / Docs CC-BY-4.0。
