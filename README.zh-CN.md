# 多项式多面体的鲁棒 SPR 综合

[English](README.md)

本仓库使用 Lean 4 / mathlib，按照分母阶数、顶点数量上界及分子实际次数，对普遍鲁棒严格正实（SPR）综合进行形式化分类。

## 本仓库证明的结论

对于一个非空有限的实系数首一 `n` 次分母族，假设**整个凸包均严格 Hurwitz 稳定**。公共 SPR 分子须对凸包内的原始分母及每个有限实频率成立：

$$
\mathrm{Re}\left(\frac{b(i\omega)}{a(i\omega)}\right)>0.
$$

对每个正阶数 `n` 及顶点数量上界 `m`，普遍存在性的分类如下：

| 分子实际次数 | 充要条件 |
| --- | --- |
| `n − 1` | `n ≤ 2` 或 `m ≤ 2` |
| `n` | `n ≤ 2` 或 `m ≤ 2` |
| `n + 1` | `n ≤ 2`、`m ≤ 2` 或 `n = m = 3` |

这里 `m` 是列出的顶点数量上界；上界为零时命题空真。三阶三角形是分子次数为 `n + 1` 时额外成立的情形。这是针对各类所有稳定多面体的结论；普遍存在性失败并不意味着每个具体多面体都失败。

公开定理为 [`SPR.Polytope.Direct.classification`](Lean/PolytopeSPR.lean)，精确谓词见 [Definitions.lean](Lean/SPR/Polytope/Common/Definitions.lean)。

## 环境安装与构建

安装 Git 和 [elan](https://github.com/leanprover/elan)（Lean 工具链管理器），并确认 `elan`、`lean`、`lake` 已加入 PATH。以下命令适用于 macOS、Linux 或 Windows 的 WSL 环境，在仓库根目录执行。

```sh
git clone https://github.com/dgjszy/polytope-spr-proof.git
cd polytope-spr-proof
lake exe cache get
lake build
```

`lean-toolchain` 固定 Lean **4.30.0**，mathlib 固定为 **v4.30.0**，精确依赖提交记录在 `lake-manifest.json`。首次运行需要联网下载工具链、依赖和编译缓存；保留锁文件，正常构建无需运行 `lake update`。缓存用于加速依赖构建，项目证明源码由 Lean 检查。

本仓库作为本地证明库使用，无需部署服务器或配置数据库。正式构建不需要 Python 或外部求解器。

## 验证与使用

```sh
lake env lean Lean/PolytopeAudit.lean
```

默认构建包含传递公理审计，仅允许 `propext`、`Classical.choice` 和 `Quot.sound`；发现其他公理时会报错。

在本工程的 Lean 环境中使用：

```lean
import PolytopeSPR

#check SPR.Polytope.Direct.classification
#print axioms SPR.Polytope.Direct.classification
```

## 仓库结构

- [`Lean/PolytopeSPR.lean`](Lean/PolytopeSPR.lean)：公开定理。
- [`Lean/SPR/Polytope/Classification.lean`](Lean/SPR/Polytope/Classification.lean)：分类定理组装。
- [`CubicSynthesis/`](Lean/SPR/Polytope/CubicSynthesis/)：三阶三角形的存在性证明。
- [`Transfer/`](Lean/SPR/Polytope/Transfer/)：跨阶传递。
- [`Lean/PolytopeAudit.lean`](Lean/PolytopeAudit.lean)：公理审计。
