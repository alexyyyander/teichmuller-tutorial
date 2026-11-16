# Über Teichmüller's Einheitliches Programm

> *继续 Oswald Teichmüller 的未竟事业：将可变黎曼曲面理论统一为可验证的形式化系统*

**[English Version](README.md)** | **[Deutsch](#vision)**

[![Build PDF](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml/badge.svg)](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

**[English Version](README.md)**

---

## 愿景

**恢复 Teichmüller 在1944年提出的统一路线，让复几何、拓扑与算术在同一个框架下重新汇合。**

1944年，Oswald Teichmüller 发表了《可变黎曼曲面》（*Veränderliche Riemannsche Flächen*），提出了统一研究黎曼曲面变化的纲领。这个纲领因他30岁英年早逝而中断。此后，他的思想分别被拟共形分析（Ahlfors, Bers）、变形理论（Kodaira, Spencer）、模函子（Grothendieck）和双曲几何（Fenchel, Nielsen）继承。

**本项目将这些分流重新汇合为一个形式化可验证的系统。**

---

## 仓库结构

```
.
├── docs/
│   ├── index.html          # GitHub Pages 入口
│   ├── tutorial/           # CI 实际编译并发布的源文件（中/英）
│   ├── full-source/        # 更完整的本地版本（不由 CI 构建）
│   └── interactive/        # 独立交互式 HTML
├── lean/
│   ├── Teichmuller.lean    # 库聚合模块（35 个）
│   ├── Teichmuller/        # Lean 4 形式化模块
│   └── Main.lean           # 演示可执行文件
├── scripts/                # 构建与翻译辅助脚本
├── .github/workflows/      # LaTeX + Lean + Pages CI
├── lakefile.lean           # Lean 构建定义
└── README.md / README.zh-CN.md
```

`docs/tutorial/` 是 CI 实际编译并发布的源文件。
`docs/full-source/` 保留更完整的本地版本：它们使用本地中文字体，**不由 CI 构建**。

## 面向初学者

**本仓库是学习 Teichmüller 理论及相关基础的综合学习资源。**

我们的教程提供从基础数学到高级主题的结构化路径：

| 级别 | 文档 | 学习内容 |
|------|------|----------|
| 📚 基础 | [入门导论](docs/tutorial/foundations/foundations_intro.tex) | 集合 → 函数 → 群 → 复分析 → 拓扑 → 黎曼曲面 → 模空间 |
| 🎓 进阶 | [进一步推导](docs/tutorial/advanced/teichmuller_program.tex) | 形式化边界、Lean 4 实现、研究前沿 |

**无需 Teichmüller 理论的先修知识。** 教程设计为自包含，从高中数学水平开始构建。

---

## 面向研究者与 AI Agent

**我们欢迎对大一统纲领的协作探索，但需通过严格的审查。**

### 开放研究框架

本项目支持多 agent 探索 Teichmüller 理论的统一路线。欢迎人类研究者和 AI agent（Claude、GPT、Gemini 等）的贡献，但需通过我们的验证流程。

### 审查流程

```
Agent 探索 → 数学验证 → 形式化检查 → 同行评审 → 合并
```

| 阶段 | 要求 | 审查者 |
|------|------|--------|
| 1. 数学严谨性 | 正确定义、有效证明 | 人类专家 |
| 2. 形式化验证 | Lean 4 编译、类型检查 | 自动化 + 人类 |
| 3. 集成性 | 与现有代码库兼容 | 维护者 |
| 4. 文档完整性 | 清晰解释、引用文献 | 社区 |

**注意：** 我们的严格审查机制仍在不断完善中。我们旨在维护最高标准的同时实现高效协作。

### 当前探索前沿

- **Beltrami 方程解**：完成可测 Riemann 映射定理
- **万有族构造**：证明任意亏格的存在性
- **坐标比较**：统一 turning-piece、Fenchel-Nielsen 与周期坐标

---

## Teichmüller 论文

| 论文 | 年份 | 链接 | 核心贡献 |
|------|------|------|----------|
| *Extremale quasikonforme Abbildungen und quadratische Differentiale* | 1939 | [GDZ](https://gdz.sub.uni-goettingen.de/id/PPN243919689_0152) | Teichmüller 距离、极值拟共形映射、二次微分 |
| *Veränderliche Riemannsche Flächen* | 1944 | [GDZ](https://gdz.sub.uni-goettingen.de/id/PPN243919689_0174) | 标记黎曼曲面、解析族、局部变形坐标 |
| *Gesammelte Abhandlungen* | 1982 | [Springer](https://link.springer.com/book/10.1007/978-3-642-46204-7) | 全集，Ahlfors & Gehring 编 |

---

## 形式化进展

### Lean 4 实现 (`lean/Teichmuller/`)

| 组件 | 文件 | 状态 | 描述 |
|------|------|------|------|
| 拓扑层 | `Topology.lean` | 🟡 接口层 | 拓扑空间、连续映射、同伦闭包 |
| 复结构层 | `Complex.lean` | 🟡 结构接口 | 图册、过渡映射、全纯性字段 |
| 解析族层 | `Family.lean` | 🟡 结构接口 | 依赖和总空间、拉回、分类字段 |
| 模群层 | `Modular.lean` | 🟡 代数/作用层 | SL₂(ℤ) 矩阵代数与作用规范 |
| Mathlib 桥接 | `MathlibTopology.lean` | 🟡 选定桥接 | 标准 Mathlib 拓扑对象 |
| 复图册 | `MathlibComplex.lean` | 🟡 具体部分层 | 选定 ℂ 图册与 `DifferentiableOn` 过渡、固定参数纤维切片、标记纤维构造 |
| 纤维丛 | `MathlibFiberBundle.lean` | 🟡 接口层 | 局部平凡化与拉回结构 |
| Čech 下降 | `MathlibCech.lean` | 🟡 首个具体层 | 开覆盖、局部全局族、双全纯重叠映射、逆律、三重重叠 cocycle |
| Čech 商 | `MathlibCechDescent.lean` | 🟡 具体商骨架 | 不交并局部总空间、cocycle 相容粘合步骤、局部单射、重叠总空间同胚、下降图册传输 |
| 具体 Čech 族 | `MathlibCechConcrete.lean` | 🟡 具体图册比较层 | 多片限制、重叠图册、精确图册传输等式、联合全纯过渡、下降图册 witness |
| 环面 Čech 桥 | `MathlibTorusCech.lean` | 🟡 选定紧纤维层 | 亏格一提升/deck witness、逐点源/靶重叠到提升的坐标比较、显式 Čech 下降 |
| Beltrami | `MathlibBeltrami.lean` | 🔄 进行中 | 可测系数、传输 cocycle |
| Beltrami 族桥 | `MathlibBeltramiFamily.lean` | 🟡 具体桥接 | 参数模型、锚定商、系数级分类、传输标记曲面族、携带数据的 `AnalyticFamily`、联合坐标族、条件性局部总空间图册 witness |
| 缩放 Neumann 族 | `MathlibBeltramiNeumannOperatorFamily.lean` | 🟡 具体算子形态 | 连续标量系数、固定算子缩放 `K_b = μ_b • S`、一致压缩半径、连续不动点族 |
| 乘子 Neumann 族 | `MathlibBeltramiNeumannMultiplierFamily.lean` | 🟡 具体 (L^p) 族 | 参数依赖系数乘子 `M_{μ_b}`、固定奇异算子 `B`、算子范数连续性、一致压缩、连续 Neumann 解族 |
| Beurling L² 族 | `MathlibBeltramiNeumannBeurlingFamily.lean` | 🟡 闭子圆盘模型 | 常系数 (L^2) 乘子 `M_μ = μ id`、Fourier 定义的 Beurling 算子、`‖μ‖ ≤ r < 1` 上的一致半径、连续 Neumann 族 |
| 剖面 Beurling 族 | `MathlibBeltramiNeumannProfileFamily.lean` | 🟡 空间剖面模型 | 固定有界可测剖面 `a(z)`、缩放系数 `μ_b(z) = b a(z)`、精确乘子恒等式 `M_{μ_b} = b M_a`、`‖b‖ ≤ r` 且 `r‖a‖∞ < 1` 上的一致 `L²` Neumann 族 |
| Neumann 状态桥 | `MathlibBeltramiNeumannBridge.lean` | 🟡 条件性解析桥 | 连续不动点状态、连续状态求值到逐点/几乎处处 Beltrami 族、以及供局部图册连续性门使用的逆求值数据 |

### 当前边界

**已证明：**
- 标记相容关系是等价关系
- Teichmüller 空间作为商空间良定义
- SL₂(ℤ) 行列式为一的乘法与结合律
- 上半平面基本域代表元定理
- j 型权零商函数构造

**进行中：**
- 可测 Riemann 映射定理（Beltrami 方程解的存在唯一性）
- 完整的图册级 cocycle 兼容性
- 全局万有族存在性

---

## 教程

| 文档 | 语言 | 内容 |
|------|------|------|
| [入门导论](docs/tutorial/foundations/foundations_intro.tex) | 中文 | 从高中数学到模空间 |
| [入门导论](docs/tutorial/foundations/foundations_intro_en.tex) | English | Complete introductory route |
| [进一步推导](docs/tutorial/advanced/teichmuller_program.tex) | 中文 | Lean 形式化边界 |
| [进一步推导](docs/tutorial/advanced/teichmuller_program_en.tex) | English | Code correspondence |

---

## 构建

```bash
# 安装依赖（需要 TeX Live 和 XeLaTeX）
./scripts/build.sh

# 或手动构建
latexmk -xelatex -outdir=build docs/tutorial/foundations/foundations_intro.tex

# Lean 4
lake build
```

---

## 研究路线图

```
P₀  统一符号         ✅
P₁  拓扑与标记       ✅
P₁.₅ Mathlib 对接    ✅
P₂  解析族接口       ✅
P₃  Beltrami 方程    🔄
P₄  模函数          🔄
P₅  万有族          ⏳
```

### 下一步

1. **Beltrami 层完成**：完成可测微分 cocycle，通过压缩映射证明存在唯一性
2. **模函数桥接**：通过周期映射连接 j-不变量与 Teichmüller 空间
3. **万有族**：构造任意标记解析族的分类函子

---

## 参考文献

- Teichmüller, O. (1944). *Veränderliche Riemannsche Flächen*. Deutsche Mathematik, 7, 344-359. [GDZ](https://gdz.sub.uni-goettingen.de/id/PPN243919689_0174)
- Ahlfors, L. V. (1966). *Lectures on Quasiconformal Mappings*. Van Nostrand.
- Bers, L. (1970). *Thom's Theorem and Riemann Surfaces*. Lecture Notes in Math.
- Hubbard, J. H. (2006). *Teichmüller Theory and Applications*. Matrix Editions.
- Schappacher, N. & Scholz, E. (1992). *Oswald Teichmüller – Leben und Werk*. Jahresber. DMV. [Online](http://dml.math.uni-bielefeld.de/JB_DMV/)

---

## 贡献

```bash
git clone https://github.com/alexyyyander/teichmuller-tutorial.git
cd teichmuller-tutorial
./scripts/build.sh
```

---

*纪念 Oswald Teichmüller (1913–1943)*