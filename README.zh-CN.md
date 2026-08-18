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
| 拓扑层 | `Topology.lean` | ✅ 完成 | 拓扑空间、连续映射、同伦闭包 |
| 复结构层 | `Complex.lean` | ✅ 完成 | 图册、过渡映射、全纯性 |
| 解析族层 | `Family.lean` | ✅ 完成 | 依赖和总空间、拉回、普适性质 |
| 模群层 | `Modular.lean` | ✅ 完成 | SL₂(ℤ) 矩阵代数、上半平面作用 |
| Mathlib 桥接 | `MathlibTopology.lean` | ✅ 完成 | 标准 Mathlib 拓扑对象 |
| 复图册 | `MathlibComplex.lean` | ✅ 完成 | 具体 ℂ 图册与 `DifferentiableOn` |
| 纤维丛 | `MathlibFiberBundle.lean` | ✅ 完成 | 局部平凡化、拉回纤维丛 |
| Beltrami 层 | `MathlibBeltrami.lean` | 🔄 进行中 | 可测系数、传输 cocycle |

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