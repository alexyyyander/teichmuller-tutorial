# Teichmüller 统一研究路线

> *继续 Oswald Teichmüller 的未竟事业：将可变黎曼曲面理论重新统一为可验证的形式化系统*

[![Build PDF](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml/badge.svg)](https://github.com/alexyyyander/teichmuller-tutorial/actions/workflows/build.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

## 核心愿景

**恢复 Teichmüller 在1944年提出的统一路线，让复几何、拓扑与算术在同一个框架下重新汇合。**

```
拓扑曲面 → 复结构 → 标记黎曼曲面 → T(S) → M(S) → 解析族
     ↑                                                    ↓
     └────────────── 形式化验证（Lean 4）──────────────────┘
```

---

## Teichmüller 与他的遗产

**Oswald Teichmüller**（1913–1943），哥廷根学派最后的继承者之一。

| 论文 | 年份 | 核心贡献 |
|------|------|----------|
| *Extremale quasikonforme Abbildungen* | 1939 | Teichmüller 距离、极值映射、二次微分 |
| *Veränderliche Riemannsche Flächen* | 1944 | 标记曲面、解析族、局部变形坐标 |

1944年的遗作提出了一条**被历史中断的统一路线**。此后，核心思想被分别继承：

```
        Teichmüller (1944)
              │
    ┌─────────┼─────────┬─────────┐
    ↓         ↓         ↓         ↓
  Ahlfors   Kodaira   Grothendieck  Fenchel
  Bers      Spencer   Mumford      Nielsen
 拟共形    变形理论    模函子      双曲几何
```

**本项目的目标：重新汇合这些分流，建立可验证的形式化核心。**

---

## 项目结构

```
teichmuller-tutorial/
├── docs/tutorial/           # 数学教程（中英文双语）
│   ├── foundations/          # 入门：从高中数学到模空间
│   └── advanced/            # 进阶：Lean 形式化边界
├── lean/Teichmuller/        # Lean 4 形式化代码
│   ├── Topology.lean        # 拓扑层
│   ├── Complex.lean         # 复结构图册
│   ├── Family.lean          # 解析族接口
│   └── Modular.lean         # 模群代数
└── scripts/                 # 构建工具
```

---

## 快速开始

### 阅读教程

| 文档 | 语言 | 内容 |
|------|------|------|
| [入门导论](docs/tutorial/foundations/foundations_intro.tex) | 中文 | 从函数到模空间的完整路线 |
| [入门导论](docs/tutorial/foundations/foundations_intro_en.tex) | English | Foundations introduction |
| [进一步推导](docs/tutorial/advanced/teichmuller_program.tex) | 中文 | Lean 形式化边界与代码对应 |

### 构建 PDF

```bash
# 本地构建
./scripts/build.sh

# 或手动构建
latexmk -xelatex -outdir=build docs/tutorial/foundations/foundations_intro.tex
```

### Lean 代码

```bash
lake build
```

---

## 研究阶段

| 阶段 | 目标 | 状态 |
|------|------|------|
| P₀ | 四条基础轴统一符号与定义 | ✅ |
| P₁ | 拓扑、同伦与标记关系 | ✅ |
| P₁.₅ | Mathlib 实体层对接 | ✅ |
| P₂ | 解析族结构接口 | ✅ |
| P₃ | Beltrami 方程与拟共形变形 | 🔄 |
| P₄ | 模函数与周期映射 | 🔄 |
| P₅ | 万有族构造 | ⏳ |

---

## 未来路线图

### 近期（1-2年）
- 形式化可测 Riemann 映射定理
- 完成 Beltrami 方程解的存在唯一性
- 连接低亏格可计算模型

### 中期（3-5年）
- 构造 Teichmüller 空间的万有性质
- 比较 turning-piece / Fenchel-Nielsen / 周期坐标
- 桥接高阶 Teichmüller 与几何 Langlands

### 长期愿景
**恢复哥廷根学派在复几何与模空间领域的领导地位。**

---

## 参考文献

1. Teichmüller, O. (1939). *Extremale quasikonforme Abbildungen und quadratische Differentiale*
2. Teichmüller, O. (1944). *Veränderliche Riemannsche Flächen*
3. Ahlfors, L. V. (1966). *Lectures on quasiconformal mappings*
4. Hubbard, J. H. (2006). *Teichmüller theory and applications*

---

## 贡献

欢迎贡献代码、文档或提出改进建议！

```bash
git clone https://github.com/alexyyyander/teichmuller-tutorial.git
cd teichmuller-tutorial
./scripts/build.sh  # 验证构建
```

---

*纪念 Oswald Teichmüller (1913–1943)*  
*愿数学的统一之光照亮未来*