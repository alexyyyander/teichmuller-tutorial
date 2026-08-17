# M3 三模式数学搜索协议 — 设计文档

- **状态**: Draft 0.1
- **日期**: 2026-08-17
- **定位**: 纯通用研究协议，不绑定任何具体猜想
- **核心**: 以"探索树"为唯一真实来源，三种搜索模式独立启停，结论状态由证据派生而非声明确认，失败探索一等公民，Lean 核验作为发现级的晋升门，可导出为 Proofweave 兼容事件流。

---

## 0. 设计原则

1. **探索树是唯一真实来源** — 所有搜索活动写入一棵 append-only 的树，报告/可视化/导出均从树派生。
2. **状态是派生的，不是声明的** — agent 写入证据；`success` 状态只有 Lean 核验（或等价的机器验证）通过才派生。作者不能直接标记 claim 为成功。
3. **负面结果是一等贡献** — 失败、撤回、no-go、反例节点永久保留，不可删除，只可追加修订。防止"事后诸葛"和重复死路。
4. **发现级必须可复现** — 任何标为"发现"的节点必须关联可执行的 Lean 源文件 + 运行命令 + 依赖锁定（可执行研究包）。
5. **三模式独立启停** — 计算搜索、工具发现、新数学发明各自有完整生命周期和独立预算。
6. **预算与交互可配置** — 预算自动追踪；交互可为"节点确认型"或"完全自主型"。
7. **成功判据 = 过程质量** — 框架的成功按协议遵循、树完整性、预算纪律、审计质量判定，不以解决猜想为判据。
8. **对外协议可插拔** — 探索树可导出为 Proofweave 兼容事件流，但协议本身（签名/哈希/网络）由外部层承担。

---

## 1. 架构总览

```
skills/math-search/
├── SKILL.md                          # 主协议：决策门、预算、报告、状态派生规则
├── modes/
│   ├── mode1-computation.md          # 模式一：自洽计算搜索
│   ├── mode2-tool-discovery.md       # 模式二：工具发现（文献 + 跨分支移植）
│   └── mode3-invention.md            # 模式三：新数学发明
├── orchestrator/
│   ├── build_tree.py                 # 探索树 JSON → D3 单文件 HTML 可视化
│   ├── export_pw.py                  # 探索树 → Proofweave 兼容事件流
│   ├── tree_schema.json              # 探索树数据模式（JSON Schema）
│   └── lean_check.py                 # Lean 复现命令封装 + 核验状态查询
└── templates/
    ├── obstacle_card.md              # 障碍卡片模板
    └── report_template.md            # 强制研究报告模板
```

### 数据流

```text
agent 动作 ──> 探索树(append-only JSON) ──> 状态派生引擎 ──> 报告 / 可视化 / Proofweave 导出
                    ▲                              │
                    └────── 新证据/修订 ─────────────┘
```

---

## 2. 探索树数据模式 (`tree_schema.json`)

### 2.1 节点

```json
{
  "$schema": "nodes",
  "root": "urn:m3:tree:<session-id>",
  "nodes": [
    {
      "id": "urn:m3:node:<uuid>",
      "revision_of": null | "<node-id>",        // 修订/撤回链，append-only
      "parent_ids": ["urn:m3:node:<parent>"],
      "type": "hypothesis | tool_candidate | certificate | no_go | counterexample | dead_end",
      "mode": "computation | tool_discovery | invention",
      "status": "in_progress | success | failed | withdrawn | superseded",
      "obstacle": {
        "fingerprint": "<障碍指纹文本>",
        "excluded_methods": ["<已排除方法类>"],
        "required_coupling": "<必须使用的耦合>"
      },
      "claim": "<尝试的命题/假设>",
      "result": "<尝试结果：证据/反例/certificate/no-go 原因>",
      "falsification": "<反证规则（如适用）>",
      "lean_binding": {
        "theorem": "<定理名>",
        "file": "lean/<file>.lean",
        "run": "lake build lean/<file>.lean",
        "verified": true,
        "verified_at": "<ISO8601>"
      },
      "verification_level": "V0 | V1 | V2 | V3 | V4",
      "audit": {
        "L1_passed": true,
        "L2_passed": false,
        "audit_log": ["<审计事件>"]
      },
      "budget_used": 0.42,
      "exported_event_ids": ["urn:pw:event:<uuid>"],
      "logs": ["<ISO8601>: <事件>"]
    }
  ]
}
```

### 2.2 状态派生规则（改自 Proofweave 的"状态是派生的"原则）

| 观察到的证据 | 派生状态 |
|---|---|
| 节点已创建，等待工作 | `proposed` |
| agent 写了 claim/result，尚无核验 | `in_progress`（锁在 L1 之前） |
| 通过 L1 合理性审计，无 Lean 绑定 | `unverified_claim`（不可升为 success） |
| 有 Lean 绑定且 `lean_check.py` 返回 verified | `success`（V1） |
| 独立重算/复现通过 | V2-V3 升级 |
| 出现反例/矛盾 | `failed` 或 `withdrawn`（保留历史） |

**晋升门（核心约束）**：节点从 `in_progress`/`failed` 升为 `success` 的唯一路径：

1. L1 审计通过
2. `lean_binding` 存在
3. `lean_check.py` 实际核验返回 verified
4. （可选，V2+）独立重验通过

缺任一 → 状态锁在 `in_progress`，报告中标为"未验证声明"。

---

## 3. 三种模式（独立子流程）

每种模式有完整生命周期：启动条件 → 执行 → 成功退出 → 失败退出 → 转换规则。

### 模式一：自洽计算搜索 (Computation)

**目标**：在已知数学框架内，通过精确计算/枚举/反例搜索/规模扩张获得信息。

**启动条件**：障碍卡片的指纹表明存在可计算的有限对象（有限验证、证书构建、反例窗口）。

**执行准则**：
- 精确性优先：只用整数算术，所有报告结果交叉乘法验证
- 有限性必须是推导出来的，不是枚举出来的
- 反例优先：寻找反例比寻找证明更便宜
- 规模阶梯：反例窗口 → 全称证书 → 若无法闭合则记录 no-go

**成功退出**：获得已验证的证书/反例/全称局部结论。
**失败退出**：预算耗尽；或产生 no-go 定理证明穷举无信息增量（强制转换）。

### 模式二：工具发现搜索 (Tool Discovery)

**目标**：从文献、已知定理库、其他数学分支发现可应用的工具（含跨分支移植）。

**启动条件**：障碍卡片指纹已知，但已排除方法类之外的候选未穷尽。

**执行流程**：
1. 用指纹筛选候选工具类（排除已被 no-go 覆盖的类）
2. 文献检索（arXiv、定理库、跨分支扫描）
3. 小型适用性实验：在 50 个困难例子上跑模拟证书
4. 通过 → 进入审计门；不通过 → 记录失败节点，扩展排除集

**转换规则**：若检索到的工具落入已排除类 → 立即终止该候选并写 no-go 节点。

### 模式三：新数学发明 (Invention)

**目标**：从头创造新机制（新对象/新不变量/新证明结构），当已知工具全部不足时启动。

**启动条件**：指纹显示已知工具类已穷尽；模式一、二均有记录在案的失败节点。

**执行准则**：
- 先分析"为什么现有工具失败"（引用 no-go 节点）
- 生成机制候选 → 先在小例子上验证一致性（一致性失败即废弃候选）
- 一致性通过 → 尝试证明
- 未证明的机制只能标记 `candidate`，绝不声称定理
- 候选升级为定理必须过晋升门

---

## 4. 审计门（所有模式强制）

| 级别 | 触发 | 动作 | 通过后状态 |
|---|---|---|---|
| L1 合理性 | 任何新结论 | 反向检查、边界测试、小窗口对照 | `unverified_claim` |
| L2 独立验证 | 候选升级为"发现" | Lean 核验 / 独立重算 / 不同实现交叉 | `success` (V1) |
| L3 完整审计 | 声称突破/证明 | 完整审查 + 用户确认 | 标记"突破级"，需用户签字 |

审计记录写入 `audit.audit_log`，不可删除。

---

## 5. 预算管理

- 每模式独立预算（步数/时间/调用数），可配置
- `budget_used` 每节点累加，主协议追踪会话总量
- 预算耗尽 → 强制停止该模式 → 写报告 → 询问加预算或切换
- 禁止预算默认继承到新模式（切换需显式配置）

---

## 6. 交互模式

- **节点确认型**（默认）：模式切换、新发现、预算耗尽、晋升门触发时请求确认
- **完全自主型**：仅在新发现/错误/L3审计触发时联系用户
- 策略在会话启动时由用户选择，运行中可切换

---

## 7. 产出三件套（每会话强制）

```
reports/<session>/report.md          # 结构化研究报告
explorations/<session>.json          # 探索树（唯一真实来源）
viz/<session>.html                   # D3 交互式可视化（单文件）
```

### 7.1 研究报告模板 (`report_template.md`)

- 会话目标与障碍卡片
- 每种模式的运行摘要（预算、节点数、成功/失败）
- 发现的定理/证书清单（Lean 绑定）
- 失败路径清单（含 no-go 定理）
- 未验证声明清单（锁在 in_progress 的节点）
- 下一步建议（含模式切换理由）

### 7.2 D3 可视化特性 (`build_tree.py`)

- 节点颜色：绿=success，红=failed，灰=withdrawn，黄=in_progress
- 节点形状：方形=certificate，圆圈=假设/候选，菱形=no-go/反例
- 点击展开详情（claim/result/lean_binding/audit）
- Lean 绑定徽章：绿色徽章 + 跳转源文件
- 过滤：按模式、按状态、按 Lean 绑定、失败路径默认可见 + "仅看失败"模式
- D3 以 CDN 引入，JSON 数据内嵌单文件

### 7.3 Lean 复现 (`lean_check.py`)

```sh
# 复现节点 <id> 的结论
lean_check.py verify <tree.json> <node-id>
# 等价于：从节点提取 lean_binding.run 并执行，返回 verified true/false
```

失败/未核验 → `lean_binding.verified=false`，节点锁在 `in_progress`。

---

## 8. Proofweave 集成（协议兼容导出）

M3 本地运行，不实现 Proofweave 协议本身。导出器 `export_pw.py` 将探索树转为兼容事件流，供后续接入 Proofweave 节点。

### 预演映射

| M3 探索树元素 | Proofweave 事件 |
|---|---|
| 根节点 + 障碍卡片 | `project.create` + `synthesis.publish` |
| success 节点（Lean 已验证） | `claim.publish` + `bundle.publish`（执行契约 = `lake build` + 定理名） |
| 审计门 L2 通过 | `verification.submit` (mode=`exact_bundle`/`ci_replay`) |
| counterexample / no_go 节点 | `challenge.open` 或 empirical claim |
| failed / withdrawn 节点 | `claim.withdraw` / `challenge.resolve`（append-only） |

### 吸收的核心原则

1. **状态派生**：作者写入证据，状态由核验事件派生（§2.2）。
2. **append-only**：修订链 `revision_of`，永不经编辑删除。
3. **负面结果一等**：失败节点导出为 challenge/withdraw，不丢失。
4. **可执行研究包**：成功节点的 `lean_binding.run` 即 bundle 执行契约。

---

## 9. 框架自身验证策略

1. **Schema 校验**：生成树用 JSON Schema 严格校验（`tree_schema.json`）。
2. **协议演练测试**：三个合成问题（一个可解、一个已知 no-go、一个开放）跑完整会话，检查：
   - 树完整性（全节点保留、修订链正确）
   - 晋升门执行（无 Lean 绑定的节点不能成为 success）
   - 预算纪律（无超支、无无限循环）
   - 可视化完整性（全节点出现，失败可见）
   - 导出正确性（事件流符合映射表）
3. **回归防线**：每次会话结束重新校验 schema + 跑演练测试。

---

## 10. 已决 / 待决决策

**已决**：
- 交付物形态：可执行 opencode 技能（主+子技能分层）
- 适用范围：纯通用框架
- 模式组织：三独立子流程
- 预算：可配置 + 自动追踪
- 交互：节点确认型 / 完全自主型可切换
- 记录：强制研究报告 + 探索树 + 可视化三件套
- 可视化栈：JSON + D3 交互式单文件
- Lean 绑定粒度：发现级绑定（晋升门）
- 成功判据：过程质量
- 审计：内置审计门
- Proofweave：协议兼容导出层

**待决**（v0.2 / 接入期）：
- Proofweave 签名/哈希/节点接入的具体实现
- V2+ 独立复现的"独立性"判定标准
- L3 审计的"突破级"定义细则