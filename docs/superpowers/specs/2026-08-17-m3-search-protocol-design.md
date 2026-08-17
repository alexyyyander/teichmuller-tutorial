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
4. **发现级必须可复现** — 任何标为"发现"的节点必须关联可执行的 Lean 源文件 + 运行命令 + 依赖锁定（`lean_binding.lock`：toolchain 内容 + lake-manifest 引用，见 §2.1）。
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
│   ├── import_workspace.py           # ★ 现有工作（日志/Lean）→ 探索树导入器
│   ├── upload_proofs.py              # ★ 已验证节点 → 本地可复现归档上传器
│   ├── export_pw.py                  # 探索树 → Proofweave 兼容事件流
│   ├── tree_schema.json              # 探索树数据模式（JSON Schema）
│   ├── lean_check.py                 # Lean 复现命令封装 + 核验状态查询
│   └── audit_gate.py                 # ★ 审计门/状态派生引擎（L1/L2/晋升门）
└── templates/
    ├── obstacle_card.md              # 障碍卡片模板
    └── report_template.md            # 强制研究报告模板
```

### 数据流

```text
现有工作 ──import_workspace.py──> 探索树(append-only JSON)
agent 动作 ────────────────────> 探索树(append-only JSON)
探索树 ──> 状态派生引擎(audit_gate.py) ──> 报告 / D3 可视化 / Proofweave 导出
                                          └─> upload_proofs.py ──> output/uploads/ 归档
                     ▲                              │
                     └────── 新证据/修订 ─────────────┘
```

---

## 2. 探索树数据模式 (`tree_schema.json`)

### 2.1 节点（存储形态）

存储 JSON 是派生视图的快照；**字段归属见 §2.3**。状态枚举是最小存储集；`proposed`/`unverified_claim`/`candidate` 是派生视图标签，不存储（见 §2.2）。

```json
{
  "root": "urn:m3:tree:<session-id>",
  "session": {
    "target": "<问题陈述>",
    "obstacle_card_ref": "<obstacle_card.md 路径或摘要>",
    "interaction_policy": "confirm_at_nodes | autonomous",
    "budgets": {
      "computation": {"units": "steps | seconds | calls", "cap": 1000},
      "tool_discovery": {"units": "steps", "cap": 400},
      "invention": {"units": "seconds", "cap": 3600}
    }
  },
  "nodes": [
    {
      "id": "urn:m3:node:<uuid>",
      "revision_of": null | "<node-id>",        // 修订/撤回链，append-only
      "parent_ids": ["urn:m3:node:<parent>"],
      "origin": "search | legacy",              // legacy=导入的历史工作
      "source_ref": null | "<文档路径+小节 | lean 文件:定理行号>",   // legacy 节点必填
      "type": "hypothesis | tool_candidate | certificate | no_go | counterexample",
      "mode": "computation | tool_discovery | invention",
      "status": "in_progress | success | failed | withdrawn | superseded",  // 仅引擎写入（§2.3）
      "obstacle": {
        "fingerprint": "<障碍指纹（定义见 §2.4）>",
        "excluded_methods": ["<已排除方法类>"],
        "required_coupling": "<必须使用的耦合>"
      },
      "claim": "<尝试的命题/假设>",
      "result": "<尝试结果：证据/反例/certificate/no-go 原因>",
      "falsification": "<反证规则（如适用）>",
      "lean_binding": {
        "theorem": "<定理名>",
        "file": "lean/<file>.lean",
        "run": "lake build lean/<file>.lean && lean_check.py --theorem <定理名> lean/<file>.lean",
        "deny_proofs_axioms": true,
        "lock": {
          "toolchain": "<lean-toolchain 内容>",
          "lake_manifest_ref": "<lake-manifest.json 相对路径或摘要>"
        },
        "verified": false,        // 引擎字段（§2.3）
        "verified_at": null
      },
      "verification_level": "V0 | V1 | V2 | V3 | V4",   // 引擎字段，详见 §2.5
      "audit": {
        "L1_passed": false,
        "L2_passed": false,
        "audit_log": ["<审计事件>"]
      },
      "budget_used": {"steps": 7, "seconds": 940, "calls": 0},
      "exported_event_ids": ["urn:pw:event:<uuid>"],
      "logs": ["<ISO8601>: <事件>"]
    }
  ]
}
```

`verification_level` 含义（v0.1 通常只用到 V0/V1）：
- `V0` 已解析：节点符合 schema，声明有效，可无 Lean 绑定
- `V1` 可复现：有完整 `lean_binding`（含锁定），Lean 核验通过
- `V2` 独立可执行：不同会话重跑 `lean_binding.run` 成功
- `V3` 独立复现：独立 agent 重推并满足独立性披露后一致
- `V4` 多元佐证：多个独立复现且材料多样（模型/代码/站点）

### 2.2 状态派生规则（改自 Proofweave 的"状态是派生的"原则）

**存储的 `status` 只有五个**：`in_progress | success | failed | withdrawn | superseded`。派生引擎按证据计算；`proposed`、`unverified_claim`、`candidate` 是导出视图上的展示标签，不落盘。

| 观察到的证据 | 存储 status | 派生视图标签 |
|---|---|---|
| 节点已创建，尚无 claim | `in_progress` | `proposed` |
| 有 claim，未过 L1 | `in_progress` | `unverified_claim`（阶段 A） |
| 过 L1，无 Lean 绑定 | `in_progress` | `unverified_claim`（阶段 B，报告中列示） |
| 过 L1 + Lean verified | `success` | `success` (V1) |
| 独立重算/复现通过 | `success` | V2/V3 升级 |
| 出现反例/矛盾 | `failed` | `failed`（保留历史） |
| no_go 定理成立（该路线被证明不可能） | `failed` | `failed`（附 no-go 证明来源） |
| counterexample 节点确认 | `failed` | `failed`（附反例数据） |
| 被修订节点取代 | `superseded` | `superseded`（原节点不可再变） |
| agent 明示放弃（经 `logs` 事件） | `withdrawn` | `withdrawn`（保留原因） |

**晋升门（核心约束）**：任何**新节点**（fresh）升为 `success` 的唯一路径（append-only，不做原地变异）；`failed`/`withdrawn` 节点需先经 `revision_of` 生成修订节点，修订节点走同一门：

1. L1 审计通过（`audit.L1_passed=true`）
2. `lean_binding` 存在且含 `lock`
3. `lean_check.py` 四步核验（编译 + `#check` 定理存在 + `#print axioms` 非公理 + 锁定核对，§7.3）返回 verified —— 此步即 L2 审计（Lean 核验），通过后引擎同时置 `audit.L2_passed=true`
4. （可选，V3+）独立复现通过

**L2 是晋升门的硬性要求**：`audit.L2_passed=false` 的节点即使满足 1-3 也不能升级；凡第 3 步通过，引擎必须置 `L2_passed=true`，两者不得出现不一致。

缺任一 → 该修订节点保持存储 `in_progress`，报告中列入"未验证声明"清单，并附缺失原因。

### 2.3 字段归属：证据 vs 派生

半智能化框架不自证：谁写哪个字段必须固定。

**agent 授权写入（证据字段）**：`id`、`revision_of`、`origin`、`source_ref`、`claim`、`result`、`falsification`、`obstacle`、`type`、`mode`、`parent_ids`，以及 `lean_binding` 内的 `theorem/file/run/deny_proofs_axioms/lock`。写入即产生新的 append 事件，历史节点不变。

**引擎独占写入（派生字段）**：`status`、`lean_binding.verified`、`lean_binding.verified_at`、`verification_level`、`audit.L1_passed/L2_passed`、`audit.audit_log`、`budget_used`、`exported_event_ids`。引擎仅在运行核验/审计程序后更新；agent 直接改这些字段视为协议违规（记录 audit_log 事件）。

**共享写入**：`logs`（agent 追加事件，引擎追加审计事件）。追加式，不覆盖。

**放弃信号**：agent 不能在 `status` 上直接写 `withdrawn`。放弃通过向 `logs` 追加 `{"event":"withdraw_request","reason":"<原因>"}` 表达；引擎读到该事件后派生 `withdrawn` 状态并保留原因，原节点历史不变。

**冲突处理**：若 agent 尝试写 `status` 或 `verified`，引擎拒绝并追加 `logs` 事件；派生状态一律以引擎最后计算结果为准。存储 JSON 是所有已接受事件的汇总快照；v0.1 单 agent 场景下，树文件即权威事件记录，不另设事件日志存储。

**`deny_proofs_axioms` 语义**：该字段为 agent 声明的自证标准，但**发现级节点强制为 true**——引擎在 L2 核验时无论该字段值如何，均执行 §7.3 第 3 步的 `#print axioms` 检查；该检查排除定理定义体与证明传递链中任何 axiom/sorry 依赖。字段值 `false` 仅在非发现级节点上允许，且不改变引擎检查行为。

### 2.4 障碍卡片与指纹（§3 共享输入）

`obstacle_card.md` 是三种模式共用的启动输入，字段：

```text
# 障碍卡片 <card-id>
- 目标: <目标命题>
- 障碍陈述: <当前无法越过的最小命题>
- 指纹: <指纹 = 该最小命题的可验证结构签名：量词结构 + 要求对象 + 必须使用的耦合（词汇表见下方"指纹推导规则"）>
- 已排除方法类: <逐个列出并附证明来源(note)>
- 候选开放类: <未被排除、仍有希望的方向>
- 参考节点: <相关探索树节点 id>
```

**指纹推导规则**：指纹不由自由文本生成，而是由 agent 从障碍陈述中提取三要素（量词结构、对象类、耦合），每要素取规范短语；两障碍指纹相同 ⇔ 两障碍可判为同一结构类（用于跨问题复用工具）。v0.1 的三要素规范短语词汇表（允许扩展，扩展需记录在障碍卡片中）：

```text
量词结构: 点态 | 存在 | 全称 | 逐层 | 密度型
对象类: 因子 | 和集 | 盒 | 相对代数性 | 绝对超越性 | 整除性 | 计数
耦合: 跨层 | 自适应 | 无耦合 | 符号保持
```

### 2.5 verification_level 分层（v0.1 范围）

| 级别 | 含义 | v0.1 是否实现 |
|---|---|---|
| V0 | 节点解析通过（schema 校验，可无绑定） | 是 |
| V1 | `lean_binding` 完整且核验通过 | 是（晋升门） |
| V2 | 独立会话重跑 run 成功 | 是（lean_check 支持） |
| V3 | 独立复现 + 独立性披露一致 | v0.2 待决 |
| V4 | 多元佐证（模型/代码/站点多样） | v0.2 待决 |

L3 审计的"突破级"判定标准本身 v0.2 细化（§4 已定义触发/动作/效果）；v0.1 中 L3 可触发，按§4 执行。

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
- 未证明的机制用 `hypothesis` 类型 + `in_progress` 状态存储，派生视图标签为 `candidate`（不落盘，见 §2.2），绝不声称定理
- 候选升级为定理必须过晋升门

---

## 4. 审计门（所有模式强制）

| 级别 | 触发 | 动作 | 通过后状态 |
|---|---|---|---|
| L1 合理性 | 任何新结论 | 反向检查、边界测试、小窗口对照 | `audit.L1_passed=true`（存储仍为 in_progress，视图标签 unverified_claim-B） |
| L2 独立验证 | 候选升级为"发现" | 发现级节点强制 Lean 双重核验（§7.3）；独立重算/不同实现交叉仅作为补充证据（不替代 Lean） | `success` (V1) |
| L3 完整审计 | 声称突破/证明 | 完整审查 + 用户确认；结论标记经 `audit_log` 事件记录 | 标记"突破级"，需用户签字 |

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

- 节点颜色：绿=success，红=failed，灰=withdrawn，黄=in_progress，蓝=superseded（虚线边框）
- `unverified_claim` 视图：in_progress 节点中未过 L1 的用实心黄，过 L1 但无 Lean 绑定的用空心黄（报告中两类分开列示）
- 节点形状：方形=certificate，圆圈=假设/候选，菱形=no-go/反例
- 点击展开详情（claim/result/lean_binding/audit）
- Lean 绑定徽章：绿色徽章 + 跳转源文件
- 过滤：按模式、按状态、按 Lean 绑定、失败路径默认可见 + "仅看失败"模式
- D3 以 CDN 引入，JSON 数据内嵌单文件

### 7.3 Lean 复现 (`lean_check.py`)

`lake build` 只证明文件编译；要证明"定理已证明"必须做双重核验：

```sh
# 复现节点 <id> 的结论（双重核验）
lean_check.py verify <tree.json> <node-id>
```

核验程序固定执行以下步骤，任一失败 → `verified=false`，节点锁在 `in_progress`：

1. **编译**：执行 `lake build lean/<file>.lean`（等价于 `lean_binding.run` 的编译部分），退出码 0 才继续。
2. **定理存在性**：在编译后的环境中执行 `#check <theorem>` 探针（`lean --run` 或注入探针文件），确认 `<theorem>` 声明存在。
3. **非公理检查**：对定理声明执行 `#print axioms <theorem>` 探针，确认输出为空（无任何依赖 axiom；`deny_proofs_axioms` 在发现级节点无条件强制 true，见 §2.3）。若输出非空（定理本身是 `axiom`，或证明传递链依赖了 axiom/sorry），即使编译通过也判定未验证。注意：Lean 4 的 `#print <theorem>` 只输出类型，不提供依赖列表；依赖检查必须用 `#print axioms`。
4. **锁定核对**：校验 `lean_binding.lock.toolchain` 与当前 `lean-toolchain` 内容一致，`lake_manifest_ref` 指向的文件存在（内容摘要可选）。

核验结果（通过/失败 + 时间戳）由引擎写入 `lean_binding.verified/verified_at`，进入 audit_log。V2 由不同会话重跑同一 `run` 得到，记为独立执行证据。

---

## 8. Proofweave 集成（协议兼容导出）

M3 本地运行，不实现 Proofweave 协议本身。导出器 `export_pw.py` 将探索树转为兼容事件流，供后续接入 Proofweave 节点。

**权威参考**：Proofweave 协议文档与其 `proofweave-core.schema.json` 是导出正确性的外部基准。v0.1 交付时需将这两份文件纳入仓库（`references/proofweave-protocol-v0.1.md` 与 `references/proofweave-core.schema.json`）——它们不是可选附件，而是导出器测试的固定基准。获取源：用户本地已有副本（见设计背景），实施时从该处复制进仓库；若用户未提供，则使用 `https://proofweave.org/spec/0.1/` 公开 URL。

### 预演映射

| M3 探索树元素 | Proofweave 事件 |
|---|---|
| 根节点 + 障碍卡片 | `project.create` + `synthesis.publish` |
| success 节点（Lean 已验证） | `claim.publish` + `bundle.publish`（执行契约 = `lean_binding.run`，即 `lake build` + `lean_check.py` 核验命令） |
| 审计门 L2 通过 | `verification.submit` (mode=`exact_bundle`/`ci_replay`) |
| counterexample / no_go 节点 | `challenge.open` 或 empirical claim |
| failed / withdrawn 节点 | `claim.withdraw` / `challenge.resolve`（append-only） |

### 吸收的核心原则

1. **状态派生**：作者写入证据，状态由核验事件派生（§2.2）。
2. **append-only**：修订链 `revision_of`，永不经编辑删除。
3. **负面结果一等**：失败节点导出为 challenge/withdraw，不丢失。
4. **可执行研究包**：成功节点的 `lean_binding.run`（`lake build` + 定理核验）即 bundle 执行契约。

---

## 8b. 现有工作导入与可证明内容上传

### 8b.1 导入器 `import_workspace.py`

**目标**：把既有数学工作（研究日志、Lean 定理文件）结构化导入探索树，作为新搜索的起点上下文。

**实施方式**：自动解析 + 人工审核。单个试点先行（Erdős–Straus，其研究结构最完整），验证流程后扩展到其他方向。

**解析来源**（试点）：
- `erdos_straus/research_log.md`（按「##」小节目录提取）——各小节映射为 `hypothesis`/`certificate`/`no_go`/`counterexample` 节点
- `lean/ErdosStraus.lean`、`ErdosStrausTail.lean`、`ErdosStrausNearQuarter.lean`——提取 `theorem`/`lemma` 声明名，绑定为 `certificate` 节点
- 文档中明确标注为「反例」「局部」「未解决」「障碍」的小节 → `no_go`/`counterexample`/`hypothesis` 节点

**导入流程**：
```sh
import_workspace.py scan    # 扫描来源，生成候选节点清单（不写树）
import_workspace.py draft   # 生成草稿树（待审）
# 人工审核后：
import_workspace.py commit <draft-tree>  # 写入正式探索树
```

**扫描规则（试点）**：研究日志中以下模式分别映射为节点类型：
- `Lean 定理名`（反引号包裹）→ `certificate`
- 「反例」「回归」「counterexample」「失败」→ `counterexample`
- 「no-go」「不被整除」「不可能」「排除」→ `no_go`
- 「必要条件」「尚未」「开放」「无法」「障碍」→ `hypothesis`（含说明性 result）
- 「已证明」「机器核验」「formalize」「machine-checked」→ `certificate`（附带来源文档引用）

每个导入节点自动继承 `parent_ids`（父子按原文档章节层级），写入 `source_ref`（文档路径+小节目录），标记 `origin: "legacy"` 以便可视化/筛选区分，并填 `obstacle` 三要素（§2.4 词汇表）。

**导入节点的验证门槛（同晋升门）**：导入的历史工作不继承原文档的"成功"状态。规则：
- 有可核验的 Lean 绑定（`lean/` 中真实存在的定理名）→ `in_progress`，运行 `lean_check.py` 核验，通过 → `success`，对应 `verification_level` 至少 V1
- 无 Lean 绑定或绑定核验失败 → 保持 `in_progress`（视图标签 `unverified_claim-B`），列入报告"未验证声明"
- 明确标为反例/no-go 的节点 → 直接 `failed`（附原文证据），即使无 Lean 绑定也记录，但**不得**升为 success

`origin: "legacy"` 的节点在编辑器与可视化中统一加「遗留」标签，不与新搜索节点混淆，但共享同一状态派生与晋升门。

### 8b.2 上传器 `upload_proofs.py`

**目标**：把探索树的"可证明内容"（成功节点）归档到本地可复现目录，保证任何人可离线查看、重跑、审计。

**过滤标准（仅已验证节点）**：只有 `status=success` 且满足全部条件的节点可上传：
- `audit.L1_passed=true` 且 `audit.L2_passed=true`
- `lean_binding` 完整（theorem/file/run/lock）
- `lean_check.py verify` 当前返回 verified（上传前重新核验，过期即拒传）
- `verification_level >= V1`

失败、撤回、`in_progress`、无 Lean 绑定的节点一律不上传——它们只留在探索树中供查看。这保证"上传内容可证明"：目录里的每个条目都能被独立重跑验证。

**上传布局**：
```text
output/uploads/<tree-id>/
├── README.md                       # 目录索引：节点清单、核验状态、复现说明
├── proofs/
│   ├── <node-id>/                  # 每个成功节点
│   │   ├── claim.md                # 声明 + 障碍指纹 + 证据
│   │   ├── proof.lean              # Lean 源文件（快照副本）
│   │   ├── run.sh                  # lean_binding.run 复现命令
│   │   ├── lock.json               # 锁定（toolchain/lake-manifest）
│   │   └── verify.json             # lean_check.py 核验结果（时间戳+指纹）
├── tree-subgraph.json              # 成功节点及其事故父节点子图（失败上下文可查看）
└── manifest.json                   # 上传清单：节点 id、定理名、摘要、时间
```

**上传流程**：
```sh
upload_proofs.py status     # 列出可上传/不可上传及原因
upload_proofs.py upload <tree.json>  # 重新核验 → 写入 output/uploads/<tree-id>/
upload_proofs.py verify <tree-id>    # 复核归档中所有 proof.lean 可重跑
```

**审计一致性**：上传前重新跑 `lean_check.py`；上传完成后生成 `verify.json` 存回树节点的 `exported_event_ids`（或新增 `uploaded_at` 时间戳字段）。归档内容再次变化时，原始探索树仍是权威——归档只是导出快照。

---

## 9. 框架自身验证策略

1. **Schema 校验**：生成树用 JSON Schema 严格校验（`tree_schema.json`，v0.1 交付物）。
2. **协议演练测试**：三个合成问题（一个可解、一个已知 no-go、一个开放）跑完整会话，检查：
   - 树完整性（全节点保留、修订链正确）
   - 晋升门执行（无 Lean 绑定或定理为 axiom 的节点不能成为 success；`L2_passed` 与 verified 一致）
   - 预算纪律（无超支、无无限循环，`budget_used` 单位明确且与 `budgets.units` 对齐）
   - 可视化完整性（全节点出现，失败可见，superseded 有独立样式）
   - 导出正确性（事件流字段映射对照 `references/` 中的 Proofweave 协议文档与其 `proofweave-core.schema.json` 校验，不以自身映射表为唯一依据）
   - **导入正确性（新增）**：用 `erdos_straus/` 真实文件跑 `import_workspace.py scan/draft/commit`，核对：(a) 节点数与文档小节数一致；(b) 反例/no-go 正确标记；(c) Lean 定理绑定名与 `lean/` 中真实声明一致；(d) 无 Lean 绑定节点不误升 success
   - **上传正确性（新增）**：对一个合成 success 节点跑 `upload_proofs.py upload`，核对归档中 `proof.lean` 可复现、`verify.json` 与 `lean_check.py` 结果一致、非 success 节点未进入归档
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
- 现有工作导入：自动解析+人工审核，试点（Erdős–Straus）先行，导入节点同过晋升门，标记 `origin:"legacy"`
- 可证明内容上传：仅已验证节点（success + L1/L2 + Lean verified），上传本地可复现归档 `output/uploads/`

**待决**（v0.2 / 接入期）：
- Proofweave 签名/哈希/节点接入的具体实现
- V3+ 独立复现的"独立性"判定标准
- L3 审计的"突破级"定义细则（v0.1 中 L3 可触发，按 §4 执行）
- 导入扩展到其他三方向的自动化程度（试点流程验证后定）