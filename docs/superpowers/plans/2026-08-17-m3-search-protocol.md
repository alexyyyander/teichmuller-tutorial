# M3 三模式数学搜索协议 Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 实现 M3 协议的可执行技能包——探索树数据模型、Lean 核验、状态派生引擎、现有工作导入、可证明内容上传、D3 可视化、Proofweave 导出，以及主协议与三模式文档。

**Architecture:** `skills/math-search/` 下分四层：`orchestrator/`（脚本 + JSON Schema + 共享 `tree_lib`）、`modes/`（三模式子协议）、`templates/`（障碍卡片/报告模板）、`SKILL.md`（主协议）。核心不变量：探索树 append-only JSON 是唯一真实来源；`audit_gate.py` 状态派生引擎独占写引擎字段；`lean_check.py` 四步核验是成功晋升的唯一门。

**Tech Stack:** Python 3.13 + pytest 9 + jsonschema 4.23、Lean 4 (v4.31.0-rc1) + Lake、标准库（json/re/subprocess/uuid/datetime）、D3.js（CDN 引入，单文件 HTML）。

**Spec:** `docs/superpowers/specs/2026-08-17-m3-search-protocol-design.md`

**工作目录约定：**
- 源码仓库根：`/Users/alexyu/Documents/ChatGPT/math`
- Lean 工程：`lean/`（`lakefile.lean` 的 `srcDir := "lean"`，模块名 = 文件名去扩展名）
- 试点导入数据：`erdos_straus/research_log.md`、`lean/ErdosStraus.lean` 等
- 上线目录：`output/uploads/`
- 测试目录：`skills/math-search/tests/`

---

## Chunk 1: 骨架与树数据模型

### Task 1.1: 包骨架与测试基础设施

**Files:**
- Create: `skills/math-search/orchestrator/__init__.py`
- Create: `skills/math-search/tests/__init__.py`
- Create: `skills/math-search/tests/conftest.py`
- Create: `skills/math-search/pyproject.toml`

- [ ] **Step 1: 建目录与空 `__init__.py`**

```bash
mkdir -p skills/math-search/orchestrator skills/math-search/tests skills/math-search/modes skills/math-search/templates references
touch skills/math-search/orchestrator/__init__.py skills/math-search/tests/__init__.py
```

- [ ] **Step 2: 写 `conftest.py` 提供共享 fixture**

`skills/math-search/tests/conftest.py`:
```python
import json
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture
def sample_node():
    """一个最小的合法探索树节点（无 Lean 绑定，in_progress）。"""
    return {
        "id": "urn:m3:node:test-01",
        "revision_of": None,
        "parent_ids": [],
        "origin": "search",
        "source_ref": None,
        "type": "hypothesis",
        "mode": "computation",
        "status": "in_progress",
        "obstacle": {"fingerprint": "点态 | 因子 | 自适应", "excluded_methods": [], "required_coupling": "跨层"},
        "claim": "测试命题",
        "result": "",
        "falsification": None,
        "lean_binding": None,
        "verification_level": "V0",
        "audit": {"L1_passed": False, "L2_passed": False, "audit_log": []},
        "budget_used": {"steps": 0, "seconds": 0, "calls": 0},
        "exported_event_ids": [],
        "uploaded_at": None,
        "logs": [],
    }


@pytest.fixture
def sample_tree(sample_node):
    return {
        "root": "urn:m3:tree:test",
        "session": {
            "target": "测试目标",
            "obstacle_card_ref": "templates/obstacle_card_test.md",
            "interaction_policy": "autonomous",
            "budgets": {
                "computation": {"units": "steps", "cap": 100},
                "tool_discovery": {"units": "steps", "cap": 100},
                "invention": {"units": "seconds", "cap": 100},
            },
        },
        "nodes": [sample_node],
    }


@pytest.fixture
def tree_path(tmp_path, sample_tree):
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(sample_tree, ensure_ascii=False, indent=2))
    return str(p)


@pytest.fixture
def repo_root():
    """Lean 工程根（lean-toolchain / lake-manifest.json 所在目录）。"""
    return Path("/Users/alexyu/Documents/ChatGPT/math")


@pytest.fixture
def repo_lock(repo_root):
    """与仓库实际锁定一致的 lean_binding.lock（供 lean_check 测试使用）。"""
    return {
        "toolchain": repo_root.joinpath("lean-toolchain").read_text(encoding="utf-8").strip(),
        "lake_manifest_ref": str(repo_root / "lake-manifest.json"),
    }


@pytest.fixture
def lean_toolchain_path(repo_root):
    return str(repo_root / "lean-toolchain")
```

- [ ] **Step 3: 写 `pyproject.toml`**

`skills/math-search/pyproject.toml`:
```toml
[tool.pytest.ini_options]
testpaths = ["tests"]
pythonpath = ["orchestrator"]
```

- [ ] **Step 4: 运行 pytest 验证骨架**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/ -v`
Expected: 无测试（退出码 5 属正常）或 0 passed

- [ ] **Step 5: 复制 Proofweave 基准进 `references/`**

```bash
cp "/Users/alexyu/Library/Mobile Documents/com~apple~CloudDocs/Documents/Codex/2026-07-12/wo-ren/outputs/proofweave-protocol-v0.1.md" references/proofweave-protocol-v0.1.md
cp "/Users/alexyu/Library/Mobile Documents/com~apple~CloudDocs/Documents/Codex/2026-07-12/wo-ren/outputs/proofweave-core.schema.json" references/proofweave-core.schema.json
```
路径不存在则从 `https://proofweave.org/spec/0.1/` 拉取；都失败则跳过并记录待决。

- [ ] **Step 6: Commit**

```bash
git add skills/ references/
git commit -m "chore: 建立 M3 skill 骨架、测试基础设施与 Proofweave 基准引用"
```

### Task 1.2: `tree_schema.json` — 探索树 JSON Schema

**Files:**
- Create: `skills/math-search/orchestrator/tree_schema.json`
- Test: `skills/math-search/tests/test_tree_schema.py`

严格 JSON Schema（draft 2020-12）：顶层 root/session/nodes；node 必含 §2.1 全部字段；条件约束：legacy⇒source_ref、success⇒lean_binding 存在。

- [ ] **Step 1: 写失败测试**

`skills/math-search/tests/test_tree_schema.py`:
```python
import json
from pathlib import Path

import pytest
import jsonschema

SCHEMA_PATH = Path(__file__).resolve().parents[1] / "orchestrator" / "tree_schema.json"


def load_schema():
    return json.loads(SCHEMA_PATH.read_text())


def test_valid_sample_tree_passes(sample_tree):
    jsonschema.validate(sample_tree, load_schema())


def test_missing_required_field_fails(sample_tree):
    node = sample_tree["nodes"][0]
    for field in ["id"]:
        bad = {k: v for k, v in node.items() if k != field}
        with pytest.raises(jsonschema.ValidationError):
            jsonschema.validate({"root": sample_tree["root"], "session": sample_tree["session"], "nodes": [bad]}, load_schema())


def test_legacy_requires_source_ref(sample_tree):
    node = dict(sample_tree["nodes"][0])
    node["origin"] = "legacy"
    node["source_ref"] = None
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate({"root": sample_tree["root"], "session": sample_tree["session"], "nodes": [node]}, load_schema())


def test_success_requires_lean_binding(sample_tree):
    node = dict(sample_tree["nodes"][0])
    node["status"] = "success"
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate({"root": sample_tree["root"], "session": sample_tree["session"], "nodes": [node]}, load_schema())
```

- [ ] **Step 2: 运行测试确认失败（schema 文件不存在）**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_tree_schema.py -v`
Expected: 失败（`FileNotFoundError`）

- [ ] **Step 3: 写 `tree_schema.json`**

用下述完整 JSON（包含 node allOf 条件：legacy⇒source_ref、success⇒lean_binding 对象）写入文件（字段源自 spec §2.1 全部字段）：

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://m3.local/schema/tree.schema.json",
  "title": "M3 Exploration Tree",
  "type": "object",
  "required": ["root", "session", "nodes"],
  "additionalProperties": false,
  "properties": {
    "root": {"type": "string", "minLength": 1},
    "session": {
      "type": "object",
      "required": ["target", "obstacle_card_ref", "interaction_policy", "budgets"],
      "additionalProperties": false,
      "properties": {
        "target": {"type": "string"},
        "obstacle_card_ref": {"type": "string"},
        "interaction_policy": {"enum": ["confirm_at_nodes", "autonomous"]},
        "budgets": {
          "type": "object",
          "additionalProperties": {
            "type": "object",
            "required": ["units", "cap"],
            "additionalProperties": false,
            "properties": {
              "units": {"enum": ["steps", "seconds", "calls"]},
              "cap": {"type": "number", "minimum": 0}
            }
          }
        }
      }
    },
    "nodes": {"type": "array", "items": {"$ref": "#/$defs/node"}}
  },
  "$defs": {
    "node": {
      "type": "object",
      "required": [
        "id", "revision_of", "parent_ids", "origin", "source_ref", "type",
        "mode", "status", "obstacle", "claim", "result", "falsification",
        "lean_binding", "verification_level", "audit", "budget_used",
        "exported_event_ids", "uploaded_at", "logs"
      ],
      "additionalProperties": false,
      "properties": {
        "id": {"type": "string", "pattern": "^urn:m3:node:"},
        "revision_of": {"type": ["string", "null"]},
        "parent_ids": {"type": "array", "items": {"type": "string"}, "uniqueItems": true},
        "origin": {"enum": ["search", "legacy"]},
        "source_ref": {"type": ["string", "null"]},
        "type": {"enum": ["hypothesis", "tool_candidate", "certificate", "no_go", "counterexample"]},
        "mode": {"enum": ["computation", "tool_discovery", "invention"]},
        "status": {"enum": ["in_progress", "success", "failed", "withdrawn", "superseded"]},
        "obstacle": {
          "type": "object",
          "required": ["fingerprint", "excluded_methods", "required_coupling"],
          "additionalProperties": false,
          "properties": {
            "fingerprint": {"type": "string"},
            "excluded_methods": {"type": "array", "items": {"type": "string"}},
            "required_coupling": {"type": "string"}
          }
        },
        "claim": {"type": "string"},
        "result": {"type": "string"},
        "falsification": {"type": ["string", "null"]},
        "lean_binding": {
          "type": ["object", "null"],
          "required": ["theorem", "file", "run", "deny_proofs_axioms", "lock", "verified", "verified_at"],
          "additionalProperties": false,
          "properties": {
            "theorem": {"type": "string"},
            "file": {"type": "string"},
            "run": {"type": "string"},
            "deny_proofs_axioms": {"type": "boolean"},
            "lock": {
              "type": "object",
              "required": ["toolchain", "lake_manifest_ref"],
              "additionalProperties": false,
              "properties": {
                "toolchain": {"type": "string"},
                "lake_manifest_ref": {"type": "string"}
              }
            },
            "verified": {"type": "boolean"},
            "verified_at": {"type": ["string", "null"]}
          }
        },
        "verification_level": {"enum": ["V0", "V1", "V2", "V3", "V4"]},
        "audit": {
          "type": "object",
          "required": ["L1_passed", "L2_passed", "audit_log"],
          "additionalProperties": false,
          "properties": {
            "L1_passed": {"type": "boolean"},
            "L2_passed": {"type": "boolean"},
            "audit_log": {"type": "array", "items": {"type": "string"}}
          }
        },
        "budget_used": {
          "type": "object",
          "required": ["steps", "seconds", "calls"],
          "additionalProperties": false,
          "properties": {
            "steps": {"type": "number", "minimum": 0},
            "seconds": {"type": "number", "minimum": 0},
            "calls": {"type": "number", "minimum": 0}
          }
        },
        "exported_event_ids": {"type": "array", "items": {"type": "string"}, "uniqueItems": true},
        "uploaded_at": {"type": ["string", "null"]},
        "logs": {"type": "array", "items": {"type": "string"}}
      },
      "allOf": [
        {"if": {"properties": {"origin": {"const": "legacy"}}},
         "then": {"required": ["source_ref"], "properties": {"source_ref": {"minLength": 1}}}},
        {"if": {"properties": {"status": {"const": "success"}}},
         "then": {"properties": {"lean_binding": {"type": "object"}}}}
      ]
    }
  }
}
```

- [ ] **Step 4: 运行测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_tree_schema.py -v`
Expected: 4 passed

- [ ] **Step 5: Commit**

```bash
git add skills/math-search/orchestrator/tree_schema.json skills/math-search/tests/test_tree_schema.py
git commit -m "feat: 探索树 JSON Schema 与校验测试"
```

### Task 1.3: `tree_lib.py` — 树数据模型

**Files:**
- Create: `skills/math-search/orchestrator/tree_lib.py`
- Test: `skills/math-search/tests/test_tree_lib.py`

职责：load/save/validate 树；构造节点；append 日志；引擎字段守卫；派生视图标签（§2.2）。

- [ ] **Step 1: 写失败测试**

`skills/math-search/tests/test_tree_lib.py`:
```python
import json

import pytest

from tree_lib import (
    ENGINE_FIELDS,
    TreeError,
    add_log,
    derive_view_label,
    guard_engine_write,
    load_tree,
    new_node,
    new_tree,
    save_tree,
    validate_tree,
)


def test_new_node_has_all_required_fields():
    node = new_node(node_id="urn:m3:node:n1")
    for field in ["id", "revision_of", "parent_ids", "origin", "source_ref", "type",
                  "mode", "status", "obstacle", "claim", "result", "falsification",
                  "lean_binding", "verification_level", "audit", "budget_used",
                  "exported_event_ids", "uploaded_at", "logs"]:
        assert field in node


def test_new_node_defaults():
    node = new_node(node_id="urn:m3:node:default")
    assert node["status"] == "in_progress"
    assert node["origin"] == "search"
    assert node["verification_level"] == "V0"
    assert node["audit"] == {"L1_passed": False, "L2_passed": False, "audit_log": []}
    assert node["budget_used"] == {"steps": 0, "seconds": 0, "calls": 0}


def test_new_tree_structure():
    tree = new_tree(root="urn:m3:tree:new", target="目标", obstacle_card_ref="card.md")
    assert tree["root"] == "urn:m3:tree:new"
    assert tree["session"]["interaction_policy"] == "confirm_at_nodes"
    assert tree["nodes"] == []
    validate_tree(tree)


def test_load_save_roundtrip(tree_path, sample_tree):
    loaded = load_tree(tree_path)
    assert loaded == sample_tree
    save_tree(loaded, tree_path)
    assert load_tree(tree_path) == sample_tree


def test_load_missing_file_raises(tmp_path):
    with pytest.raises(FileNotFoundError):
        load_tree(str(tmp_path / "nope.json"))


def test_validate_rejects_bad_tree(sample_tree):
    bad = dict(sample_tree)
    bad["nodes"][0] = {k: v for k, v in bad["nodes"][0].items() if k != "id"}
    with pytest.raises(TreeError):
        validate_tree(bad)


def test_add_log_appends_timestamped():
    from tree_lib import new_node
    node = new_node(node_id="urn:m3:node:l")
    add_log(node, {"event": "claim", "text": "x"})
    assert len(node["logs"]) == 1
    assert node["logs"][0].startswith("20")
    assert '"event": "claim"' in node["logs"][0]


def test_withdraw_request_event():
    node = new_node(node_id="urn:m3:node:w")
    add_log(node, {"event": "withdraw_request", "reason": "放弃"})
    assert "withdraw_request" in node["logs"][0]


def test_guard_engine_write_rejects_status():
    with pytest.raises(TreeError) as exc:
        guard_engine_write({"status": "success"})
    assert "status" in str(exc.value)


def test_guard_engine_write_rejects_nested_verified():
    with pytest.raises(TreeError):
        guard_engine_write({"lean_binding": {"verified": True}})


def test_guard_engine_write_allows_evidence_fields():
    guard_engine_write({"claim": "ok", "origin": "legacy", "source_ref": "x.md", "type": "hypothesis"})


def test_derive_view_labels(sample_node):
    node = dict(sample_node)
    node["claim"] = ""  # 无 claim → proposed
    assert derive_view_label(node) == "proposed"
    node["claim"] = "命题"
    assert derive_view_label(node) == "unverified_claim-A"
    node["audit"] = {"L1_passed": True, "L2_passed": False, "audit_log": []}
    assert derive_view_label(node) == "unverified_claim-B"
    node["status"] = "success"
    assert derive_view_label(node) == "success"
    node["status"] = "failed"
    assert derive_view_label(node) == "failed"
    node["status"] = "withdrawn"
    assert derive_view_label(node) == "withdrawn"
    node["status"] = "superseded"
    assert derive_view_label(node) == "superseded"


def test_derive_view_candidate(sample_node):
    node = dict(sample_node)
    node["mode"] = "invention"
    node["type"] = "hypothesis"
    node["claim"] = "机制候选"
    node["audit"] = {"L1_passed": True, "L2_passed": False, "audit_log": []}
    assert derive_view_label(node) == "candidate"


def test_engine_fields_exported():
    assert "status" in ENGINE_FIELDS
```

- [ ] **Step 2: 运行测试确认失败**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_tree_lib.py -v`
Expected: FAIL（`ModuleNotFoundError: tree_lib`）

- [ ] **Step 3: 写实现**

`skills/math-search/orchestrator/tree_lib.py`:
```python
"""M3 探索树数据模型。

职责：load/save/validate 树；构造节点；append 日志；引擎字段写入守卫；
派生视图标签（§2.2）。
"""

import json
from datetime import datetime, timezone
from pathlib import Path

import jsonschema

SCHEMA_PATH = Path(__file__).parent / "tree_schema.json"
SCHEMA = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))

ENGINE_FIELDS = frozenset({
    "status", "verification_level", "uploaded_at", "budget_used", "exported_event_ids",
})
ENGINE_NESTED_PATHS = frozenset({
    ("lean_binding", "verified"),
    ("lean_binding", "verified_at"),
    ("audit", "L1_passed"),
    ("audit", "L2_passed"),
    ("audit", "audit_log"),
})

DEFAULT_STATUS = "in_progress"
ALLOWED_TYPES = ("hypothesis", "tool_candidate", "certificate", "no_go", "counterexample")
ALLOWED_MODES = ("computation", "tool_discovery", "invention")


class TreeError(Exception):
    """探索树协议错误（schema 校验失败 / 引擎字段违规）。"""


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"


def validate_tree(tree: dict) -> None:
    try:
        jsonschema.validate(tree, SCHEMA)
    except jsonschema.ValidationError as exc:
        raise TreeError(f"探索树 schema 校验失败: {exc.message} at {list(exc.absolute_path)}")


def load_tree(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as fh:
        tree = json.load(fh)
    validate_tree(tree)
    return tree


def save_tree(tree: dict, path: str) -> None:
    validate_tree(tree)
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(tree, fh, ensure_ascii=False, indent=2)


def new_node(node_id: str, parent_ids=None, origin: str = "search", source_ref=None,
             node_type: str = "hypothesis", mode: str = "computation",
             obstacle=None, claim: str = "", result: str = "") -> dict:
    if origin not in ("search", "legacy"):
        raise TreeError(f"非法 origin: {origin}")
    if node_type not in ALLOWED_TYPES:
        raise TreeError(f"非法 type: {node_type}")
    if mode not in ALLOWED_MODES:
        raise TreeError(f"非法 mode: {mode}")
    return {
        "id": node_id,
        "revision_of": None,
        "parent_ids": list(parent_ids or []),
        "origin": origin,
        "source_ref": source_ref,
        "type": node_type,
        "mode": mode,
        "status": DEFAULT_STATUS,
        "obstacle": obstacle or {"fingerprint": "", "excluded_methods": [], "required_coupling": ""},
        "claim": claim,
        "result": result,
        "falsification": None,
        "lean_binding": None,
        "verification_level": "V0",
        "audit": {"L1_passed": False, "L2_passed": False, "audit_log": []},
        "budget_used": {"steps": 0, "seconds": 0, "calls": 0},
        "exported_event_ids": [],
        "uploaded_at": None,
        "logs": [],
    }


def new_tree(root: str, target: str, obstacle_card_ref: str,
             interaction_policy: str = "confirm_at_nodes", budgets=None) -> dict:
    if interaction_policy not in ("confirm_at_nodes", "autonomous"):
        raise TreeError(f"非法 interaction_policy: {interaction_policy}")
    default_budgets = {
        "computation": {"units": "steps", "cap": 1000},
        "tool_discovery": {"units": "steps", "cap": 400},
        "invention": {"units": "seconds", "cap": 3600},
    }
    return {
        "root": root,
        "session": {
            "target": target,
            "obstacle_card_ref": obstacle_card_ref,
            "interaction_policy": interaction_policy,
            "budgets": budgets or default_budgets,
        },
        "nodes": [],
    }


def add_log(node: dict, event: dict) -> None:
    node["logs"].append(f"{_now_iso()} {json.dumps(event, ensure_ascii=False)}")


def guard_engine_write(payload: dict) -> None:
    """拒绝 agent 直接写引擎字段（§2.3）。"""
    for key, value in payload.items():
        if value is not None:
            if key in ENGINE_FIELDS:
                raise TreeError(f"引擎字段 {key} 不能由 agent 写入")
            if isinstance(value, dict):
                for nested_key in value:
                    if (key, nested_key) in ENGINE_NESTED_PATHS:
                        raise TreeError(f"引擎字段 {key}.{nested_key} 不能由 agent 写入")


def derive_view_label(node: dict) -> str:
    """按 §2.2 计算派生视图标签（不落盘）。"""
    status = node.get("status", DEFAULT_STATUS)
    if status in ("success", "failed", "withdrawn", "superseded"):
        return status
    claim = (node.get("claim") or "").strip()
    if not claim:
        return "proposed"
    l1 = node.get("audit", {}).get("L1_passed", False)
    if not l1:
        return "unverified_claim-A"
    binding = node.get("lean_binding")
    verified = bool(binding and binding.get("verified"))
    if not verified and node.get("mode") == "invention" and node.get("type") == "hypothesis":
        return "candidate"
    if not verified:
        return "unverified_claim-B"
    return "success"


def main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description="M3 探索树工具")
    sub = parser.add_subparsers(dest="cmd", required=True)
    pn = sub.add_parser("new", help="建树")
    pn.add_argument("--root", default="urn:m3:tree:new")
    pn.add_argument("--target", required=True)
    pn.add_argument("--obstacle-card", required=True)
    pn.add_argument("-o", "--out", required=True)
    pv = sub.add_parser("validate", help="校验树")
    pv.add_argument("tree")
    args = parser.parse_args(argv)
    if args.cmd == "new":
        tree = new_tree(args.root, args.target, args.obstacle_card)
        save_tree(tree, args.out)
        print(f"建树 → {args.out}")
    elif args.cmd == "validate":
        load_tree(args.tree)
        print("OK")


if __name__ == "__main__":
    main()
```

- [ ] **Step 4: 运行测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_tree_lib.py -v`
Expected: 全部 passed

- [ ] **Step 5: Commit**

```bash
git add skills/math-search/orchestrator/tree_lib.py skills/math-search/tests/test_tree_lib.py
git commit -m "feat: 探索树数据模型（构建/读写/守卫/视图标签）"
```

---

## Chunk 2: Lean 核验 `lean_check.py`

### Task 2.1: `lean_check.py` — 四步核验

**Files:**
- Create: `skills/math-search/orchestrator/lean_check.py`
- Test: `skills/math-search/tests/test_lean_check.py`

四步（§7.3）：编译（`lake build`）、`#check` 定理存在、`#print axioms` 非公理（白名单）、锁定核对。运行可注入 `run_cmd` 以隔离测试。

- [ ] **Step 1: 探测真实 Lean 输出（确定白名单）**

```bash
cd /Users/alexyu/Documents/ChatGPT/math
printf 'import Mathlib\n#check Nat.add_comm\n#print axioms Nat.add_comm\n' > /tmp/m3probe.lean
lake env lean /tmp/m3probe.lean
printf 'axiom my_axiom : False\ntheorem bad : False := my_axiom\n#print axioms bad\n' > /tmp/m3probe2.lean
lake env lean /tmp/m3probe2.lean
```
记录实际输出，用于校准 `ALLOWED_AXIOMS` 与解析函数。若 `#print axioms` 对标准定理输出含 `propext`/`Classical.choice`/`funext` 等，加入白名单；用户自定义 `my_axiom` 必须在输出中出现（应判未通过）。

- [ ] **Step 2: 写失败测试**

`skills/math-search/tests/test_lean_check.py`:
```python
import json

import pytest

import lean_check
from tree_lib import new_tree


class FakeResult:
    def __init__(self, returncode=0, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def verified_node(repo_lock):
    from tree_lib import new_node
    n = new_node(node_id="urn:m3:node:ok", type="certificate", mode="computation", claim="c")
    n["audit"] = {"L1_passed": True, "L2_passed": False, "audit_log": []}
    n["lean_binding"] = {
        "theorem": "Nat.add_comm",
        "file": "lean/Foo.lean",
        "run": "lake build lean/Foo.lean && lean_check.py probe --file lean/Foo.lean --theorem Nat.add_comm",
        "deny_proofs_axioms": True,
        "lock": dict(repo_lock),
        "verified": False,
        "verified_at": None,
    }
    return n


def write_tree(tmp_path, node):
    tree = new_tree(root="urn:m3:tree:t", target="t", obstacle_card_ref="c.md")
    tree["nodes"] = [node]
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(tree, ensure_ascii=False, indent=2))
    return str(p)


def test_verify_all_steps_pass(tmp_path, monkeypatch, repo_lock, lean_toolchain_path):
    calls = []

    def fake_run(cmd):
        calls.append(tuple(cmd))
        if cmd[:2] == ("lake", "build"):
            return FakeResult(0, "", "")
        # lean probe
        return FakeResult(0, "Nat.add_comm : ...\npropext\nClassical.choice\n", "")

    p = write_tree(tmp_path, verified_node(repo_lock))
    monkeypatch.setattr(lean_check, "_default_run_cmd", lambda c: fake_run(c))
    res = lean_check.verify_node(p, "urn:m3:node:ok", toolchain_path=lean_toolchain_path)
    assert res["verified"] is True


def test_fail_on_compile_error(tmp_path, monkeypatch, repo_lock, lean_toolchain_path):
    def fake_run(cmd):
        if cmd[:2] == ("lake", "build"):
            return FakeResult(1, "", "error")
        return FakeResult(0, "Nat.add_comm : ...\npropext\n", "")
    p = write_tree(tmp_path, verified_node(repo_lock))
    monkeypatch.setattr(lean_check, "_default_run_cmd", lambda c: fake_run(c))
    res = lean_check.verify_node(p, "urn:m3:node:ok", toolchain_path=lean_toolchain_path)
    assert res["verified"] is False
    assert "compile" in res["failed_steps"]


def test_fail_when_theorem_missing(tmp_path, monkeypatch, repo_lock, lean_toolchain_path):
    def fake_run(cmd):
        if cmd[:2] == ("lake", "build"):
            return FakeResult(0, "", "")
        return FakeResult(0, "", "unknown identifier 'Nat.add_comm'")
    p = write_tree(tmp_path, verified_node(repo_lock))
    monkeypatch.setattr(lean_check, "_default_run_cmd", lambda c: fake_run(c))
    res = lean_check.verify_node(p, "urn:m3:node:ok", toolchain_path=lean_toolchain_path)
    assert "theorem_exists" in res["failed_steps"]


def test_fail_when_user_axiom_dependency(tmp_path, monkeypatch, repo_lock, lean_toolchain_path):
    def fake_run(cmd):
        if cmd[:2] == ("lake", "build"):
            return FakeResult(0, "", "")
        return FakeResult(0, "my_axiom\n", "")
    p = write_tree(tmp_path, verified_node(repo_lock))
    monkeypatch.setattr(lean_check, "_default_run_cmd", lambda c: fake_run(c))
    res = lean_check.verify_node(p, "urn:m3:node:ok", toolchain_path=lean_toolchain_path)
    assert "no_axioms" in res["failed_steps"]


def test_deny_proofs_axioms_flag_not_checked_when_false(tmp_path, monkeypatch, repo_lock, lean_toolchain_path):
    """§2.3：发现级节点无条件执行 axiom 检查——flag 不关闭检查。"""
    n = verified_node(repo_lock)
    n["lean_binding"]["deny_proofs_axioms"] = False
    def fake_run(cmd):
        if cmd[:2] == ("lake", "build"):
            return FakeResult(0, "", "")
        return FakeResult(0, "my_axiom\n", "")
    p = write_tree(tmp_path, n)
    monkeypatch.setattr(lean_check, "_default_run_cmd", lambda c: fake_run(c))
    res = lean_check.verify_node(p, n["id"], toolchain_path=lean_toolchain_path)
    assert "no_axioms" in res["failed_steps"]


def test_lock_mismatch_fails(tmp_path, monkeypatch, repo_lock, lean_toolchain_path):
    n = verified_node(repo_lock)
    n["lean_binding"]["lock"]["toolchain"] = "wrong"
    def fake_run(cmd):
        if cmd[:2] == ("lake", "build"):
            return FakeResult(0, "", "")
        return FakeResult(0, "Nat.add_comm : ...\npropext\n", "")
    p = write_tree(tmp_path, n)
    monkeypatch.setattr(lean_check, "_default_run_cmd", lambda c: fake_run(c))
    res = lean_check.verify_node(p, n["id"], toolchain_path=lean_toolchain_path)
    assert "lock" in res["failed_steps"]


def test_verify_writes_back_fields_on_pass(tmp_path, monkeypatch, repo_lock, lean_toolchain_path):
    def fake_run(cmd):
        if cmd[:2] == ("lake", "build"):
            return FakeResult(0, "", "")
        return FakeResult(0, "Nat.add_comm : ...\npropext\n", "")
    p = write_tree(tmp_path, verified_node(repo_lock))
    monkeypatch.setattr(lean_check, "_default_run_cmd", lambda c: fake_run(c))
    lean_check.verify_node(p, "urn:m3:node:ok", toolchain_path=lean_toolchain_path)
    with open(p, encoding="utf-8") as fh:
        tree = json.load(fh)
    assert tree["nodes"][0]["lean_binding"]["verified"] is True
    assert tree["nodes"][0]["status"] == "success"
    assert tree["nodes"][0]["audit"]["L2_passed"] is True
```

- [ ] **Step 3: 运行测试确认失败**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests/test_lean_check.py -v`
Expected: FAIL（`ModuleNotFoundError: lean_check`）

- [ ] **Step 4: 写实现**

`skills/math-search/orchestrator/lean_check.py`:
```python
"""Lean 四步核验（§7.3）。

四步：编译（lake build）→ #check 定理存在 → #print axioms 非公理（白名单）
→ 锁定核对。任一失败 → verified=False。

`verify_node` 接受 `run_cmd` 回调支持隔离测试（默认 subprocess.run）。
通过时引擎写回 lean_binding.verified/verified_at、status=success、
verification_level=V1、audit.L2_passed=true（§2.2 晋升门第 3 步）。
"""

import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

# Lean/Mathlib 标准公理白名单。用户自定义 axiom 不在此列。
ALLOWED_AXIOMS = frozenset({
    "propext", "funext", "Classical.choice", "Quot.sound", "Classical.choiceAxiom",
})


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"


def _default_run_cmd(cmd):
    return subprocess.run(cmd, capture_output=True, text=True)


def _module_name_from_file(file: str) -> str:
    return Path(file).stem


def _probe_script(module: str, theorem: str) -> str:
    return f"import {module}\n#check {theorem}\n#print axioms {theorem}\n"


def _theorem_exists(stdout: str) -> bool:
    for line in stdout.splitlines():
        if " : " in line and "unknown" not in line and "warning" not in line:
            return True
    return False


def _no_user_axioms(stdout: str) -> bool:
    for line in stdout.splitlines():
        name = line.strip()
        if name and name not in ALLOWED_AXIOMS and not name.startswith("warning") \
           and "import" not in name and ":" not in name:
            return False
    return True


def verify_node(tree_path: str, node_id: str, run_cmd=_default_run_cmd,
                toolchain_path: str = "lean-toolchain") -> dict:
    with open(tree_path, "r", encoding="utf-8") as fh:
        tree = json.load(fh)
    node = next((n for n in tree.get("nodes", []) if n.get("id") == node_id), None)
    if node is None:
        return {"verified": False, "error": f"节点不存在: {node_id}", "steps": [], "failed_steps": ["node_lookup"]}

    binding = node.get("lean_binding")
    if not binding:
        return {"verified": False, "error": "无 lean_binding", "steps": [], "failed_steps": ["binding_missing"]}

    steps = []
    failed = []

    # Step 1: 编译（取 run 中 lake build 的目标文件）
    build_target = Path(binding["file"]).as_posix()
    r = run_cmd(["lake", "build", build_target])
    steps.append("compile")
    if r.returncode != 0:
        failed.append("compile")

    # Step 2+3: 探针（#check + #print axioms 在一个文件中）
    module = _module_name_from_file(binding["file"])
    probe_path = Path("/tmp/m3-probe.lean")
    probe_path.write_text(_probe_script(module, binding["theorem"]), encoding="utf-8")

    r = run_cmd(["lake", "env", "lean", str(probe_path)])
    steps.append("theorem_exists")
    if r.returncode != 0 or not _theorem_exists(r.stdout):
        failed.append("theorem_exists")
    # 非公理检查：无条件执行（§2.3），使用同一探针输出
    steps.append("no_axioms")
    if r.returncode != 0 or not _no_user_axioms(r.stdout):
        failed.append("no_axioms")

    # Step 4: 锁定核对（toolchain 内容比较 + manifest 存在）
    lock = binding.get("lock", {})
    steps.append("lock")
    try:
        actual = Path(toolchain_path).read_text(encoding="utf-8").strip()
    except OSError:
        actual = None
    if lock.get("toolchain") != actual or not Path(lock.get("lake_manifest_ref", "")).exists():
        failed.append("lock")

    if fail_set_if_empty(failed) == 0:
        ts = _now_iso()
        binding["verified"] = True
        binding["verified_at"] = ts
        node["status"] = "success"
        node["verification_level"] = "V1"
        node["audit"]["L2_passed"] = True
        node["audit"]["audit_log"].append(f"{ts} lean_check verify passed")
        with open(tree_path, "w", encoding="utf-8") as fh:
            json.dump(tree, fh, ensure_ascii=False, indent=2)

    return {"verified": (len(failed) == 0), "steps": steps, "failed_steps": failed}


def fail_set_if_empty(failed):
    return len(failed)


def verify(file: str, theorem: str, lock: dict = None, run_cmd=_default_run_cmd) -> dict:
    module = _module_name_from_file(file)
    probe_path = Path("/tmp/m3-probe.lean")
    probe_path.write_text(_probe_script(module, theorem), encoding="utf-8")
    r = run_cmd(["lake", "env", "lean", str(probe_path)])
    return {
        "verified": r.returncode == 0 and _theorem_exists(r.stdout) and _no_user_axioms(r.stdout),
        "stdout": r.stdout,
        "stderr": r.stderr,
    }


def main(argv=None):
    import argparse
    import sys
    parser = argparse.ArgumentParser(description="M3 Lean 核验")
    sub = parser.add_subparsers(dest="cmd", required=True)
    pv = sub.add_parser("verify", help="核验树中节点")
    pv.add_argument("tree")
    pv.add_argument("node_id")
    pv.add_argument("--toolchain-path", default="lean-toolchain")
    pd = sub.add_parser("probe", help="直接核验文件+定理")
    pd.add_argument("--file", required=True)
    pd.add_argument("--theorem", required=True)
    args = parser.parse_args(argv)
    if args.cmd == "verify":
        res = verify_node(args.tree, args.node_id, toolchain_path=args.toolchain_path)
    else:
        res = verify(args.file, args.theorem)
    print(json.dumps(res, ensure_ascii=False, indent=2))
    sys.exit(0 if res.get("verified") else 1)


if __name__ == "__main__":
    main()
```

- [ ] **Step 5: 运行测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests/test_lean_check.py -v`
Expected: 全部 passed

- [ ] **Step 6: Commit**

```bash
git add skills/math-search/orchestrator/lean_check.py skills/math-search/tests/test_lean_check.py
git commit -m "feat: Lean 四步核验（编译/存在/非公理/锁定）"
```

---

## Chunk 3: 状态派生引擎 `audit_gate.py`

### Task 3.1: `audit_gate.py` — L1/L2/晋升门

**Files:**
- Create: `skills/math-search/orchestrator/audit_gate.py`
- Test: `skills/math-search/tests/test_audit_gate.py`

职责（§4）：L1 检查、Lean 核验（L2）、按 §2.2 派生 status/verification_level、晋升门。`gate <tree> <node>` 命令。

- [ ] **Step 1: 写失败测试**

`skills/math-search/tests/test_audit_gate.py`:
```python
import json

import pytest

import audit_gate
from tree_lib import new_node, new_tree


def mk_tree(nodes):
    tree = new_tree(root="urn:m3:tree:t", target="t", obstacle_card_ref="c.md")
    tree["nodes"] = nodes
    return tree


def write(tmp_path, tree):
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(tree, ensure_ascii=False, indent=2))
    return str(p)


def binding_node():
    n = new_node(node_id="urn:m3:node:a", type="certificate", mode="computation", claim="命题")
    n["audit"] = {"L1_passed": True, "L2_passed": False, "audit_log": []}
    n["lean_binding"] = {
        "theorem": "t", "file": "lean/T.lean", "run": "lake build lean/T.lean",
        "deny_proofs_axioms": True,
        "lock": {"toolchain": "tc", "lake_manifest_ref": "lake-manifest.json"},
        "verified": False, "verified_at": None,
    }
    return n


def test_gate_returns_in_progress_without_l1(tmp_path):
    n = new_node(node_id="urn:m3:node:a", claim="命题")
    p = write(tmp_path, mk_tree([n]))
    res = audit_gate.gate(p, n["id"], run_lean=lambda t, nid: {"verified": True, "failed_steps": []})
    assert res["status"] == "in_progress"
    assert any("L1" in r for r in res["reasons"])


def test_gate_rejects_no_binding(tmp_path):
    n = new_node(node_id="urn:m3:node:a", claim="命题")
    n["audit"] = {"L1_passed": True, "L2_passed": False, "audit_log": []}
    p = write(tmp_path, mk_tree([n]))
    res = audit_gate.gate(p, n["id"], run_lean=lambda t, nid: {"verified": False, "failed_steps": []})
    assert res["status"] == "in_progress"
    assert any("binding" in r or "lean" in r.lower() for r in res["reasons"])


def test_gate_promotes_when_all_pass(tmp_path):
    n = binding_node()
    p = write(tmp_path, mk_tree([n]))
    res = audit_gate.gate(p, n["id"], run_lean=lambda t, nid: {"verified": True, "failed_steps": []})
    assert res["status"] == "success"
    assert res["verification_level"] == "V1"


def test_gate_writes_engine_fields_back(tmp_path):
    n = binding_node()
    p = write(tmp_path, mk_tree([n]))
    audit_gate.gate(p, n["id"], run_lean=lambda t, nid: {"verified": True, "failed_steps": []})
    with open(p, encoding="utf-8") as fh:
        saved = json.load(fh)["nodes"][0]
    assert saved["status"] == "success"
    assert saved["audit"]["L2_passed"] is True
    assert saved["verification_level"] == "V1"


def test_gate_marks_counterexample_failed_without_lean(tmp_path):
    n = new_node(node_id="urn:m3:node:c", type="counterexample", mode="computation",
                 claim="反例", result="n=5 矛盾")
    p = write(tmp_path, mk_tree([n]))
    res = audit_gate.gate(p, n["id"], run_lean=lambda t, nid: {})
    assert res["status"] == "failed"
    assert any("反例" in r for r in res["reasons"])
```

- [ ] **Step 2: 运行测试确认失败**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_audit_gate.py -v`
Expected: FAIL（`ModuleNotFoundError: audit_gate`）

- [ ] **Step 3: 写实现**

`skills/math-search/orchestrator/audit_gate.py`:
```python
"""状态派生引擎与晋升门（§2.2 / §4）。

gate 对节点：
1. 反例/no_go → 直接 failed（不强制 Lean 核验，§8b.1）；
2. 检查 L1；
3. 检查 lean_binding 完整（含 lock）；
4. 调用 lean_check 核验（run_lean 可注入）；
5. 通过 → success (V1)，L2_passed=true；否则保持 in_progress。

引擎独占写 status/verification_level/L2_passed/audit_log。
"""

import json

from tree_lib import TreeError


def _why_not_ready(node: dict) -> list:
    reasons = []
    audit = node.get("audit", {})
    if not audit.get("L1_passed"):
        reasons.append("L1 未通过")
    binding = node.get("lean_binding")
    if not binding:
        reasons.append("lean_binding 缺失")
    elif not binding.get("lock"):
        reasons.append("lean_binding.lock 缺失")
    elif not binding.get("theorem"):
        reasons.append("lean_binding.theorem 缺失")
    return reasons


def gate(tree_path: str, node_id: str, run_lean=None) -> dict:
    with open(tree_path, "r", encoding="utf-8") as fh:
        tree = json.load(fh)
    node = next((n for n in tree["nodes"] if n.get("id") == node_id), None)
    if node is None:
        return {"status": None, "reasons": [f"节点不存在: {node_id}"]}

    if node.get("type") in ("counterexample", "no_go"):
        if node.get("status") == "in_progress":
            node["status"] = "failed"
            node["audit"]["audit_log"].append(f"gate -> failed（{node.get('type')}）")
            with open(tree_path, "w", encoding="utf-8") as fh:
                json.dump(tree, fh, ensure_ascii=False, indent=2)
        reason = "反例，不强制 Lean 核验" if node.get("type") == "counterexample" else \
                 "no-go 反证，不强制 Lean 核验"
        return {"status": node["status"], "reasons": [reason]}

    reasons = _why_not_ready(node)
    if reasons:
        return {"status": "in_progress", "reasons": reasons}

    if run_lean is None:
        from lean_check import verify_node
        lean_res = verify_node(tree_path, node_id)
    else:
        lean_res = run_lean(tree_path, node_id)

    if not lean_res.get("verified"):
        return {"status": "in_progress",
                "reasons": [f"Lean 核验失败: {lean_res.get('failed_steps', [])}"]}

    node["status"] = "success"
    node["verification_level"] = "V1"
    node["audit"]["L2_passed"] = True
    node["audit"]["audit_log"].append("gate -> success (V1)，L2 通过")
    with open(tree_path, "w", encoding="utf-8") as fh:
        json.dump(tree, fh, ensure_ascii=False, indent=2)
    return {"status": "success", "verification_level": "V1", "reasons": []}


def main(argv=None):
    import argparse
    import sys
    parser = argparse.ArgumentParser(description="M3 审计门/状态派生")
    parser.add_argument("tree")
    parser.add_argument("node_id")
    args = parser.parse_args(argv)
    res = gate(args.tree, args.node_id)
    print(json.dumps(res, ensure_ascii=False, indent=2))
    sys.exit(0 if res.get("status") not in (None, "in_progress") else 1)


if __name__ == "__main__":
    main()
```

- [ ] **Step 4: 运行测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_audit_gate.py -v`
Expected: 全部 passed

- [ ] **Step 5: Commit**

```bash
git add skills/math-search/orchestrator/audit_gate.py skills/math-search/tests/test_audit_gate.py
git commit -m "feat: 状态派生引擎 audit_gate（L1/L2/晋升门）"
```

---

## Chunk 4: 现有工作导入 `import_workspace.py`

### Task 4.1: 日志解析与节点映射

**Files:**
- Create: `skills/math-search/orchestrator/import_workspace.py`
- Test: `skills/math-search/tests/test_import_workspace.py`

解析 `research_log.md` 的 `##` 小节，按关键词（§8b.1）映射节点类型，提取 Lean 定理名。

- [ ] **Step 1: 预览试点日志结构**

```bash
grep -n '^## ' /Users/alexyu/Documents/ChatGPT/math/erdos_straus/research_log.md | head -30
```
确认标题格式与关键短语，用于校准正则/关键词。

- [ ] **Step 2: 写失败测试**

`skills/math-search/tests/test_import_workspace.py`:
```python
import pytest

import import_workspace as imp


SAMPLE_LOG = """# Title

Lead.

## near-quarter 因子准则

If a prime q | x satisfies q == 2 mod 3, then `b1_divisor_admissibility`
and `type0_gate_iff_residual_divisor_box` certify a solution. 这是已证明的局部结论。

## 反例与障碍

The pair (p,A)=(73,43) is a counterexample to the quadratic escape route;
`quadratic_residue_layer_obstruction` shows the box misses. 该层目前失败。

## 尚未解决的开放问题

No pointwise factor-distribution theorem exists; `hard_two_target_kneser`
给出充分条件。当前无 uniform adaptive layer selection。
"""


def test_parse_sections():
    sections = imp.parse_sections(SAMPLE_LOG)
    assert len(sections) == 3


def test_classify_certificate_section():
    t, body = imp.parse_sections(SAMPLE_LOG)[0]
    assert imp.classify_section(t, body) == "certificate"
    names = imp.extract_lean_theorems(body)
    assert "b1_divisor_admissibility" in names
    assert "type0_gate_iff_residual_divisor_box" in names


def test_classify_counterexample_section():
    t, body = imp.parse_sections(SAMPLE_LOG)[1]
    assert imp.classify_section(t, body) == "counterexample"
    assert imp.extract_lean_theorems(body) == ["quadratic_residue_layer_obstruction"]


def test_classify_open_section():
    t, body = imp.parse_sections(SAMPLE_LOG)[2]
    cls = imp.classify_section(t, body)
    assert cls == "hypothesis"


def test_scan_generates_candidates(tmp_path):
    log_path = tmp_path / "log.md"
    log_path.write_text(SAMPLE_LOG, encoding="utf-8")
    cands = imp.scan(str(log_path))
    assert len(cands) == 3
    assert all(c["origin"] == "legacy" for c in cands)
    assert all(c["source_ref"] for c in cands)
    types = [c["type"] for c in cands]
    assert types[0] == "certificate"
    assert types[1] == "counterexample"
```

- [ ] **Step 3: 运行测试确认失败**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_import_workspace.py -v`
Expected: FAIL（`ModuleNotFoundError: import_workspace`）

- [ ] **Step 4: 写实现**

`skills/math-search/orchestrator/import_workspace.py`:
```python
"""现有工作 → 探索树导入器（§8b.1）。

scan: 解析研究日志 `##` 小节，按关键词映射节点类型，生成候选清单（不写树）。
draft/commit: 草稿树 → 人工审核 → 正式树。
导入节点 origin=legacy、source_ref=文件:小节、obstacle 三要素自动推断（可审）。
"""

import argparse
import json
import re
import sys
import uuid
from pathlib import Path

from tree_lib import new_node, new_tree, save_tree, validate_tree

SECTION_RE = re.compile(r"^##\s+(.+)$")
CERT_KEYWORDS = ("已证明", "机器核验", "formalize", "machine-checked", "certificate", "定理", "证毕")
NOGO_KEYWORDS = ("no-go", "no go", "不被整除", "不可能", "排除", "不能", "不可", "障碍", "obstruction", "阻止")
CTREX_KEYWORDS = ("反例", "回归", "counterexample", "失败", "regression", "反证")
OPEN_KEYWORDS = ("必要条件", "尚未", "开放", "无法", "未解决", "missing", "open", "待决", "缺口", "gap", "仍远弱")

THEOREM_RE = re.compile(r"`([a-zA-Z_][a-zA-Z0-9_']*)`")
LEAN_DECL_RE = re.compile(r"\b(?:theorem|lemma)\s+([a-zA-Z_][a-zA-Z0-9_']*)")


def parse_sections(md_text):
    lines = md_text.splitlines()
    sections = []
    current_title, current_body = None, []
    for line in lines:
        stripped = line.strip()
        m = SECTION_RE.match(stripped)
        if m:
            if current_title is not None:
                sections.append((current_title, "\n".join(current_body)))
            current_title = m.group(1)
            current_body = []
        elif current_title is not None:
            current_body.append(line)
    if current_title is not None:
        sections.append((current_title, "\n".join(current_body)))
    return sections


def _has_any(text, keywords):
    low = text.lower()
    return any(k.lower() in low for k in keywords)


def classify_section(title, body):
    text = f"{title}\n{body}"
    if _has_any(text, CTREX_KEYWORDS):
        return "counterexample"
    if _has_any(text, NOGO_KEYWORDS):
        return "no_go"
    if _has_any(text, CERT_KEYWORDS):
        return "certificate"
    return "hypothesis"


def extract_lean_theorems(body):
    names = []
    for m in THEOREM_RE.finditer(body):
        name = m.group(1)
        if name not in names:
            names.append(name)
    for m in LEAN_DECL_RE.finditer(body):
        name = m.group(1)
        if name not in names:
            names.append(name)
    return names


def _fingerprint(text):
    q = "点态" if ("点态" in text or "pointwise" in text.lower()) else \
        ("全称" if ("全称" in text or "uniform" in text.lower()) else
         ("逐层" if "层" in text else "存在"))
    o = "相对代数性" if "相对" in text else \
        ("因子" if ("因子" in text or "divisor" in text.lower()) else
         ("和集" if ("和集" in text or "sumset" in text.lower()) else "计数"))
    c = "自适应" if ("自适应" in text or "adaptive" in text.lower()) else \
        ("跨层" if "层" in text else "无耦合")
    return f"{q} | {o} | {c}"


def scan(log_path):
    text = Path(log_path).read_text(encoding="utf-8")
    cands = []
    for title, body in parse_sections(text):
        cands.append({
            "id": f"urn:m3:node:legacy-{uuid.uuid4().hex[:8]}",
            "origin": "legacy",
            "source_ref": f"{log_path}#{title[:40]}",
            "type": classify_section(title, body),
            "mode": "computation",
            "status": "in_progress",
            "claim": title,
            "result": body[:400] + ("…" if len(body) > 400 else ""),
            "obstacle": {"fingerprint": _fingerprint(title + "\n" + body),
                         "excluded_methods": [], "required_coupling": "跨层"},
            "theorem_names": extract_lean_theorems(body),
        })
    return cands


def draft(log_path, out_path):
    cands = scan(log_path)
    tree = new_tree(root="urn:m3:tree:legacy-" + uuid.uuid4().hex[:8],
                    target=f"导入 {log_path}", obstacle_card_ref="templates/obstacle_card.md")
    for c in cands:
        node = new_node(node_id=c["id"], origin="legacy", source_ref=c["source_ref"],
                        node_type=c["type"], mode=c["mode"], obstacle=c["obstacle"],
                        claim=c["claim"], result=c["result"])
        tree["nodes"].append(node)
    save_tree(tree, out_path)
    print(f"草稿树: {out_path}（{len(cands)} 节点，待人工审核）")


def commit(draft_path, out_path):
    tree = json.loads(Path(draft_path).read_text(encoding="utf-8"))
    validate_tree(tree)
    save_tree(tree, out_path)
    print(f"已提交正式树: {out_path}")


def main(argv=None):
    parser = argparse.ArgumentParser(description="M3 现有工作导入器")
    sub = parser.add_subparsers(dest="cmd", required=True)
    ps = sub.add_parser("scan"); ps.add_argument("log")
    pd = sub.add_parser("draft"); pd.add_argument("log"); pd.add_argument("-o", "--out", required=True)
    pc = sub.add_parser("commit"); pc.add_argument("draft"); pc.add_argument("-o", "--out", required=True)
    args = parser.parse_args(argv)
    if args.cmd == "scan":
        print(json.dumps(scan(args.log), ensure_ascii=False, indent=2))
    elif args.cmd == "draft":
        draft(args.log, args.out)
    elif args.cmd == "commit":
        commit(args.draft, args.out)


if __name__ == "__main__":
    main()
```

- [ ] **Step 5: 运行测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_import_workspace.py -v`
Expected: 全部 passed

- [ ] **Step 6: 真实试点扫描（人工审核前不提交）**

Run:
```bash
cd /Users/alexyu/Documents/ChatGPT/math && python3 skills/math-search/orchestrator/import_workspace.py scan erdos_straus/research_log.md
```
Expected: 输出候选 JSON；类型分布合理。

- [ ] **Step 7: Commit**

```bash
git add skills/math-search/orchestrator/import_workspace.py skills/math-search/tests/test_import_workspace.py
git commit -m "feat: 现有工作导入器（日志小节解析/类型映射/draft/commit）"
```

---

## Chunk 5: 可证明内容上传 `upload_proofs.py`

### Task 5.1: 上传器

**Files:**
- Create: `skills/math-search/orchestrator/upload_proofs.py`
- Test: `skills/math-search/tests/test_upload_proofs.py`

仅上传 success + L1/L2 + Lean verified + V≥1（§8b.2），写入 `output/uploads/<tree-id>/`。

- [ ] **Step 1: 写失败测试**

`skills/math-search/tests/test_upload_proofs.py`:
```python
import json

import pytest

import upload_proofs
from tree_lib import new_node, new_tree


def success_node():
    n = new_node(node_id="urn:m3:node:s", type="certificate", mode="computation", claim="定理T", result="lean 已验证")
    n["status"] = "success"
    n["verification_level"] = "V1"
    n["audit"] = {"L1_passed": True, "L2_passed": True, "audit_log": []}
    n["lean_binding"] = {
        "theorem": "add_comm", "file": "lean/Foo.lean",
        "run": "lake build lean/Foo.lean && lean_check.py probe --file lean/Foo.lean --theorem add_comm",
        "deny_proofs_axioms": True,
        "lock": {"toolchain": "tc", "lake_manifest_ref": "lake-manifest.json"},
        "verified": True, "verified_at": "2026-08-17T00:00:00Z",
    }
    return n


def failing_node():
    n = new_node(node_id="urn:m3:node:f", type="hypothesis", mode="computation", claim="未验证")
    return n


def mk_tree(outdir, nodes):
    tree = new_tree(root="urn:m3:tree:test", target="t", obstacle_card_ref="c.md")
    tree["nodes"] = nodes
    p = outdir / "tree.json"
    p.write_text(json.dumps(tree, ensure_ascii=False, indent=2))
    return str(p)


def test_status_lists_eligible_and_excluded(tmp_path, monkeypatch):
    tree_path = mk_tree(tmp_path, [success_node(), failing_node()])
    monkeypatch.setattr(upload_proofs, "_lean_verify_ok", lambda t, n: True)
    st = upload_proofs.status(tree_path)
    assert "urn:m3:node:s" in [n["id"] for n in st["eligible"]]
    assert "urn:m3:node:f" in [n["id"] for n in st["excluded"]]


def _arch_root(tmp_path):
    return tmp_path / "uploads" / "urn:m3:tree:test"


def test_upload_creates_archive_layout(tmp_path, monkeypatch):
    tree_path = mk_tree(tmp_path, [success_node()])
    monkeypatch.setattr(upload_proofs, "_lean_verify_ok", lambda t, n: True)
    upload_proofs.upload(tree_path, out_root=str(tmp_path / "uploads"))
    arch_root = _arch_root(tmp_path)
    assert (arch_root / "manifest.json").exists()
    assert (arch_root / "README.md").exists()
    proof_dir = arch_root / "proofs" / "urn:m3:node:s"
    for f in ["claim.md", "proof.lean", "run.sh", "lock.json", "verify.json"]:
        assert (proof_dir / f).exists()


def test_upload_rejects_unverified(tmp_path, monkeypatch):
    tree_path = mk_tree(tmp_path, [failing_node()])
    monkeypatch.setattr(upload_proofs, "_lean_verify_ok", lambda t, n: True)
    upload_proofs.upload(tree_path, out_root=str(tmp_path / "uploads"))
    arch_root = _arch_root(tmp_path)
    proofs = arch_root / "proofs"
    entries = list(proofs.iterdir()) if proofs.exists() else []
    assert entries == []


def test_upload_sets_uploaded_at(tmp_path, monkeypatch):
    tree_path = mk_tree(tmp_path, [success_node()])
    monkeypatch.setattr(upload_proofs, "_lean_verify_ok", lambda t, n: True)
    upload_proofs.upload(tree_path, out_root=str(tmp_path / "uploads"))
    with open(tree_path, encoding="utf-8") as fh:
        tree = json.load(fh)
    assert tree["nodes"][0]["uploaded_at"] is not None
```

- [ ] **Step 2: 运行测试确认失败**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_upload_proofs.py -v`
Expected: FAIL（`ModuleNotFoundError: upload_proofs`）

- [ ] **Step 3: 写实现**

`skills/math-search/orchestrator/upload_proofs.py`:
```python
"""可证明内容上传器（§8b.2）。

仅上传：status=success + L1/L2 通过 + lean_binding 完整 + lean 当前核验通过 + V>=1。
写入 output/uploads/<tree-id>/：proofs/<node>/（claim.md, proof.lean, run.sh,
lock.json, verify.json）+ tree-subgraph.json + manifest.json + README.md。
成功后引擎写回节点 uploaded_at。
"""

import json
import shutil
from datetime import datetime, timezone
from pathlib import Path

from tree_lib import load_tree, save_tree


def _now_iso():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"


def _lean_verify_ok(tree_path, node):
    from lean_check import verify_node
    res = verify_node(tree_path, node["id"])
    return bool(res.get("verified"))


def _is_eligible(tree_path, node):
    reasons = []
    if node.get("status") != "success":
        reasons.append(f"status={node.get('status')}")
    audit = node.get("audit", {})
    if not audit.get("L1_passed"):
        reasons.append("L1 未通过")
    if not audit.get("L2_passed"):
        reasons.append("L2 未通过")
    binding = node.get("lean_binding")
    if not binding or not binding.get("theorem") or not binding.get("file") \
       or not binding.get("run") or not binding.get("lock"):
        reasons.append("lean_binding 不完整")
    if node.get("verification_level", "V0") == "V0":
        reasons.append("verification_level < V1")
    if not reasons:
        try:
            if not _lean_verify_ok(tree_path, node):
                reasons.append("当前 Lean 核验未通过")
        except Exception as exc:  # noqa: BLE001
            reasons.append(f"核验异常: {exc}")
    return (not reasons, reasons)


def status(tree_path):
    tree = load_tree(tree_path)
    eligible, excluded = [], []
    for node in tree["nodes"]:
        ok, reasons = _is_eligible(tree_path, node)
        item = {"id": node["id"], "claim": node.get("claim"), "reasons": reasons if not ok else []}
        (eligible if ok else excluded).append(item)
    return {"eligible": eligible, "excluded": excluded}


def upload(tree_path, out_root="output/uploads"):
    tree = load_tree(tree_path)
    root_id = tree["root"]
    arch_root = Path(out_root) / root_id
    proofs_dir = arch_root / "proofs"
    proofs_dir.mkdir(parents=True, exist_ok=True)

    uploaded = []
    for node in tree["nodes"]:
        ok, _ = _is_eligible(tree_path, node)
        if not ok:
            continue
        node_dir = proofs_dir / node["id"]
        node_dir.mkdir(parents=True, exist_ok=True)

        b = node["lean_binding"]
        md = [
            f"# Claim: {node.get('claim')}",
            f"- node: {node['id']}",
            f"- type: {node['type']}",
            f"- mode: {node['mode']}",
            f"- fingerprint: {node.get('obstacle', {}).get('fingerprint')}",
            f"- theorem: {b.get('theorem')}",
            f"- file: {b.get('file')}",
            f"- level: {node.get('verification_level')}",
            "",
            "## Result",
            "",
            node.get("result") or "",
        ]
        (node_dir / "claim.md").write_text("\n".join(md), encoding="utf-8")

        src = Path(b["file"])
        if src.exists():
            shutil.copyfile(src, node_dir / "proof.lean")

        (node_dir / "run.sh").write_text("#!/bin/sh\nset -e\n" + b["run"] + "\n", encoding="utf-8")
        (node_dir / "run.sh").chmod(0o755)
        (node_dir / "lock.json").write_text(json.dumps(b["lock"], ensure_ascii=False, indent=2), encoding="utf-8")

        # verify.json 使用同一可注入核验入口（生产=真实 lean_check，测试=monkeypatch）
        ver = {"verified": _lean_verify_ok(tree_path, node)}
        (node_dir / "verify.json").write_text(json.dumps(ver, ensure_ascii=False, indent=2), encoding="utf-8")

        node["uploaded_at"] = _now_iso()
        uploaded.append(node["id"])

    success_ids = {n["id"] for n in tree["nodes"] if n.get("status") == "success"}
    sub_ids = set(success_ids)
    for n in tree["nodes"]:
        if n["id"] in success_ids:
            sub_ids.update(n.get("parent_ids", []))
    (arch_root / "tree-subgraph.json").write_text(
        json.dumps({"root": root_id, "nodes": [n for n in tree["nodes"] if n["id"] in sub_ids]},
                   ensure_ascii=False, indent=2), encoding="utf-8")

    manifest = {"root": root_id, "generated_at": _now_iso(),
                "uploaded_nodes": uploaded, "count": len(uploaded)}
    (arch_root / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    (arch_root / "README.md").write_text(
        f"# {root_id}\n\n上传可复现证明归档。{len(uploaded)} 个已验证节点。\n", encoding="utf-8")

    save_tree(tree, tree_path)
    return manifest


def main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description="M3 可证明内容上传器")
    sub = parser.add_subparsers(dest="cmd", required=True)
    ps = sub.add_parser("status"); ps.add_argument("tree")
    pu = sub.add_parser("upload"); pu.add_argument("tree"); pu.add_argument("--out-root", default="output/uploads")
    pv = sub.add_parser("verify"); pv.add_argument("archive")
    args = parser.parse_args(argv)
    if args.cmd == "status":
        print(json.dumps(status(args.tree), ensure_ascii=False, indent=2))
    elif args.cmd == "upload":
        print(json.dumps(upload(args.tree, out_root=args.out_root), ensure_ascii=False, indent=2))
    elif args.cmd == "verify":
        arch = Path(args.archive)
        results = [{"node": vj.parent.name, "verified": bool(json.loads(vj.read_text()).get("verified"))}
                   for vj in arch.glob("proofs/*/verify.json")]
        print(json.dumps(results, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
```

- [ ] **Step 4: 运行测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_upload_proofs.py -v`
Expected: 全部 passed

- [ ] **Step 5: Commit**

```bash
git add skills/math-search/orchestrator/upload_proofs.py skills/math-search/tests/test_upload_proofs.py
git commit -m "feat: 可证明内容上传器（仅已验证节点 → 本地归档）"
```

---

## Chunk 6: D3 可视化 `build_tree.py`

### Task 6.1: 单文件交互式 HTML

**Files:**
- Create: `skills/math-search/orchestrator/build_tree.py`
- Test: `skills/math-search/tests/test_build_tree.py`

生成单文件 HTML：内嵌树 JSON + D3 CDN + 颜色/形状/详情/筛选/失败可见。

- [ ] **Step 1: 写失败测试**

`skills/math-search/tests/test_build_tree.py`:
```python
import json

import pytest

import build_tree
from tree_lib import new_node, new_tree


def sample_nodes():
    n1 = new_node(node_id="urn:m3:node:a", type="certificate", mode="computation", claim="定理A", result="ok")
    n1["status"] = "success"
    n1["audit"] = {"L1_passed": True, "L2_passed": True, "audit_log": []}
    n1["lean_binding"] = {"theorem": "t", "file": "lean/A.lean", "run": "run",
                          "deny_proofs_axioms": True,
                          "lock": {"toolchain": "tc", "lake_manifest_ref": "x"},
                          "verified": True, "verified_at": None}
    n2 = new_node(node_id="urn:m3:node:b", type="no_go", mode="invention", claim="排除X", result="no-go")
    n2["status"] = "failed"
    n3 = new_node(node_id="urn:m3:node:c", type="hypothesis", mode="tool_discovery", claim="待验证", result="")
    return [n1, n2, n3]


def build_tree_for(tmp_path):
    tree = new_tree(root="urn:m3:tree:viz", target="t", obstacle_card_ref="c.md")
    tree["nodes"] = sample_nodes()
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(tree, ensure_ascii=False, indent=2))
    return str(p)


def test_render_contains_all_nodes(tmp_path):
    html = build_tree.render(build_tree_for(tmp_path))
    for cid in ["urn:m3:node:a", "urn:m3:node:b", "urn:m3:node:c"]:
        assert cid in html


def test_render_inlines_json(tmp_path):
    html = build_tree.render(build_tree_for(tmp_path))
    assert "const TREE" in html
    assert '"root"' in html


def test_render_has_d3_cdn(tmp_path):
    html = build_tree.render(build_tree_for(tmp_path))
    assert "cdn" in html.lower() and "d3" in html.lower()


def test_render_has_failure_filter(tmp_path):
    html = build_tree.render(build_tree_for(tmp_path))
    assert "仅看失败" in html


def test_render_color_and_labels(tmp_path):
    html = build_tree.render(build_tree_for(tmp_path))
    assert "superseded" in html and "unverified_claim" in html
```

- [ ] **Step 2: 运行测试确认失败**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_build_tree.py -v`
Expected: FAIL（`ModuleNotFoundError: build_tree`）

- [ ] **Step 3: 写实现**

`skills/math-search/orchestrator/build_tree.py`:
```python
"""探索树 → D3 单文件 HTML 可视化（§7.2）。

颜色：success 绿 / failed 红 / withdrawn 灰 / in_progress 黄（未过 L1 实心、
过 L1 无绑定空心）/ superseded 蓝虚线。
形状：certificate 方形 / hypothesis 圆圈 / no_go+counterexample 菱形。
过滤：按模式/状态/Lean 绑定；失败默认可见 + “仅看失败”。
D3 以 CDN 引入，树 JSON 内嵌。
"""

import argparse
import json
from pathlib import Path

HTML_TEMPLATE = """<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<title>M3 探索树</title>
<style>
  :root{--bg:#f7f8fb;--line:#dfe5ed}
  body{margin:0;background:var(--bg);font-family:-apple-system,"Segoe UI","PingFang SC",sans-serif;color:#182230}
  .bar{padding:12px 20px;display:flex;gap:10px;flex-wrap:wrap;align-items:center;background:#fff;border-bottom:1px solid var(--line)}
  .bar button{cursor:pointer;padding:6px 12px;border:1px solid var(--line);border-radius:999px;background:#fff;font:inherit;font-size:.82rem}
  .bar button.on{border-color:#2367d1;background:#eaf2ff;color:#1e53a1}
  #tree{width:100%;height:calc(100vh - 56px)}
  .node{cursor:pointer}
  .node text{font:11px -apple-system,sans-serif}
  .detail{position:fixed;right:14px;top:64px;width:360px;max-height:80vh;overflow:auto;background:#fff;border:1px solid var(--line);border-radius:14px;padding:16px;box-shadow:0 18px 50px #22344f21}
  .detail h3{margin:0 0 8px;font-size:1rem}
  .detail pre{white-space:pre-wrap;font:12px ui-monospace,monospace;background:#f4f6fa;padding:8px;border-radius:8px}
  .badge{display:inline-block;padding:2px 8px;border-radius:999px;font-size:.72rem;font-weight:700;background:#e8f7f5;color:#147d77;margin-right:4px}
  .legend{position:fixed;left:14px;bottom:14px;background:#fff;border:1px solid var(--line);border-radius:10px;padding:8px 10px;font-size:.74rem}
</style>
</head>
<body>
<div class="bar">
  <strong>M3 探索树</strong>
  <button id="f-fail">仅看失败</button>
  <button id="f-lean">仅看 Lean</button>
  <button id="f-computation">模式一</button>
  <button id="f-tool">模式二</button>
  <button id="f-invention">模式三</button>
</div>
<div id="tree"></div>
<div class="legend">绿=success 红=failed 灰=withdrawn 黄=in_progress(实心=未过L1, 空心=unverified_claim-B) 蓝=superseded
 · 方=certificate 圆=假设 菱=no-go/反例<br>失败路径默认可见</div>
<script src="https://cdn.jsdelivr.net/npm/d3@7/dist/d3.min.js"></script>
<script>
const TREE = __TREE_JSON__;
const nodes = TREE.nodes;
const byId = new Map(nodes.map(n => [n.id, n]));
const childrenMap = new Map();
nodes.forEach(n => (n.parent_ids||[]).forEach(p => {
  if(!childrenMap.has(p)) childrenMap.set(p, []);
  childrenMap.get(p).push(n);
}));
function color(n){
  switch(n.status){
    case 'success': return '#2e7d32';
    case 'failed': return '#c62828';
    case 'withdrawn': return '#757575';
    case 'superseded': return '#1565c0';
    default: return n.audit && n.audit.L1_passed ? '#f6c344' : '#f9a825';
  }
}
function stroke(n){ return n.status === 'superseded' ? '#0d47a1' : 'none'; }
function dash(n){ return n.status === 'superseded' ? '4,3' : null; }
function shapeSym(d){
  if(d.type === 'certificate') return d3.symbolSquare;
  if(d.type === 'no_go' || d.type === 'counterexample') return d3.symbolDiamond;
  return d3.symbolCircle;
}
let shown = {fail:false, lean:false, mode:null};
function render(){
  d3.select('#tree').selectAll('*').remove();
  const h = document.querySelector('#tree').clientHeight;
  const w = document.querySelector('#tree').clientWidth;
  const svg = d3.select('#tree').append('svg').attr('width','100%').attr('height',h);
  const g = svg.append('g');
  const view = nodes.filter(n => {
    if(shown.fail && n.status !== 'failed') return false;
    if(shown.lean && !(n.lean_binding && n.lean_binding.verified)) return false;
    if(shown.mode && n.mode !== shown.mode) return false;
    return true;
  });
  // 简易分层布局：先给全部节点分配深度（带父节点也需有位置）
  const depth = new Map();
  function assign(n, k){
    if(depth.has(n.id)) { depth.set(n.id, Math.min(depth.get(n.id), k)); return; }
    depth.set(n.id, k);
    (n.parent_ids||[]).forEach(p => { const pp = byId.get(p); if(pp) assign(pp, k+1); });
  }
  // 从 view 中的无父节点开始，逐层向下：这里 parent_ids 指向上级，
  // 因此先对每个无父节点给深度 0，再对带父节点用父深度+1。
  view.filter(n => !(n.parent_ids||[]).length).forEach(n => { depth.set(n.id, 0); });
  // 带父节点的深度 = 父深度 + 1（父可能在 view 外，用 byId 查）
  function depthOf(n){
    if(depth.has(n.id)) return depth.get(n.id);
    const ps = (n.parent_ids||[]).map(pid => byId.get(pid)).filter(Boolean);
    const d = ps.length ? Math.max(...ps.map(depthOf)) + 1 : 0;
    depth.set(n.id, d);
    return d;
  }
  view.forEach(n => depthOf(n));
  const placed = new Map();
  const layers = new Map();
  for(const [id, dep] of depth){ if(!layers.has(dep)) layers.set(dep, []); layers.get(dep).push(byId.get(id)); }
  let y = 60;
  for(const [dep, group] of [...layers.entries()].sort((a,b)=>a[0]-b[0])){
    const x = 80 + dep * 170;
    group.forEach(n => { placed.set(n.id, {x, y}); y += 80; });
  }
  for(const n of view) for(const pid of (n.parent_ids||[])){
    const a = placed.get(pid), b = placed.get(n.id);
    if(a && b) g.append('line').attr('x1',a.x).attr('y1',a.y).attr('x2',b.x).attr('y2',b.y)
      .attr('stroke','#cfd8ea').attr('stroke-width',1.5);
  }
  for(const n of view){
    const pos = placed.get(n.id);
    if(!pos) continue;  // 无位置跳过而非中断整个渲染
    const grp = g.append('g').attr('class','node').attr('transform',`translate(${pos.x},${pos.y})`);
    const path = d3.symbol().type(shapeSym(n)).size(120)();
    grp.append('path').attr('d', path).attr('fill', color(n)).attr('stroke', stroke(n))
       .attr('stroke-dasharray', dash(n));
    grp.append('text').attr('dy',4).attr('text-anchor','middle').attr('fill','#fff')
       .style('font-size','10px').text(n.id.slice(-4));
    grp.on('click', () => showDetail(n));
  }
}
function showDetail(n){
  d3.select('.detail').remove();
  const box = d3.select('body').append('div').attr('class','detail');
  box.append('h3').text(n.claim || n.id);
  let tags = [`<span class="badge">${n.status}</span>`,`<span class="badge">${n.mode}</span>`];
  if(n.lean_binding && n.lean_binding.verified) tags.push(`<span class="badge">Lean✓</span>`);
  box.append('p').style('margin','6px 0').html(tags.join(''));
  box.append('pre').text('ID: '+n.id);
  if(n.type) box.append('pre').text('type: '+n.type);
  if(n.obstacle && n.obstacle.fingerprint) box.append('pre').text('obstacle: '+n.obstacle.fingerprint);
  if(n.lean_binding) box.append('pre').text('Lean: '+n.lean_binding.file+' :: '+n.lean_binding.theorem);
  if(n.result) box.append('pre').text('result: '+n.result);
  if(n.audit) box.append('pre').text('audit L1='+n.audit.L1_passed+' L2='+n.audit.L2_passed);
}
d3.select('#f-fail').on('click', function(){ shown.fail=!shown.fail; d3.select(this).classed('on',shown.fail); render(); });
d3.select('#f-lean').on('click', function(){ shown.lean=!shown.lean; d3.select(this).classed('on',shown.lean); render(); });
d3.select('#f-computation').on('click', function(){ setMode(this,'computation'); });
d3.select('#f-tool').on('click', function(){ setMode(this,'tool_discovery'); });
d3.select('#f-invention').on('click', function(){ setMode(this,'invention'); });
function setMode(btn,m){ shown.mode = shown.mode===m?null:m; d3.selectAll('.bar button').classed('on',false); d3.select(btn).classed('on', shown.mode===m); render(); }
render();
</script>
</body>
</html>
"""


def render(tree_path: str) -> str:
    tree = json.loads(Path(tree_path).read_text(encoding="utf-8"))
    return HTML_TEMPLATE.replace("__TREE_JSON__", json.dumps(tree))


def main(argv=None):
    parser = argparse.ArgumentParser(description="M3 探索树可视化")
    parser.add_argument("tree")
    parser.add_argument("-o", "--out", default="viz/tree.html")
    args = parser.parse_args(argv)
    html = render(args.tree)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(html, encoding="utf-8")
    print(f"可视化已生成: {out}")


if __name__ == "__main__":
    main()
```

- [ ] **Step 4: 运行测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_build_tree.py -v`
Expected: 全部 passed

- [ ] **Step 5: Commit**

```bash
git add skills/math-search/orchestrator/build_tree.py skills/math-search/tests/test_build_tree.py
git commit -m "feat: D3 单文件探索树可视化"
```

---

## Chunk 7: Proofweave 导出 `export_pw.py`

### Task 7.1: 兼容事件流

**Files:**
- Create: `skills/math-search/orchestrator/export_pw.py`
- Test: `skills/math-search/tests/test_export_pw.py`

按 §8 映射生成 Proofweave 事件流（不签名/联网）。

- [ ] **Step 1: 写失败测试**

`skills/math-search/tests/test_export_pw.py`:
```python
import json

import pytest

import export_pw
from tree_lib import new_node, new_tree


def pw_tree():
    n1 = new_node(node_id="urn:m3:node:s", type="certificate", mode="computation", claim="定理A")
    n1["status"] = "success"
    n1["verification_level"] = "V1"
    n1["audit"] = {"L1_passed": True, "L2_passed": True, "audit_log": []}
    n1["lean_binding"] = {"theorem": "t", "file": "lean/A.lean",
                          "run": "lake build lean/A.lean", "deny_proofs_axioms": True,
                          "lock": {"toolchain": "tc", "lake_manifest_ref": "x"},
                          "verified": True, "verified_at": None}
    n2 = new_node(node_id="urn:m3:node:f", type="counterexample", mode="computation", claim="反例")
    n2["status"] = "failed"
    tree = new_tree(root="urn:m3:tree:x", target="t", obstacle_card_ref="c.md")
    tree["nodes"] = [n1, n2]
    return tree


def test_success_emits_claim_publish(tmp_path):
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(pw_tree(), ensure_ascii=False))
    types = [e["type"] for e in export_pw.export(str(p))]
    assert "claim.publish" in types
    pub = next(e for e in export_pw.export(str(p)) if e["type"] == "claim.publish")
    assert pub["body"]["statement"] != ""


def test_failed_emits_challenge(tmp_path):
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(pw_tree(), ensure_ascii=False))
    types = [e["type"] for e in export_pw.export(str(p))]
    assert "challenge.open" in types


def test_envelope_required_fields(tmp_path):
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(pw_tree(), ensure_ascii=False))
    for e in export_pw.export(str(p)):
        for f in ["protocol", "id", "type", "occurred_at", "actor", "body", "signature"]:
            assert f in e
        assert e["protocol"] == "proofweave/0.1"


def test_success_emits_bundle_and_verification(tmp_path):
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(pw_tree(), ensure_ascii=False))
    types = [e["type"] for e in export_pw.export(str(p))]
    assert "bundle.publish" in types
    assert "verification.submit" in types


def test_synthesis_present(tmp_path):
    p = tmp_path / "tree.json"
    p.write_text(json.dumps(pw_tree(), ensure_ascii=False))
    types = [e["type"] for e in export_pw.export(str(p))]
    assert "synthesis.publish" in types
```

- [ ] **Step 2: 运行测试确认失败**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_export_pw.py -v`
Expected: FAIL（`ModuleNotFoundError: export_pw`）

- [ ] **Step 3: 写实现**

`skills/math-search/orchestrator/export_pw.py`:
```python
"""探索树 → Proofweave 兼容事件流（§8）。

映射：success → claim.publish + bundle.publish(执行契约=lean_binding.run) +
verification.submit；counterexample/no_go(failed) → challenge.open；
failed/withdrawn → claim.withdraw；根+障碍卡片 → project.create + synthesis.publish。
签名为 placeholder，供后续接入 Proofweave 节点。
"""

import json
import uuid
from datetime import datetime, timezone
from pathlib import Path

from tree_lib import load_tree


def _now_iso():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"


def _uid():
    return str(uuid.uuid4())


def _envelope(etype, body, actor="urn:pw:agent:m3-local"):
    return {
        "protocol": "proofweave/0.1",
        "id": f"urn:pw:event:{_uid()}",
        "type": etype,
        "occurred_at": _now_iso(),
        "actor": actor,
        "body": body,
        "signature": {"alg": "EdDSA", "kid": f"{actor}#key-1", "value": "placeholder"},
    }


def export(tree_path, actor="urn:pw:agent:m3-local"):
    tree = load_tree(tree_path)
    events = []

    events.append(_envelope("project.create", {
        "object_type": "extension",
        "extension_uri": "https://m3.local/ext/project-init",
        "data": {"target": tree["session"]["target"],
                 "obstacle_card_ref": tree["session"]["obstacle_card_ref"]},
    }, actor))

    for node in tree["nodes"]:
        if node.get("status") == "success":
            statement = node.get("claim") or node.get("id")
            claim_id = f"urn:pw:claim:{_uid()}"
            events.append(_envelope("claim.publish", {
                "object_type": "claim",
                "claim_id": claim_id,
                "kind": "theoretical",
                "statement": statement,
                "scope": {"node": node.get("id"),
                          "fingerprint": node.get("obstacle", {}).get("fingerprint")},
                "assumptions": node.get("obstacle", {}).get("excluded_methods", []),
                "dependencies": [],
                "tags": ["m3", node.get("mode")],
            }, actor))

            b = node.get("lean_binding", {})
            bundle_id = f"urn:pw:bundle:{_uid()}"
            events.append(_envelope("bundle.publish", {
                "object_type": "research_bundle",
                "bundle_id": bundle_id,
                "claim_ids": [claim_id],
                "delivery": {"kind": "git", "uri": "git@local:m3/tree",
                             "immutable_ref": tree_path, "access": "public"},
                "execution_contract": {
                    "entrypoint": {"kind": "command", "command": [b.get("run", "")]},
                    "inputs": [],
                    "outputs": ["verify.json"],
                    "timeout_seconds": 7200,
                    "resource_limits": {"cpu": 1, "memory_gb": 4},
                    "network_policy": "none",
                    "success_criteria": ["exit_code == 0", "verified"],
                },
                "expected_results": {"verified": True},
                "license": "Apache-2.0",
                "sensitivity": "public",
            }, actor))

            events.append(_envelope("verification.submit", {
                "object_type": "verification",
                "verification_id": f"urn:pw:verification:{_uid()}",
                "target_claim": claim_id,
                "target_bundle": bundle_id,
                "target_run": f"urn:pw:run:{_uid()}",
                "mode": "exact_bundle",
                "result": "pass",
                "checks": [{"name": "lean_verified", "result": "pass",
                            "observed": b.get("verified", False)}],
                "receipt": {"artifact_id": f"urn:pw:artifact:{_uid()}",
                            "digest": "sha256:placeholder",
                            "media_type": "application/json",
                            "locations": ["https://local/m3/receipt.json"]},
                "independence": {"owner_distinct": False},
            }, actor))

        elif node.get("status") == "failed" and node.get("type") in ("counterexample", "no_go"):
            events.append(_envelope("challenge.open", {
                "object_type": "challenge",
                "challenge_id": f"urn:pw:challenge:{_uid()}",
                "target": node.get("id"),
                "category": "counterexample" if node.get("type") == "counterexample" else "methodology",
                "description": node.get("claim") or node.get("result"),
                "resolution_condition": "m3 节点状态更新",
            }, actor))
        elif node.get("status") in ("failed", "withdrawn"):
            events.append(_envelope("claim.withdraw", {
                "object_type": "extension",
                "extension_uri": "https://m3.local/ext/withdraw",
                "data": {"node": node.get("id"), "status": node.get("status")},
            }, actor))

    events.append(_envelope("synthesis.publish", {
        "object_type": "synthesis",
        "content": "M3 会话导出",
        "claim_ids": [e["body"].get("claim_id", "") for e in events if e["type"] == "claim.publish"],
        "node_ids": [n["id"] for n in tree["nodes"]],
    }, actor))

    return events


def main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description="M3 → Proofweave 事件导出")
    parser.add_argument("tree")
    parser.add_argument("--out", default="output/pw-events.json")
    parser.add_argument("--actor", default="urn:pw:agent:m3-local")
    args = parser.parse_args(argv)
    events = export(args.tree, actor=args.actor)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(events, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"已导出 {len(events)} 个事件 → {out}")


if __name__ == "__main__":
    main()
```

- [ ] **Step 4: 运行测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_export_pw.py -v`
Expected: 全部 passed

- [ ] **Step 5: Commit**

```bash
git add skills/math-search/orchestrator/export_pw.py skills/math-search/tests/test_export_pw.py
git commit -m "feat: Proofweave 兼容事件流导出器"
```

---

## Chunk 8: 协议文档（SKILL.md / modes / templates）

### Task 8.1: 障碍卡片与报告模板

**Files:**
- Create: `skills/math-search/templates/obstacle_card.md`
- Create: `skills/math-search/templates/report_template.md`

- [ ] **Step 1: 写障碍卡片模板**（按 spec §2.4 字段 + 指纹词汇表）

```
# 障碍卡片 {card-id}
- 目标: {目标命题}
- 障碍陈述: {当前无法越过的最小命题}
- 指纹: {量词结构}(点态/存在/全称/逐层/密度型) | {对象类}(因子/和集/盒/相对代数性/绝对超越性/整除性/计数) | {耦合}(跨层/自适应/无耦合/符号保持)
- 已排除方法类: {逐个列出并附证明来源(note)}
- 候选开放类: {未被排除、仍有希望的方向}
- 参考节点: {相关探索树节点 id}
```

- [ ] **Step 2: 写报告模板**（按 spec §7.1）

```
# M3 会话研究报告 {session-id}
- 会话目标与障碍卡片: {target} / {obstacle_card_ref}
## 模式运行摘要
- computation: {预算, 节点数, 成功/失败}
- tool_discovery: {预算, 节点数, 成功/失败}
- invention: {预算, 节点数, 成功/失败}
## 发现的定理/证书
- {Lean 绑定定理: file::theorem, level}
## 失败路径
- {no-go 定理/反例, 来源}
## 未验证声明
- {锁在 in_progress 的节点及缺失原因}
## 下一步建议
- {含模式切换理由}
```

- [ ] **Step 3: Commit**

```bash
git add skills/math-search/templates/
git commit -m "docs: 障碍卡片与报告模板"
```

### Task 8.2: 三模式子协议

**Files:**
- Create: `skills/math-search/modes/mode1-computation.md`
- Create: `skills/math-search/modes/mode2-tool-discovery.md`
- Create: `skills/math-search/modes/mode3-invention.md`

- [ ] **Step 1: 写三份模式文档**（各含：目标/启动/执行准则/成功退出/失败退出/转换规则，按 spec §3 展开，共约 60 行）

- [ ] **Step 2: Commit**

```bash
git add skills/math-search/modes/
git commit -m "docs: 三模式子协议"
```

### Task 8.3: 主协议 `SKILL.md`

**Files:**
- Create: `skills/math-search/SKILL.md`

- [ ] **Step 1: 写 SKILL.md**（按 spec §0-§9 组织：设计原则、启动流程、探索树追加规则、三模式决策门、审计门、预算、交互、产出三件套、命令参考）

```markdown
# M3 三模式数学搜索协议

用三"模式"组织数学研究的搜索：模式一自洽计算、模式二工具发现、模式三新数学发明。
探索树（append-only JSON）是唯一真实来源；结论状态由证据派生，成功必须过 Lean
核验晋升门；失败探索是一等公民。

## 启动流程
1. 建障碍卡片（templates/obstacle_card.md）：目标/障碍陈述/指纹/已排除类/候选类。
2. 建树：`python3 orchestrator/tree_lib.py new --root <id> --target <问题> --obstacle-card <card> -o <tree>.json`
3. 可选：导入既有工作：`import_workspace.py draft <log> -o draft.json` → 人工审核 → `commit`。
4. 按障碍指纹选择模式（mode1/2/3 文档），配置预算与交互策略。

## 追加规则（append-only）
- agent 只写证据字段（claim/result/type/mode/parent_ids 等，字段归属见 spec §2.3）。
- 引擎字段（status/verified/L2/...）仅由 audit_gate.py/lean_check.py 写。
- 失败永不删除：failed/withdrawn/superseded 经 revision_of 修订。

## 审计门
- L1 合理性：任何新结论；L2 Lean 核验：升级"发现"；L3 突破：需用户确认。
- `audit_gate.py gate tree.json <node-id>`：晋升门（反例/no_go 直接 failed）。

## 预算与交互
- session.budgets 配置三模式独立预算；耗尽强制停止并询问。
- 交互策略 confirm_at_nodes | autonomous 在 session.interaction_policy。

## 产出三件套
- reports/<session>/report.md、explorations/<session>.json、viz/<session>.html。

## 命令参考
- 建树: tree_lib.py new/validate
- 导入: import_workspace.py scan/draft/commit
- 核验: lean_check.py verify <tree> <node-id> | probe --file --theorem
- 门: audit_gate.py gate <tree> <node-id>
- 可视化: build_tree.py <tree> -o viz/tree.html
- 上传: upload_proofs.py status/upload <tree>
- 导出: export_pw.py <tree> --out output/pw-events.json
```

- [ ] **Step 2: Commit**

```bash
git add skills/math-search/SKILL.md
git commit -m "docs: M3 主协议 SKILL.md"
```

---

## Chunk 9: 端到端流程演练与集成验证

### Task 9.1: 合成演练测试（§9）

**Files:**
- Create: `skills/math-search/tests/test_e2e_pipeline.py`

三个合成问题（可解/已知 no-go/开放）走完整 pipeline。

- [ ] **Step 1: 写失败测试**

`skills/math-search/tests/test_e2e_pipeline.py`:
```python
import json
import sys
from pathlib import Path

import pytest

ORCH = Path(__file__).resolve().parents[1] / "orchestrator"
sys.path.insert(0, str(ORCH))

from tree_lib import new_node, new_tree, save_tree  # noqa: E402
import build_tree  # noqa: E402
import upload_proofs  # noqa: E402
import export_pw  # noqa: E402
import audit_gate  # noqa: E402


def ok_binding():
    return {
        "theorem": "add_comm", "file": "lean/Foo.lean",
        "run": "lake build lean/Foo.lean",
        "deny_proofs_axioms": True,
        "lock": {"toolchain": "tc", "lake_manifest_ref": "lake-manifest.json"},
        "verified": True, "verified_at": None,
    }


def test_e2e_pipeline(tmp_path, monkeypatch):
    # 建立真实存在的 lean 文件，供上传复制 proof.lean
    lean_dir = tmp_path / "lean"
    lean_dir.mkdir(exist_ok=True)
    (lean_dir / "Foo.lean").write_text("theorem add_comm : True := by trivial\n", encoding="utf-8")
    ok = ok_binding()
    ok["file"] = str(lean_dir / "Foo.lean")

    tree = new_tree(root="urn:m3:tree:e2e", target="综合演练", obstacle_card_ref="c.md")
    solved = new_node(node_id="urn:m3:node:s", type="certificate", mode="computation", claim="已解决")
    solved["status"] = "success"
    solved["verification_level"] = "V1"
    solved["audit"] = {"L1_passed": True, "L2_passed": True, "audit_log": []}
    solved["lean_binding"] = ok

    nog = new_node(node_id="urn:m3:node:g", type="no_go", mode="invention", claim="方法X被证排除")
    nog["status"] = "failed"

    openq = new_node(node_id="urn:m3:node:o", type="hypothesis", mode="tool_discovery", claim="开放问题")

    tree["nodes"] = [solved, nog, openq]
    tree_path = tmp_path / "tree.json"
    save_tree(tree, str(tree_path))

    # 可视化包含全部节点（失败可见）
    html = build_tree.render(str(tree_path))
    for cid in ["urn:m3:node:s", "urn:m3:node:g", "urn:m3:node:o"]:
        assert cid in html

    # 上传：仅成功节点（归档目录 = 原始 root id，与实现一致）
    monkeypatch.setattr(upload_proofs, "_lean_verify_ok", lambda t, n: True)
    upload_proofs.upload(str(tree_path), out_root=str(tmp_path / "uploads"))
    with open(tree_path, encoding="utf-8") as fh:
        updated = json.load(fh)
    assert updated["nodes"][0]["uploaded_at"] is not None
    arch = tmp_path / "uploads" / "urn:m3:tree:e2e"
    assert arch.exists()
    entries = list((arch / "proofs").iterdir())
    assert len(entries) == 1  # 只有 success 节点

    # 导出
    events = export_pw.export(str(tree_path))
    types = [e["type"] for e in events]
    assert "claim.publish" in types
    assert "challenge.open" in types

    # 树仍可被 gate（不报错）
    res = audit_gate.gate(str(tree_path), "urn:m3:node:o", run_lean=lambda t, n: {"verified": False, "failed_steps": []})
    assert res["status"] in ("in_progress", "success", "failed")


def test_gate_rejects_axiom_free(tmp_path):
    """合成场景：找不到 Lean 证明的节点不能升级。"""
    tree = new_tree(root="urn:m3:tree:e2e", target="t", obstacle_card_ref="c.md")
    n = new_node(node_id="urn:m3:node:n", type="certificate", mode="computation", claim="未证")
    n["audit"] = {"L1_passed": True, "L2_passed": False, "audit_log": []}
    n["lean_binding"] = {
        "theorem": "t", "file": "lean/T.lean", "run": "lake build lean/T.lean",
        "deny_proofs_axioms": True,
        "lock": {"toolchain": "tc", "lake_manifest_ref": "lake-manifest.json"},
        "verified": False, "verified_at": None,
    }
    tree["nodes"] = [n]
    tree_path = tmp_path / "tree.json"
    save_tree(tree, str(tree_path))
    res = audit_gate.gate(str(tree_path), n["id"], run_lean=lambda t, nid: {"verified": False, "failed_steps": ["compile"]})
    assert res["status"] == "in_progress"
    assert "核验" in " ".join(res["reasons"])
```

- [ ] **Step 2: 运行测试确认失败**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/test_e2e_pipeline.py -v`
Expected: FAIL（依赖模块未全部实现，或 import 错误）

- [ ] **Step 3: 运行全部测试确认通过**

Run: `cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests tests/ -v`
Expected: 全部通过（若失败修复）

- [ ] **Step 4: 真实试点端到端演练（人工审核）**

```bash
cd /Users/alexyu/Documents/ChatGPT/math
python3 skills/math-search/orchestrator/import_workspace.py draft erdos_straus/research_log.md -o /tmp/m3-draft.json
python3 skills/math-search/orchestrator/build_tree.py /tmp/m3-draft.json -o /tmp/m3-tree.html
python3 skills/math-search/orchestrator/export_pw.py /tmp/m3-draft.json --out /tmp/m3-events.json
```
Expected: 三者均成功；检查 /tmp/m3-tree.html 可在浏览器打开并显示全部节点（含失败）。

- [ ] **Step 5: Commit**

```bash
git add skills/math-search/tests/test_e2e_pipeline.py
git commit -m "test: 端到端协议演练（建树/核验/可视化/上传/导出）"
```

---

## 完成清单（Done 定义）

- [ ] 全部 9 个 task 的测试通过（`cd /Users/alexyu/Documents/ChatGPT/math && python3 -m pytest skills/math-search/tests -v` 全绿）
- [ ] 6 个脚本均有 CLI：tree_lib / lean_check / audit_gate / import_workspace / upload_proofs / export_pw
- [ ] `build_tree.py` 输出单文件 HTML 可直接打开查看
- [ ] 试点 `erdos_straus/research_log.md` 能 scan/draft 出草稿树
- [ ] `upload_proofs.py verify` 子命令按 `verify.json` 的 `verified` 布尔值判断（非仅字段存在）
- [ ] 全部提交记录存在，spec/plan 均收在 docs/