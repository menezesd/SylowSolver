"""Tree-structured proof output for cleaner visualization."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Dict, List, Optional, Set, Tuple

if TYPE_CHECKING:
    from .facts import Disjunction, Fact


@dataclass
class DisjMeta:
    """Metadata for a disjunction to display it nicely."""

    var_name: str
    pred_name: str
    branch_values: List[str]


@dataclass
class FactInfo:
    """Simplified fact info for display."""

    label: str
    fact: "Fact"
    theorem: Optional[str]
    deps: List[str]


@dataclass
class CaseBranch:
    """A branch in a case split."""

    disj_id: str
    branch_idx: int
    label: str
    children: "ProofTree"


@dataclass
class ProofTree:
    """Tree structure for proof."""

    kind: str  # "empty", "fact", "case_split", "contradiction"
    fact_info: Optional[FactInfo] = None
    next_tree: Optional["ProofTree"] = None
    disj_id: Optional[str] = None
    var_name: Optional[str] = None
    branches: List[CaseBranch] = field(default_factory=list)
    explanation: Optional[str] = None


def infer_disj_meta(disj: "Disjunction") -> DisjMeta:
    """Infer human-readable metadata from a disjunction's facts."""
    facts = disj.facts
    if not facts:
        return DisjMeta("?", "false", [])

    pred_name = facts[0].name

    all_args = [f.args for f in facts]
    if not all_args or not all_args[0]:
        return DisjMeta("?", pred_name, [str(i) for i in range(len(facts))])

    transposed = list(zip(*all_args))
    varying_idx = None
    for i, col in enumerate(transposed):
        if len({str(x) for x in col}) > 1:
            varying_idx = i
            break

    var_name = _make_var_name(pred_name, varying_idx, facts[0].args)
    if varying_idx is not None:
        branch_values = [str(f.args[varying_idx]) for f in facts]
    else:
        branch_values = [str(i) for i in range(len(facts))]

    return DisjMeta(var_name, pred_name, branch_values)


def _make_var_name(pred_name: str, varying_idx: Optional[int], args: List) -> str:
    """Create a nice variable name for the varying argument."""
    subscript_map = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")

    if pred_name == "num_sylow" and varying_idx == 2:
        if len(args) >= 2:
            p = str(args[0])
            return f"n{p.translate(subscript_map)}"
        return "n"
    elif pred_name == "sylow_order" and varying_idx == 2:
        if len(args) >= 2:
            p = str(args[0])
            return f"ord{p.translate(subscript_map)}"
        return "ord"
    elif varying_idx is not None:
        return f"x{str(varying_idx).translate(subscript_map)}"
    else:
        return "case"


def build_proof_tree(
    facts: List["Fact"],
    disjunctions: List["Disjunction"],
    disj_meta: Dict[str, DisjMeta],
) -> ProofTree:
    """Build a proof tree from the environment facts."""
    grouped: Dict[frozenset[Tuple[str, int]], List["Fact"]] = {}
    for fact in facts:
        key = frozenset(fact.dis_ancestors)
        grouped.setdefault(key, []).append(fact)
    return _build_tree(disj_meta, frozenset(), grouped)


def _build_tree(
    meta_map: Dict[str, DisjMeta],
    current_case: frozenset[Tuple[str, int]],
    grouped_facts: Dict[frozenset[Tuple[str, int]], List["Fact"]],
) -> ProofTree:
    """Build tree recursively, grouping by case context."""
    matching = grouped_facts.get(current_case, [])
    if not matching and len(grouped_facts) == 0:
        return ProofTree(kind="empty")

    fact_infos = [
        FactInfo(
            label=fe.label or "?",
            fact=fe,
            theorem=fe.conc_thm.name if fe.conc_thm else None,
            deps=fe.dependencies,
        )
        for fe in matching
    ]

    has_contradiction = any(fi.fact.name == "false" for fi in fact_infos)

    if has_contradiction:
        if not fact_infos:
            return ProofTree(kind="empty")
        result = ProofTree(kind="contradiction", explanation="contradiction")
        for fi in reversed(fact_infos[:-1]):
            result = ProofTree(kind="fact", fact_info=fi, next_tree=result)
        return result

    next_split = _find_next_split(current_case, grouped_facts)
    if next_split is None:
        result = ProofTree(kind="empty")
        for fi in reversed(fact_infos):
            result = ProofTree(kind="fact", fact_info=fi, next_tree=result)
        return result

    disj_id, _branches = next_split
    meta = meta_map.get(disj_id, DisjMeta("case", "unknown", []))

    case_branches = []
    for idx, label in enumerate(meta.branch_values):
        new_case = frozenset(tuple(current_case | {(disj_id, idx)}))
        subtree = _build_tree(meta_map, new_case, grouped_facts)
        case_branches.append(CaseBranch(disj_id, idx, label, subtree))

    result = ProofTree(
        kind="case_split",
        disj_id=disj_id,
        var_name=meta.var_name,
        branches=case_branches,
    )
    for fi in reversed(fact_infos):
        result = ProofTree(kind="fact", fact_info=fi, next_tree=result)
    return result


def _find_next_split(
    current_case: frozenset[Tuple[str, int]],
    grouped_facts: Dict[frozenset[Tuple[str, int]], List["Fact"]],
) -> Optional[Tuple[str, List[int]]]:
    """Find the next case split point."""
    extensions: List[Tuple[str, int]] = []
    for anc in grouped_facts.keys():
        if current_case.issubset(anc):
            for d, i in anc - current_case:
                extensions.append((d, i))

    if not extensions:
        return None

    d, _ = extensions[0]
    branches = list(set(i for d2, i in extensions if d2 == d))
    return (d, branches)


def render_tree(
    facts: List["Fact"],
    disjunctions: List["Disjunction"],
    disj_meta: Dict[str, DisjMeta],
) -> List[str]:
    """Render the proof as ASCII art tree."""
    # Filter to essential facts
    essential = _get_essential_facts(facts)
    tree = build_proof_tree(essential, disjunctions, disj_meta)

    # Find contradictions for summary
    contradictions = [f for f in facts if f.name == "false"]
    summary = _render_summary(disj_meta, contradictions)

    lines = ["", "Proof Structure:", "════════════════", ""]
    lines.extend(_render_node(disj_meta, "", tree))
    lines.extend(summary)
    return lines


def _get_essential_facts(facts: List["Fact"]) -> List["Fact"]:
    """Get only facts that contribute to contradictions."""
    # Build label -> fact map
    fact_map = {f.label: f for f in facts if f.label}

    # Find all false() facts
    contradictions = [f for f in facts if f.name == "false"]

    # Trace back to find essential facts
    essential_labels: Set[str] = set()
    for contra in contradictions:
        _trace_essential(fact_map, contra.label, essential_labels)

    # Filter and deduplicate
    seen: Set[Tuple[Tuple, frozenset]] = set()
    result = []
    for f in facts:
        if f.label not in essential_labels:
            continue
        key = (f.name, tuple(f.args)), frozenset(f.dis_ancestors)
        if key not in seen:
            seen.add(key)
            result.append(f)
    return result


def _trace_essential(fact_map: Dict[str, "Fact"], label: Optional[str], visited: Set[str]) -> None:
    """Recursively trace dependencies to find essential facts."""
    if not label or label in visited:
        return
    visited.add(label)

    fact = fact_map.get(label)
    if fact:
        for dep in fact.dependencies:
            _trace_essential(fact_map, dep, visited)


def _render_node(meta: Dict[str, DisjMeta], prefix: str, tree: ProofTree) -> List[str]:
    """Render a single node of the proof tree."""
    if tree.kind == "empty":
        return []

    if tree.kind == "contradiction":
        return [f"{prefix}└─ ⊥ (contradiction)"]

    if tree.kind == "fact":
        fi = tree.fact_info
        assert fi is not None
        fact_str = f"{fi.fact.name}({', '.join(str(a) for a in fi.fact.args)})"
        thm_str = f"[{fi.theorem}]" if fi.theorem else "[hypothesis]"
        line = f"{prefix}• {fi.label}: {fact_str} {thm_str}"
        rest = _render_node(meta, prefix, tree.next_tree) if tree.next_tree else []
        return [line] + rest

    if tree.kind == "case_split":
        header = f"{prefix}┌─ Case split on {tree.var_name}:"
        lines = [header]
        total = len(tree.branches)
        for idx, branch in enumerate(tree.branches):
            is_last = idx == total - 1
            connector = "└" if is_last else "├"
            child_prefix = prefix + ("  " if is_last else "│ ")
            branch_header = f"{prefix}{connector}─ {branch.label}:"
            lines.append(branch_header)
            lines.extend(_render_node(meta, child_prefix, branch.children))
        return lines

    return []


def render_clean(
    facts: List["Fact"],
    disjunctions: List["Disjunction"],
    disj_meta: Dict[str, DisjMeta],
) -> List[str]:
    """Render cleaner linear output with improvements:
    1. Filter to essential facts only
    2. Group by case context with headers
    3. Add proof summary
    4. Highlight contradictions
    """
    # Get essential facts
    essential = _get_essential_facts(facts)

    # Group by case context
    grouped = _group_by_case_context(essential)

    # Render each group
    lines: List[str] = []
    for ctx, group_facts in grouped:
        lines.extend(_render_case_group(ctx, group_facts, disj_meta))

    # Add summary
    contradictions = [f for f in facts if f.name == "false"]
    lines.extend(_render_summary(disj_meta, contradictions))

    return lines


def _group_by_case_context(facts: List["Fact"]) -> List[Tuple[frozenset, List["Fact"]]]:
    """Group facts by their case context, sorted by context size."""
    contexts: Set[frozenset] = set()
    for f in facts:
        contexts.add(frozenset(f.dis_ancestors))

    sorted_contexts = sorted(contexts, key=len)

    return [
        (ctx, [f for f in facts if frozenset(f.dis_ancestors) == ctx]) for ctx in sorted_contexts
    ]


def _render_case_group(
    ctx: frozenset, facts: List["Fact"], disj_meta: Dict[str, DisjMeta]
) -> List[str]:
    """Render a case group with header."""
    if not ctx:
        header = ["═══ Hypotheses ═══", ""]
    else:
        ctx_str = _render_case_context(ctx, disj_meta)
        header = [f"═══ Case: {ctx_str} ═══", ""]

    body = []
    for f in facts:
        body.extend(_render_fact_clean(f, disj_meta))

    return header + body


def _render_case_context(ctx: frozenset, disj_meta: Dict[str, DisjMeta]) -> str:
    """Render a case context as a string."""
    parts = []
    for d, idx in sorted(ctx):
        meta = disj_meta.get(d)
        if meta and idx < len(meta.branch_values):
            parts.append(f"{meta.var_name}={meta.branch_values[idx]}")
        else:
            parts.append(f"{d}.{idx}")
    return ", ".join(parts)


def _render_fact_clean(fact: "Fact", disj_meta: Dict[str, DisjMeta]) -> List[str]:
    """Render a single fact with clean formatting."""
    is_false = fact.name == "false"
    rendered_args = ", ".join(str(a) for a in fact.args)
    fact_str = "⊥ (contradiction)" if is_false else f"{fact.name}({rendered_args})"
    label_str = fact.label or "?"

    if fact.conc_thm:
        thm_str = f"by {_pretty_theorem_name(fact.conc_thm.name)}"
    else:
        thm_str = "hypothesis"
    dep_str = ""
    if fact.dependencies:
        dep_str = " from " + " ".join(fact.dependencies)

    prefix = "  ✓ " if is_false else "  "
    return [
        f"{prefix}{label_str} : {fact_str}",
        f"{prefix}    {thm_str}{dep_str}",
        "",
    ]


def _render_summary(disj_meta: Dict[str, DisjMeta], contradictions: List["Fact"]) -> List[str]:
    """Render proof summary showing closed branches."""
    if not contradictions:
        return ["", "No contradictions found."]

    # Group by case context
    by_context: Dict[frozenset, List["Fact"]] = {}
    for c in contradictions:
        ctx = frozenset(c.dis_ancestors)
        by_context.setdefault(ctx, []).append(c)

    num_branches = len(by_context)
    plural = "" if num_branches == 1 else "es"

    lines = [
        "",
        "═══ Proof Summary ═══",
        "",
        f"Proved contradiction in {num_branches} branch{plural}:",
        "",
    ]

    for ctx in sorted(by_context.keys(), key=len):
        contra = by_context[ctx][0]
        ctx_str = _render_case_context(ctx, disj_meta) if ctx else "base case"
        thm_str = _pretty_theorem_name(contra.conc_thm.name) if contra.conc_thm else "hypothesis"
        lines.append(f"  ✓ {ctx_str} → {thm_str}")

    return lines


def _pretty_theorem_name(name: str) -> str:
    """Pretty-print theorem names."""
    name_map = {
        "sylow": "Sylow's theorem",
        "single_sylow_normal": "unique Sylow subgroup is normal",
        "not_simple": "simple ∧ not_simple → ⊥",
        "counting_contradiction": "element counting",
        "alternating_order": "order of alternating group",
        "alternating_simple": "Aₙ is simple (n≥5)",
        "lagrange": "Lagrange's theorem",
        "divides_contradiction": "divisibility contradiction",
        "embed_An": "embedding into Aₙ",
        "coset_action": "coset action",
        "simple_group_action": "simple group action",
        "count_order_pk_elements": "counting p^k-order elements",
        "subgroup_index": "subgroup index",
    }
    return name_map.get(name, name)
