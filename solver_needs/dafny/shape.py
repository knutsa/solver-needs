"""The shape of an assertion: is its equality between collections, is it nonlinear.

The equality-seed probe labels a passing seed AX when one side of the
equality has collection type (sequence, set, multiset, map, string, or
their ``Keys``, ``Values`` and ``Items``) and INST otherwise. The type is
read from the AST mapping the Dafny fork writes (``--ast-mapping``) when
one exists for the source, and from the text otherwise.

Usage (writes ``work/ast/<source>.json`` for every source of a dataset)::

    uv run python -m solver_needs.dafny.shape data/essential/essential_dafny_z3.json
"""

import argparse
import json
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from solver_needs import config
from solver_needs.dafny.source import BOOL_OPS, top_level_split

AST_DIR = config.WORK / "ast"
COLLECTION_NODES = {
    "SeqSlice",
    "SeqDisplayExpr",
    "SeqUpdate",
    "SetDisplayExpr",
    "MultiSetDisplayExpr",
    "MultiSetFormingExpr",
    "SeqConstructionExpr",
    "SetComprehension",
}
COLLECTION_TYPES = ("seq", "set", "multiset", "map", "iset", "imap", "string")
COLLECTION_MEMBERS = {"Keys", "Values", "Items"}
COLLECTION_TEXT_RE = re.compile(
    r"\[\.\.|\.\.\]|\+\s*\[|\{|\.Keys|\.Values|\.Items|multiset\(|\bset\b|\bseq\("
)
NONLINEAR_TEXT_RE = re.compile(r"[*/%]|\d\.\d")


def ast_path(source_rel: str) -> Path:
    """Where the AST mapping of a source (path relative to the repository root) is kept."""
    return AST_DIR / (source_rel.replace("/", "__") + ".json")


def generate(source_rel: str) -> tuple[str, bool]:
    """Run the fork's ``--ast-mapping`` on one source; returns ``(source, produced)``."""
    out = ast_path(source_rel)
    cmd = [
        "dotnet",
        str(config.dafny_dll()),
        "verify",
        str(config.ROOT / source_rel),
        "--allow-warnings",
        "--solver-path",
        str(config.z3()),
        "--verification-time-limit",
        "60",
        "--ast-mapping",
        str(out),
    ]
    subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    return source_rel, out.exists()


def load_ast_node(source_rel: str, line: int) -> tuple[dict | None, dict]:
    """The mapping's node of the assertion at ``line`` and the method's variables, if mapped."""
    path = ast_path(source_rel)
    if not path.exists():
        return None, {}
    ast = json.loads(path.read_text())
    for method in ast.get("methods", []):
        for assertion in method.get("assertions", []):
            if assertion.get("location", {}).get("line") == line:
                return assertion, method.get("variables", {})
    return None, {}


def is_collection(node_id: str, nodes: dict, variables: dict) -> bool | None:
    """Whether an expression node has collection type; None when the mapping cannot tell."""
    node = nodes[node_id]
    kind = node["type"]
    if kind in COLLECTION_NODES:
        return True
    if kind == "Identifier":
        vtype = variables.get(node.get("variable", ""), {}).get("type", "")
        return vtype.split("<")[0] in COLLECTION_TYPES if vtype else None
    if kind == "MemberSelect":
        return True if node.get("name") in COLLECTION_MEMBERS else None
    if kind == "BinaryExpr" and node.get("op") in ("Add", "Sub"):
        verdicts = [is_collection(c, nodes, variables) for c in node["children"]]
        return True if True in verdicts else (None if None in verdicts else False)
    if kind in ("Old", "TernaryExpr", "IfThenElse"):
        verdicts = [is_collection(c, nodes, variables) for c in node["children"]]
        return True if True in verdicts else None
    if kind == "FunctionCall":
        return None
    return False


def shape_from_ast(assertion: dict, variables: dict) -> dict:
    """Shape of an assertion from its AST mapping node."""
    nodes = assertion["expressionAst"]
    root = assertion["expressionId"]
    shape = {"collection_eq": False, "nonlinear": False, "unknown_eq": False}

    def walk_eq(node_id: str) -> None:
        node = nodes[node_id]
        if node["type"] == "BinaryExpr" and node.get("op") in ("Imp", "And", "Iff"):
            children = node["children"][1:] if node.get("op") == "Imp" else node["children"]
            for c in children:
                walk_eq(c)
        elif node["type"] == "BinaryExpr" and node.get("op") in ("Eq", "Neq"):
            verdicts = [is_collection(c, nodes, variables) for c in node["children"]]
            if True in verdicts:
                shape["collection_eq"] = True
            elif None in verdicts:
                shape["unknown_eq"] = True

    walk_eq(root)
    for node in nodes.values():
        if node["type"] == "BinaryExpr" and node.get("op") in ("Div", "Mod"):
            shape["nonlinear"] = True
        if node["type"] == "BinaryExpr" and node.get("op") == "Mul":
            kinds = [nodes[c]["type"] for c in node["children"]]
            if "Literal" not in kinds:
                shape["nonlinear"] = True
        if node["type"] == "Literal" and "." in str(node.get("value", "")):
            shape["nonlinear"] = True
    return shape


def shape_from_text(expr: str) -> dict:
    """Shape of an assertion from its text, when no AST mapping is available."""
    has_eq = any("==" in a for a in top_level_split(expr, BOOL_OPS))
    return {
        "collection_eq": bool(has_eq and COLLECTION_TEXT_RE.search(expr)),
        "nonlinear": bool(NONLINEAR_TEXT_RE.search(expr)),
        "unknown_eq": has_eq,
    }


def shape_of(source_rel: str, line: int, expr: str) -> dict:
    """Shape of the assertion at ``line`` of ``source_rel``, from the AST mapping if it exists."""
    node, variables = load_ast_node(source_rel, line)
    shape = shape_from_ast(node, variables) if node else shape_from_text(expr)
    shape["from_ast"] = node is not None
    return shape


def main() -> int:
    """Generate the AST mapping of every source in a dataset and report unmapped assertions."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("dataset", type=Path, help="an essential-assertion dataset")
    parser.add_argument("--workers", type=int, default=6)
    args = parser.parse_args()

    dataset = json.loads(args.dataset.read_text())
    sources = sorted({a["source_path"] for a in dataset["assertions"]})
    AST_DIR.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        produced = dict(pool.map(generate, sources))

    unmapped = []
    for a in dataset["assertions"]:
        if not produced[a["source_path"]]:
            unmapped.append((a["key"], "no mapping produced"))
            continue
        ast = json.loads(ast_path(a["source_path"]).read_text())
        lines = {
            x.get("location", {}).get("line")
            for m in ast.get("methods", [])
            for x in m.get("assertions", [])
        }
        if a["line"] not in lines:
            unmapped.append((a["key"], "assert line not in mapping"))

    print(
        f"{len(sources)} sources, {len(dataset['assertions'])} assertions, {len(unmapped)} unmapped"
    )
    for key, why in unmapped:
        print(f"  {key}: {why}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
