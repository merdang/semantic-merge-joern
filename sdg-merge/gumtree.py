"""
Subprocess wrapper around the GumTree CLI.

The binary is resolved from `GUMTREE_BIN`, else `gumtree` on PATH.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path


class GumTreeNotFound(RuntimeError):
    pass


class GumTreeError(RuntimeError):
    pass


@dataclass
class AstNode:
    type: str
    label: str
    pos: int           # 0-based character offset of node start
    length: int        # node length in characters
    children: list["AstNode"] = field(default_factory=list)

    @property
    def end(self) -> int:
        return self.pos + self.length


def _binary() -> str:
    return os.environ.get("GUMTREE_BIN", "gumtree")


def _run(*args: str, timeout: float = 60.0) -> str:
    try:
        result = subprocess.run(
            [_binary(), *args],
            capture_output=True, text=True, check=True, timeout=timeout,
        )
        return result.stdout
    except FileNotFoundError as e:
        raise GumTreeNotFound(
            f"gumtree CLI not found (tried {_binary()!r}). "
            "Set GUMTREE_BIN to the full path of the gumtree script, or put it on PATH."
        ) from e
    except subprocess.CalledProcessError as e:
        raise GumTreeError(
            f"`gumtree {' '.join(args)}` exited {e.returncode}: {e.stderr.strip()}"
        ) from e
    except subprocess.TimeoutExpired as e:
        raise GumTreeError(f"`gumtree {' '.join(args)}` timed out after {timeout}s") from e


def parse_tree(source: Path) -> AstNode:
    """Parse a source file with GumTree and return the AST root."""
    raw = _run("parse", str(source), "-f", "JSON")
    data = json.loads(raw)
    root = data["root"] if "root" in data else data
    return _to_ast(root)


def _to_ast(d: dict) -> AstNode:
    return AstNode(
        type=str(d.get("type", "")),
        label=str(d.get("label", "")),
        pos=int(d.get("pos", 0)),
        length=int(d.get("length", 0)),
        children=[_to_ast(c) for c in d.get("children", [])],
    )


# Match descriptor format: "Type[: label] [start,end]"
_RANGE_RE = re.compile(r"\[(\d+),(\d+)\]\s*$")


def diff_matches(
    src: Path, dst: Path
) -> list[tuple[tuple[int, int], tuple[int, int]]]:
    """GumTree's AST-node matches, as 0-based character offsets:
    ((src_start, src_end), (dst_start, dst_end))."""
    raw = _run("textdiff", str(src), str(dst), "-f", "JSON")
    data = json.loads(raw)
    out: list[tuple[tuple[int, int], tuple[int, int]]] = []
    for m in data.get("matches", []):
        out.append((_parse_range(m["src"]), _parse_range(m["dest"])))
    return out


def _parse_range(descriptor: str) -> tuple[int, int]:
    m = _RANGE_RE.search(descriptor)
    if not m:
        raise GumTreeError(f"unrecognised match descriptor: {descriptor!r}")
    return int(m.group(1)), int(m.group(2))


def is_available() -> bool:
    """Return True iff the gumtree binary is callable."""
    try:
        _run("--help", timeout=10.0)
        return True
    except (GumTreeNotFound, GumTreeError):
        return False
