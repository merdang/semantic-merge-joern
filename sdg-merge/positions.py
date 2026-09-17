"""
Convert GumTree's 0-based character offsets to Joern's 1-based
(line, column).
"""

from __future__ import annotations

from bisect import bisect_right


class LineIndex:
    """O(log n) lookup from char offset to (line, column), built once per file."""

    def __init__(self, source: str) -> None:
        # Sentinel at index 0, so a 1-based line number indexes directly.
        starts = [0, 0]
        for i, ch in enumerate(source):
            if ch == "\n":
                starts.append(i + 1)
        self._line_starts = starts

    def locate(self, offset: int) -> tuple[int, int]:
        """Returns 1-based (line, column) for a 0-based character offset."""
        line = bisect_right(self._line_starts, offset) - 1
        if line < 1:
            line = 1
        col = offset - self._line_starts[line] + 1
        return line, col
