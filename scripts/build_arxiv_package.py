#!/usr/bin/env python3
"""Build the flattened, comment-free arXiv source archive for the PF4 paper."""

from __future__ import annotations

from pathlib import Path
import re
import tarfile


ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPT = ROOT / "paper" / "manuscript"
OUTPUT = ROOT / "paper" / "arxiv" / "main.tex"
ARCHIVE = ROOT / "paper" / "ax.tar"
INPUT = re.compile(r"^\s*\\input\{([^}]+)\}\s*$")
FOUR_PASS_SIGNAL = (
    r"\typeout{get arXiv to do 4 passes: Label(s) may have changed. Rerun}"
)


def resolve_input(name: str, parent: Path) -> Path:
    relative = Path(name)
    if relative.suffix != ".tex":
        relative = relative.with_suffix(".tex")
    candidates = (MANUSCRIPT / relative, parent / relative)
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise FileNotFoundError(f"unresolved TeX input: {name}")


def strip_comment(line: str) -> str:
    for index, character in enumerate(line):
        if character != "%":
            continue
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and line[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2 == 0:
            return line[:index].rstrip()
    return line.rstrip()


def expand(path: Path, stack: tuple[Path, ...] = ()) -> list[str]:
    if path in stack:
        raise RuntimeError(f"recursive TeX input: {path}")
    lines: list[str] = []
    for source_line in path.read_text(encoding="utf-8").splitlines():
        uncommented = strip_comment(source_line)
        match = INPUT.match(uncommented)
        if match:
            child = resolve_input(match.group(1), path.parent)
            lines.extend(expand(child, stack + (path,)))
        elif uncommented:
            lines.append(uncommented)
        elif lines and lines[-1] != "":
            lines.append("")
    return lines


def main() -> None:
    lines = expand(MANUSCRIPT / "main.tex")
    if any(INPUT.match(line) for line in lines):
        raise RuntimeError("flattening left an input directive")
    if sum(line.startswith(r"\documentclass") for line in lines) != 1:
        raise RuntimeError("flattened source must contain one document class")
    if lines.count(r"\begin{document}") != 1:
        raise RuntimeError("flattened source must contain one document beginning")
    if lines.count(r"\end{document}") != 1 or lines[-1] != r"\end{document}":
        raise RuntimeError("flattened source must end at its sole document boundary")
    lines.append(FOUR_PASS_SIGNAL)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    data = ("\n".join(lines) + "\n").encode("ascii")
    OUTPUT.write_bytes(data)

    info = tarfile.TarInfo("main.tex")
    info.size = len(data)
    info.mode = 0o644
    info.mtime = 0
    with ARCHIVE.open("wb") as stream, tarfile.open(
        fileobj=stream, mode="w", format=tarfile.USTAR_FORMAT
    ) as archive:
        from io import BytesIO

        archive.addfile(info, BytesIO(data))

    print(
        f"wrote {OUTPUT.relative_to(ROOT)} with {len(lines)} lines and "
        f"{ARCHIVE.relative_to(ROOT)}"
    )


if __name__ == "__main__":
    main()
