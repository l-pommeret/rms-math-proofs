#!/usr/bin/env python3
"""Build publication sections from audited Markdown answers.

The captured answers use a small, predictable Markdown dialect.  In particular,
display math delimiters were captured as lines containing ``[`` and ``]`` and
some alignment equals signs became lines of repeated ``=``.  This module repairs
those *typographical* capture artefacts while leaving the mathematical prose and
formulae in their original order.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RESPONSES = ROOT / "responses"
REVIEWS = ROOT / "reviews"
SECTIONS = ROOT / "publication" / "sections"


VERDICT_NAMES = {
    "A": "complete and apparently correct",
    "B": "essentially complete with a small repair",
    "C": "substantial progress, but incomplete",
    "D": "incorrect, negligible, or mismatched",
}


def _repair_math(text: str) -> str:
    """Repair mechanical damage introduced while capturing rendered TeX."""
    text = re.sub(r"={3,}", "=", text)
    text = re.sub(r"^\s*#\s*", "= ", text)
    text = text.replace(r"\operatorname{rem}*{", r"\operatorname{rem}_{")
    text = text.replace(r"\operatorname*{arg,max}", r"\operatorname*{arg\,max}")
    text = text.replace("*{", "_{")
    text = text.replace(r"\operatorname_{arg\,max}", r"\operatorname*{arg\,max}")
    text = text.replace(r"\operatorname_{argmin}", r"\operatorname*{argmin}")
    text = text.replace(r"\operatorname_{argmax}", r"\operatorname*{argmax}")
    text = re.sub(r"(?<=[)\]])\*([A-Za-z])\b", r"_\1", text)
    for command in ("sum", "prod", "max", "min", "lim", "varepsilon"):
        text = text.replace(rf"\{command}*{{", rf"\{command}_{{")
    text = re.sub(r"\\([A-Za-z]+)!", r"\\\1\\!", text)
    text = text.replace("O!", r"O\!")
    text = text.replace(r"|h|*\infty", r"\lVert h\rVert_\infty")
    text = text.replace(r"\right|*\infty", r"\right\rVert_\infty")
    text = text.replace(r"\left|", r"\left\lvert ")
    text = text.replace(r"\right|", r"\right\rvert ")
    text = text.replace(r"\left{", r"\left\{")
    text = text.replace(r"\right}", r"\right\}")
    text = text.replace(r"\bigl{", r"\bigl\{")
    text = text.replace(r"\bigr}", r"\bigr\}")
    text = text.replace(",,", ",")
    text = text.replace("≤", r"\le ").replace("≥", r"\ge ")
    text = text.replace("∞", r"\infty ").replace("∈", r"\in ")
    text = text.replace("→", r"\to ").replace("⇒", r"\Rightarrow ")
    text = text.replace("±", r"\pm ").replace("≠", r"\ne ")
    text = text.replace("⋯", r"\cdots ").replace("ε", r"\varepsilon ")
    text = text.replace("α", r"\alpha ").replace("β", r"\beta ")
    text = text.replace("λ", r"\lambda ").replace("ρ", r"\rho ")
    text = text.replace("δ", r"\delta ").replace("σ", r"\sigma ")
    text = text.replace(r"\le r\j\ne", r"\le r\\j\ne")
    text = text.replace(r"<15\1\le", r"<15\\1\le")
    text = text.replace(r"\i\ne", r"\\i\ne")
    return text


def _looks_like_math(content: str) -> bool:
    if not content or len(content) > 180:
        return False
    if any(token in content for token in ("\\", "_", "^", "=", "<", ">", "∞", "∈", "⇒", "→")):
        return True
    if re.fullmatch(r"[A-Za-z0-9]+(?:[+\-][A-Za-z0-9]+)*", content):
        return True
    return bool(re.fullmatch(r"[A-Za-z][A-Za-z0-9]*\([^)]*\)", content))


def _escape_text(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "≤": r"\(\le\)",
        "≥": r"\(\ge\)",
        "∞": r"\(\infty\)",
        "∈": r"\(\in\)",
        "→": r"\(\to\)",
        "⇒": r"\(\Rightarrow\)",
        "±": r"\(\pm\)",
        "≠": r"\(\ne\)",
        "α": r"\(\alpha\)",
        "β": r"\(\beta\)",
        "λ": r"\(\lambda\)",
        "ρ": r"\(\rho\)",
        "δ": r"\(\delta\)",
        "σ": r"\(\sigma\)",
        "—": "---",
        "–": "--",
        "“": "``",
        "”": "''",
        "’": "'",
        "∎": r"\(\square\)",
    }
    return "".join(replacements.get(char, char) for char in text)


def _inline(text: str) -> str:
    """Convert captured inline math and the small Markdown emphasis subset."""
    output: list[str] = []
    plain: list[str] = []

    def flush() -> None:
        if plain:
            output.append(_escape_text("".join(plain)))
            plain.clear()

    i = 0
    while i < len(text):
        if text[i] == "$" and (i == 0 or text[i - 1] != "\\"):
            end = text.find("$", i + 1)
            if end >= 0:
                flush()
                output.append(r"\(" + _repair_math(text[i + 1 : end]) + r"\)")
                i = end + 1
                continue
        if text.startswith(r"\(", i):
            end = text.find(r"\)", i + 2)
            if end >= 0:
                flush()
                output.append(r"\(" + _repair_math(text[i + 2 : end]) + r"\)")
                i = end + 2
                continue
        if text.startswith("**", i):
            end = text.find("**", i + 2)
            if end >= 0:
                flush()
                output.append(r"\textbf{" + _inline(text[i + 2 : end]) + "}")
                i = end + 2
                continue
        if text[i] == "`":
            end = text.find("`", i + 1)
            if end >= 0:
                flush()
                output.append(r"\texttt{" + _escape_text(text[i + 1 : end]) + "}")
                i = end + 1
                continue
        if text[i] == "(":
            depth = 1
            end = i + 1
            while end < len(text) and depth:
                if text[end] == "(":
                    depth += 1
                elif text[end] == ")":
                    depth -= 1
                end += 1
            if depth == 0:
                content = text[i + 1 : end - 1]
                if _looks_like_math(content):
                    flush()
                    output.append(r"\(" + _repair_math(content) + r"\)")
                    i = end
                    continue
        plain.append(text[i])
        i += 1
    flush()
    return "".join(output)


def _display_line(line: str) -> str:
    # A blank source line inside ``\[...\]`` is only capture whitespace; a TeX
    # paragraph break is illegal in display math, so preserve it as a comment.
    if not line.strip():
        return "%"
    repaired = _repair_math(line)
    repaired = re.sub(r"\\+\s+\\hline", lambda _: r"\\ \hline", repaired)
    if re.fullmatch(r"\s*=+\s*", repaired):
        return "="
    repaired = re.sub(r",\s*\[(\d+(?:\.\d+)?(?:mm|cm|pt|ex|em))\]\s*$", r",\\\\[\1]", repaired)
    repaired = re.sub(r"^\s*\[(\d+(?:\.\d+)?(?:mm|cm|pt|ex|em))\]\s*$", r"\\\\[\1]", repaired)
    if repaired.endswith("\\") and not repaired.endswith("\\\\"):
        repaired += "\\"
    return repaired


def markdown_to_latex(markdown: str, *, skip_title: str | None = None) -> str:
    lines = markdown.splitlines()
    out: list[str] = []
    in_display = False
    in_code = False
    list_kind: str | None = None
    table_rows: list[list[str]] = []

    def close_list() -> None:
        nonlocal list_kind
        if list_kind:
            out.append(rf"\end{{{list_kind}}}")
            list_kind = None

    def close_table() -> None:
        nonlocal table_rows
        if not table_rows:
            return
        columns = max(len(row) for row in table_rows)
        out.extend([r"\begin{center}", r"\small", rf"\begin{{tabular}}{{{'l' * columns}}}", r"\hline"])
        for index, row in enumerate(table_rows):
            padded = row + [""] * (columns - len(row))
            out.append(" & ".join(_inline(cell.strip()) for cell in padded) + r" \\")
            if index == 0:
                out.append(r"\hline")
        out.extend([r"\hline", r"\end{tabular}", r"\end{center}"])
        table_rows = []

    for original in lines:
        line = re.sub(r"^> ?", "", original)
        stripped = line.strip()

        if stripped.startswith("```"):
            close_list()
            close_table()
            if in_code:
                out.append(r"\end{verbatim}")
            else:
                out.append(r"\begin{verbatim}")
            in_code = not in_code
            continue
        if in_code:
            out.append(line)
            continue

        if in_display:
            if stripped in {"]", "$$", r"\$\$"}:
                out.append(r"\]")
                in_display = False
            else:
                out.append(_display_line(line))
            continue
        if stripped in {"[", "$$", r"\$\$"}:
            close_list()
            close_table()
            out.append(r"\[")
            in_display = True
            continue

        if stripped.startswith("|") and stripped.endswith("|"):
            close_list()
            cells = [cell.strip() for cell in stripped[1:-1].split("|")]
            if all(re.fullmatch(r":?-{3,}:?", cell.replace(" ", "")) for cell in cells):
                continue
            table_rows.append(cells)
            continue
        close_table()

        heading = re.match(r"^(#{1,6})\s+(.+)$", stripped)
        if heading:
            close_list()
            title = heading.group(2).replace("**", "")
            if skip_title and skip_title in title:
                continue
            depth = len(heading.group(1))
            command = {1: "subsection", 2: "subsubsection", 3: "paragraph"}.get(depth, "subparagraph")
            out.append(rf"\{command}{{{_inline(title)}}}")
            continue
        if stripped == "---":
            close_list()
            out.append(r"\medskip\hrule\medskip")
            continue

        bullet = re.match(r"^\s*[*+-]\s+(.+)$", line)
        numbered = re.match(r"^\s*\d+\.\s+(.+)$", line)
        if bullet or numbered:
            wanted = "itemize" if bullet else "enumerate"
            if list_kind != wanted:
                close_list()
                list_kind = wanted
                out.append(rf"\begin{{{wanted}}}")
            out.append(r"\item " + _inline((bullet or numbered).group(1)))
            continue
        close_list()

        if not stripped:
            out.append("")
        else:
            out.append(_inline(line))

    close_list()
    close_table()
    if in_display or in_code:
        raise ValueError("unterminated Markdown block")
    return "\n".join(out).strip() + "\n"


def verdict_line(review: str, fallback: str) -> str:
    lines = review.splitlines()
    try:
        start = next(i for i, line in enumerate(lines) if line.strip() == "## Verdict") + 1
    except StopIteration:
        return VERDICT_NAMES.get(fallback, fallback)
    for line in lines[start:]:
        if line.strip():
            return line.strip()
    return VERDICT_NAMES.get(fallback, fallback)


def build_section(qid: str, item: dict) -> str:
    response_path = RESPONSES / f"{qid}.md"
    review_path = REVIEWS / f"{qid}-review.md"
    for path in (response_path, review_path):
        if not path.is_file() or not path.read_text(encoding="utf-8").strip():
            raise SystemExit(f"Required nonempty file is missing: {path.relative_to(ROOT)}")
    if not item.get("lean_scope"):
        raise SystemExit(f"{qid} is verified but has no lean_scope in pipeline.json")
    coverage = item.get("lean_coverage", "partial")
    if coverage not in {"full", "partial"}:
        raise SystemExit(f"{qid} has invalid lean_coverage {coverage!r}")

    review = review_path.read_text(encoding="utf-8")
    answer = response_path.read_text(encoding="utf-8")
    verdict = verdict_line(review, item.get("review_verdict", ""))
    coverage_title = "Lean coverage" if coverage == "full" else "Lean coverage (partial)"
    return "\n".join(
        [
            "% Generated by publication/build_sections.py; do not edit by hand.",
            r"\paragraph{Informal verdict.}",
            _inline(verdict),
            "",
            rf"\paragraph{{{coverage_title}.}}",
            _inline(item["lean_scope"]),
            "",
            r"\subsection{Audited informal answer}",
            markdown_to_latex(answer, skip_title=qid).rstrip(),
            "",
        ]
    )


def generate_sections(data: dict, *, prune: bool = True) -> list[str]:
    verified = sorted(
        (qid for qid, item in data["questions"].items() if item.get("lean_status") == "verified"),
        key=lambda qid: int(qid.removeprefix("Q")),
    )
    SECTIONS.mkdir(parents=True, exist_ok=True)
    for qid in verified:
        (SECTIONS / f"{qid}.tex").write_text(build_section(qid, data["questions"][qid]), encoding="utf-8")
    if prune:
        expected = {f"{qid}.tex" for qid in verified}
        for path in SECTIONS.glob("Q*.tex"):
            if path.name not in expected:
                path.unlink()
    return verified


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, default=ROOT / "pipeline.json")
    args = parser.parse_args()
    data = json.loads(args.manifest.read_text(encoding="utf-8"))
    qids = generate_sections(data)
    print(f"Generated {len(qids)} sections: {', '.join(qids)}")


if __name__ == "__main__":
    main()
