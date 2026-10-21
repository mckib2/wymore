"""CLI: JSON design → TikZ figure PDFs → LaTeX report PDF."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .models import SchemaError, load_isr_package
from .render_figures import build_all_figures
from .render_report import compile_report, write_report_tex


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="techdoc",
        description="Render ISR package JSON to TikZ figure PDFs and a report PDF",
    )
    parser.add_argument(
        "--in",
        dest="infile",
        required=True,
        type=Path,
        help="Path to design.json from mbse-doc-export",
    )
    parser.add_argument(
        "--out-dir",
        required=True,
        type=Path,
        help="Output directory (figures/ and report.pdf)",
    )
    parser.add_argument(
        "--latex",
        default="pdflatex",
        help="LaTeX engine (default: pdflatex)",
    )
    parser.add_argument(
        "--skip-latex",
        action="store_true",
        help="Only write .tex sources; do not run pdflatex",
    )
    args = parser.parse_args(argv)

    try:
        data = json.loads(args.infile.read_text(encoding="utf-8"))
        doc = load_isr_package(data)
    except (OSError, json.JSONDecodeError, SchemaError) as exc:
        print(f"error: failed to load {args.infile}: {exc}", file=sys.stderr)
        return 1

    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    # Keep a copy of the input design next to the report when paths differ.
    design_copy = out_dir / "design.json"
    if args.infile.resolve() != design_copy.resolve():
        design_copy.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")

    try:
        if args.skip_latex:
            from .render_figures import write_figure_sources

            write_figure_sources(doc, out_dir / "figures")
            write_report_tex(doc, out_dir)
            print(f"wrote TeX sources under {out_dir} (skipped pdflatex)")
            return 0

        pdfs = build_all_figures(doc, out_dir, latex_cmd=args.latex)
        report_tex = write_report_tex(doc, out_dir)
        report_pdf = compile_report(report_tex, latex_cmd=args.latex)
    except RuntimeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    print(f"figures: {', '.join(str(p) for p in pdfs.values())}")
    print(f"report: {report_pdf}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
