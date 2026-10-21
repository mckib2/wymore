"""Assemble a publication-quality LaTeX report that includes figure PDFs."""

from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path
from string import Template

from .models import IsrPackageDoc
from . import theme


def _escape_latex(s: str) -> str:
    """Escape LaTeX special characters while preserving math sentinels."""
    s = (
        s.replace("×", "<<TIMES>>")
        .replace("→", "<<TO>>")
        .replace("↔", "<<IFF>>")
        .replace("—", "---")
        .replace("–", "--")
        .replace("“", "``")
        .replace("”", "''")
        .replace("‘", "`")
        .replace("’", "'")
    )
    s = (
        s.replace("\\", "\\textbackslash{}")
        .replace("&", "\\&")
        .replace("%", "\\%")
        .replace("#", "\\#")
        .replace("_", "\\_")
        .replace("{", "\\{")
        .replace("}", "\\}")
        .replace("~", "\\textasciitilde{}")
        .replace("^", "\\textasciicircum{}")
    )
    return (
        s.replace("<<TIMES>>", r"$\times$")
        .replace("<<TO>>", r"$\to$")
        .replace("<<IFF>>", r"$\leftrightarrow$")
    )


def markdown_to_latex(text: str) -> str:
    """Convert common inline Markdown formatting into clean LaTeX."""
    if not text:
        return ""

    # Replace inline code spans first using pure alphabetic sentinels
    code_spans: list[str] = []
    def _code_repl(m: re.Match) -> str:
        code_spans.append(m.group(1))
        return f"PHCODEX{len(code_spans) - 1}X"

    text = re.sub(r"`([^`]+)`", _code_repl, text)

    # Replace bold **text**
    bold_spans: list[str] = []
    def _bold_repl(m: re.Match) -> str:
        bold_spans.append(m.group(1))
        return f"PHBOLDX{len(bold_spans) - 1}X"

    text = re.sub(r"\*\*([^*]+)\*\*", _bold_repl, text)

    # Replace italic *text*
    italic_spans: list[str] = []
    def _italic_repl(m: re.Match) -> str:
        italic_spans.append(m.group(1))
        return f"PHITALICX{len(italic_spans) - 1}X"

    text = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", _italic_repl, text)

    # Escape raw text for LaTeX
    escaped = _escape_latex(text)

    # Re-substitute formatting with LaTeX commands
    for i, span in enumerate(bold_spans):
        escaped = escaped.replace(f"PHBOLDX{i}X", f"\\textbf{{{_escape_latex(span)}}}")
    for i, span in enumerate(italic_spans):
        escaped = escaped.replace(f"PHITALICX{i}X", f"\\textit{{{_escape_latex(span)}}}")
    for i, span in enumerate(code_spans):
        escaped = escaped.replace(f"PHCODEX{i}X", f"\\texttt{{{_escape_latex(span)}}}")

    return escaped


_REPORT_TEMPLATE = Template(r"""\documentclass[11pt,letterpaper]{article}
\usepackage[margin=1in]{geometry}
\usepackage{graphicx}
\usepackage{adjustbox}
\usepackage{booktabs}
\usepackage{longtable}
\usepackage{float}
\usepackage{xcolor}
\usepackage{lmodern}
\usepackage{microtype}
\usepackage[hidelinks]{hyperref}
$color_defs

\hypersetup{
  colorlinks=true,
  linkcolor=techNavy,
  urlcolor=techNavy,
  citecolor=techNavy
}

\title{\LARGE\bfseries $title}
\author{\large MBSE Technical Documentation Package\\[2pt]\normalsize Design ID: \texttt{$doc_id}}
\date{\today}

\begin{document}
\maketitle

\begin{abstract}
\noindent
$summary
\end{abstract}

\section{System Overview}
\begin{itemize}\setlength{\itemsep}{2pt}
  \item \textbf{Technology Catalog:} \texttt{$tech_name}
  \item \textbf{Coupling Recipe:} \texttt{$coupling_name}
  \item \textbf{Input/Output Requirement (IOR):} \texttt{$ior_name} ($ior_horizon)
  \item \textbf{Functional System Spec:} \texttt{$functional_system}
  \item \textbf{Buildable Resultant:} \texttt{$buildable_system}
\end{itemize}

\section{Technology Shelf}
\begin{figure}[H]
  \centering
  \adjustimage{max width=0.92\linewidth, max height=0.32\textheight, keepaspectratio}{figures/technology.pdf}
  \caption{Technology catalog \texttt{$tech_name} active members and available shelf components.}
\end{figure}

\noindent
\textbf{Active Members:} $member_list.
$unused_line

\section{Coupling Recipe}
\begin{figure}[H]
  \centering
  \adjustimage{max width=0.96\linewidth, max height=0.36\textheight, keepaspectratio}{figures/coupling.pdf}
  \caption{Coupling recipe \texttt{$coupling_name} internal connections and boundary ports.}
\end{figure}

\subsection{Components}
$components_table

\subsection{Wires (CSCR)}
\begin{longtable}{lll}
\toprule
\textbf{Wire Name} & \textbf{Source (From)} & \textbf{Target (To)} \\
\midrule
\endfirsthead
\toprule
\textbf{Wire Name} & \textbf{Source (From)} & \textbf{Target (To)} \\
\midrule
\endhead
\bottomrule
\endfoot
$wire_rows
\end{longtable}

\section{Input/Output Requirement (IOR)}
\begin{figure}[H]
  \centering
  \adjustimage{max width=0.88\linewidth, max height=0.38\textheight, keepaspectratio}{figures/lsc.pdf}
  \caption{Universal Live Sequence Chart (LSC) corresponding to requirement \texttt{$ior_name}.}
\end{figure}

\begin{itemize}\setlength{\itemsep}{2pt}
  \item \textbf{Requirement Name:} \texttt{$ior_name}
  \item \textbf{Alphabet:} \texttt{$ior_in} $$\longrightarrow$$ \texttt{$ior_out}
  \item \textbf{Horizon:} $ior_horizon
  \item \textbf{Universal LSC Encoding:} $$\mathcal{L}(\mathtt{$ior_name})$$ (\texttt{Mbse.IORToLSC})
  \item \textbf{Semantic Equivalence:} $$\mathrm{Satisfies}(Z, \mathcal{L}(\mathrm{IOR})) \iff \mathrm{SatisfiesIOR}(Z, \mathrm{IOR})$$
  \item \textbf{Description:} $ior_desc
\end{itemize}

\section{Proof of Implementation (ISR / PoI)}
\begin{figure}[H]
  \centering
  \adjustimage{max width=0.95\linewidth, max height=0.36\textheight, keepaspectratio}{figures/poi.pdf}
  \caption{Proof of Implementation (ISR / PoI cotyledon bridge) for design \texttt{$doc_id}.}
\end{figure}

\begin{itemize}\setlength{\itemsep}{2pt}
  \item \textbf{Functional System Spec (FSR):} \texttt{$impl_fs}
  \item \textbf{Implementing Buildable System (BSR):} \texttt{$impl_bs}
  \item \textbf{Mode Witness:} $impl_mode
  \item \textbf{Homomorphism Witness:} $impl_hom
\end{itemize}

$impl_notes

\section{Formal Lean References}
\begin{itemize}\setlength{\itemsep}{2pt}
$ref_items
\end{itemize}

\end{document}
""")


def write_report_tex(doc: IsrPackageDoc, out_dir: Path) -> Path:
    """Write publication-quality report.tex with figures included."""
    has_state = any(bool(c.state_type) for c in doc.coupling.components)
    has_role = any(bool(c.role) for c in doc.coupling.components)

    comp_rows = []
    for c in doc.coupling.components:
        inns = ", ".join(
            f"\\texttt{{{_escape_latex(p.name)}}}" + (f":\\texttt{{{_escape_latex(p.value_type)}}}" if p.value_type else "")
            for p in c.in_ports
        ) or "\\textemdash"
        outs = ", ".join(
            f"\\texttt{{{_escape_latex(p.name)}}}" + (f":\\texttt{{{_escape_latex(p.value_type)}}}" if p.value_type else "")
            for p in c.out_ports
        ) or "\\textemdash"

        cols = [f"\\texttt{{{_escape_latex(c.name)}}}"]
        if has_state:
            cols.append(f"\\texttt{{{_escape_latex(c.state_type)}}}" if c.state_type else "\\textemdash")
        cols.append(inns)
        cols.append(outs)
        if has_role:
            cols.append(_escape_latex(c.role) if c.role else "\\textemdash")
        comp_rows.append(" & ".join(cols) + " \\\\")

    col_spec = ["l"]
    headers = ["\\textbf{Component}"]
    if has_state:
        col_spec.append("p{2.5cm}")
        headers.append("\\textbf{State Type}")
    col_spec.append("p{3.5cm}")
    headers.append("\\textbf{In Ports}")
    col_spec.append("p{3.5cm}")
    headers.append("\\textbf{Out Ports}")
    if has_role:
        col_spec.append("p{3.5cm}")
        headers.append("\\textbf{Role}")

    header_str = " & ".join(headers) + " \\\\"
    col_spec_str = "".join(col_spec)
    components_table = (
        f"\\begin{{longtable}}{{{col_spec_str}}}\n"
        f"\\toprule\n{header_str}\n\\midrule\n"
        f"\\endfirsthead\n"
        f"\\toprule\n{header_str}\n\\midrule\n"
        f"\\endhead\n"
        f"\\bottomrule\n"
        f"\\endfoot\n"
        + "\n".join(comp_rows)
        + "\n\\end{longtable}"
    )

    wire_rows = []
    for w in doc.coupling.wires:
        w_name = f"\\texttt{{{_escape_latex(w.name)}}}" if w.name else "\\textemdash"
        w_from = f"\\texttt{{{_escape_latex(w.from_component)}}}.\\texttt{{{_escape_latex(w.from_port)}}}"
        w_to = f"\\texttt{{{_escape_latex(w.to_component)}}}.\\texttt{{{_escape_latex(w.to_port)}}}"
        wire_rows.append(f"{w_name} & {w_from} & {w_to} \\\\")
    if not wire_rows:
        wire_rows.append("\\textemdash & \\textemdash & \\textemdash \\\\")

    ref_items = "\n".join(f"  \\item \\texttt{{{_escape_latex(r)}}}" for r in doc.formal_refs)
    if not ref_items:
        ref_items = "  \\item (none)"

    member_list = ", ".join(f"\\texttt{{{_escape_latex(m)}}}" for m in doc.technology.members)
    if doc.technology.unused_shelf:
        unused_line = "\n\\noindent\n\\textbf{Available Shelf Components:} " + ", ".join(
            f"\\texttt{{{_escape_latex(m)}}}" for m in doc.technology.unused_shelf
        ) + "."
    else:
        unused_line = ""

    impl_mode_val = f"\\texttt{{{_escape_latex(doc.implements.mode_witness)}}}" if doc.implements.mode_witness else "\\textit{canonical self-mode of buildable resultant}"
    impl_hom_val = f"\\texttt{{{_escape_latex(doc.implements.hom_witness)}}}" if doc.implements.hom_witness else "\\textit{canonical homomorphism}"

    impl_notes_sec = ""
    if doc.implements.notes:
        impl_notes_sec = f"\n\\subsection*{{Implementation Notes}}\n{markdown_to_latex(doc.implements.notes)}\n"

    ior_desc_val = markdown_to_latex(doc.ior.description) if doc.ior.description else "\\textemdash"

    tex = _REPORT_TEMPLATE.substitute(
        color_defs=theme.COLOR_DEFS,
        title=_escape_latex(doc.title or doc.id),
        doc_id=_escape_latex(doc.id),
        summary=markdown_to_latex(doc.summary),
        tech_name=_escape_latex(doc.technology.name),
        coupling_name=_escape_latex(doc.coupling.name),
        ior_name=_escape_latex(doc.ior.name),
        ior_horizon=_escape_latex(doc.ior.horizon),
        ior_in=_escape_latex(doc.ior.input_type or "---"),
        ior_out=_escape_latex(doc.ior.output_type or "---"),
        ior_desc=ior_desc_val,
        functional_system=_escape_latex(doc.functional_system),
        buildable_system=_escape_latex(doc.buildable_system),
        member_list=member_list,
        unused_line=unused_line,
        components_table=components_table,
        wire_rows="\n".join(wire_rows),
        impl_fs=_escape_latex(doc.implements.functional_system),
        impl_bs=_escape_latex(doc.implements.implementing_system),
        impl_mode=impl_mode_val,
        impl_hom=impl_hom_val,
        impl_notes=impl_notes_sec,
        ref_items=ref_items,
    )

    out_dir.mkdir(parents=True, exist_ok=True)
    path = out_dir / "report.tex"
    path.write_text(tex, encoding="utf-8")
    return path


def compile_report(report_tex: Path, latex_cmd: str = "pdflatex") -> Path:
    if shutil.which(latex_cmd) is None:
        raise RuntimeError(
            f"'{latex_cmd}' not found on PATH; install a TeX distribution to build the report"
        )
    work = report_tex.parent
    cmd = [
        latex_cmd,
        "-interaction=nonstopmode",
        "-halt-on-error",
        report_tex.name,
    ]
    for _ in range(2):
        proc = subprocess.run(cmd, cwd=work, capture_output=True, check=False)
        stdout = proc.stdout.decode("utf-8", errors="replace")
        stderr = proc.stderr.decode("utf-8", errors="replace")
        if proc.returncode != 0:
            raise RuntimeError(
                f"pdflatex failed for {report_tex}:\n{stdout[-2000:]}\n{stderr[-2000:]}"
            )
    pdf = work / "report.pdf"
    if not pdf.is_file():
        raise RuntimeError(f"report PDF missing after compile: {pdf}")
    return pdf
