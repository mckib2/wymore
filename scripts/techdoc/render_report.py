"""Assemble a LaTeX report that includes figure PDFs."""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path
from string import Template

from .models import IsrPackageDoc
from . import theme


def _escape(s: str) -> str:
    # Normalize characters that break classic pdflatex / Template.
    # Use sentinels so later backslash escaping does not mangle math.
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
    )
    return (
        s.replace("<<TIMES>>", r"$\times$")
        .replace("<<TO>>", r"$\to$")
        .replace("<<IFF>>", r"$\leftrightarrow$")
    )


_REPORT_TEMPLATE = Template(r"""\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage{graphicx}
\usepackage{booktabs}
\usepackage{longtable}
\usepackage{hyperref}
\usepackage{xcolor}
$color_defs

\title{$title}
\author{MBSE techdoc \\ \texttt{$doc_id}}
\date{\today}

\begin{document}
\maketitle

\begin{abstract}
$summary
\end{abstract}

\section{Overview}
\begin{itemize}
  \item Technology: \texttt{$tech_name}
  \item Coupling: \texttt{$coupling_name}
  \item IOR: \texttt{$ior_name} ($ior_horizon)
  \item Functional system: \texttt{$functional_system}
  \item Buildable system: \texttt{$buildable_system}
\end{itemize}

\section{Technology shelf}
\begin{figure}[ht]
  \centering
  \includegraphics[width=0.9\linewidth]{figures/technology.pdf}
  \caption{Technology $tech_name members.}
\end{figure}

Members: $member_list.
$unused_line

\section{Coupling recipe}
\begin{figure}[ht]
  \centering
  \includegraphics[width=0.95\linewidth]{figures/coupling.pdf}
  \caption{Coupling $coupling_name.}
\end{figure}

\subsection{Components}
\begin{longtable}{lp{2cm}p{3cm}p{3cm}p{4cm}}
\toprule
Name & State & In ports & Out ports & Role \\
\midrule
\endfirsthead
\toprule
Name & State & In ports & Out ports & Role \\
\midrule
\endhead
\bottomrule
\endfoot
$comp_rows
\end{longtable}

\subsection{Wires (CSCR)}
\begin{longtable}{lll}
\toprule
Name & From & To \\
\midrule
\endfirsthead
\toprule
Name & From & To \\
\midrule
\endhead
\bottomrule
\endfoot
$wire_rows
\end{longtable}

\section{Input/output requirement}
\begin{itemize}
  \item Name: \texttt{$ior_name}
  \item Alphabet: $ior_in $$\to$$ $ior_out
  \item Horizon: $ior_horizon
  \item Description: $ior_desc
\end{itemize}

\section{Proof of implementation}
\begin{figure}[ht]
  \centering
  \includegraphics[width=0.95\linewidth]{figures/poi.pdf}
  \caption{ISR / PoI packaging for $doc_id.}
\end{figure}

\begin{itemize}
  \item Functional system: \texttt{$impl_fs}
  \item Implementing system: \texttt{$impl_bs}
  \item Mode witness: \texttt{$impl_mode}
  \item Homomorphism witness: \texttt{$impl_hom}
\end{itemize}

$impl_notes

\section{Formal references}
\begin{itemize}
$ref_items
\end{itemize}

\end{document}
""")


def write_report_tex(doc: IsrPackageDoc, out_dir: Path) -> Path:
    """Write report.tex that includes figure PDFs under figures/."""
    comp_rows = []
    for c in doc.coupling.components:
        inns = ", ".join(
            f"{p.name}:{p.value_type}" if p.value_type else p.name for p in c.in_ports
        )
        outs = ", ".join(
            f"{p.name}:{p.value_type}" if p.value_type else p.name for p in c.out_ports
        )
        comp_rows.append(
            f"{_escape(c.name)} & {_escape(c.state_type)} & {_escape(inns)} & "
            f"{_escape(outs)} & {_escape(c.role)} \\\\"
        )

    wire_rows = []
    for w in doc.coupling.wires:
        wire_rows.append(
            f"{_escape(w.name)} & {_escape(w.from_component)}.{_escape(w.from_port)} & "
            f"{_escape(w.to_component)}.{_escape(w.to_port)} \\\\"
        )
    if not wire_rows:
        wire_rows.append("--- & --- & --- \\\\")

    ref_items = "\n".join(f"  \\item \\texttt{{{_escape(r)}}}" for r in doc.formal_refs)
    if not ref_items:
        ref_items = "  \\item (none)"

    member_list = ", ".join(
        f"\\texttt{{{_escape(m)}}}" for m in doc.technology.members
    )
    if doc.technology.unused_shelf:
        unused_line = "Unused shelf: " + ", ".join(
            f"\\texttt{{{_escape(m)}}}" for m in doc.technology.unused_shelf
        ) + "."
    else:
        unused_line = ""

    tex = _REPORT_TEMPLATE.substitute(
        color_defs=theme.COLOR_DEFS,
        title=_escape(doc.title or doc.id),
        doc_id=_escape(doc.id),
        summary=_escape(doc.summary),
        tech_name=_escape(doc.technology.name),
        coupling_name=_escape(doc.coupling.name),
        ior_name=_escape(doc.ior.name),
        ior_horizon=_escape(doc.ior.horizon),
        ior_in=_escape(doc.ior.input_type),
        ior_out=_escape(doc.ior.output_type),
        ior_desc=_escape(doc.ior.description),
        functional_system=_escape(doc.functional_system),
        buildable_system=_escape(doc.buildable_system),
        member_list=member_list,
        unused_line=unused_line,
        comp_rows="\n".join(comp_rows),
        wire_rows="\n".join(wire_rows),
        impl_fs=_escape(doc.implements.functional_system),
        impl_bs=_escape(doc.implements.implementing_system),
        impl_mode=_escape(doc.implements.mode_witness),
        impl_hom=_escape(doc.implements.hom_witness),
        impl_notes=_escape(doc.implements.notes),
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
