"""Emit standalone TikZ figures and compile them to PDF."""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

from .models import IsrPackageDoc
from . import theme


def _escape(s: str) -> str:
    s = (
        s.replace("×", "<<TIMES>>")
        .replace("→", "<<TO>>")
        .replace("↔", "<<IFF>>")
        .replace("—", "---")
        .replace("–", "--")
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


def _standalone(body: str) -> str:
    return (
        "\\documentclass[tikz,border=8pt]{standalone}\n"
        + theme.PREAMBLE_PACKAGES
        + theme.COLOR_DEFS
        + "\\begin{document}\n"
        + body
        + "\\end{document}\n"
    )


def technology_tikz(doc: IsrPackageDoc) -> str:
    members = doc.technology.members
    unused = doc.technology.unused_shelf
    nodes: list[str] = []
    for i, name in enumerate(members):
        nodes.append(
            f"\\node[draw,rounded corners,fill={theme.COLORS['tech']},"
            f"minimum width=2.4cm,minimum height=0.9cm] "
            f"(m{i}) at ({i * 2.8},0) {{{_escape(name)}}};"
        )
    for j, name in enumerate(unused):
        nodes.append(
            f"\\node[draw,rounded corners,dashed,fill=black!5,"
            f"minimum width=2.4cm,minimum height=0.9cm] "
            f"(u{j}) at ({j * 2.8},-1.4) {{{_escape(name)} (shelf)}};"
        )
    title = _escape(doc.technology.name)
    fit_targets = " ".join(f"(m{i})" for i in range(len(members)))
    unused_fit = " ".join(f"(u{j})" for j in range(len(unused)))
    fit_all = (fit_targets + " " + unused_fit).strip()
    body = (
        "\\begin{tikzpicture}\n"
        f"\\node[font=\\bfseries] at ({max(0, len(members) - 1) * 1.4},1.2)"
        f" {{Technology: {title}}};\n"
        + "\n".join(nodes)
        + "\n"
    )
    if fit_all:
        body += (
            f"\\node[draw,thick,dashed,fit={{{fit_all}}},inner sep=8pt,"
            f"label={{[above left]shelf}}] {{}};\n"
        )
    body += "\\end{tikzpicture}\n"
    return _standalone(body)


def coupling_tikz(doc: IsrPackageDoc) -> str:
    comps = doc.coupling.components
    name_to_idx = {c.name: i for i, c in enumerate(comps)}
    nodes: list[str] = []
    n = max(len(comps), 1)
    for i, c in enumerate(comps):
        x = i * 3.2
        ports_in = ", ".join(p.name for p in c.in_ports) or "—"
        ports_out = ", ".join(p.name for p in c.out_ports) or "—"
        label = (
            f"{_escape(c.name)}\\\\"
            f"{{\\scriptsize in: {_escape(ports_in)}}}\\\\"
            f"{{\\scriptsize out: {_escape(ports_out)}}}"
        )
        nodes.append(
            f"\\node[draw,rounded corners,fill={theme.COLORS['comp']},"
            f"align=center,minimum width=2.6cm,minimum height=1.4cm] "
            f"(c{i}) at ({x},0) {{{label}}};"
        )

    edges: list[str] = []
    for w in doc.coupling.wires:
        fi = name_to_idx.get(w.from_component)
        ti = name_to_idx.get(w.to_component)
        if fi is None or ti is None:
            continue
        lbl = _escape(w.name or f"{w.from_port}→{w.to_port}")
        if fi == ti:
            edges.append(
                f"\\draw[-{{Stealth}},thick,color={theme.COLORS['wire']}] "
                f"(c{fi}.north) to[out=60,in=120,looseness=2] "
                f"node[above,font=\\scriptsize] {{{lbl}}} (c{ti}.north);"
            )
        else:
            edges.append(
                f"\\draw[-{{Stealth}},thick,color={theme.COLORS['wire']}] "
                f"(c{fi}) -- node[above,font=\\scriptsize] {{{lbl}}} (c{ti});"
            )

    for b in doc.coupling.boundary_ports:
        idx = name_to_idx.get(b.component)
        if idx is None:
            continue
        if b.direction == "in":
            edges.append(
                f"\\node[draw,fill={theme.COLORS['boundary']},font=\\scriptsize] "
                f"(bin{idx}) at ($(c{idx})+(-1.6,0)$) {{in: {_escape(b.port)}}};\n"
                f"\\draw[-{{Stealth}},dashed] (bin{idx}) -- (c{idx});"
            )
        else:
            edges.append(
                f"\\node[draw,fill={theme.COLORS['boundary']},font=\\scriptsize] "
                f"(bout{idx}) at ($(c{idx})+(1.6,0)$) {{out: {_escape(b.port)}}};\n"
                f"\\draw[-{{Stealth}},dashed] (c{idx}) -- (bout{idx});"
            )

    mid_x = (n - 1) * 1.6
    body = (
        "\\begin{tikzpicture}\n"
        f"\\node[font=\\bfseries] at ({mid_x},2.2)"
        f" {{Coupling: {_escape(doc.coupling.name)}}};\n"
        + "\n".join(nodes)
        + "\n"
        + "\n".join(edges)
        + "\n\\end{tikzpicture}\n"
    )
    return _standalone(body)


def poi_tikz(doc: IsrPackageDoc) -> str:
    fsr = _escape(doc.functional_system or doc.implements.functional_system)
    bsr = _escape(doc.buildable_system or doc.implements.implementing_system)
    ior = _escape(doc.ior.name)
    tech = _escape(doc.technology.name)
    mode = _escape(doc.implements.mode_witness or "(mode)")
    hom = _escape(doc.implements.hom_witness or "(hom)")
    pkg = _escape(doc.id)
    body = f"""\\begin{{tikzpicture}}[
  box/.style={{draw,rounded corners,align=center,minimum width=3.2cm,minimum height=1.1cm}}]
\\node[font=\\bfseries] at (3.5,3.2) {{Proof of implementation (ISR / PoI)}};
\\node[box,fill={theme.COLORS['fsr']}] (fsr) at (0,1.5)
  {{FSR\\\\{fsr}\\\\{{\\scriptsize IOR: {ior}}}}};
\\node[box,fill={theme.COLORS['bsr']}] (bsr) at (7,1.5)
  {{BSR\\\\{bsr}\\\\{{\\scriptsize TYR: {tech}}}}};
\\node[box,fill={theme.COLORS['poi']}] (isr) at (3.5,0)
  {{ISR = ImplementableSystemDesign\\\\{pkg}}};
\\draw[-{{Stealth}},thick] (fsr) -- node[above,font=\\scriptsize] {{{hom}}} (isr);
\\draw[-{{Stealth}},thick] (bsr) -- node[above,font=\\scriptsize] {{{mode}}} (isr);
\\draw[{{Stealth}}-{{Stealth}},thick,dashed] (fsr) -- node[above,font=\\scriptsize]
  {{Implements}} (bsr);
\\end{{tikzpicture}}
"""
    return _standalone(body)


def write_figure_sources(doc: IsrPackageDoc, fig_dir: Path) -> dict[str, Path]:
    fig_dir.mkdir(parents=True, exist_ok=True)
    sources = {
        "technology": fig_dir / "technology.tex",
        "coupling": fig_dir / "coupling.tex",
        "poi": fig_dir / "poi.tex",
    }
    sources["technology"].write_text(technology_tikz(doc), encoding="utf-8")
    sources["coupling"].write_text(coupling_tikz(doc), encoding="utf-8")
    sources["poi"].write_text(poi_tikz(doc), encoding="utf-8")
    return sources


def compile_tikz_pdf(tex_path: Path, latex_cmd: str = "pdflatex") -> Path:
    """Compile a standalone TikZ .tex to PDF beside it. Returns PDF path."""
    if shutil.which(latex_cmd) is None:
        raise RuntimeError(
            f"'{latex_cmd}' not found on PATH; install a TeX distribution to build figures"
        )
    work = tex_path.parent
    cmd = [
        latex_cmd,
        "-interaction=nonstopmode",
        "-halt-on-error",
        tex_path.name,
    ]
    proc = subprocess.run(
        cmd,
        cwd=work,
        capture_output=True,
        check=False,
    )
    stdout = proc.stdout.decode("utf-8", errors="replace")
    stderr = proc.stderr.decode("utf-8", errors="replace")
    pdf = work / (tex_path.stem + ".pdf")
    if proc.returncode != 0 or not pdf.is_file():
        raise RuntimeError(
            f"pdflatex failed for {tex_path}:\n{stdout[-2000:]}\n{stderr[-2000:]}"
        )
    return pdf


def build_all_figures(doc: IsrPackageDoc, out_dir: Path, latex_cmd: str = "pdflatex") -> dict[str, Path]:
    fig_dir = out_dir / "figures"
    sources = write_figure_sources(doc, fig_dir)
    pdfs: dict[str, Path] = {}
    for key, tex in sources.items():
        pdfs[key] = compile_tikz_pdf(tex, latex_cmd=latex_cmd)
    return pdfs
