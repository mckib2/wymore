"""Emit standalone TikZ figures and compile them to PDF."""

from __future__ import annotations

import re
import shutil
import subprocess
from collections import defaultdict, deque
from pathlib import Path

from .models import ComponentDoc, IsrPackageDoc, WireDoc
from . import theme


def _escape(s: str) -> str:
    s = (
        s.replace("×", "<<TIMES>>")
        .replace("→", "<<TO>>")
        .replace("↔", "<<IFF>>")
        .replace("∈", "<<IN>>")
        .replace("∉", "<<NOTIN>>")
        .replace("⊆", "<<SUBSET>>")
        .replace("∀", "<<FORALL>>")
        .replace("∃", "<<EXISTS>>")
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
        .replace("<<IN>>", r"\in ")
        .replace("<<NOTIN>>", r"\notin ")
        .replace("<<SUBSET>>", r"\subseteq ")
        .replace("<<FORALL>>", r"\forall ")
        .replace("<<EXISTS>>", r"\exists ")
    )


def _split_long_identifier(name: str, max_chunk: int = 15) -> str:
    """Split long Lean identifiers cleanly across lines for TikZ labels."""
    if len(name) <= max_chunk:
        return _escape(name)
    parts = name.split("_")
    lines: list[str] = []
    current: list[str] = []
    current_len = 0
    for part in parts:
        escaped_part = _escape(part)
        p_len = len(part) + 1
        if current and (current_len + p_len > max_chunk):
            lines.append(r"\_".join(current) + r"\_")
            current = [escaped_part]
            current_len = p_len
        else:
            current.append(escaped_part)
            current_len += p_len
    if current:
        lines.append(r"\_".join(current))
    return r"\\".join(lines)


def _standalone(body: str) -> str:
    return (
        "\\documentclass[tikz,border=12pt]{standalone}\n"
        + theme.PREAMBLE_PACKAGES
        + theme.COLOR_DEFS
        + "\\begin{document}\n"
        + body
        + "\\end{document}\n"
    )


def technology_tikz(doc: IsrPackageDoc) -> str:
    """Render publication-quality Technology catalog and shelf."""
    members = doc.technology.members
    unused = doc.technology.unused_shelf
    nodes: list[str] = []

    # If 4 members, put all 4 on 1 row; if 5-6, 3 per row; if <=3, 1 row
    if len(members) == 4:
        cols = 4
    elif len(members) >= 5:
        cols = 3
    else:
        cols = max(len(members), 1)

    col_spacing = 3.5
    row_spacing = 1.9

    for i, name in enumerate(members):
        r = i // cols
        c = i % cols
        x = c * col_spacing
        y = -r * row_spacing
        nodes.append(
            f"\\node[compnode,fill=techNavy!6,draw=techNavy!70] (m{i}) at ({x:.2f},{y:.2f}) "
            f"{{\\textbf{{{_escape(name)}}}\\\\[2pt]{{\\scriptsize\\color{{techNavy}}Active Member}}}};"
        )

    # Layout unused shelf below active members
    base_shelf_y = -( (len(members) - 1) // cols + 1 ) * row_spacing if members else 0.0
    for j, name in enumerate(unused):
        r = j // cols
        c = j % cols
        x = c * col_spacing
        y = base_shelf_y - (r * row_spacing)
        nodes.append(
            f"\\node[shelfind] (u{j}) at ({x:.2f},{y:.2f}) "
            f"{{\\textbf{{{_escape(name)}}}\\\\[2pt]{{\\scriptsize\\color{{shelfSlate}}Available Shelf}}}};"
        )

    all_active = " ".join(f"(m{i})" for i in range(len(members)))
    all_unused = " ".join(f"(u{j})" for j in range(len(unused)))
    all_targets = (all_active + " " + all_unused).strip()

    title = _escape(doc.technology.name)
    body = (
        "\\begin{tikzpicture}[\n"
        + theme.TIKZ_BASE_STYLE
        + "]\n"
        + "\n".join(nodes)
        + "\n"
    )

    if all_targets:
        body += (
            f"\\begin{{scope}}[on background layer]\n"
            f"\\node[draw=techNavy!60,thick,rounded corners=6pt,fit={{{all_targets}}},inner sep=14pt,"
            f"label={{[anchor=south west,font=\\small\\sffamily\\bfseries,text=techNavy]north west:Technology Catalog: {title}}}] {{}};\n"
            f"\\end{{scope}}\n"
        )

    body += "\\end{tikzpicture}\n"
    return _standalone(body)


def _order_components(comps: list[ComponentDoc], wires: list[WireDoc], boundary_in: set[str], boundary_out: set[str]) -> list[str]:
    """Compute topological / signal-flow ordering of components."""
    comp_names = [c.name for c in comps]
    adj: dict[str, list[str]] = defaultdict(list)
    in_degree: dict[str, int] = {name: 0 for name in comp_names}

    for w in wires:
        if w.from_component != w.to_component and w.from_component in in_degree and w.to_component in in_degree:
            adj[w.from_component].append(w.to_component)
            in_degree[w.to_component] += 1

    start_nodes = [name for name in comp_names if name in boundary_in]
    if not start_nodes:
        start_nodes = [name for name in comp_names if in_degree[name] == 0]
    if not start_nodes and comp_names:
        start_nodes = [comp_names[0]]

    rank: dict[str, int] = {}
    queue = deque()
    for s in start_nodes:
        rank[s] = 0
        queue.append(s)

    while queue:
        u = queue.popleft()
        for v in adj[u]:
            new_r = rank[u] + 1
            if v not in rank or new_r > rank[v]:
                rank[v] = new_r
                queue.append(v)

    pipeline = sorted([name for name in comp_names if name in rank], key=lambda n: (rank[n], comp_names.index(n)))
    remaining = [name for name in comp_names if name not in rank]

    return pipeline + remaining


def coupling_tikz(doc: IsrPackageDoc) -> str:
    """Render publication-quality System Coupling Recipe (SCR) diagram."""
    comps = doc.coupling.components
    wires = doc.coupling.wires
    boundary = doc.coupling.boundary_ports

    boundary_in = {b.component: b.port for b in boundary if b.direction == "in"}
    boundary_out = {b.component: b.port for b in boundary if b.direction == "out"}

    ordered_names = _order_components(comps, wires, set(boundary_in.keys()), set(boundary_out.keys()))
    comp_map = {c.name: c for c in comps}

    connected_to_others = set()
    for w in wires:
        if w.from_component != w.to_component:
            connected_to_others.add(w.from_component)
            connected_to_others.add(w.to_component)
    for b in boundary:
        connected_to_others.add(b.component)

    pipeline_names = [n for n in ordered_names if n in connected_to_others]
    aux_names = [n for n in ordered_names if n not in connected_to_others]

    coords: dict[str, tuple[float, float]] = {}
    # Increased spacing so labels have generous breathing room
    x_spacing = 4.8
    for i, name in enumerate(pipeline_names):
        coords[name] = (i * x_spacing, 0.0)

    # Place auxiliary components above the pipeline centered
    aux_y = 2.4
    mid_x = (max(len(pipeline_names) - 1, 0) * x_spacing) / 2.0
    for j, name in enumerate(aux_names):
        ax = mid_x + (j - (len(aux_names) - 1) / 2.0) * x_spacing
        coords[name] = (ax, aux_y)

    nodes: list[str] = []
    for name in ordered_names:
        c = comp_map[name]
        x, y = coords[name]
        in_ports_str = ", ".join(p.name for p in c.in_ports) or "---"
        out_ports_str = ", ".join(p.name for p in c.out_ports) or "---"
        
        state_info = f"\\\\{{\\tiny\\color{{techNavy}}state: {_escape(c.state_type)}}}" if c.state_type else ""
        label = (
            f"\\textbf{{{_escape(c.name)}}}"
            f"{state_info}\\\\[2pt]"
            f"{{\\scriptsize\\color{{black!65}}in: {_escape(in_ports_str)} \\enspace$\\vert$\\enspace out: {_escape(out_ports_str)}}}"
        )
        safe_id = re.sub(r"\W", "_", name)
        nodes.append(
            f"\\node[compnode] (c_{safe_id}) at ({x:.2f},{y:.2f}) {{{label}}};"
        )

    # Boundary ports with generous clearance
    b_nodes: list[str] = []
    b_edges: list[str] = []
    for b in boundary:
        safe_id = re.sub(r"\W", "_", b.component)
        if b.component not in coords:
            continue
        cx, cy = coords[b.component]
        if b.direction == "in":
            b_id = f"bin_{safe_id}_{re.sub(r'\W', '_', b.port)}"
            bx = cx - 2.5
            b_nodes.append(
                f"\\node[portbadge] ({b_id}) at ({bx:.2f},{cy:.2f}) {{in: {_escape(b.port)}}};"
            )
            b_edges.append(
                f"\\draw[-{{Stealth}},thick,draw=boundGreen] ({b_id}) -- (c_{safe_id}.west);"
            )
        else:
            b_id = f"bout_{safe_id}_{re.sub(r'\W', '_', b.port)}"
            bx = cx + 2.5
            b_nodes.append(
                f"\\node[portbadge] ({b_id}) at ({bx:.2f},{cy:.2f}) {{out: {_escape(b.port)}}};"
            )
            b_edges.append(
                f"\\draw[-{{Stealth}},thick,draw=boundGreen] (c_{safe_id}.east) -- ({b_id});"
            )

    # Internal Wires
    edges: list[str] = []
    loop_top_targets: list[str] = []
    for w in wires:
        if w.from_component not in coords or w.to_component not in coords:
            continue
        from_id = re.sub(r"\W", "_", w.from_component)
        to_id = re.sub(r"\W", "_", w.to_component)
        lbl = _escape(w.name or f"{w.from_port}→{w.to_port}")

        fx, fy = coords[w.from_component]
        tx, ty = coords[w.to_component]

        if w.from_component == w.to_component:
            # Self-loop overhead with clean, controlled height
            top_coord = f"looptop_{from_id}"
            loop_top_targets.append(f"({top_coord})")
            edges.append(
                f"\\coordinate ({top_coord}) at ($(c_{from_id}.north)+(0,1.15)$);\n"
                f"\\draw[-{{Stealth}},thick,color=wireInk] (c_{from_id}.115) "
                f"to[out=105,in=75,looseness=2.2] "
                f"node[above,wirelabel] {{{lbl}}} (c_{to_id}.65);"
            )
        elif abs(fy - ty) < 0.1:
            # Same horizontal row
            idx_diff = pipeline_names.index(w.to_component) - pipeline_names.index(w.from_component)
            if idx_diff == 1:
                # Direct adjacent forward connection
                edges.append(
                    f"\\draw[-{{Stealth}},thick,color=wireInk] (c_{from_id}.east) -- "
                    f"node[above=2pt,wirelabel] {{{lbl}}} (c_{to_id}.west);"
                )
            elif idx_diff > 1:
                # Forward skip connection: curve overhead to avoid intermediate boxes
                edges.append(
                    f"\\draw[-{{Stealth}},thick,color=wireInk] (c_{from_id}.north) "
                    f"to[out=40,in=140] "
                    f"node[above=2pt,wirelabel] {{{lbl}}} (c_{to_id}.north);"
                )
            else:
                # Backward connection: curve underneath
                edges.append(
                    f"\\draw[-{{Stealth}},thick,color=wireInk] (c_{from_id}.south) "
                    f"to[out=-140,in=-40] "
                    f"node[below=2pt,wirelabel] {{{lbl}}} (c_{to_id}.south);"
                )
        else:
            # Cross-row connection
            edges.append(
                f"\\draw[-{{Stealth}},thick,color=wireInk] (c_{from_id}) -- "
                f"node[above=2pt,sloped,wirelabel] {{{lbl}}} (c_{to_id});"
            )

    all_node_refs = " ".join(f"(c_{re.sub(r'\W', '_', n)})" for n in ordered_names)
    all_b_refs = " ".join(
        [f"(bin_{re.sub(r'\W', '_', b.component)}_{re.sub(r'\W', '_', b.port)})" for b in boundary if b.direction == "in"]
        + [f"(bout_{re.sub(r'\W', '_', b.component)}_{re.sub(r'\W', '_', b.port)})" for b in boundary if b.direction == "out"]
    )
    all_loops = " ".join(loop_top_targets)
    all_fit = (all_node_refs + " " + all_b_refs + " " + all_loops).strip()

    title = _escape(doc.coupling.name)
    body = (
        "\\begin{tikzpicture}[\n"
        + theme.TIKZ_BASE_STYLE
        + "]\n"
        + "\n".join(nodes)
        + "\n"
        + "\n".join(b_nodes)
        + "\n"
        + "\n".join(edges)
        + "\n"
        + "\n".join(b_edges)
        + "\n"
    )

    if all_fit:
        body += (
            f"\\begin{{scope}}[on background layer]\n"
            f"\\node[draw=black!45,dashed,thick,rounded corners=6pt,fit={{{all_fit}}},inner sep=14pt,"
            f"label={{[anchor=south west,font=\\small\\sffamily\\bfseries,text=black!70]north west:Coupling Recipe: {title}}}] {{}};\n"
            f"\\end{{scope}}\n"
        )

    body += "\\end{tikzpicture}\n"
    return _standalone(body)


def poi_tikz(doc: IsrPackageDoc) -> str:
    """Render publication-quality Proof of Implementation (ISR Cotyledon Triangle)."""
    fsr = _escape(doc.functional_system or doc.implements.functional_system)
    bsr = _escape(doc.buildable_system or doc.implements.implementing_system)
    ior = _escape(doc.ior.name)
    tech = _escape(doc.technology.name)
    raw_mode = doc.implements.mode_witness or "canonical resultant mode"
    raw_hom = doc.implements.hom_witness or "canonical homomorphism"
    pkg = _escape(doc.id)

    hom_wrapped = _split_long_identifier(raw_hom, max_chunk=14)
    mode_wrapped = _split_long_identifier(raw_mode, max_chunk=14)

    # Expanded geometry: width 10.2cm, height 4.2cm
    body = f"""\\begin{{tikzpicture}}[
{theme.TIKZ_BASE_STYLE}
]
\\node[fsrnode] (fsr) at (0, 4.2) {{
  \\textbf{{Functional Specification (FSR)}}\\\\[2pt]
  \\texttt{{{fsr}}}\\\\[3pt]
  {{\\scriptsize\\color{{fsrBlue!80!black}}IOR: \\texttt{{{ior}}}}}
}};

\\node[bsrnode] (bsr) at (10.2, 4.2) {{
  \\textbf{{Buildable Resultant (BSR)}}\\\\[2pt]
  \\texttt{{{bsr}}}\\\\[3pt]
  {{\\scriptsize\\color{{bsrTeal!80!black}}TYR: \\texttt{{{tech}}}}}
}};

\\node[isrnode] (isr) at (5.1, 0.0) {{
  \\textbf{{Implementable Design (ISR)}}\\\\[2pt]
  \\texttt{{ImplementableSystemDesign}}\\\\[3pt]
  {{\\scriptsize\\color{{poiPurple!80!black}}Package: \\texttt{{{pkg}}}}}
}};

% Implements resultant relation (top)
\\draw[{{Stealth}}-{{Stealth}},thick,dashed,draw=black!70] (fsr.east) --
  node[above=3pt,wirelabel] {{\\textbf{{Implements}} (Def. 5.71)}} (bsr.west);

% Homomorphism bridge (left diagonal): from ISR top-left to FSR bottom-right
\\draw[-{{Stealth}},thick,draw=fsrBlue] (isr.140) --
  node[pos=0.46,sloped,above=4pt,wirelabel] {{\\parbox{{2.4cm}}{{\\centering\\scriptsize\\color{{fsrBlue}}$h$: \\texttt{{{hom_wrapped}}}}}}} (fsr.-40);

% Mode bridge (right diagonal): from ISR top-right to BSR bottom-left
\\draw[-{{Stealth}},thick,draw=bsrTeal] (isr.40) --
  node[pos=0.46,sloped,above=4pt,wirelabel] {{\\parbox{{2.4cm}}{{\\centering\\scriptsize\\color{{bsrTeal}}mode: \\texttt{{{mode_wrapped}}}}}}} (bsr.-140);

\\begin{{scope}}[on background layer]
\\node[draw=poiPurple!50,dashed,thick,rounded corners=6pt,fit=(fsr)(bsr)(isr),inner sep=16pt,
      label={{[anchor=south west,font=\\small\\sffamily\\bfseries,text=poiPurple]north west:Proof of Implementation (ISR Cotyledon Bridge)}}] {{}};
\\end{{scope}}

\\end{{tikzpicture}}
"""
    return _standalone(body)


def _format_lsc_cond(cond: str) -> str:
    """Format an LSC condition string nicely for LaTeX math mode."""
    s = cond.strip()
    s = s.replace("∈", r"\in ").replace("∉", r"\notin ")

    # Check for <ior>.itr
    m_itr = re.search(r"^(.*?)\s*(\\in|\\notin)\s*([\w]+)\.itr\s*$", s)
    if m_itr:
        var = m_itr.group(1).strip()
        rel = m_itr.group(2)
        ior_id = _escape(m_itr.group(3))
        return f"{var} {rel} \\mathtt{{{ior_id}.itr}}"

    # Check for <ior>.er <var>
    m_er = re.search(r"^(.*?)\s*(\\in|\\notin)\s*([\w]+)\.er\s+([\w]+)\s*$", s)
    if m_er:
        var_out = m_er.group(1).strip()
        rel = m_er.group(2)
        ior_id = _escape(m_er.group(3))
        var_in = m_er.group(4).strip()
        return f"{var_out} {rel} \\mathtt{{{ior_id}.er}}({var_in})"

    return _escape(s)


def lsc_tikz(doc: IsrPackageDoc) -> str:
    """Render publication-quality Universal Live Sequence Chart (LSC) corresponding to the IOR."""
    ior = doc.ior
    lsc = ior.lsc

    chart_name = _escape((lsc.chart_name if lsc and lsc.chart_name else f"LSC_{ior.name}"))
    in_type = _escape(ior.input_type or "IR")
    out_type = _escape(ior.output_type or "OR")
    horizon = _escape(ior.horizon or "infinite")
    ior_name = _escape(ior.name)

    raw_pre = lsc.pre_condition if lsc and lsc.pre_condition else f"f ∈ {ior.name}.itr"
    raw_main = lsc.main_condition if lsc and lsc.main_condition else f"g ∈ {ior.name}.er f"
    pre_cond = _format_lsc_cond(raw_pre)
    main_cond = _format_lsc_cond(raw_main)
    in_msg = _escape((lsc.in_message if lsc and lsc.in_message else f"in(f(t)) : {ior.input_type}"))
    out_msg = _escape((lsc.out_message if lsc and lsc.out_message else f"out(g(t)) : {ior.output_type}"))

    body = f"""\\begin{{tikzpicture}}[
{theme.TIKZ_BASE_STYLE}
]
% Lifeline Heads
\\node[lifelinehead] (env) at (0, 0) {{\\textbf{{Env}}}};
\\node[lifelinehead] (sys) at (7.4, 0) {{\\textbf{{Sys}}}};

% Pre-Chart (Cold Trigger Region)
\\node[coldframe, minimum width=9.2cm, minimum height=2.2cm, anchor=north] (pre_box) at (3.7, -1.25) {{}};
\\node[font=\\footnotesize\\sffamily\\bfseries, text=coldBlue, anchor=south west] at (pre_box.north west)
  {{Pre-Chart: Cold Trigger ($f \\in \\mathrm{{ITR}}$)}};

% Main-Chart (Hot Guarantee Region)
\\node[hotframe, minimum width=9.2cm, minimum height=2.9cm, anchor=north] (main_box) at (3.7, -4.25) {{}};
\\node[font=\\footnotesize\\sffamily\\bfseries, text=hotRed, anchor=south west] at (main_box.north west)
  {{Main-Chart: Hot Guarantee ($g \\in \\mathrm{{ER}}(f)$)}};

% Vertical Lifeline Rays (drawn on top of chart fills so they are continuously visible)
\\draw[dashed, thick, black!45] (env.south) -- (0, -7.8);
\\draw[dashed, thick, black!45] (sys.south) -- (7.4, -7.8);

% Cold Input Message (Env -> Sys)
\\draw[-{{Stealth}}, dashed, thick, draw=coldBlue] (0, -1.95) --
  node[above=2pt, font=\\scriptsize\\sffamily, text=coldBlue] {{\\texttt{{{in_msg}}}}} (7.4, -1.95);

% Cold Guard Condition
\\node[lsccond, draw=coldBlue, dashed] at (3.7, -2.75)
  {{\\textbf{{Cold Condition:}} ${pre_cond}$\\\\[1pt]\\scriptsize(Eligible Input Trajectory)}};

% Tick Synchronization
\\draw[dashdotted, thick, black!40] (-0.7, -4.9) --
  node[above=1pt, font=\\tiny\\sffamily, text=black!60] {{Discrete Tick Sync $t \\in \\mathrm{{TSR}}$ \\quad (Horizon: {horizon})}} (8.1, -4.9);

% Hot Output Message (Sys -> Env)
\\draw[-{{Stealth}}, solid, thick, draw=hotRed] (7.4, -5.6) --
  node[above=2pt, font=\\scriptsize\\sffamily, text=hotRed] {{\\texttt{{{out_msg}}}}} (0, -5.6);

% Hot Envelope Condition
\\node[lsccond, draw=hotRed, solid, thick] at (3.7, -6.45)
  {{\\textbf{{Hot Guarantee:}} ${main_cond}$\\\\[1pt]\\scriptsize(Full Envelope Membership)}};

% Outer Universal LSC Frame
\\begin{{scope}}[on background layer]
\\node[draw=black!55, thick, rounded corners=6pt, fit=(env)(sys)(pre_box)(main_box), inner sep=16pt,
      label={{[anchor=south west, font=\\small\\sffamily\\bfseries, text=black!85]north west:Universal LSC: \\texttt{{{chart_name}}} \\enspace$\\vert$\\enspace $\\mathcal{{L}}(\\mathtt{{{ior_name}}})$}}] (chart_frame) {{}};
\\end{{scope}}

% Semantic Equivalence Footer
\\node[font=\\scriptsize\\sffamily, text=black!70, anchor=north] at ($(chart_frame.south)+(0,-0.25)$)
  {{Assertional Semantics: $\\mathrm{{Satisfies}}(Z, \\mathcal{{L}}(\\mathrm{{IOR}})) \\iff \\mathrm{{SatisfiesIOR}}(Z, \\mathrm{{IOR}})$ \\enspace(\\texttt{{Mbse.IORToLSC}})}};

\\end{{tikzpicture}}
"""
    return _standalone(body)


def write_figure_sources(doc: IsrPackageDoc, fig_dir: Path) -> dict[str, Path]:
    fig_dir.mkdir(parents=True, exist_ok=True)
    sources = {
        "technology": fig_dir / "technology.tex",
        "coupling": fig_dir / "coupling.tex",
        "poi": fig_dir / "poi.tex",
        "lsc": fig_dir / "lsc.tex",
    }
    sources["technology"].write_text(technology_tikz(doc), encoding="utf-8")
    sources["coupling"].write_text(coupling_tikz(doc), encoding="utf-8")
    sources["poi"].write_text(poi_tikz(doc), encoding="utf-8")
    sources["lsc"].write_text(lsc_tikz(doc), encoding="utf-8")
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
