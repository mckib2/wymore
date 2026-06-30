#!/usr/bin/env python3
"""Generate unified swarm verification-architecture TikZ from Lean sources."""

from __future__ import annotations

import argparse
import re
import shlex
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import swarm_diagram_theme as theme  # noqa: E402


@dataclass
class SystemSchema:
    """Extracted swarm system vocabulary from Lean sources."""

    spec_state_fields: list[str] = field(default_factory=list)
    swarm_state_fields: list[str] = field(default_factory=list)
    mission_out_fields: list[str] = field(default_factory=list)
    agent_status_fields: list[str] = field(default_factory=list)
    uav_state_fields: list[str] = field(default_factory=list)
    mission_phases: list[str] = field(default_factory=list)
    mission_cmds: list[str] = field(default_factory=list)
    swarm_size: int = 100


def _parse_inductive(content: str, name: str) -> list[str]:
    pattern = rf"inductive\s+{name}\s*\|\s*([^\n]+)"
    match = re.search(pattern, content)
    if not match:
        return []
    body = match.group(1).strip()
    parts = re.split(r"\s*\|\s*", body)
    return [p.split()[0] for p in parts if p.strip()]


def _parse_structure_fields(content: str, name: str) -> list[str]:
    pattern = rf"structure\s+{name}(?:\s*\([^)]*\))?\s+where\s+(.*?)(?=\n(?:@\[|theorem|def|structure|inductive|abbrev|noncomputable|private|end\b))"
    match = re.search(pattern, content, re.DOTALL)
    if not match:
        return []
    block = match.group(1)
    fields: list[str] = []
    for line in block.splitlines():
        line = line.strip()
        if not line or line.startswith("/-"):
            continue
        m = re.match(r"(\w+)\s*:", line)
        if m:
            fields.append(m.group(1))
    return fields


def _parse_nat_const(content: str, name: str, default: int) -> int:
    match = re.search(rf"def\s+{name}\s*:\s*Nat\s*:=\s*(\d+)", content)
    return int(match.group(1)) if match else default


def extract_schema(case_study_path: Path, examples_path: Path) -> SystemSchema:
    case_content = case_study_path.read_text(encoding="utf-8")
    examples_content = examples_path.read_text(encoding="utf-8")
    return SystemSchema(
        spec_state_fields=_parse_structure_fields(case_content, "SpecState"),
        swarm_state_fields=_parse_structure_fields(case_content, "SwarmState"),
        mission_out_fields=_parse_structure_fields(case_content, "MissionOut"),
        agent_status_fields=_parse_structure_fields(case_content, "AgentStatus"),
        uav_state_fields=_parse_structure_fields(examples_content, "UavState"),
        mission_phases=_parse_inductive(case_content, "MissionPhase"),
        mission_cmds=_parse_inductive(case_content, "MissionCmd"),
        swarm_size=_parse_nat_const(case_content, "swarmSize", 100),
    )


def _script_path_for_banner() -> str:
    invoked = Path(sys.argv[0])
    if invoked.name:
        return invoked.as_posix()
    script = Path(__file__).resolve()
    try:
        return script.relative_to(Path.cwd().resolve()).as_posix()
    except ValueError:
        return script.as_posix()


def _format_cli_args(args: argparse.Namespace) -> str:
    parts: list[str] = []
    for key, value in sorted(vars(args).items()):
        flag = f"--{key.replace('_', '-')}"
        if isinstance(value, bool):
            if value:
                parts.append(flag)
        else:
            parts.append(flag)
            parts.append(str(value))
    return " ".join(shlex.quote(part) for part in parts)


def _file_banner(*, args: argparse.Namespace, output_name: str) -> str:
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    return "\n".join(
        [
            "% Auto-generated — do not edit by hand.",
            f"% Script: {_script_path_for_banner()}",
            f"% Arguments: {_format_cli_args(args)}",
            f"% Output: {output_name}",
            f"% Generated: {timestamp}",
        ]
    )


def build_verification_tikz(banner: str, schema: SystemSchema) -> str:
    """Dual verification paths on Z_impl; quintuple detail lives in the paper table."""
    mission_out_label = ", ".join(f"\\texttt{{{f}}}" for f in schema.mission_out_fields)
    return "\n".join(
        [
            banner,
            rf"\begin{{tikzpicture}}{theme.TIKZ_VERIFICATION_PREAMBLE}",
            r"  \node[font=\small\sffamily, align=center] (zimplhdr)",
            r"    {$Z_{\text{impl}}$\\CSY swarm ($N$ agents)};",
            r"  \node[agentinner, below=0.24cm of zimplhdr] (agent)",
            r"    {representative $Z_i$\\$(x_i,y_i,\ldots)$; RTB};",
            r"  \begin{scope}[on background layer]",
            r"    \node[implcontainer, fit=(zimplhdr)(agent)] (zimplbox) {};",
            r"  \end{scope}",
            r"  \node[iolabel, above=0.18cm of zimplbox.north] (inputlbl) {\texttt{MissionCmd}};",
            r"  \draw[arr] (inputlbl.south) -- (zimplbox.north);",
            r"  \node[iolabel, below=0.18cm of zimplbox.south] (outputlbl)",
            rf"    {{\texttt{{MissionOut}}\\({mission_out_label})}};",
            r"  \draw[arr] (zimplbox.south) -- (outputlbl.north);",
            r"  \node[assertblock, anchor=east, left=2.6cm of zimplbox.west] (phi)",
            r"    {Property set $\Phi$\\$\varphi_{\text{safe}}$, $\varphi_{\text{live}}$\\(FO-LTL)};",
            r"  \node[specblock, anchor=west, right=2.6cm of zimplbox.east] (zspec)",
            r"    {Behavioral $Z_{\text{spec}}$\\aggregate $(K,t,a)$\\$(S,I,O,\delta,\rho)$};",
            r"  \node[iolabel, above=0.18cm of zspec.north] (specinputlbl) {\texttt{MissionCmd}};",
            r"  \draw[arr] (specinputlbl.south) -- (zspec.north);",
            r"  \node[iolabel, below=0.18cm of zspec.south] (specoutputlbl)",
            rf"    {{\texttt{{MissionOut}}\\({mission_out_label})}};",
            r"  \draw[arr] (zspec.south) -- (specoutputlbl.north);",
            r"  \draw[dashedarr] (phi.east) -- node[midway, above, font=\scriptsize, align=center]",
            r"    {property checking\\$Z_{\text{impl}} \models_{\mathcal{L}} \Phi$} (zimplbox.west);",
            r"  \draw[biarr] (zimplbox.east) -- node[midway, above, font=\scriptsize, align=center]",
            r"    {homomorphism $h$\\constructive FC} (zspec.west);",
            r"\end{tikzpicture}",
            "",
        ]
    )


def render_figure(
    out_dir: Path,
    args: argparse.Namespace,
    schema: SystemSchema,
) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "swarm_verification.tex"
    out_path.write_text(
        build_verification_tikz(_file_banner(args=args, output_name=out_path.name), schema),
        encoding="utf-8",
    )
    return out_path


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Render unified swarm verification-architecture TikZ."
    )
    parser.add_argument("--case-study", type=Path, default=Path("Mbse/SwarmCaseStudy.lean"))
    parser.add_argument("--examples", type=Path, default=Path("Mbse/SwarmExamples.lean"))
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("papers/ltl_paper/build"),
    )
    parser.add_argument(
        "--agents",
        type=int,
        default=3,
        help="Schematic agent count shown in the diagram (parametric N in prose)",
    )
    args = parser.parse_args()

    if args.agents < 1:
        print("error: --agents must be >= 1", file=sys.stderr)
        return 1

    # Schema extraction keeps Makefile dependency on Lean sources; labels are conceptual in TikZ.
    schema = extract_schema(args.case_study, args.examples)
    out_path = render_figure(args.out_dir, args, schema)
    print(f"Wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
