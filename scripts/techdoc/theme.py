"""Shared TikZ / report styling for techdoc figures."""

from __future__ import annotations

COLOR_DEFS = r"""
\definecolor{techNavy}{HTML}{1F4E79}
\definecolor{compBorder}{HTML}{343A40}
\definecolor{compFill}{HTML}{F8F9FA}
\definecolor{wireInk}{HTML}{212529}
\definecolor{boundGreen}{HTML}{2B8A3E}
\definecolor{fsrBlue}{HTML}{1864AB}
\definecolor{bsrTeal}{HTML}{087F5B}
\definecolor{poiPurple}{HTML}{5F3DC4}
\definecolor{shelfSlate}{HTML}{495057}
\definecolor{accentAmber}{HTML}{D97706}
"""

PREAMBLE_PACKAGES = r"""
\usepackage{tikz}
\usetikzlibrary{positioning,arrows.meta,fit,calc,shapes.geometric,backgrounds}
\usepackage{xcolor}
\usepackage{lmodern}
"""

TIKZ_BASE_STYLE = r"""font=\small\sffamily,
>=Stealth,
every node/.style={font=\small\sffamily},
compnode/.style={
  draw=compBorder,
  fill=compFill,
  thick,
  rounded corners=3pt,
  minimum width=2.8cm,
  minimum height=1.3cm,
  align=center,
  font=\small\sffamily
},
shelfind/.style={
  draw=shelfSlate,
  dashed,
  fill=black!3,
  rounded corners=3pt,
  minimum width=2.6cm,
  minimum height=1.1cm,
  align=center,
  font=\small\sffamily
},
wirelabel/.style={
  fill=white,
  draw=black!25,
  thin,
  rounded corners=2pt,
  inner sep=2pt,
  font=\scriptsize\sffamily,
  align=center
},
portbadge/.style={
  draw=boundGreen,
  fill=boundGreen!12,
  thick,
  rounded corners=2pt,
  font=\scriptsize\sffamily\bfseries,
  inner sep=3pt,
  align=center
},
fsrnode/.style={
  draw=fsrBlue,
  fill=fsrBlue!8,
  thick,
  rounded corners=4pt,
  minimum width=3.6cm,
  minimum height=1.35cm,
  align=center,
  font=\small\sffamily
},
bsrnode/.style={
  draw=bsrTeal,
  fill=bsrTeal!8,
  thick,
  rounded corners=4pt,
  minimum width=3.6cm,
  minimum height=1.35cm,
  align=center,
  font=\small\sffamily
},
isrnode/.style={
  draw=poiPurple,
  fill=poiPurple!8,
  thick,
  rounded corners=4pt,
  minimum width=4.0cm,
  minimum height=1.4cm,
  align=center,
  font=\small\sffamily
}""".strip()
