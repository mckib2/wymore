"""Publication theme for swarm verification TikZ (matches papers/ltl_paper/main.tex fig:comparison)."""

from __future__ import annotations

TIKZ_VERIFICATION_PREAMBLE = r"""[
  auto,
  >=stealth,
  thick,
  font=\small\sffamily,
  node distance=0.5cm and 0.75cm,
  assertblock/.style={
    draw=blue!60,
    fill=blue!5,
    rectangle,
    rounded corners,
    text width=0.14\textwidth,
    minimum height=1.05cm,
    align=center,
    thick,
    inner sep=3pt
  },
  specblock/.style={
    draw=blue!60,
    fill=blue!5,
    rectangle,
    rounded corners,
    text width=0.14\textwidth,
    minimum height=1.05cm,
    align=center,
    thick,
    inner sep=3pt
  },
  implcontainer/.style={
    draw=orange!60,
    fill=orange!5,
    rectangle,
    rounded corners,
    thick,
    inner sep=9pt
  },
  agentinner/.style={
    draw=orange!80,
    fill=orange!10,
    rectangle,
    rounded corners,
    text width=0.15\textwidth,
    minimum height=0.9cm,
    align=center,
    thick,
    inner sep=3pt,
    font=\scriptsize\sffamily
  },
  iolabel/.style={
    font=\scriptsize\sffamily,
    align=center,
    inner sep=1pt
  },
  arr/.style={->, >=stealth, thick, draw=black!70},
  dashedarr/.style={->, >=stealth, thick, dashed, draw=blue!70},
  biarr/.style={<->, >=stealth, thick, draw=black!70}
]"""
