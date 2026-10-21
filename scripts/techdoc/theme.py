"""Shared TikZ / report styling for techdoc figures."""

# Keep distinct from papers/ltl_paper swarm theme.
COLORS = {
    "tech": "techBlue!20",
    "comp": "compSand!40",
    "wire": "wireInk",
    "boundary": "boundGreen!35",
    "fsr": "fsrRose!30",
    "bsr": "bsrTeal!30",
    "poi": "poiGold!35",
}

COLOR_DEFS = r"""
\definecolor{techBlue}{HTML}{2E5A88}
\definecolor{compSand}{HTML}{C4A574}
\definecolor{wireInk}{HTML}{2B2B2B}
\definecolor{boundGreen}{HTML}{3D7A5A}
\definecolor{fsrRose}{HTML}{A65D5D}
\definecolor{bsrTeal}{HTML}{3A7A78}
\definecolor{poiGold}{HTML}{B0892C}
"""

PREAMBLE_PACKAGES = r"""
\usepackage{tikz}
\usetikzlibrary{positioning,arrows.meta,fit,calc,shapes.geometric}
\usepackage{xcolor}
"""
