# Keep all LaTeX outputs under build/ (see Makefile).
$out_dir = 'build';
$aux_dir = 'build';
$pdf_mode = 1;

# main.tex uses biblatex; route bibliography through biber.
$bibtex_use = 2;

# Fail the build on undefined citations/references.
$latexmk_force = 0;
