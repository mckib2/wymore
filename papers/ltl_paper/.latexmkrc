# Keep all LaTeX outputs under build/ (see Makefile).
$out_dir = 'build';
$aux_dir = 'build';
$pdf_mode = 1;

# wiley-article uses natbib + BibTeX (ama.bst), not biblatex/biber.
$bibtex_use = 1;

$latexmk_force = 0;
