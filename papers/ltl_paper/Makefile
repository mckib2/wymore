# Makefile for compiling the INCOSE LaTeX paper

LATEXMK  ?= latexmk
MAIN     := main
BUILD_DIR := build
PDF      := $(BUILD_DIR)/$(MAIN).pdf

FLAGS := -pdf -outdir=$(BUILD_DIR) -auxdir=$(BUILD_DIR) -interaction=nonstopmode

# Driver and every \input{} target listed in main.tex
TEX_SOURCES := \
	main.tex \
	preamble.tex \
	frontmatter.tex \
	sections/introduction.tex \
	sections/background.tex \
	sections/methodology.tex \
	sections/case-study.tex \
	sections/discussion.tex \
	sections/conclusions.tex \
	sections/references.tex \
	sections/biography.tex \
	appendix/hom-biimp.tex \
	appendix/encoding.tex

# Optional appendix (commented out in main.tex); rebuild if enabled later
TEX_OPTIONAL := appendix/pathology-sketches.tex

ASSETS := refs.bib \
	$(wildcard template-images/*) \
	$(wildcard figures/*)

# Root-level artifacts from older in-tree builds (removed by distclean)
ROOT_ARTIFACTS := \
	$(MAIN).aux $(MAIN).bbl $(MAIN).bcf $(MAIN).blg \
	$(MAIN).fdb_latexmk $(MAIN).fls $(MAIN).log $(MAIN).out \
	$(MAIN).pdf $(MAIN).run.xml $(MAIN).synctex.gz

.PHONY: all clean distclean

all: $(PDF)

$(PDF): $(TEX_SOURCES) $(TEX_OPTIONAL) $(ASSETS) Makefile .latexmkrc
	mkdir -p $(BUILD_DIR)
	$(LATEXMK) $(FLAGS) $(MAIN).tex

clean:
	$(LATEXMK) -C -outdir=$(BUILD_DIR) -auxdir=$(BUILD_DIR) $(MAIN).tex
	rm -rf $(BUILD_DIR)

distclean: clean
	rm -f $(ROOT_ARTIFACTS)
