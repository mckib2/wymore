# Makefile for the Wiley Systems Engineering article

LATEXMK   ?= latexmk
MAIN      := main
BUILD_DIR := build
PDF       := $(BUILD_DIR)/$(MAIN).pdf

FLAGS := -pdf -outdir=$(BUILD_DIR) -auxdir=$(BUILD_DIR) -interaction=nonstopmode

TEX_SOURCES := \
	main.tex \
	preamble.tex \
	sections/introduction.tex \
	sections/background.tex \
	sections/methodology.tex \
	sections/case-study.tex \
	sections/case-study-discrete.tex \
	sections/case-study-real.tex \
	sections/discussion.tex \
	sections/conclusions.tex \
	appendix/hom-biimp.tex \
	appendix/encoding.tex

TEX_OPTIONAL := appendix/pathology-sketches.tex

ASSETS := refs.bib ama.bst wiley-article.cls \
	$(wildcard template-images/*) \
	$(wildcard figures/*)

ROOT_ARTIFACTS := \
	$(MAIN).aux $(MAIN).bbl $(MAIN).blg \
	$(MAIN).fdb_latexmk $(MAIN).fls $(MAIN).log $(MAIN).out \
	$(MAIN).pdf $(MAIN).synctex.gz

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
