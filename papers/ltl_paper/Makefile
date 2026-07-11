# Makefile for the Wiley Systems Engineering article

LATEXMK   ?= latexmk
MAIN      := main
BUILD_DIR := build
PDF       := $(BUILD_DIR)/$(MAIN).pdf

FLAGS := -pdf -outdir=$(BUILD_DIR) -auxdir=$(BUILD_DIR) -interaction=nonstopmode

TEX_SOURCES := \
	main.tex \
	preamble.tex \
	sections/00-introduction.tex \
	sections/01-background.tex \
	sections/02-methodology.tex \
	sections/03-case-study.tex \
	sections/03-case-study-basics.tex \
	sections/03-case-study-alternates.tex \
	sections/03-case-study-fibonacci.tex \
	sections/04-discussion.tex \
	sections/05-conclusions.tex \
	appendix/hom-biimp.tex

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
