# Makefile for compiling the INCOSE LaTeX paper

LATEXMK = latexmk
FLAGS = -pdf -outdir=build -interaction=nonstopmode
SRC = main.tex refs.bib

.PHONY: all clean

all: build/main.pdf

build/main.pdf: $(SRC)
	mkdir -p build
	$(LATEXMK) $(FLAGS) main.tex

clean:
	$(LATEXMK) -C -outdir=build
	rm -rf build
