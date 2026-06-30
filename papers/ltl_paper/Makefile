# Makefile for compiling the INCOSE LaTeX paper

LATEXMK = latexmk
FLAGS = -pdf -outdir=build -interaction=nonstopmode
SRC = main.tex refs.bib

PYTHON       ?= python3
REPO_ROOT    := ../..
SWARM_SCRIPT := $(REPO_ROOT)/scripts/render_swarm_systems.py
SWARM_LEAN   := $(REPO_ROOT)/Mbse/SwarmCaseStudy.lean \
                $(REPO_ROOT)/Mbse/SwarmExamples.lean
SWARM_THEME  := $(REPO_ROOT)/scripts/swarm_diagram_theme.py
BUILD_DIR    := build
SWARM_TEX    := $(BUILD_DIR)/swarm_verification.tex
SWARM_AGENTS ?= 3

FIGURES := $(SWARM_TEX)

.PHONY: all figures clean

all: build/main.pdf

figures: $(FIGURES)

$(SWARM_TEX): $(SWARM_LEAN) $(SWARM_SCRIPT) $(SWARM_THEME)
	mkdir -p $(BUILD_DIR)
	$(PYTHON) $(SWARM_SCRIPT) \
	  --case-study $(REPO_ROOT)/Mbse/SwarmCaseStudy.lean \
	  --examples $(REPO_ROOT)/Mbse/SwarmExamples.lean \
	  --out-dir $(BUILD_DIR) \
	  --agents $(SWARM_AGENTS)

build/main.pdf: $(SRC) $(FIGURES)
	mkdir -p build
	$(LATEXMK) $(FLAGS) main.tex

clean:
	$(LATEXMK) -C -outdir=build
	rm -rf build
