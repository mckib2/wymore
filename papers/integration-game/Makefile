# Makefile for building CSER27 paper into a dedicated build directory.

TARGET    ?= main
BUILD_DIR ?= build
PDF       := $(BUILD_DIR)/$(TARGET).pdf
SRC       := $(TARGET).tex
DEPS      := $(wildcard *.tex *.bib *.cls *.sty *.png sections/*.tex figures/* images/*)

LATEXMK       ?= latexmk
LATEXMK_FLAGS ?= -pdf -outdir=$(BUILD_DIR) -interaction=nonstopmode -halt-on-error

.PHONY: all pdf clean clean-intermediates distclean view watch

.DEFAULT_GOAL := all

all: $(PDF)

pdf: $(PDF)

$(PDF): $(DEPS)
	@mkdir -p $(BUILD_DIR)
	$(LATEXMK) $(LATEXMK_FLAGS) $(SRC)

# Clean intermediate files while preserving the PDF
clean-intermediates:
	@if [ -d "$(BUILD_DIR)" ]; then \
		$(LATEXMK) -c -outdir=$(BUILD_DIR) $(SRC); \
	fi

# Clean all build artifacts and the build directory
clean:
	@if [ -d "$(BUILD_DIR)" ]; then \
		$(LATEXMK) -C -outdir=$(BUILD_DIR) $(SRC) 2>/dev/null || true; \
	fi
	rm -rf $(BUILD_DIR)

distclean: clean

# Continuous compilation / watch mode
watch:
	@mkdir -p $(BUILD_DIR)
	$(LATEXMK) -pvc $(LATEXMK_FLAGS) $(SRC)

# Open the generated PDF with the default system viewer
view: $(PDF)
	@xdg-open $(PDF) 2>/dev/null || open $(PDF) 2>/dev/null || echo "Please open $(PDF) manually."
