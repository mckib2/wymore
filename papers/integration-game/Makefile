# Makefile for building CSER27 paper into a dedicated build directory.

TARGET    ?= main
BUILD_DIR ?= build
PDF       := $(BUILD_DIR)/$(TARGET).pdf
SRC       := $(TARGET).tex
DEPS      := $(wildcard *.tex *.bib *.cls *.sty *.png sections/*.tex figures/* images/*)

LATEXMK       ?= latexmk
LATEXMK_FLAGS ?= -pdf -outdir=$(BUILD_DIR) -interaction=nonstopmode -halt-on-error
TEXCOUNT      ?= texcount
WORDCOUNT_PY  ?= scripts/wordcount.py

.PHONY: all pdf words clean clean-intermediates distclean view watch

.DEFAULT_GOAL := all

all: $(PDF)
	@$(MAKE) --no-print-directory words

pdf: $(PDF)

$(PDF): $(DEPS)
	@mkdir -p $(BUILD_DIR)
	$(LATEXMK) $(LATEXMK_FLAGS) $(SRC)

# Word count excluding References/bibliography and Acknowledgments.
# Bibliography is omitted via texcount -nobib (and %TC:ignore around
# \printbibliography). Section titles matching Acknowledgment(s)/References
# are also dropped; wrap Acknowledgments with %TC:ignore ... %TC:endignore.
words:
	@$(TEXCOUNT) -merge -sub=section -nobib -sum $(SRC) 2>/dev/null | python3 $(WORDCOUNT_PY)

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
