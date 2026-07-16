SHELL := /bin/sh

MANUSCRIPT := manuscript/main.tex
BUILD_DIR := build
OUTPUT := $(BUILD_DIR)/strict-global-pf4-riemann-kernel.pdf

.PHONY: all clean

all: $(OUTPUT)

$(OUTPUT): $(MANUSCRIPT) $(shell find manuscript -type f -name '*.tex' -o -name '*.bib')
	@command -v tectonic >/dev/null 2>&1 || { echo "tectonic is required"; exit 1; }
	@mkdir -p $(BUILD_DIR)
	cd manuscript && tectonic --keep-logs --keep-intermediates --outdir ../$(BUILD_DIR) main.tex
	mv $(BUILD_DIR)/main.pdf $(OUTPUT)

clean:
	rm -f $(BUILD_DIR)/main.aux $(BUILD_DIR)/main.log $(BUILD_DIR)/main.out \
		$(BUILD_DIR)/main.toc $(OUTPUT)

