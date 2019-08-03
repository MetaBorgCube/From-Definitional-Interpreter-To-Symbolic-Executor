## Optionally add extra latex source folders (must end with colon!)
export TEXINPUTS = lib/:

LATEXMK   = latexmk -r latexmkrc

.SUFFIXES: .pdf

.PRECIOUS: build/%.pdf

%.pdf: build/%.pdf
	cp "$<" "$@"

%.tex: %.lhs.tex FORCE
	lhs2TeX "$<" > "$@"

%.tex: %.lhs FORCE
	lhs2TeX "$<" > "$@"

build/%.pdf: %.tex FORCE
	$(LATEXMK) "$<"

.PHONY: all bib clean

all: document.pdf

clean:
	$(LATEXMK) -C .

FORCE:
