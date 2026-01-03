# Makefile for LaTeX paper compilation

MAIN = main
LATEX = pdflatex
BIBTEX = bibtex

.PHONY: all clean view

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex
	$(LATEX) $(MAIN).tex
	$(BIBTEX) $(MAIN) || true
	$(LATEX) $(MAIN).tex
	$(LATEX) $(MAIN).tex

clean:
	rm -f *.aux *.log *.out *.toc *.bbl *.blg *.lot *.lof *.nav *.snm *.vrb
	rm -f $(MAIN).pdf

view: $(MAIN).pdf
	xdg-open $(MAIN).pdf || open $(MAIN).pdf || evince $(MAIN).pdf

quick:
	$(LATEX) $(MAIN).tex
