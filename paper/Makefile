# Makefile for LaTeX paper compilation

MAIN = main
LATEX = pdflatex
BIBTEX = bibtex

# Section files
SECTIONS = sections/introduction.tex \
           sections/related_work.tex \
           sections/architecture.tex \
           sections/implementation.tex \
           sections/evaluation.tex \
           sections/future_work.tex \
           sections/conclusion.tex

.PHONY: all clean view quick

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(SECTIONS) reference.bib
	$(LATEX) $(MAIN).tex
	$(BIBTEX) $(MAIN) || true
	$(LATEX) $(MAIN).tex
	$(LATEX) $(MAIN).tex

clean:
	rm -f *.aux *.log *.out *.toc *.bbl *.blg *.lot *.lof *.nav *.snm *.vrb
	rm -f sections/*.aux
	rm -f $(MAIN).pdf

view: $(MAIN).pdf
	xdg-open $(MAIN).pdf || open $(MAIN).pdf || evince $(MAIN).pdf

quick:
	$(LATEX) $(MAIN).tex

