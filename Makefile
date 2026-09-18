# Makefile for the gh-pages branch of smtlib/jSMTLIB, published at
# https://smtlib.github.io/jSMTLIB/
#
# Typical flow: edit the LaTeX source in TEXDIR, `make build` to regenerate
# SMTLIBTutorial.pdf here, commit it, then `make push` to publish.

TEXDIR  := $(HOME)/cok/texstuff/papers/SMTLIBTutorial
TEXNAME := SMTLIBTutorial

.PHONY: build push

# Builds SMTLIBTutorial.pdf from its LaTeX source (runs pdflatex/bibtex/
# makeindex as needed via latexmk) and copies the result into this branch.
build:
	latexmk -pdf -cd $(TEXDIR)/$(TEXNAME).tex
	cp $(TEXDIR)/$(TEXNAME).pdf ./$(TEXNAME).pdf

# Publishes this branch to GitHub Pages. Refuses to push if the working
# tree isn't clean, so what's live always matches a real commit.
push:
	@if [ -n "$$(git status --porcelain)" ]; then \
		echo "Working tree is not clean -- commit or stash changes before pushing." >&2; \
		exit 1; \
	fi
	git push origin gh-pages
