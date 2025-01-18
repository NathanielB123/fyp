ifdef LUALATEX
LUALATEX = "False"
endif 

.PHONY: clean

default: main.pdf

main.bbl: main.bib
	biber main

main.tex : c0_main.lagda c1_introduction.lagda c2_background.lagda c3_simplytyped.lagda c4_dependentlytyped.lagda c5_plan.lagda lib.fmt
ifeq (LUALATEX, "True")
	echo "%let lua = True" > config.lagda
else
	echo "%let lua = False" > config.lagda
endif
	lhs2TeX --agda $< > $@

main.pdf: main.bbl main.tex
ifeq (LUALATEX, "True")
	lualatex main.tex
else
	pdflatex main.tex
endif

clean:
	rm *.aux || true
	rm *.log || true
	rm *.out || true
	rm *.pdf || true
	rm *.toc || true
	rm *.bbl || true
	rm *.blg || true
	rm *.ptb || true
	rm *.mw || true
	rm *.run.xml || true
	rm main.tex || true
