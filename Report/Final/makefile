ifdef LUALATEX
LUALATEX = "False"
endif 

.PHONY: default update clean

default: main.pdf

# main.pdf: main.bbl main.tex
# ifeq (LUALATEX, "True")
# 	lualatex main.tex
# else
# 	pdflatex main.tex
# endif
# 
# main.bbl: main.bib main.bcf
# 	biber main
# 
# main.bcf: main.bib main.tex
# 	pdflatex -draftmode main.tex

main.pdf : main.tex main.bib
	latexmk -pdf $<

main.tex : c0_main.lagda c1_introduction.lagda c2_background.lagda c3_simplytyped.lagda c4_dependentlytyped.lagda c5_plan.lagda c6_nbe.lagda lib.fmt
ifeq (LUALATEX, "True")
	echo "%let lua = True" > config.lagda
else
	echo "%let lua = False" > config.lagda
endif
	lhs2TeX --agda $< > $@

# Hack for not running pdflatex/lualatex twice because it is sometimes not
# necessary
# update: main.tex
# ifeq (LUALATEX, "True")
# 	biber main
# 	lualatex main.tex
# else
# 	biber main
# 	pdflatex main.tex
# endif

clean:
	rm -f *.aux
	rm -f *.log
	rm -f *.out
	rm -f *.pdf
	rm -f *.toc
	rm -f *.bbl
	rm -f *.blg
	rm -f *.ptb
	rm -f *.mw
	rm -f *.run.xml
	rm -f *.bcf
	rm -f main.tex
