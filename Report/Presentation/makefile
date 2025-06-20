.PHONY: default update clean

default: main.pdf

main.pdf : main.tex
	latexmk -pdf $<

main.tex : c0_main.lagda lib.fmt
	lhs2TeX --agda $< > $@

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
	rm -f *.fdb_latexmk
	rm -f *.fls
	rm -f main.tex
