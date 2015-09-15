TARGET    = Cryptol
TMP       = tmp
MAIN      = main
MAINTARGET= ${MAIN}/${TARGET}
SRCS      = ${wildcard *.tex */*.tex *.sty */*.sty} ${wildcard *.bib */*.bib} \
	    ${wildcard *.sty} Makefile ${wildcard *.cry */*.cry}
SPELLSRC  = ${filter-out ${wildcard utils/*.tex}, ${wildcard *.tex */*.tex}}
LTMPDIR   = tmp
NEWSPELL  = ${LTMPDIR}/${TARGET}.SPELLNEW
OLDSPELL  = ${LTMPDIR}/${TARGET}.SPELLOLD
SPELL     = aspell -t -l
AUX       = ${wildcard ${TMP}/*.blg} ${wildcard ${TMP}/*.bbl} ${wildcard ${TMP}/*.aux} \
            ${wildcard ${TMP}/*.eps} ${wildcard ${TMP}/*.log} ${wildcard ${TMP}/*.toc} \
	    ${wildcard ${TMP}/*.out} ${wildcard ${TMP}/*.idx} ${wildcard ${TMP}/*.ilg} \
	    ${wildcard ${TMP}/*.ind} ${wildcard ${TMP}/*.brf} ${wildcard ${TMP}/*.glg} \
	    ${wildcard ${TMP}/*.glo} ${wildcard ${TMP}/*.gls} ${wildcard ${TMP}/*.ist} \

LATEXMK = latexmk -xelatex -outdir=${TMP}

# LATEX     = xelatex -output-driver=xdvipdfmx -output-directory=${TMP} -halt-on-error -file-line-error

# TODO: Switch to using pdflatex or rubber?
# TODO: Ensure that TEXINPUTS is set correctly to make \includes and \usepackages more robust?

all: pdf
	cp ${TMP}/Cryptol.pdf ..

test:
	cd aes ; make test
	cd highAssurance ; make test
	cd enigma ; make test

pdf: ${TARGET}.pdf

${TARGET}.pdf: ${SRCS}
	${LATEXMK} ${MAINTARGET}.tex

.PHONY: squeaky superClean clean quickSpell

clean:
	${LATEXMK} -c ${MAINTARGET}.tex
	rm -f ${AUX}

squeaky: clean
	${LATEXMK} -C ${MAINTARGET}.tex
	rm -f ${AUX}
	make -C tools clean

spellClean:
	rm -f ${NEWSPELL} ${OLDSPELL}

quickSpell:
	@touch ${NEWSPELL}
	@mv -f ${NEWSPELL} ${OLDSPELL}
	@cat ${SPELLSRC} | ${SPELL} | tr "A-Z" "a-z" | sort | uniq | less > ${NEWSPELL}
	@echo '(The ones marked with < are new.)'
	@diff ${NEWSPELL} ${OLDSPELL}

.PHONY: continuous
continuous:
	@make -C tools
