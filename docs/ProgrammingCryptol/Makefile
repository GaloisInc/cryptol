TARGET    = Cryptol
TMP       = tmp
MAIN      = main
MAINTARGET= ${MAIN}/${TARGET}
TMPTARGET = ${TMP}/${TARGET}
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

LATEX     = xelatex -output-driver=xdvipdfmx -output-directory=${TMP} -halt-on-error -file-line-error
BIBTEX    = bibtex
MAKEINDEX = makeindex

# TODO: Switch to using pdflatex or rubber?
# TODO: Ensure that TEXINPUTS is set correctly to make \includes and \usepackages more robust?

all: pdf
	cp ${TMP}/Cryptol.pdf ..

test:
	cd aes ; make test
	cd highAssurance ; make test
	cd enigma ; make test

pdf: ${TARGET}.pdf

${TMP}:
	mkdir -p ${TMP}

${TARGET}.pdf: ${SRCS} ${TMP}
	# surely I don't need this many latex's and indexes etc; but this looks like a sure fire way of
	# getting numbers right.. heh
	${LATEX}     ${MAINTARGET}
	${MAKEINDEX} ${TMP}/Cryptol.glo -s ${TMP}/Cryptol.ist -t ${TMP}/Cryptol.glg -o ${TMP}/Cryptol.gls
	${MAKEINDEX} ${TMPTARGET}
	${BIBTEX}    ${TMPTARGET}
	${LATEX}     ${MAINTARGET}
	${MAKEINDEX} ${TMPTARGET}
	${MAKEINDEX} ${TMP}/Cryptol.glo -s ${TMP}/Cryptol.ist -t ${TMP}/Cryptol.glg -o ${TMP}/Cryptol.gls
	${BIBTEX}    ${TMPTARGET}
	${LATEX}     ${MAINTARGET}
	${LATEX}     ${MAINTARGET}

# for quickly seeing changes; might get the labels wrong
quick: ${SRCS}
	${LATEX}     ${MAINTARGET}

# load into Cryptol
cry:
	cryptol-2 ${MAINTARGET}.tex
# TODO see ticket #276
#	cryptol -n ${MAINTARGET}

.PHONY: spellClean superClean clean quickSpell

clean:
	rm -f ${AUX}

superClean: clean
	rm -f ${TARGET}.pdf 
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
