MARKDOWN = Syntax.pdf CryptolPrims.pdf Version2Changes.pdf
BOOK = Cryptol.pdf

.PHONY: all
all: markdown book

Version2Table.pdf: Version2Table.markdown
	pandoc -f markdown+tex_math_dollars $^ -o $@

.PHONY: markdown
markdown: ${MARKDOWN}

.PHONY: book
book:
	(cd ProgrammingCryptol; make)
	cp ProgrammingCryptol/tmp/${BOOK} .

%.pdf: %.markdown
	pandoc $^ --toc -o $@

.PHONY: clean
clean:
	rm -f ${MARKDOWN}
	rm -f ${BOOK}
