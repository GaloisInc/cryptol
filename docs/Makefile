MARKDOWN = Syntax.pdf CryptolPrims.pdf Version2Changes.pdf
BOOK = Cryptol.pdf

.PHONY: all
all: markdown book

Version2Table.pdf: Version2Table.md
	pandoc -f markdown+tex_math_dollars -V geometry:"margin=0.25in" $^ -o $@

.PHONY: markdown
markdown: ${MARKDOWN}

.PHONY: book
book:
	(cd ProgrammingCryptol; make)
	cp ProgrammingCryptol/tmp/${BOOK} ./ProgrammingCryptol.pdf

%.pdf: %.md
	pandoc $^ --toc -o $@

.PHONY: clean
clean:
	rm -f ${MARKDOWN}
	rm -f ${BOOK}
