.PHONY: all
all: compileProgrammingCryptol
	@./compileProgrammingCryptol


compileProgrammingCryptol: compileProgrammingCryptol.hs
	@ghc --make -o $@ $<

clean:
	@rm -f *.hi *.o
