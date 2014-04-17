Classic.cry:
	ln -s ../classic/Classic.cry .

Enigma.cry:
	ln -s ../enigma/Enigma.cry .

test: Enigma.cry Classic.cry
	cryptol-2 -b sanity.icry
