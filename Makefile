boot:
	cabal install --force-reinstalls --disable-documentation

clean:
	cabal clean

FILE="src/Language/HERMIT/Shell/Command.hs"
ghci:
	ghc --interactive -Wall -package ghc -isrc/ ${FILE}
