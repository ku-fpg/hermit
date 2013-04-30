boot:
	cabal install --force-reinstalls --disable-documentation

clean:
	cabal clean

FILE="src/Language/HERMIT/Shell/Command.hs"
ghci:
	happy src/Language/HERMIT/Parser.y
	happy src/Language/HERMIT/ParserCore.y
	ghc --interactive -Wall -package ghc -isrc/ ${FILE}

test:
	( cd tests ; runghc Test.hs )
