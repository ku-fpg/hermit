boot:
	cabal install --force-reinstalls --disable-documentation

clean:
	cabal clean

FILE="src/HERMIT/Plugin.hs"
ghci:
	happy src/HERMIT/Parser.y
	happy src/HERMIT/ParserCore.y
	ghc --interactive -Wall -package ghc -isrc/ ${FILE}

test:
	( cd tests ; runghc Main.hs )
