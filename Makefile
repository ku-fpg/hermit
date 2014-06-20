boot:
	cabal configure
	cabal build # because newer cabal doesn't show build output with install
	cabal install --force-reinstalls --disable-documentation

clean:
	cabal clean

FILE="src/HERMIT/Plugin.hs"
ghci:
	happy src/HERMIT/Parser.y
	happy src/HERMIT/ParserCore.y
	happy src/HERMIT/ParserType.y
	ghc --interactive -Wall -fno-warn-orphans -package ghc -isrc/ -optP-include -optPdist/build/autogen/cabal_macros.h ${FILE}

test:
	( cd tests ; runghc Main.hs )
