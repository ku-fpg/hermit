boot:
	cabal configure
	cabal build # because newer cabal doesn't show build output with install
	cabal install --force-reinstalls --disable-documentation

clean:
	cabal clean

ghci:
	cabal repl

test:
	( cd tests ; runghc Main.hs )
