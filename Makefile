boot:
	cabal build # because newer cabal doesn't show build output with install
	cabal install --enable-tests --force-reinstalls --disable-documentation

install:
	cabal install --force-reinstalls --disable-documentation

clean:
	cabal clean

ghci:
	cabal repl

test:
	cabal test --show-details=streaming
