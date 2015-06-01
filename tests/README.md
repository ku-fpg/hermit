Run examples en masse with:

    cabal test

If you're using `cabal-install-1.20` or later, you can see the tests run live with:

    cabal test --show-details=streaming

To update a golden file, delete it from the `golden/` directory, re-run the tests,
and commit.
