## Note: 2025 update for Luck Haskell implementation

After a little update, Luck builds with a modern GHC (9.6.5) using `cd luck && cabal build`.


# Luck -- A Language for Property-Based Generators

Accompanying material for the following POPL 2017 paper:
Beginner's Luck: A Language for Property-Based Generators.
Leonidas Lampropoulos, Diane Gallois-Wong, Catalin Hritcu, John
Hughes, Benjamin C. Pierce, Li-yao Xia.
https://arxiv.org/abs/1607.05443

`/coq`

 Coq proofs for narrowing fragment of the Luck core language.
 Works with Coq 8.4pl6. Simply run `make` there to check proofs.

`/luck`

 Luck interpreter. Known to work with GHC 7.10 -- 8.01

 Running `cabal install` there will produce a `luck` executable.
 Try out `luck examples/BST.luck`.
 `luck --help` provides a list of useful flags.
