# ModalFRP
Implementation of Krishnaswami's [simple-frp](https://people.mpi-sws.org/~neelk/simple-frp.pdf) paper in Haskell as as DSL embedded with QuasiQuoters.

## Installation
Using Stack

## Organization
    src
      `- FRP
          `- AST
              `- Construct.hs
              `- QuasiQuoter.hs
              `- Reflect.hs
          `- Parser
              `- Construct.hs
              `- Decl.hs
              `- Lang.hs
              `- Program.hs
              `- Term.hs
              `- Type.hs
          `- AST.hs
          `- Pretty.hs
          `- Semantics.hs
          `- TypeChecker.hs
          `- TypeInference.hs
      `- FRP.hs
      `- Utils.hs

The structure of the files mirror the module hierarchy in the source.
`FRP.hs` is the main entry point of the project. It re-exports
other modules and defines functions to run `ModalFRP` programs and definitions.
`Utils.hs` simply contains a few un-interesting utility functions.
The `FRP` module contains most of the implementation. It has two
sub-modules: `AST` and `Parser`. The `AST.hs` file contains
definitions for the Abstract Syntax of both terms and types of the language,
along with type-class instances and functions to work with them. The submodules
of `AST` provide helper functions to `Construct` the AST,
`QuasiQuoter`s to construct ASTs at compile-time, and methods
to `Reflect` the type of the AST into a Haskell-type.

The `Parser` sub-modules simply contains parser definitions and helpers,
that allows us to parse an AST from a `String` using combinators
provided by the `Parsec` library.

`Pretty.hs` is a tiny type-class that deals with pretty-printing things.
`Semantics.hs` contains a complete interpreter of `ModalFRP`
using the operational semantics defined in the paper.
`TypeChecker.hs` contains the first implementation of a type-checker for `ModalFRP`.
While this type-checker rigidly follows the typing judgments described in the paper,
it does not perform any inference whatsoever, and as such requires programs to
be fully annotated. As this is less than ideal, this file is actually deprecated
in favor of `TypeInference.hs`, which implements a Hindley-Milner style
inference algorithm for the type-system described in the paper.

In all, the implementation measures two-thousand source-lines of Haskell code.

## Usage
Mainly, one would use the QuasiQuoters re-exported is `AST.QuasiQuoter` (re-exported in `FRP`)
to write and type-check `ModalFRP` programs. `transform` and `execute` from `FRP`
can then be used to apply the programs as stream-transformers or stream-producers.


## Gotcha's
Recursive top-level declarations are converted to fixpoints, so beware of this
when testing...