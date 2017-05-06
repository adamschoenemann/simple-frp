# ModalFRP
Implementation of Krishnaswami's [simple-frp](https://people.mpi-sws.org/~neelk/simple-frp.pdf) paper in Haskell as as DSL embedded with QuasiQuoters.

It is very much research-grade software!

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
to write and type-check `ModalFRP` programs. They are called
`decl` and `prog` for declarations and programs respectively.
`transform` and `execute` from `FRP`
can then be used to apply the programs as stream-transformers or stream-producers.

## Syntax
The syntax closely resembles the syntax from the paper, but with some additions
and discrepancies. In `test/FRP/TestFunctions.hs` there are several
functions and small programs that showcase how to write and use programs.

The parser is not white-space or indentation sensitive. Thus, declarations
must be ended with a `.` (dot) as in `Coq`.

## Example
The program below simply takes a stream of natural numbers and increases
them by one.

    frp_incr :: FRP (TStream TAlloc :->: TStream TNat :->: TStream TNat)
    frp_incr = [prog|
      map : S alloc -> #(a -> b) -> S a -> S b
      map us h xs =
        let cons(u, delay(us')) = us in
        let cons(x, delay(xs')) = xs in
        let stable(f) = h in
        cons(f x, delay(u, (((map us') stable(f)) xs'))).


      main : S alloc -> S Nat -> S Nat
      main allocs lst =
        map allocs stable(\x -> x + 1) lst.
    |]

You can then run this program on a Haskell stream like so:

    take 10 $ transform [0..] frp_incr
    >> [1,2,3,4,5,6,7,8,9,10]

## Gotcha's
Recursive top-level declarations are converted to fixpoints, so beware of this
when testing...