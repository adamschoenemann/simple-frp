# Notes

## Command for interactive testing
stack repl --test [--trace]

Use `:r` to reload and `Main.main` or `main` to run tests.
Use `:rr Spec.main` to reload and run `Spec.main` (or any other def you want)

## TODO

### Need
- Rewrite Program to not require main functions (easy)
    - Rewrite evaluation to be partial and fail if no main function given
      (perhaps parameterized by the name of the main function)
- Type-check and eval into and out (easy)
- Recursive type constructor (mu binding) (easy)
- Figure out how to interface with Haskell (medium)
- Improve quasi-quotation features (medium)

### Want
- Reduce some primitives from the language, e.g. fst, snd, stream
- Type inference (medium)
- Switch to using a recursive type for the ast (big refactor!) (hard)
- Inductive types <3 (hard)