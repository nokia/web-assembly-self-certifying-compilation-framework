# A Self-Certifying Compilation Framework for WebAssembly 
---

## About

In a *self-certifying* compiler, every optimization pass is designed to produce a candidate *proof* of its own correctness.  Proofs generated during a compilation run are checked automatically by an independent proof validator. The outcome is formally verified compilation, achieved *without* having to formally verify or trust the compiler code. Only the validator implementation must be trusted.

A proof is in the form of a relation between the states of the source and the target programs of an optimization pass. It is also called a *certificate* or a *witness*.


## Structure

The `src/compiler` directory contains proof-generating versions of several common compiler passes. 

The compiler is called `whisk`. It runs a sequence of optimization passes on a WebAssembly program, validating each in turn, and produces an optimized WebAssembly program as output.

The `src/validator` directory contains the validator code. It uses external SMT solvers such as [Z3](https://github.com/Z3Prover/z3) and [CVC4](https://cvc4.github.io/) to check proofs.


## Requirements and Building

Before proceeding, you may need:

  * [OCaml 4.07.1](https://ocaml.org/docs/install.html)
  
  * [opam](https://opam.ocaml.org/) and opam packages:
    * ocamlbuild: `opam install ocamlbuild`
    * Z3: `opam install z3`

  * The standard WASM reference interpreter, modified to make more functions public.
    [https://github.com/AntonXue/spec](https://github.com/AntonXue/spec)
    
    Clone this into a top-level `spec` directory. Then `make` and `make install` from the `spec/interpreter` directory.


After these requirements are met, simply run `make` at the toplevel to build the `whisk` compiler.


## Using whisk

`./whisk.native --help` lists all options.

To run the SSA and unSSA passes in sequence, with proof checking enabled:

 `./whisk.native -pass ssa -pass unssa -proofchk source.wast`

Please see doc/WHISK.md for more information.
