## Architecture

Our checker operates over a
control flow graph-based internal representation (IR)
which can be extracted from (and converted back to)
the WASM reference interpreter's
abstract syntax.

The proof-generating compiler is in the `src/compiler` directory, it is split into: 

  * `main`: front-end for aggregating all components;
    contains the main function.


  * `passes`: compiler optimization passes that work over the IR.
    Can also generate proofs of correctness
    that are fed into an SMT solver for validation.
    Third-party users can also extend this with their
    own optimizations and correspondingly generated proof,
    which was an original goal of the project.



The proof validator is in the `src/validator` directory, split into: 

  * `proofs`: construct proofs and further encode the graph-based IR
    into a proof-IR over which can reason about program properties
    at a high level and generate SMT formulaic encodings.

  
  * `solver`: interfacing with SMT solvers.
  

  * `syntax`: translate to and from the WebAssembly's
    reference interpreter grammar to and from the IR.
    In order to reuse code from the reference interpreter
    we borrow much of the existing type definitions,
    but some extensions are made to augment the reference syntax.
    Note that for simplicity on our end,
    many of the types such as `func`, `script`, etc
    all have the same name, so it's crucial to differentiate
    between a `func` and a `Wasm.Ast.func`, for instance.
    As a consequence, it helps if `open Wasm.Ast` or equivalent is never used
    in critically important files where namespace collision may happen.

    The key files are `func_ir.ml`,
    which extracts (and re-converts) an graph-based IR
    from (and to) a `func` type in the reference interpreter;
    and `script_ir.ml`,
    which converts augments the `script` type in the reference interpreter
    to include extra annotations.


  * `test`: various test scripts constructed during development.

  * `utils`: define additional data structures,
    string manipulation functions,
    and printing, among others.

    
  * `validator-api`: contains convenience functions. 



