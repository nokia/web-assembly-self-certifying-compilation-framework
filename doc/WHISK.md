## The Whisk self-certifying compiler

Upon running `./whisk.native --help` you will be greeted with something like:
```
WebAssembly optimizer 
      run as whisk -pass <pass> source.wast
      run as whisk --help for more options
   
  -debug set debug level (default none)
  -o <output file> (default is <source>.out.wast)
  -list-passes list available passes
  -pass <pass name>
  -proofgen turn on proof generation
  -proofchk turn on proof generation and checking
  -nowast do not generate a file
  -dump-init-cfgs dump the initial CFGs
  -dump-final-cfgs dump the initial CFGs
  -spec-bench run spec benchmarks
  -filter filter out certain source files
  -help  Display this list of options
  --help  Display this list of options

```

We primarily care about only a few flags:
`-pass`, `-debug`, and `-proofchk` flags for regular usage.

  * The `-pass` flag is used to specify which passes to run.
    A number of passes such as basic block merging and constant folding
    are implemented, but we primarily showcase `ssa`, `unssa`, `dse`, and (loop) `unroll`.
    A few examples are included below to illustrate how passes are used
  
  * The `-debug` flag specifies the level of information to be dumped,
    ranging from levels `-debug 0` to `-debug 3`.
    
  * The `-proofchk` flag will query Z3 with SMTLIB2-format queries,
    which are also dumped in a `__query.smt2` file in this directory to assist debugging.

For instance, to run SSA on `spec/test/core/block.wast`:

  * `./whisk.native -pass ssa spec/test/core/block.wast`
  
To turn on proof checking with SSA:

  * `./whisk.native -pass ssa -proofchk spec/test/core/block.wast`

To enable proof checking with SSA + unSSA:

  * `./whisk.native -pass ssa -pass unssa -proofchk spec/test/core/block.wast`
  
Note that the output `.wast` file generation is currently somewhat incomplete,
and that verification is done over the internal CFG representations.
However, the `-dump-initial-cfgs` and `-dump-final-cfgs` will dump a textual
representation of the CFGs present.

For instance:

  * `./whisk.native -pass ssa -pass unssa -proofchk -dump-initial-cfgs -dump-final-cfgs spec/test/core/block.wast`

will print textual representation of CFGs in the console output.

One can run a pass or a sequence of passes over the entire `spec` test bench using: 
  * `./whisk.native -pass ssa -proofchk -spec-bench`
  
Among the spec test files, `spec/test/core/br_table.wast` contains a function `large` that generates an excessive number of SMT lemmas during validation. It may be helpful to comment this out.


