# A Formal Semantics of Solidity in Isabelle/HOL

This repository contains the code supporting the thesis documents for a
formal semantics of Solidity in Isabelle/HOL.

The main Isabelle theories live at the repository root and can be loaded
through [Solidity_Main.thy](./Solidity_Main.thy). The file
[functions.md](./functions.md) provides an index of the functions,
definitions, and lemmas referenced explicitly in the thesis.

The type-safety-specific theory files are prefixed with `TypeSafe_`,
for example [TypeSafe_Def.thy](./TypeSafe_Def.thy) and
[TypeSafe_Expressions.thy](./TypeSafe_Expressions.thy).

## Prerequisites

* The formalization should be used with
  [Isabelle2025-2](https://isabelle.in.tum.de/).
  Please follow the instructions on the Isabelle home page for your operating 
  system. In the following, we assume that the ``isabelle`` tool is available
  on the command line. This might require to add the Isabelle binary directory
  to the ``PATH`` environment variable of your system. 

* The Solidity evaluator used for testing the formalization against the 
  real Solidity system requires [The Haskell Tool Stack](https://docs.haskellstack.org/en/stable/README/). 
  The Haskell Tool Stack can either be installed as a stand-alone tool
  or as integrated tool within Isabelle. For the latter, one only 
  needs to execute:

  ```sh
  isabelle ghc_setup
  ```

## Using the Formalization

The formalization can be loaded into Isabelle/jEdit by executing

```sh
isabelle jedit Solidity_Main.thy
```

on the command line. Alternatively, you can start Isabelle/jEdit by 
clicking on the Isabelle icon and loading the theory 
[Solidity_Main.thy](./Solidity_Main.thy) manually. 

To build the session from the command line and generate the document output,
first add ``path/to/TypeSafe-Isabelle-Solidity-Thesis`` to your Isabelle roots file which is
a file called ``ROOTS`` in your Isabelle home directory.
Then, the build can be started by executing:

```sh
isabelle build -D .
```

To export the generated Haskell sources, use the ``-e`` option during 
the build, e.g.:

```sh
isabelle build -e -D .
```

The sources of the Solidity evaluator are exported into the directory 
[solidity-evaluator](./solidity-evaluator). The sources
can be compiled using the Haskell Stack, either in its stand-alone version or using 
the version integrated into Isabelle. For the former use:

```
stack build --coverage 
stack run solidity-evaluator
```

For the Haskell Stack integrated into Isabelle use (you might need to run 
``isabelle ghc_setup`` first):

```
isabelle ghc_stack build --coverage 
isabelle ghc_stack run solidity-evaluator
```

## Code Coverage

### General (from <https://docs.haskellstack.org/en/stable/coverage/>)

To obtain coverage info do following 
1. Build with `stack build --coverage`
2. Executing solidity-exe generates a file `solidity-exe.tix`
3. Copy `solidity-exe.tix` to solidity home and execute `stack hpc report solidity-exe.tix`
4. HTML reports are available at `$(stack path --local-hpc-root)`

### Include specific modules
To create a coverage report which includes only specific modules use `stack exec hpc -- markup solidity-evaluator.tix --hpcdir=.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/hpc --srcdir=. --include=Accounts Declarations Environment Expressions Statements Storage Store Utils Valuetypes`

### Exclude testing code (from <http://wiki.haskell.org/Haskell_program_coverage>)
To exclude testing related code do the following:
1. Create complete coverage file with `stack exec hpc -- draft --hpcdir=.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/hpc --srcdir=. solidity-evaluator.tix > draft.txt`
2. Modify draft.txt to check all the commands which should not be considered in the coverage. In particular replace `:` with `/` in `solidity-evaluator-0.1.0.0-E6rYduruX84J8q3ItmGdtm:Solidity`
3. Create tix file with `stack exec hpc -- overlay --hpcdir=.stack-work/dist/x86_64-linux-tinfo6/Cabal-2.4.0.1/hpc --srcdir=. draft.txt > draft.tix`
4. Create combined tix file with `stack exec hpc -- combine solidity-evaluator.tix draft.tix --union > combined.tix`
5. Execute `stack hpc report combined.tix`
