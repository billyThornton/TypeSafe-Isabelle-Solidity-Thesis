chapter AFP

session "Solidity-dev" = "HOL-Library" +
  options [document = pdf, document_output = "output"]
  sessions
    "HOL-Eisbach"
  theories
    Utils
    ReadShow
    StateMonad
    Valuetypes
    Storage
    Accounts
    Environment
    Contracts
    Expressions
    Statements
    Solidity_Main
    Solidity_Symbex
    Solidity_Evaluator
    Solidity_Tests
  theories [condition = ISABELLE_GHC]
    Compile_Evaluator

  export_files (in ".") [2] "*:**.hs" "*:**.ML" "MYCommand.ML"
  export_files (in "solidity-evaluator/bin") [1] "*:solidity-evaluator"
