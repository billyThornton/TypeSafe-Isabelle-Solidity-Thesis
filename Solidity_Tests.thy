section \<open>Unit Tests for Solidity Semantics\<close>

text \<open>
  Executable unit tests using @{command eval} to assert that contract execution
  produces correct final states.  Each test group models a real-world Solidity
  contract and uses a @{command global_interpretation} of
  @{locale statement_with_gas} to instantiate an evaluator for that contract.

  Pattern per contract:
  \<^enum> Define the contract environment with @{term loadProc}.
  \<^enum> Interpret the locale to obtain a concrete @{term eval} function.
  \<^enum> Write @{command lemma} ... @{text "by eval"} assertions comparing the
    evaluator output string against the expected final state.

  The expected string encodes all variable values then account balances,
  mirroring @{term dump\<^sub>E\<^sub>n\<^sub>v\<^sub>i\<^sub>r\<^sub>o\<^sub>n\<^sub>m\<^sub>e\<^sub>n\<^sub>t} and @{term dump\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<^sub>s}.

  Notes:
  \<^item> @{term EXTERNAL} requires the callee address to differ from the caller.
  \<^item> @{term EQUAL} only compares @{term TSInt}/@{term TUInt}; address comparison
    is not supported by the semantics and is avoided here.
  \<^item> Contract storage is initially empty; use method calls to populate it.
  \<^item> The @{term dat} argument of @{term eval} pre-loads storage/stack values
    into the \<^emph>{caller}'s address (@{term addr}), not the callee's storage.
\<close>

theory Solidity_Tests
  imports Solidity_Evaluator
begin

(* ================================================================== *)
subsection \<open>SimpleStorage\<close>
(* ================================================================== *)

text \<open>
  Models:
  ```solidity
  contract SimpleStorage {
      uint storedData;
      function set(uint x) public { storedData = x; }
  }
  ```
  Tests:
  \<^item> @{text "set(42)"} stores 42 in contract storage
  \<^item> @{text "set(0)"}  stores 0 (zero-value round-trip)
\<close>

definition "simplestorage_env \<equiv>
  loadProc (STR ''SimpleStorage'')
    ([(STR ''storedData'', Var (STValue (TUInt b256))),
      (STR ''set'',
        Method ([(STR ''x'', Value (TUInt b256))], True,
          ASSIGN (Ref (STR ''storedData'') []) (LVAL (Id (STR ''x'')))))],
     ([], SKIP),
     SKIP)
  fmempty"

global_interpretation simplestorage: statement_with_gas costs_ex simplestorage_env costs_min
  defines stmt_ss = "simplestorage.stmt"
      and lexp_ss = simplestorage.lexp
      and expr_ss = simplestorage.expr
      and ssel_ss = simplestorage.ssel
      and rexp_ss = simplestorage.rexp
      and msel_ss = simplestorage.msel
      and load_ss = simplestorage.load
      and eval_ss = simplestorage.eval
  by unfold_locales auto

text \<open>@{text "set(42)"}: storedData in contract storage becomes 42.\<close>
lemma "eval_ss 1000
          (EXTERNAL (ADDRESS (STR ''StorageAddr'')) (STR ''set'') [UINT b256 42] (UINT b256 0))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''StorageAddr'', STR ''100'', atype.Contract (STR ''SimpleStorage''), 0),
           (STR ''CallerAddr'',  STR ''100'', EOA, 0)]
          []
  = STR ''StorageAddr: balance==100 - SimpleStorage(storedData==42\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval

text \<open>@{text "set(0)"}: storedData becomes 0 (explicit zero write).\<close>
lemma "eval_ss 1000
          (EXTERNAL (ADDRESS (STR ''StorageAddr'')) (STR ''set'') [UINT b256 0] (UINT b256 0))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''StorageAddr'', STR ''100'', atype.Contract (STR ''SimpleStorage''), 0),
           (STR ''CallerAddr'',  STR ''100'', EOA, 0)]
          []
  = STR ''StorageAddr: balance==100 - SimpleStorage(storedData==0\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval

text \<open>Two sequential sets: second write wins.\<close>
lemma "eval_ss 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''StorageAddr'')) (STR ''set'') [UINT b256 99] (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''StorageAddr'')) (STR ''set'') [UINT b256 7]  (UINT b256 0)))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''StorageAddr'', STR ''100'', atype.Contract (STR ''SimpleStorage''), 0),
           (STR ''CallerAddr'',  STR ''100'', EOA, 0)]
          []
  = STR ''StorageAddr: balance==100 - SimpleStorage(storedData==7\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval


(* ================================================================== *)
subsection \<open>Counter\<close>
(* ================================================================== *)

text \<open>
  Models:
  ```solidity
  contract Counter {
      uint public count;
      function increment() public { count += 1; }
      function decrement() public { count -= 1; }
      function reset()     public { count = 0;  }
  }
  ```
  Tests:
  \<^item> single increment: 0 \<rightarrow> 1
  \<^item> two increments:   0 \<rightarrow> 2
  \<^item> increment then decrement: 0 \<rightarrow> 1 \<rightarrow> 0
  \<^item> reset from any state: \<rightarrow> 0
\<close>

definition counter_inc :: s
  where "counter_inc \<equiv>
    ASSIGN (Ref (STR ''count'') [])
           (PLUS (LVAL (Ref (STR ''count'') [])) (UINT b256 1))"

definition counter_dec :: s
  where "counter_dec \<equiv>
    ASSIGN (Ref (STR ''count'') [])
           (MINUS (LVAL (Ref (STR ''count'') [])) (UINT b256 1))"

definition counter_reset :: s
  where "counter_reset \<equiv>
    ASSIGN (Ref (STR ''count'') []) (UINT b256 0)"

definition "counter_env \<equiv>
  loadProc (STR ''Counter'')
    ([(STR ''count'',     Var (STValue (TUInt b256))),
      (STR ''increment'', Method ([], True, counter_inc)),
      (STR ''decrement'', Method ([], True, counter_dec)),
      (STR ''reset'',     Method ([], True, counter_reset))],
     ([], SKIP),
     SKIP)
  fmempty"

global_interpretation counter: statement_with_gas costs_ex counter_env costs_min
  defines stmt_ctr = "counter.stmt"
      and lexp_ctr = counter.lexp
      and expr_ctr = counter.expr
      and ssel_ctr = counter.ssel
      and rexp_ctr = counter.rexp
      and msel_ctr = counter.msel
      and load_ctr = counter.load
      and eval_ctr = counter.eval
  by unfold_locales auto

text \<open>Single increment: count 0 \<rightarrow> 1.\<close>
lemma "eval_ctr 1000
          (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''CtrAddr'',    STR ''100'', atype.Contract (STR ''Counter''), 0),
           (STR ''CallerAddr'', STR ''100'', EOA, 0)]
          []
  = STR ''CtrAddr: balance==100 - Counter(count==1\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval

text \<open>Two increments: count 0 \<rightarrow> 2.\<close>
lemma "eval_ctr 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0)))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''CtrAddr'',    STR ''100'', atype.Contract (STR ''Counter''), 0),
           (STR ''CallerAddr'', STR ''100'', EOA, 0)]
          []
  = STR ''CtrAddr: balance==100 - Counter(count==2\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval

text \<open>Increment then decrement: count 0 \<rightarrow> 1 \<rightarrow> 0.\<close>
lemma "eval_ctr 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''decrement'') [] (UINT b256 0)))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''CtrAddr'',    STR ''100'', atype.Contract (STR ''Counter''), 0),
           (STR ''CallerAddr'', STR ''100'', EOA, 0)]
          []
  = STR ''CtrAddr: balance==100 - Counter(count==0\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval

text \<open>Reset from non-zero: five increments then reset yields 0.\<close>
lemma "eval_ctr 1000
          (COMP (COMP (COMP (COMP (COMP
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0)))
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0)))
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0)))
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''increment'') [] (UINT b256 0)))
            (EXTERNAL (ADDRESS (STR ''CtrAddr'')) (STR ''reset'')     [] (UINT b256 0)))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''CtrAddr'',    STR ''100'', atype.Contract (STR ''Counter''), 0),
           (STR ''CallerAddr'', STR ''100'', EOA, 0)]
          []
  = STR ''CtrAddr: balance==100 - Counter(count==0\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval


(* ================================================================== *)
subsection \<open>Token (ERC20-like)\<close>
(* ================================================================== *)

text \<open>
  Models:
  ```solidity
  contract Token {
      mapping(address => uint) public balances;
      function mint(address to, uint amount) public {
          balances[to] += amount;
      }
      function transfer(address to, uint amount) public {
          balances[msg.sender] -= amount;
          balances[to]         += amount;
      }
  }
  ```
  Note: no require guard is modelled since the semantics lacks a require statement.
  Underflow on transfer with insufficient balance wraps via @{term createUInt}.

  Tests:
  \<^item> mint gives tokens to an address
  \<^item> transfer moves tokens between two addresses
\<close>

definition token_mint :: s
  where "token_mint \<equiv>
    ASSIGN (Ref (STR ''balances'') [LVAL (Id (STR ''to''))])
           (PLUS (LVAL (Ref (STR ''balances'') [LVAL (Id (STR ''to''))]))
                 (LVAL (Id (STR ''amount''))))"

definition token_transfer :: s
  where "token_transfer \<equiv>
    COMP
      (ASSIGN (Ref (STR ''balances'') [SENDER])
              (MINUS (LVAL (Ref (STR ''balances'') [SENDER]))
                     (LVAL (Id (STR ''amount'')))))
      (ASSIGN (Ref (STR ''balances'') [LVAL (Id (STR ''to''))])
              (PLUS  (LVAL (Ref (STR ''balances'') [LVAL (Id (STR ''to''))]))
                     (LVAL (Id (STR ''amount'')))))"

definition "token_env \<equiv>
  loadProc (STR ''Token'')
    ([(STR ''balances'',
        Var (STMap TAddr (STValue (TUInt b256)))),
      (STR ''mint'',
        Method ([(STR ''to'', Value TAddr), (STR ''amount'', Value (TUInt b256))],
          True, token_mint)),
      (STR ''transfer'',
        Method ([(STR ''to'', Value TAddr), (STR ''amount'', Value (TUInt b256))],
          True, token_transfer))],
     ([], SKIP),
     SKIP)
  fmempty"

global_interpretation token: statement_with_gas costs_ex token_env costs_min
  defines stmt_tok = "token.stmt"
      and lexp_tok = token.lexp
      and expr_tok = token.expr
      and ssel_tok = token.ssel
      and rexp_tok = token.rexp
      and msel_tok = token.msel
      and load_tok = token.load
      and eval_tok = token.eval
  by unfold_locales auto

text \<open>@{text "mint(Alice, 100)"}: Alice's token balance becomes 100.\<close>
lemma "eval_tok 1000
          (EXTERNAL (ADDRESS (STR ''TokenAddr''))
            (STR ''mint'')
            [ADDRESS (STR ''AliceAddr''), UINT b256 100]
            (UINT b256 0))
          (STR ''OwnerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''TokenAddr'', STR ''0'',    atype.Contract (STR ''Token''), 0),
           (STR ''AliceAddr'', STR ''1000'', EOA, 0),
           (STR ''OwnerAddr'', STR ''1000'', EOA, 0)]
          []
  = STR ''TokenAddr: balance==0 - Token(balances[AliceAddr]==100\<newline>)\<newline>AliceAddr: balance==1000 - EOA\<newline>OwnerAddr: balance==1000 - EOA''"
  by eval

text \<open>@{text "transfer(Bob, 30)"} after Alice has 100: Alice \<rightarrow> 70, Bob \<rightarrow> 30.\<close>
lemma "eval_tok 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''TokenAddr''))
              (STR ''mint'')
              [ADDRESS (STR ''AliceAddr''), UINT b256 100]
              (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''TokenAddr''))
              (STR ''transfer'')
              [ADDRESS (STR ''BobAddr''), UINT b256 30]
              (UINT b256 0)))
          (STR ''AliceAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''TokenAddr'', STR ''0'',    atype.Contract (STR ''Token''), 0),
           (STR ''AliceAddr'', STR ''1000'', EOA, 0),
           (STR ''BobAddr'',   STR ''1000'', EOA, 0)]
          []
  = STR ''TokenAddr: balance==0 - Token(balances[AliceAddr]==70\<newline>balances[BobAddr]==30\<newline>)\<newline>AliceAddr: balance==1000 - EOA\<newline>BobAddr: balance==1000 - EOA''"
  by eval

text \<open>
  Models:
  ```solidity
  // mint(Alice, 40); mint(Alice, 2);
  // balances[Alice] == 42
  ```
  Repeated minting to the same address accumulates in the mapping entry.
\<close>
lemma "eval_tok 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''TokenAddr''))
              (STR ''mint'')
              [ADDRESS (STR ''AliceAddr''), UINT b256 40]
              (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''TokenAddr''))
              (STR ''mint'')
              [ADDRESS (STR ''AliceAddr''), UINT b256 2]
              (UINT b256 0)))
          (STR ''OwnerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''TokenAddr'', STR ''0'',    atype.Contract (STR ''Token''), 0),
           (STR ''AliceAddr'', STR ''1000'', EOA, 0),
           (STR ''OwnerAddr'', STR ''1000'', EOA, 0)]
          []
  = STR ''TokenAddr: balance==0 - Token(balances[AliceAddr]==42\<newline>)\<newline>AliceAddr: balance==1000 - EOA\<newline>OwnerAddr: balance==1000 - EOA''"
  by eval

text \<open>
  Models:
  ```solidity
  // mint(Alice, 100); transfer(Alice, 30);
  // transferring to yourself should leave the final balance unchanged
  // because the subtraction and addition hit the same mapping slot.
  ```
\<close>
lemma "eval_tok 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''TokenAddr''))
              (STR ''mint'')
              [ADDRESS (STR ''AliceAddr''), UINT b256 100]
              (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''TokenAddr''))
              (STR ''transfer'')
              [ADDRESS (STR ''AliceAddr''), UINT b256 30]
              (UINT b256 0)))
          (STR ''AliceAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''TokenAddr'', STR ''0'',    atype.Contract (STR ''Token''), 0),
           (STR ''AliceAddr'', STR ''1000'', EOA, 0)]
          []
  = STR ''TokenAddr: balance==0 - Token(balances[AliceAddr]==100\<newline>)\<newline>AliceAddr: balance==1000 - EOA''"
  by eval


(* ================================================================== *)
subsection \<open>Pausable\<close>
(* ================================================================== *)

text \<open>
  Models:
  ```solidity
  contract Pausable {
      bool public paused;
      function pause()   public { paused = true;  }
      function unpause() public { paused = false; }
  }
  ```
  Note: the semantics does not support address comparison via @{term EQUAL}
  (which only applies to integer types), so an access-control guard is omitted.

  Tests:
  \<^item> pause():   paused false \<rightarrow> true
  \<^item> pause then unpause: back to false
\<close>

definition "pausable_env \<equiv>
  loadProc (STR ''Pausable'')
    ([(STR ''paused'',  Var (STValue TBool)),
      (STR ''pause'',   Method ([], True, ASSIGN (Ref (STR ''paused'') []) TRUE)),
      (STR ''unpause'', Method ([], True, ASSIGN (Ref (STR ''paused'') []) FALSE))],
     ([], SKIP),
     SKIP)
  fmempty"

global_interpretation pausable: statement_with_gas costs_ex pausable_env costs_min
  defines stmt_pau = "pausable.stmt"
      and lexp_pau = pausable.lexp
      and expr_pau = pausable.expr
      and ssel_pau = pausable.ssel
      and rexp_pau = pausable.rexp
      and msel_pau = pausable.msel
      and load_pau = pausable.load
      and eval_pau = pausable.eval
  by unfold_locales auto

text \<open>pause(): paused becomes true.\<close>
lemma "eval_pau 1000
          (EXTERNAL (ADDRESS (STR ''PausableAddr'')) (STR ''pause'') [] (UINT b256 0))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''PausableAddr'', STR ''100'', atype.Contract (STR ''Pausable''), 0),
           (STR ''CallerAddr'',   STR ''100'', EOA, 0)]
          []
  = STR ''PausableAddr: balance==100 - Pausable(paused==true\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval

text \<open>pause then unpause: paused returns to false.\<close>
lemma "eval_pau 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''PausableAddr'')) (STR ''pause'')   [] (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''PausableAddr'')) (STR ''unpause'') [] (UINT b256 0)))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''PausableAddr'', STR ''100'', atype.Contract (STR ''Pausable''), 0),
           (STR ''CallerAddr'',   STR ''100'', EOA, 0)]
          []
  = STR ''PausableAddr: balance==100 - Pausable(paused==false\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval

text \<open>
  Models:
  ```solidity
  // pause(); pause();
  // repeated writes of true remain true
  ```
  This gives a basic idempotence check for a boolean storage flag.
\<close>
lemma "eval_pau 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''PausableAddr'')) (STR ''pause'') [] (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''PausableAddr'')) (STR ''pause'') [] (UINT b256 0)))
          (STR ''CallerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''PausableAddr'', STR ''100'', atype.Contract (STR ''Pausable''), 0),
           (STR ''CallerAddr'',   STR ''100'', EOA, 0)]
          []
  = STR ''PausableAddr: balance==100 - Pausable(paused==true\<newline>)\<newline>CallerAddr: balance==100 - EOA''"
  by eval


(* ================================================================== *)
subsection \<open>Escrow\<close>
(* ================================================================== *)

text \<open>
  Models:
  ```solidity
  contract Escrow {
      address public beneficiary;
      function setBeneficiary(address to) public { beneficiary = to; }
      function deposit()  public payable { /* ETH auto-received */ }
      function release()  public { payable(beneficiary).transfer(address(this).balance); }
  }
  ```
  There is no @{term deposit} method: depositing ETH is a plain @{term TRANSFER}
  to the contract address (which triggers the fallback @{term SKIP}).

  Tests:
  \<^item> setBeneficiary + deposit (50 ETH) + release drains the escrow to the beneficiary
\<close>

definition escrow_release :: s
  where "escrow_release \<equiv>
    TRANSFER (LVAL (Ref (STR ''beneficiary'') [])) (BALANCE THIS)"

definition "escrow_env \<equiv>
  loadProc (STR ''Escrow'')
    ([(STR ''beneficiary'', Var (STValue TAddr)),
      (STR ''setBeneficiary'',
        Method ([(STR ''to'', Value TAddr)], True,
          ASSIGN (Ref (STR ''beneficiary'') []) (LVAL (Id (STR ''to''))))),
      (STR ''release'',
        Method ([], True, escrow_release))],
     ([], SKIP),
     SKIP)
  fmempty"

global_interpretation escrow: statement_with_gas costs_ex escrow_env costs_min
  defines stmt_esc = "escrow.stmt"
      and lexp_esc = escrow.lexp
      and expr_esc = escrow.expr
      and ssel_esc = escrow.ssel
      and rexp_esc = escrow.rexp
      and msel_esc = escrow.msel
      and load_esc = escrow.load
      and eval_esc = escrow.eval
  by unfold_locales auto

text \<open>
  Full escrow lifecycle from Payer's perspective:
  \<^enum> @{term setBeneficiary} sets the recipient to BeneficiaryAddr.
  \<^enum> @{term TRANSFER} sends 50 ETH from Payer to Escrow (triggers fallback SKIP).
  \<^enum> @{term release} sends Escrow's full balance (50 ETH) to BeneficiaryAddr.

  Start:  Escrow=0, Payer=200, Beneficiary=100.
  Finish: Escrow=0, Payer=150, Beneficiary=150.
\<close>
lemma "eval_esc 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''EscrowAddr''))
              (STR ''setBeneficiary'')
              [ADDRESS (STR ''BeneficiaryAddr'')]
              (UINT b256 0))
            (COMP
              (TRANSFER (ADDRESS (STR ''EscrowAddr'')) (UINT b256 50))
              (EXTERNAL (ADDRESS (STR ''EscrowAddr''))
                (STR ''release'') [] (UINT b256 0))))
          (STR ''PayerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''EscrowAddr'',      STR ''0'',   atype.Contract (STR ''Escrow''), 0),
           (STR ''PayerAddr'',       STR ''200'', EOA, 0),
           (STR ''BeneficiaryAddr'', STR ''100'', EOA, 0)]
          []
  = STR ''EscrowAddr: balance==0 - Escrow(beneficiary==BeneficiaryAddr\<newline>)\<newline>PayerAddr: balance==150 - EOA\<newline>BeneficiaryAddr: balance==150 - EOA''"
  by eval

text \<open>
  Models:
  ```solidity
  // setBeneficiary(beneficiary);
  // release();
  // releasing an empty escrow should be a no-op on balances.
  ```
\<close>
lemma "eval_esc 1000
          (COMP
            (EXTERNAL (ADDRESS (STR ''EscrowAddr''))
              (STR ''setBeneficiary'')
              [ADDRESS (STR ''BeneficiaryAddr'')]
              (UINT b256 0))
            (EXTERNAL (ADDRESS (STR ''EscrowAddr''))
              (STR ''release'') [] (UINT b256 0)))
          (STR ''PayerAddr'')
          EMPTY
          EMPTY
          (STR ''0'')
          [(STR ''EscrowAddr'',      STR ''0'',   atype.Contract (STR ''Escrow''), 0),
           (STR ''PayerAddr'',       STR ''200'', EOA, 0),
           (STR ''BeneficiaryAddr'', STR ''100'', EOA, 0)]
          []
  = STR ''EscrowAddr: balance==0 - Escrow(beneficiary==BeneficiaryAddr\<newline>)\<newline>PayerAddr: balance==200 - EOA\<newline>BeneficiaryAddr: balance==100 - EOA''"
  by eval

end
