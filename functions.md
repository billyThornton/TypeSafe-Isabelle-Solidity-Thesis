# Solidity Isabelle/HOL — Definitions and Lemmas

<a name="typesD"></a>
<a name="Types"></a>

### types — datatype
[`datatype types`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Valuetypes.thy#L117-L120)

<a name="resultM"></a>
<a name="result"></a>

### result — datatype
[`datatype result`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L7)

<a name="StateMonad"></a>
<a name="state_monad"></a>

### state_monad — type_synonym
[`type_synonym state_monad`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L9)

<a name="bindM"></a>
<a name="bind"></a>

### bind — fun
[`fun bind`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L32-L35)

<a name="returnM"></a>
<a name="return"></a>

### return — fun
[`fun return`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L26-L27)

<a name="throwM"></a>
<a name="throw"></a>

### throw — fun
[`fun throw`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L29-L30)

<a name="get"></a>

### get — fun
[`fun get`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L139-L140)

<a name="put"></a>

### put — fun
[`fun put`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L142-L143)

<a name="modify"></a>

### modify — fun
[`fun modify`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L152-L154)

<a name="applyfM"></a>
<a name="applyf"></a>

### applyf — fun
[`fun applyf`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L147-L149)

<a name="assert"></a>

### assert — fun
[`fun assert`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L156-L158)

<a name="option"></a>

### option — fun
[`fun option`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/StateMonad.thy#L160-L164)

<a name="bitsD"></a>
<a name="bits"></a>

### bits — typedef
[`typedef bits`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Valuetypes.thy#L25-L27)

<a name="createUInt"></a>

### createUInt — definition
[`definition createUInt`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Valuetypes.thy#L224-L225)

<a name="createSInt"></a>

### createSInt — definition
[`definition createSInt`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Valuetypes.thy#L123-L129)

<a name="mtypesD"></a>
<a name="mtypes"></a>

### mtypes — datatype
[`datatype mtypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L199-L201)

<a name="stypesD"></a>
<a name="stypes"></a>

### stypes — datatype
[`datatype stypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L140-L143)

<a name="comp"></a>

### comp — fun
[`fun comp`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Valuetypes.thy#L332-L339)

<a name="convert"></a>

### convert — definition
[`definition convert`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Valuetypes.thy#L341-L357)

<a name="cps2mTypeCompatible"></a>

### cps2mTypeCompatible — definition
[`definition cps2mTypeCompatible`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L395-L399)

<a name="arraysGreaterZero"></a>

### arraysGreaterZero — primrec
[`primrec arraysGreaterZero`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L287-L289)

<a name="storeD"></a>
<a name="Store"></a>

### store — record
[`record store`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L73-L75)

<a name="emptyStore"></a>

### emptyStore — definition
[`definition emptyStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L82-L83)

<a name="accSto"></a>
<a name="accessStore"></a>

### accessStore — definition
[`definition accessStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L77-L78)

<a name="updSto"></a>
<a name="updateStore"></a>

### updateStore — definition
[`definition updateStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L105-L106)

<a name="allocate"></a>

### allocate — definition
[`definition allocate`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L87-L88)

<a name="push"></a>

### push — definition
[`definition push`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L118-L119)

<a name="hashD"></a>
<a name="hash"></a>

### hash — definition
[`definition hash`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L10-L11)

<a name="hash_injective"></a>

### hash_injective — lemma
[`lemma hash_injective`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L32-L69)

<a name="stackvalD"></a>
<a name="Stackvalue"></a>

### stackvalue — datatype
[`datatype stackvalue`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L125-L128)

<a name="stackD"></a>
<a name="Stack"></a>

### stack — type_synonym
[`type_synonym stack`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L28)

<a name="storageD"></a>
<a name="storageT"></a>

### storageT — type_synonym
[`type_synonym storageT`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L96)

<a name="ivalD"></a>
<a name="ival"></a>

### ival — definition
[`definition ival`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Valuetypes.thy#L255-L272)

<a name="accStorD"></a>
<a name="accessStorage"></a>

### accessStorage — definition
[`definition accessStorage`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L41)

<a name="memValD"></a>
<a name="memoryvalue"></a>

### memoryvalue — datatype
[`datatype memoryvalue`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L195-L198)

<a name="typedstoreD"></a>
<a name="typedstore"></a>

### typedstore — record
[`record typedstore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L203)

<a name="emptyTypedStore"></a>

### emptyTypedStore — definition
[`definition emptyTypedStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L227)

<a name="accessTypeStore"></a>

### accessTypeStore — definition
[`definition accessTypeStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L211)

<a name="updateTypeStore"></a>

### updateTypeStore — definition
[`definition updateTypeStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L217)

<a name="updateTypedStore"></a>

### updateTypedStore — definition
[`definition updateTypedStore`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L223)

<a name="memoryD"></a>
<a name="memoryT"></a>

### memoryT — type_synonym
[`type_synonym memoryT`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L243)

<a name="minitRec"></a>

### minitRec — primrec
[`primrec minitRec`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L270-L276)

<a name="minit"></a>

### minit — definition
[`definition minit`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L278-L283)

<a name="calldataD"></a>
<a name="calldataT"></a>

### calldataT — type_synonym
[`type_synonym calldataT`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L245)

<a name="iterP"></a>
<a name="iter'"></a>

### iter — definition
[`definition iter`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Finite_Map_Extras.thy#L18)

<a name="cpm2mD"></a>
<a name="cpm2m"></a>

### cpm2m — definition
[`definition cpm2m`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L255-L269)

<a name="cpm2mRecD"></a>
<a name="cpm2mRec"></a>

### cpm2mRec — primrec
[`primrec cpm2mRec`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L248-L253)

<a name="cps2m"></a>

### cps2m — definition
[`definition cps2m`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L272)

<a name="cpm2s"></a>

### cpm2s — definition
[`definition cpm2s`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L273)

<a name="stateD"></a>
<a name="State"></a>

### state — record
[`record state`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Accounts.thy#L2)

<a name="atypeD"></a>
<a name="atype"></a>

### atype — datatype
[`datatype atype`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Accounts.thy#L9)

<a name="accountD"></a>
<a name="account"></a>

### account — record
[`record account`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Accounts.thy#L13)

<a name="hashVersionD"></a>
<a name="hash_version"></a>

### hash_version — definition
[`definition hash_version`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Accounts.thy#L35)

<a name="typeD"></a>
<a name="type"></a>

### type — datatype
[`datatype type`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L2-L8)

<a name="denvalue"></a>

### denvalue — datatype
[`datatype denvalue`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L12-L14)

<a name="Denvalue"></a>

### Denvalue — definition
[`definition Denvalue`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L45-L46)

<a name="environmentD"></a>
<a name="environment"></a>

### environment — record
[`record environment`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L19-L26)

<a name="emptyEnvD"></a>
<a name="emptyEnv"></a>

### emptyEnv — definition
[`definition emptyEnv`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L63-L65)

<a name="updateEnvDup"></a>

### updateEnvDup — definition
[`definition updateEnvDup`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L71-L75)

<a name="astack"></a>

### astack — definition
[`definition astack`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L77-L82)

<a name="astackDupD"></a>
<a name="astack_dup"></a>

### astack_dup — definition
[`definition astack_dup`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L127-L140)

<a name="declD"></a>
<a name="decl"></a>

### decl — definition
[`definition decl`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Environment.thy#L153-L166)

<a name="declEnvInvariantL"></a>
<a name="Decl_Env"></a>

### Decl_Env — lemma
[`lemma Decl_Env`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Environment.thy#L1)

<a name="decl_env_monotonic"></a>
<a name="Decl_Denvalue_Monotonic"></a>

### Decl_Denvalue_Monotonic — lemma
[`lemma Decl_Denvalue_Monotonic`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Environment.thy#L1)

<a name="memberD"></a>
<a name="Member"></a>

### member — datatype
[`datatype member`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Contracts.thy#L2-L4)

<a name="contractD"></a>
<a name="Contract"></a>

### contract — record
[`record contract`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Contracts.thy#L8-L12)

<a name="envPD"></a>
<a name="$Environment_p$"></a>

### environment_p — type_synonym
[`type_synonym environment_p`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Contracts.thy#L14)

<a name="initD"></a>
<a name="init"></a>

### init — definition
[`definition init`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Contracts.thy#L16-L30)

<a name="exprWithGasD"></a>
<a name="expressions_with_gas"></a>

### expressions_with_gas — inductive
[`inductive expressions_with_gas`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L3-L20)

<a name="stmtWithGasD"></a>
<a name="statement_with_gas"></a>

### statement_with_gas — inductive
[`inductive statement_with_gas`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L3-L18)

<a name="wptoState"></a>
<a name="toState"></a>

### toState — definition
[`definition toState`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Weakest_Precondition.thy#L6)

<a name="gascheck_eq"></a>
<a name="gascheck"></a>

### gascheck — definition
[`definition gascheck`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Weakest_Precondition.thy#L20)

<a name="lD"></a>
<a name="l"></a>

### l — definition
[`definition l`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L127)

<a name="eD"></a>
<a name="e"></a>

### e — definition
[`definition e`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L131)

<a name="inBound_eq"></a>
<a name="inBound"></a>

### inBound — definition
[`definition inBound`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L140)

<a name="mselD"></a>
<a name="msel"></a>

### msel — fun
[`fun msel`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L160-L175)

<a name="msel_array_single"></a>
<a name="msel-single"></a>

### msel array single — case
[`msel case single`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L167)

<a name="msel_array_multi"></a>
<a name="msel-multi"></a>

### msel array multi — case
[`msel case multi`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L172)

<a name="msel_default"></a>
<a name="msel-default"></a>

### msel default — case
[`msel case default`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L174)

<a name="sselD"></a>
<a name="ssel"></a>

### ssel — fun
[`fun ssel`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L176-L187)

<a name="ssel_array"></a>
<a name="ssel-array"></a>

### ssel array — case
[`ssel case array`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L177)

<a name="ssel_map"></a>
<a name="ssel-map"></a>

### ssel map — case
[`ssel case map`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L184)

<a name="ssel_base"></a>
<a name="ssel-base"></a>

### ssel base — case
[`ssel case base`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L187)

<a name="lTypeD"></a>
<a name="ltype"></a>

### ltype — definition
[`definition ltype`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L190-L198)

<a name="lexpD"></a>
<a name="lexp"></a>

### lexp — fun
[`fun lexp`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L199-L214)

<a name="lexp_id"></a>
<a name="lexp-id"></a>

### lexp\_id — case
[`lexp case id`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L202)

<a name="lexp_ref"></a>
<a name="lexp-ref"></a>

### lexp ref — case
[`lexp case ref`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L208-L214)

<a name="rexpD"></a>
<a name="rexp"></a>

### rexp — fun
[`fun rexp`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L216-L235)

<a name="rexp_id"></a>
<a name="rexp-id"></a>

### rexp\_id — case
[`rexp case id`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L217)

<a name="rexp_ref"></a>
<a name="rexp-ref"></a>

### rexp ref — case
[`rexp case ref`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L224)

<a name="rexp_ref_stack"></a>
<a name="rexp-ref-stack"></a>

### rexp ref stack — case
[`rexp case stack`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L226)

<a name="rexp_ref_storage"></a>
<a name="rexp-ref-storage"></a>

### rexp ref storage — case
[`rexp case storage`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L231)

<a name="expr"></a>

### expr — fun
[`fun expr`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L237-L298)

<a name="expr_bool_consts"></a>
<a name="expr-bool"></a>

### expr bool consts — case
[`expr case bool`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L239-L241)

<a name="expr_address"></a>
<a name="expr-address"></a>

### expr address — case
[`expr case address`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L242-L243)

<a name="expr_int_uint"></a>
<a name="expr-int"></a>

### expr int uint — case
[`expr case int`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L244-L250)

<a name="expr_context_consts"></a>
<a name="expr-context"></a>

### expr context consts — case
[`expr case context`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L251-L255)

<a name="expr_lval"></a>
<a name="expr-lval"></a>

### expr lval — case
[`expr case lval`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L256)

<a name="expr_balance"></a>
<a name="expr-balance"></a>

### expr balance — case
[`expr case balance`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L257-L259)

<a name="expr_contracts"></a>
<a name="expr-contracts"></a>

### expr contracts — case
[`expr case contracts`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L260-L262)

<a name="expr_not"></a>
<a name="expr-not"></a>

### expr not — case
[`expr case not`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L263-L266)

<a name="expr_plus"></a>
<a name="expr-plus"></a>

### expr plus — case
[`expr case plus`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L267-L275)

<a name="load"></a>

### load — fun
[`fun load`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L300-L335)

<a name="load_recurse"></a>
<a name="load-recurse"></a>

### load recurse — case
[`load case recurse`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L302-L307)

<a name="load_bind"></a>
<a name="load-bind"></a>

### load bind — case
[`load case bind`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L308-L310)

<a name="load_base"></a>
<a name="load-base"></a>

### load base — case
[`load case base`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L311-L312)

<a name="load_result"></a>
<a name="load-result"></a>

### load result — case
[`load case result`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L313-L335)

<a name="expr_call_internal"></a>
<a name="expr-call"></a>

### expr call internal — case
[`expr case call internal`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L276-L298)

<a name="expr_call_external"></a>
<a name="expr-ecall"></a>

### expr call external — case
[`expr case call external`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Expressions.thy#L337-L348)

<a name="statementsD"></a>
<a name="S"></a>

### S — datatype
[`datatype S`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L20-L32)

<a name="stmt"></a>

### stmt — fun
[`fun stmt`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L34-L82)

<a name="stmt_skip"></a>
<a name="stmt-skip"></a>

### stmt skip — case
[`stmt case skip`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L35)

<a name="stmt_comp"></a>
<a name="stmt-comp"></a>

### stmt composition — case
[`stmt case composition`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L37)

<a name="stmt_ite"></a>
<a name="stmt-ite"></a>

### stmt if-then-else — case
[`stmt case if-then-else`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L40-L41)

<a name="stmt_while"></a>
<a name="stmt-while"></a>

### stmt while — case
[`stmt case while`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L43)

<a name="stmt_block"></a>
<a name="stmt-block"></a>

### stmt block — case
[`stmt case block`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L46)

<a name="stmt_assign"></a>
<a name="stmt-assign"></a>

### stmt assign — case
[`stmt case assign`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L48-L49)

<a name="assignValue_eq"></a>
<a name="assignValue"></a>

### assignValue — fun
[`fun assignValue`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L84-L93)

<a name="assignCalldata_eq"></a>
<a name="assignCalldata"></a>

### assignCalldata — fun
[`fun assignCalldata`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L94-L102)

<a name="assignMemory_eq"></a>
<a name="assignMemory"></a>

### assignMemory — fun
[`fun assignMemory`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L103-L115)

<a name="assignStorageArr_eq"></a>
<a name="assignStorageArr"></a>

### assignStorageArr — fun
[`fun assignStorageArr`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L116-L128)

<a name="assignMapping_eq"></a>
<a name="assignMapping"></a>

### assignMapping — fun
[`fun assignMapping`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L129-L139)

<a name="stmt_invoke_internal"></a>
<a name="stmt-invoke"></a>

### stmt invoke — case
[`stmt case invoke`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L50)

<a name="stmt_external"></a>
<a name="stmt-external"></a>

### stmt external — case
[`stmt case external`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L51)

<a name="stmt_transfer"></a>
<a name="stmt-transfer"></a>

### stmt transfer — case
[`stmt case transfer`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L53)

<a name="stmt_new"></a>
<a name="stmt-new"></a>

### stmt new — case
[`stmt case new`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Statements.thy#L54)

<a name="typeconD"></a>
<a name="TypeCon"></a>

### typeConformity — definition
[`definition typeConformity`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Valuetypes.thy#L274-L299)

<a name="sublocD"></a>
<a name="LSubPrefL2"></a>

### subPrefixes — definition
[`definition subPrefixes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L101-L115)

<a name="sconD"></a>
<a name="SCon"></a>

### SCon — definition
[`definition SCon`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/Storage.thy#L73-L95)

<a name="typeStoSubD"></a>
<a name="TypedStoSubpref"></a>

### TypedStoSubpref — informal definition
Defined in thesis ch5/TypeConsistency.tex. See TypeSafe_Storage.thy for related lemmas.

<a name="compStoSubD"></a>
<a name="CompStoType"></a>

### CompStoType — informal definition
Defined in thesis ch5/TypeConsistency.tex. See TypeSafe_Storage.thy for related lemmas.

<a name="sconImpliesSublocsL"></a>
<a name="SCon_imps_sublocs"></a>

### SCon_imps_sublocs — informal lemma
Proved in thesis ch5/TypeConsistency.tex. See TypeSafe_Storage.thy for related proofs.

<a name="mconD"></a>
<a name="MCon"></a>

### MCon — informal definition
Defined in thesis ch5/TypeConsistency.tex. See TypeSafe_Memory.thy for related lemmas.

<a name="typMemSubD"></a>
<a name="TypedMemSubPrefPtrs"></a>

### TypedMemSubPrefPtrs — informal lemma
Proved in thesis ch5/TypeConsistency.tex. See TypeSafe_Memory.thy for related proofs.

<a name="compMemSubD"></a>
<a name="CompMemType"></a>

### CompMemType — informal definition
Defined in thesis ch5/TypeConsistency.tex. See TypeSafe_Memory.thy for related lemmas.

<a name="typesafeBaseD"></a>
<a name="typesafe_base"></a>

### typesafe_base — locale
[`locale typesafe_base`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L462)

<a name="typesafeVacuousD"></a>
<a name="typesafe_vacuous"></a>

### typesafe_vacuous — global\_interpretation
[`global_interpretation typesafe_vacuous`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L1122-L1123)

<a name="typesafeNonvacuousD"></a>
<a name="typesafe_nonvacuous"></a>

### typesafe_nonvacuous — global\_interpretation
[`global_interpretation typesafe_nonvacuous`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L1150-L1151)

<a name="uniqLocD"></a>
<a name="UniqueLocations"></a>

### unique_locations — definition
[`definition unique_locations`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L12-L18)

<a name="compPointersD"></a>
<a name="CompPointers"></a>

### typeSafeCompPointers — lemma
[`lemma typeSafeCompPointers`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L727)

<a name="lesstopD"></a>
<a name="LessThanTopLocs"></a>

### typeSafeAllPtrsNotTop — lemma
[`lemma typeSafeAllPtrsNotTop`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L868)

<a name="denvalTypCorrD"></a>
<a name="denvalueTypeCorrectness"></a>

### denvalueTypeCorrectness — definition
[`definition denvalueTypeCorrectness`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L573)

<a name="subPrefStrucD"></a>
<a name="subPrefixStructuralConsistency"></a>

### subPrefixStructuralConsistency — definition
[`definition subPrefixStructuralConsistency`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L583)

<a name="someValSomeTypD"></a>
<a name="SomeValSomeTyp"></a>

### SomeValSomeTyp — definition
[`definition SomeValSomeTyp`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L595)

<a name="envAddressesWellFormedD"></a>
<a name="envAddressesWellFormed"></a>

### typeSafeEnvAddresses — lemma
[`lemma typeSafeEnvAddresses`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L719)

<a name="AddressTypesD"></a>
<a name="AddressTypes"></a>

### AddressTypes — definition
[`definition AddressTypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L534)

<a name="baltypesD"></a>
<a name="balanceTypes"></a>

### balanceTypes — definition
[`definition balanceTypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L356)

<a name="svaluetypesD"></a>
<a name="svalueTypes"></a>

### svalueTypes — definition
[`definition svalueTypes`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L365)

<a name="safecontractD"></a>
<a name="safeContract"></a>

### safeContract — definition
[`definition safeContract`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L558)

<a name="typesafeDef"></a>
<a name="TypeSafe"></a>

### TypeSafe — definition
[`definition TypeSafe`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Def.thy#L606)

<a name="mselTcL"></a>
<a name="exprTypeconInduct(1)"></a>

### exprTypeconInduct (msel case) — lemma case
[`lemma exprTypeconInduct case 1`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Expressions.thy#L192)

<a name="sselTcL"></a>
<a name="exprTypeconInduct(2)"></a>

### exprTypeconInduct (ssel case) — lemma case
[`lemma exprTypeconInduct case 2`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Expressions.thy#L192)

<a name="rexpTcL"></a>
<a name="exprTypeconInduct(5)"></a>

### exprTypeconInduct (rexp case) — lemma case
[`lemma exprTypeconInduct case 5`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Expressions.thy#L192)

<a name="lexpStorageL"></a>
<a name="lexpStorageG"></a>

### lexpStorageG — informal lemma
Proved in thesis ch5/VerifyingStatementExpr.tex. See TypeSafe_Environment.thy for related proofs.

<a name="lexpMemL"></a>
<a name="lexpIndexMem"></a>

### lexpIndexMem — informal lemma
Proved in thesis ch5/VerifyingStatementExpr.tex. See TypeSafe_Memory.thy for related proofs.

<a name="TSStatementL"></a>
<a name="TypeSafe_Statements"></a>

### TypeSafe_Statements — lemma
[`lemma TypeSafe_Statements`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe.thy#L1065)

<a name="exprTcL"></a>
<a name="exprTypeconInduct(3)"></a>

### exprTypeconInduct (expr case) — lemma case
[`lemma exprTypeconInduct case 3`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Expressions.thy#L192)

<a name="typesafeExamplesF"></a>
<a name="TypeSafe_Examples.thy"></a>

### TypeSafe\_Examples.thy — file
[`TypeSafe_Examples.thy`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Examples.thy)

<a name="mcCpm2mL"></a>
<a name="MCon_cpm2m"></a>

### MCon_cpm2m — lemma
[`lemma MCon_cpm2m`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Memory_Copies.thy#L2648)

<a name="loadTcL"></a>
<a name="exprTypeconInduct(4)"></a>

### exprTypeconInduct (load case) — lemma case
[`lemma exprTypeconInduct case 4`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Expressions.thy#L192)

<a name="tsDeclL"></a>
<a name="typeSafeDecl"></a>

### typeSafeDecl — lemma
[`lemma typeSafeDecl`](https://github.com/billyThornton/TypeSafe-Isabelle-Solidity-Thesis/blob/main/TypeSafe_Environment.thy#L2165)
