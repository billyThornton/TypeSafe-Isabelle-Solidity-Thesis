theory TypeSafe_Examples
  imports TypeSafe
begin
text \<open>Concrete usability demo for @{thm typesafe_base.TypeSafe_Statements} with a non-empty contract environment.

Solidity sketch that this setup models:

```solidity
contract C {
    bool x;
    uint8 y;

    function ping() public {
        // SKIP
    }
}
```

Mapping notes:
  * contract id @{term "STR ''C''"} is looked up in @{term ep_nonvacuous}
  * storage vars @{term "STR ''x''"} / @{term "STR ''y''"} map to
    @{term "Var (STValue TBool)"} / @{term "Var (STValue (TUInt b8))"} in @{term nv_ct}
  * environment is produced via @{term ffold_init} so Denvalue has Storeloc entries
  * statement @{term SKIP} plays the role of an empty function body
\<close>

definition demo_addr :: address
  where "demo_addr = createAddress (STR ''A'')"

definition demo_sender :: address
  where "demo_sender = createAddress (STR ''S'')"

definition demo_svalue :: valuetype
  where "demo_svalue = createUInt b256 0"

definition demo_env :: environment
  where "demo_env =
    ffold_init nv_ct (emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue) (fmdom nv_ct)"

definition demo_acc :: accounts
  where "demo_acc =
    emptyAccount(demo_addr := emptyAcc\<lparr>Type := Some (atype.Contract (STR ''C''))\<rparr>)"

definition demo_state :: state
  where "demo_state =
    \<lparr>Accounts = demo_acc,
     Stack = emptyStore,
     Memory = emptyTypedStore,
     Storage = emptyStorage,
     Gas = 1\<rparr>"

definition demo_cd :: calldataT
  where "demo_cd = emptyTypedStore"

lemma demo_safeContract_base:
  "typesafe_base.safeContract ep_nonvacuous demo_acc emptyStorage"
proof (unfold typesafe_nonvacuous.safeContract_def, intro allI impI)
  fix e ct dud i tp
  assume h:
    "Type (demo_acc (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
     ep_nonvacuous $$ environment.Contract (e::environment) = Some (ct, dud) \<and>
     fmlookup ct i = Some (Var tp)"

  have tc_ival: "\<And>t. typeCon t (ival t)"
  proof -
    fix t
    show "typeCon t (ival t)"
      using ivalTypeCon[of t "ival t"] by simp
  qed

  from h have ct_def: "ct = nv_ct"
    unfolding ep_nonvacuous_def nv_contract_def
    by (simp add: fmap_of_list_simps split:if_splits)
  from h ct_def consider
     (1) "(i = STR ''x'' \<and> tp = STValue TBool)"
    | (2) "(i = STR ''y'' \<and> tp = STValue (TUInt b8))"
    unfolding nv_ct_def
    by (auto split: if_splits member.splits)

  then show "SCon tp i (emptyStorage (Address e))" 
  proof (cases)
    case 1
    then show ?thesis
      unfolding emptyStorage_def accessStorage_def
      using tc_ival 
      by (metis SCon.simps(1) accessStorage_def fmempty_lookup option.case(1))
  next
    case 2
    then show ?thesis
      unfolding emptyStorage_def accessStorage_def
      using tc_ival by (metis SCon.simps(1) accessStorage_def fmempty_lookup option.case(1))
  qed
qed

lemma demo_safeContract:
  "typesafe_nonvacuous.safeContract demo_acc emptyStorage"
  using demo_safeContract_base
  by (simp add: typesafe_nonvacuous.safeContract_def)

lemma demo_safeContract_rewrite:
  "typesafe_nonvacuous.safeContract demo_acc sto =
   typesafe_base.safeContract ep_nonvacuous demo_acc sto"
  by (simp add: typesafe_nonvacuous.safeContract_def)

lemma demo_safeContract_base_literal:
  "typesafe_base.safeContract
     {STR ''C'' $$:= ({STR ''y'' $$:= Var (STValue (TUInt b8)),
                       STR ''x'' $$:= Var (STValue TBool)}, nv_ctor, SKIP)}
     demo_acc
     (\<lambda>uu. {$$})"
  using demo_safeContract_base
  unfolding ep_nonvacuous_def nv_contract_def nv_ct_def emptyStorage_def
  by simp

lemma demo_addressFormat_addr: "addressFormat demo_addr"
  unfolding addressFormat_def typeCon.simps checkAddress_def demo_addr_def
  using createAddressNoDots by blast

lemma demo_addressFormat_sender: "addressFormat demo_sender"
  unfolding addressFormat_def typeCon.simps checkAddress_def demo_sender_def
  using createAddressNoDots by blast

lemma demo_balanceTypes: "balanceTypes demo_acc"
  unfolding balanceTypes_def demo_acc_def emptyAccount_def emptyAcc_def
  by (simp add: checkUInt_def, eval)

lemma demo_AddressTypes: "typesafe_base.AddressTypes ep_nonvacuous demo_acc"
proof -
  have c_dom: "STR ''C'' |\<in>| fmdom ep_nonvacuous"
    unfolding ep_nonvacuous_def by simp
  have type_cases:
    "Type (demo_acc adv) =
     (if adv = demo_addr then Some (atype.Contract (STR ''C'')) else None)" for adv
    unfolding demo_acc_def emptyAccount_def emptyAcc_def
    by simp
  have case_eval:
    "case Type (demo_acc adv) of
       Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep_nonvacuous
     | _ \<Rightarrow> True =
     (if adv = demo_addr then addressFormat adv \<and> STR ''C'' |\<in>| fmdom ep_nonvacuous else True)" for adv
    using type_cases 
    using c_dom demo_addressFormat_addr by auto
  show ?thesis
    unfolding typesafe_nonvacuous.AddressTypes_def    
  proof (intros)
    fix adv
    show "case Type (demo_acc adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep_nonvacuous"
      using case_eval demo_addressFormat_addr c_dom 
      by (simp add: type_cases)
  qed
qed

lemma demo_typeSafe:
  "typesafe_base.TypeSafe ep_nonvacuous demo_env (Accounts demo_state) (Stack demo_state) (Memory demo_state) (Storage demo_state) demo_cd"
proof -
  have sc: "typesafe_base.safeContract ep_nonvacuous (Accounts demo_state) (Storage demo_state)"
    using demo_safeContract_base unfolding demo_state_def by simp
  have bt: "balanceTypes (Accounts demo_state)"
    using demo_balanceTypes unfolding demo_state_def by simp
  have sv: "svalueTypes demo_svalue"
    unfolding demo_svalue_def svalueTypes_def typeCon.simps checkUInt_def createUInt_def by eval
  have ltp: "lessThanTopLocs emptyTypedStore"
    using typesafe_nonvacuous.typedEmptyTopLocs by simp
  have ep_lookup:
    "ep_nonvacuous $$ Contract (emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue)
      = Some (nv_ct, (nv_ctor, SKIP))"
    unfolding ep_nonvacuous_def nv_contract_def by simp
  have af1: "addressFormat demo_addr" using demo_addressFormat_addr .
  have af2: "addressFormat demo_sender" using demo_addressFormat_sender .
  have at: "typesafe_nonvacuous.AddressTypes demo_acc" using demo_AddressTypes .
  have sp: "typesafe_nonvacuous.subPrefixStructuralConsistency emptyTypedStore"
    unfolding typesafe_nonvacuous.subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
  have svt: "typesafe_nonvacuous.SomeValSomeTyp emptyTypedStore"
    unfolding typesafe_nonvacuous.SomeValSomeTyp_def accessStore_def accessTypeStore_def emptyTypedStore_def by simp
  have coh: "Type (demo_acc demo_addr) = Some (atype.Contract (STR ''C''))"
    unfolding demo_state_def demo_acc_def demo_env_def ffold_init_def emptyAccount_def emptyAcc_def by simp
  have initTS:
    "\<forall>e' x y.
      ffold (init nv_ct) (emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue) (fmdom nv_ct) = e' \<longrightarrow>
      typesafe_base.TypeSafe ep_nonvacuous e' demo_acc emptyStore emptyTypedStore emptyStorage emptyTypedStore \<and>
      (Denvalue e' $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and>
      (Denvalue e' $$ x = Some y \<longrightarrow> (\<exists>t1. nv_ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
    using typesafe_nonvacuous.ffoldInitTypeSafe[OF sc bt sv ltp ep_lookup af1 af2 ] at demo_state_def 
    by (metis coh emptyEnv_members sp state.select_convs(1,4) svt)
  then show ?thesis
    unfolding demo_env_def demo_state_def demo_cd_def ffold_init_def 
    by simp
qed

lemma demo_fullyInitialised:
  "typesafe_base.fullyInitialised ep_nonvacuous demo_env (Accounts demo_state) (Stack demo_state)"
proof -
  have cfi:
    "Type (Accounts demo_state (Address demo_env)) = Some (atype.Contract (STR ''C'')) \<and> Contract demo_env = (STR ''C'')"
    unfolding demo_state_def demo_acc_def demo_env_def ffold_init_def emptyAccount_def emptyAcc_def
    by simp
  have epfi: "ep_nonvacuous $$ Contract demo_env = Some (nv_ct, (nv_ctor, SKIP))"
    unfolding demo_env_def ffold_init_def ep_nonvacuous_def nv_contract_def by simp
  have mapfi:
    "\<forall>id v. (nv_ct $$ id = Some (Var v)) = (Denvalue demo_env $$ id = Some (type.Storage v, Storeloc id))"
    using typesafe_nonvacuous.ffoldInit_var_storage_mapping_eq[of nv_ct demo_addr "STR ''C''" demo_sender demo_svalue demo_env]
    unfolding demo_env_def ffold_init_def by simp
  have locfi:
    "\<forall>id v loc. Denvalue demo_env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
  proof (intro allI impI)
    fix id v loc
    assume h: "Denvalue demo_env $$ id = Some (type.Storage v, Storeloc loc)"
    have hloc:
      "Denvalue demo_env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
      using typesafe_nonvacuous.ffoldInitAllLocsStorage[
          of nv_ct
             "emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue"
             "emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue"
             "emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue"
             demo_svalue
             "fmdom nv_ct"]
      unfolding demo_env_def ffold_init_def by simp
    then show "id = loc" using h by simp
  qed
  have ptrfi:
    "\<forall>t l p.
      (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue demo_env) \<and>
      accessStore l (Stack demo_state) = Some (KStoptr p) \<longrightarrow>
      (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue demo_env) \<and> CompStoType t' t l' p)"
    unfolding demo_state_def by (simp add: accessStore_def emptyStore_def)
  show ?thesis
    unfolding typesafe_base.fullyInitialised_def demo_state_def
    using cfi epfi mapfi locfi ptrfi 
    by (simp add: demo_state_def typesafe_nonvacuous.fullyInitialised_def)
qed

text \<open>Concrete non-vacuous witness for the pointer conjunct in @{thm typesafe_base.fullyInitialised_def}.
Unlike @{term demo_fullyInitialised}, this setup includes a storage-typed stack binding that points to
an existing storage location, so the pointer implication is exercised with a true antecedent.\<close>

definition demo_ptr_id :: Identifier
  where "demo_ptr_id = STR ''ptr_tmp''"

definition demo_ptr_stack_loc :: location
  where "demo_ptr_stack_loc = STR ''0''"

definition demo_ptr_target_loc :: location
  where "demo_ptr_target_loc = STR ''x''"

definition demo_env_with_stptr :: environment
  where "demo_env_with_stptr =
    demo_env\<lparr>Denvalue := fmupd demo_ptr_id
      (type.Storage (STValue TBool), Stackloc demo_ptr_stack_loc) (Denvalue demo_env)\<rparr>"

definition demo_state_with_stptr :: state
  where "demo_state_with_stptr =
    demo_state\<lparr>Stack := updateStore demo_ptr_stack_loc (KStoptr demo_ptr_target_loc) (Stack demo_state)\<rparr>"

lemma demo_pointer_clause_nonvacuous:
  "\<exists>t l p.
      (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue demo_env_with_stptr) \<and>
      accessStore l (Stack demo_state_with_stptr) = Some (KStoptr p) \<and>
      (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue demo_env_with_stptr) \<and> CompStoType t' t l' p)"
proof -
  have mapfi:
    "\<forall>id v. (nv_ct $$ id = Some (Var v)) = (Denvalue demo_env $$ id = Some (type.Storage v, Storeloc id))"
    using typesafe_nonvacuous.ffoldInit_var_storage_mapping_eq[of nv_ct demo_addr "STR ''C''" demo_sender demo_svalue demo_env]
    unfolding demo_env_def ffold_init_def by simp
  have den_target:
    "Denvalue demo_env $$ demo_ptr_target_loc =
      Some (type.Storage (STValue TBool), Storeloc demo_ptr_target_loc)"
    unfolding demo_ptr_target_loc_def using mapfi nv_ct_def 
    by (metis fmap_of_list_simps(2) fmupd_lookup)
  have den_ptr:
    "Denvalue demo_env_with_stptr $$ demo_ptr_id =
      Some (type.Storage (STValue TBool), Stackloc demo_ptr_stack_loc)"
    unfolding demo_env_with_stptr_def by simp
  have den_target':
    "Denvalue demo_env_with_stptr $$ demo_ptr_target_loc =
      Some (type.Storage (STValue TBool), Storeloc demo_ptr_target_loc)"
    unfolding demo_env_with_stptr_def using den_target
    by (simp add: demo_ptr_id_def demo_ptr_target_loc_def)
  have in_stack:
    "(type.Storage (STValue TBool), Stackloc demo_ptr_stack_loc) |\<in>| fmran (Denvalue demo_env_with_stptr)"
    using den_ptr by (simp add: fmranI)
  have in_store:
    "(type.Storage (STValue TBool), Storeloc demo_ptr_target_loc) |\<in>| fmran (Denvalue demo_env_with_stptr)"
    using den_target' by (simp add: fmranI)
  have ptr_stack:
    "accessStore demo_ptr_stack_loc (Stack demo_state_with_stptr) = Some (KStoptr demo_ptr_target_loc)"
    unfolding demo_state_with_stptr_def by simp
  have comp_self:
    "CompStoType (STValue TBool) (STValue TBool) demo_ptr_target_loc demo_ptr_target_loc"
    using CompStoType_sameLocNdTyp by simp
  show ?thesis
    using in_stack in_store ptr_stack comp_self by blast
qed

text \<open>Concrete 3D memory-array witness aligned with @{term decl} initialisation:
an outer array of length 2 whose element type is a 2D bool array.\<close>

definition demo_mem3d_elem_type :: mtypes
  where "demo_mem3d_elem_type = MTArray 2 (MTArray 2 (MTValue TBool))"

definition demo_mem3d_type :: mtypes
  where "demo_mem3d_type = MTArray 2 demo_mem3d_elem_type"

definition demo_mem3d_root :: location
  where "demo_mem3d_root = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory demo_state))"

definition demo_mem3d :: memoryT
  where "demo_mem3d = minit 2 demo_mem3d_elem_type (Memory demo_state)"

definition demo_mem3d_id :: Identifier
  where "demo_mem3d_id = STR ''m3d''"

definition demo_mem3d_stack_loc :: location
  where "demo_mem3d_stack_loc = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Stack demo_state))"

definition demo_stack_mem3d :: stack
  where "demo_stack_mem3d = push (KMemptr demo_mem3d_root) (Stack demo_state)"

definition demo_env_mem3d :: environment
  where "demo_env_mem3d =
    updateEnv demo_mem3d_id (type.Memory demo_mem3d_type) (Stackloc demo_mem3d_stack_loc) demo_env"

definition demo_state_mem3d :: state
  where "demo_state_mem3d = demo_state\<lparr>Stack := demo_stack_mem3d, Memory := demo_mem3d\<rparr>"

lemma demo_mem3d_id_fresh:
  "Denvalue demo_env $$ demo_mem3d_id = None"
proof (rule ccontr)
  assume h: "Denvalue demo_env $$ demo_mem3d_id \<noteq> None"
  then obtain x where hx: "Denvalue demo_env $$ demo_mem3d_id = Some x"
    by (cases "Denvalue demo_env $$ demo_mem3d_id") auto
  have in_dom: "demo_mem3d_id |\<in>| fmdom nv_ct"
  proof -
    have imp:
      "Denvalue demo_env $$ demo_mem3d_id = Some x \<longrightarrow> demo_mem3d_id |\<in>| fmdom nv_ct"
      using ffold_init_emptyDen[of nv_ct demo_addr "STR ''C''" demo_sender demo_svalue
          "fmdom nv_ct" demo_mem3d_id x]
      unfolding demo_env_def ffold_init_def .
    show ?thesis
      using imp hx by blast
  qed
  show False
    using in_dom
    unfolding demo_mem3d_id_def nv_ct_def
    by simp
qed

lemma demo_decl_mem3d_matches:
  "decl demo_mem3d_id (type.Memory demo_mem3d_type) None False
      demo_cd (Memory demo_state) (Storage demo_state (Address demo_env))
      (demo_cd, Memory demo_state, Stack demo_state, demo_env) =
   Some (demo_cd, demo_mem3d, demo_stack_mem3d, demo_env_mem3d)"
proof -
  have fresh: "Denvalue demo_env $$ demo_mem3d_id = None"
    using demo_mem3d_id_fresh .
  have arrs: "arraysGreaterZero demo_mem3d_type"
    unfolding demo_mem3d_type_def demo_mem3d_elem_type_def by simp
  have stk_env:
    "astack_dup demo_mem3d_id (type.Memory demo_mem3d_type) (KMemptr demo_mem3d_root)
      (Stack demo_state, demo_env) = (demo_stack_mem3d, demo_env_mem3d)"
  proof -
    have "astack_dup demo_mem3d_id (type.Memory demo_mem3d_type) (KMemptr demo_mem3d_root)
        (Stack demo_state, demo_env) =
      astack demo_mem3d_id (type.Memory demo_mem3d_type) (KMemptr demo_mem3d_root)
        (Stack demo_state, demo_env)"
      using astack_dup_is_astack[OF fresh] by auto
    also have "... = (demo_stack_mem3d, demo_env_mem3d)"
      unfolding demo_stack_mem3d_def demo_env_mem3d_def
                demo_mem3d_stack_loc_def demo_mem3d_root_def
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    unfolding demo_mem3d_id_def demo_mem3d_type_def demo_mem3d_elem_type_def
              demo_cd_def demo_state_def demo_mem3d_def demo_stack_mem3d_def
              demo_env_mem3d_def demo_mem3d_root_def demo_mem3d_stack_loc_def
    using fresh arrs stk_env 
    by (simp add: decl.simps(18) demo_mem3d_id_def)
qed

lemma demo_mem3d_root_empty:
  "accessStore demo_mem3d_root demo_mem3d = None"
  unfolding demo_mem3d_def demo_mem3d_elem_type_def demo_mem3d_root_def demo_state_def
  by eval

lemma demo_stack_mem3d_pointer:
  "accessStore demo_mem3d_stack_loc demo_stack_mem3d = Some (KMemptr demo_mem3d_root)"
  unfolding demo_mem3d_stack_loc_def demo_stack_mem3d_def demo_state_def accessStore_def
  by (metis Option.option.simps(3) accessStore_def decl_env_memory demo_decl_mem3d_matches demo_mem3d_id_fresh demo_mem3d_root_def demo_stack_mem3d_def
      demo_state_def)

lemma demo_env_mem3d_binding:
  "Denvalue demo_env_mem3d $$ demo_mem3d_id =
    Some (type.Memory demo_mem3d_type, Stackloc demo_mem3d_stack_loc)"
  unfolding demo_env_mem3d_def
  by simp



lemma demo_typeSafe_mem3d:
  "typesafe_base.TypeSafe ep_nonvacuous demo_env_mem3d
    (Accounts demo_state_mem3d) (Stack demo_state_mem3d) (Memory demo_state_mem3d) (Storage demo_state_mem3d) demo_cd"
proof -
  have base_ts:
    "typesafe_base.TypeSafe ep_nonvacuous demo_env
      (Accounts demo_state) (Stack demo_state) (Memory demo_state) (Storage demo_state) demo_cd"
    using demo_typeSafe .
  have decl_ok:
    "decl demo_mem3d_id (type.Memory demo_mem3d_type) None False
        demo_cd (Memory demo_state) (Storage demo_state (Address demo_env))
        (demo_cd, Memory demo_state, Stack demo_state, demo_env) =
     Some (demo_cd, demo_mem3d, demo_stack_mem3d, demo_env_mem3d)"
    using demo_decl_mem3d_matches .
  have step:
    "typesafe_base.TypeSafe ep_nonvacuous demo_env_mem3d
      (Accounts demo_state) demo_stack_mem3d demo_mem3d (Storage demo_state) demo_cd"
    using typesafe_nonvacuous.typeSafeDeclNone[OF base_ts decl_ok]
    by blast
  show ?thesis
    using step
    unfolding demo_state_mem3d_def
    by simp
qed

lemma demo_mem3d_lessThanTopLocs:
  "lessThanTopLocs demo_mem3d"
  using demo_typeSafe_mem3d
  unfolding typesafe_nonvacuous.TypeSafe_def demo_state_mem3d_def
  by simp

lemma demo_mem3d_subPrefixStructuralConsistency:
  "typesafe_nonvacuous.subPrefixStructuralConsistency demo_mem3d"
  using demo_typeSafe_mem3d
  unfolding typesafe_nonvacuous.TypeSafe_def demo_state_mem3d_def
  by simp

lemma demo_mem3d_SomeValSomeTyp:
  "typesafe_nonvacuous.SomeValSomeTyp demo_mem3d"
  using demo_typeSafe_mem3d
  unfolding typesafe_nonvacuous.TypeSafe_def demo_state_mem3d_def
  by simp

lemma demo_fullyInitialised_mem3d:
  "typesafe_base.fullyInitialised ep_nonvacuous demo_env_mem3d (Accounts demo_state_mem3d) (Stack demo_state_mem3d)"
proof -
  have cfi:
    "Type (Accounts demo_state_mem3d (Address demo_env_mem3d)) = Some (atype.Contract (STR ''C'')) \<and>
     Contract demo_env_mem3d = (STR ''C'')"
    unfolding demo_state_mem3d_def demo_state_def demo_acc_def demo_env_mem3d_def
              demo_env_def ffold_init_def emptyAccount_def emptyAcc_def
    by simp
  have epfi:
    "ep_nonvacuous $$ Contract demo_env_mem3d = Some (nv_ct, (nv_ctor, SKIP))"
    unfolding demo_env_mem3d_def demo_env_def ffold_init_def ep_nonvacuous_def nv_contract_def
    by simp
  have mapfi_base:
    "\<forall>id v. (nv_ct $$ id = Some (Var v)) = (Denvalue demo_env $$ id = Some (type.Storage v, Storeloc id))"
    using typesafe_nonvacuous.ffoldInit_var_storage_mapping_eq[of nv_ct demo_addr "STR ''C''" demo_sender demo_svalue demo_env]
    unfolding demo_env_def ffold_init_def by simp
  have mapfi:
    "\<forall>id v. (nv_ct $$ id = Some (Var v)) = (Denvalue demo_env_mem3d $$ id = Some (type.Storage v, Storeloc id))"
    using mapfi_base
    unfolding demo_env_mem3d_def demo_mem3d_id_def nv_ct_def
    by force
  have locfi_base:
    "\<forall>id v loc. Denvalue demo_env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
  proof (intro allI impI)
    fix id v loc
    assume h: "Denvalue demo_env $$ id = Some (type.Storage v, Storeloc loc)"
    have hloc:
      "Denvalue demo_env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
      using typesafe_nonvacuous.ffoldInitAllLocsStorage[
          of nv_ct
             "emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue"
             "emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue"
             "emptyEnv demo_addr (STR ''C'') demo_sender demo_svalue"
             demo_svalue
             "fmdom nv_ct"]
      unfolding demo_env_def ffold_init_def by simp
    then show "id = loc" using h by simp
  qed
  have locfi:
    "\<forall>id v loc. Denvalue demo_env_mem3d $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
    using locfi_base
    unfolding demo_env_mem3d_def demo_mem3d_id_def
    by auto
  have ptrfi:
    "\<forall>t l p.
      (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue demo_env_mem3d) \<and>
      accessStore l (Stack demo_state_mem3d) = Some (KStoptr p) \<longrightarrow>
      (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue demo_env_mem3d) \<and> CompStoType t' t l' p)"
    unfolding demo_env_mem3d_def demo_state_mem3d_def demo_stack_mem3d_def demo_state_def
    by (simp add: accessStore_def emptyStore_def push_def allocate_def updateStore_def)
  show ?thesis
    unfolding typesafe_base.fullyInitialised_def typesafe_nonvacuous.fullyInitialised_def
    using cfi epfi mapfi locfi ptrfi
    by auto
qed

lemma demo_stmt_normal:
  "typesafe_nonvacuous.stmt SKIP demo_env demo_cd demo_state = Normal ((), demo_state)"
  unfolding demo_state_def demo_cd_def 
  by (simp add: typesafe_nonvacuous.stmt.simps demo_state_def demo_cd_def)    

lemma demo_stmt_normal_mem3d:
  "typesafe_nonvacuous.stmt SKIP demo_env_mem3d demo_cd demo_state_mem3d = Normal ((), demo_state_mem3d)"
  unfolding demo_env_mem3d_def demo_state_mem3d_def demo_state_def demo_cd_def
  by (simp add: typesafe_nonvacuous.stmt.simps)

text \<open>Explicit prerequisite chain for applying @{thm typesafe_base.TypeSafe_Statements}.\<close>

lemma demo_mem3d_prereq_TypeSafe:
  "typesafe_base.TypeSafe ep_nonvacuous demo_env_mem3d
     (Accounts demo_state_mem3d) (Stack demo_state_mem3d) (Memory demo_state_mem3d) (Storage demo_state_mem3d) demo_cd"
  using demo_typeSafe_mem3d .

lemma demo_mem3d_prereq_stmt_normal:
  "typesafe_nonvacuous.stmt SKIP demo_env_mem3d demo_cd demo_state_mem3d = Normal ((), demo_state_mem3d)"
  using demo_stmt_normal_mem3d .

lemma demo_mem3d_prereq_fullyInitialised:
  "typesafe_base.fullyInitialised ep_nonvacuous demo_env_mem3d (Accounts demo_state_mem3d) (Stack demo_state_mem3d)"
  using demo_fullyInitialised_mem3d .

lemma demo_StateInvariant_from_TypeSafe_Statements:
  "typesafe_base.StateInvariant ep_nonvacuous demo_env demo_state demo_state demo_cd"
  using typesafe_nonvacuous.TypeSafe_Statements[OF demo_typeSafe demo_stmt_normal demo_fullyInitialised] .

lemma demo_mem3d_StateInvariant_from_TypeSafe_Statements_explicit:
  "typesafe_base.StateInvariant ep_nonvacuous demo_env_mem3d demo_state_mem3d demo_state_mem3d demo_cd"
proof -
  have ts:
    "typesafe_base.TypeSafe ep_nonvacuous demo_env_mem3d
      (Accounts demo_state_mem3d) (Stack demo_state_mem3d) (Memory demo_state_mem3d) (Storage demo_state_mem3d) demo_cd"
    using demo_mem3d_prereq_TypeSafe .
  have st:
    "typesafe_nonvacuous.stmt SKIP demo_env_mem3d demo_cd demo_state_mem3d = Normal ((), demo_state_mem3d)"
    using demo_mem3d_prereq_stmt_normal .
  have fi:
    "typesafe_base.fullyInitialised ep_nonvacuous demo_env_mem3d (Accounts demo_state_mem3d) (Stack demo_state_mem3d)"
    using demo_mem3d_prereq_fullyInitialised .
  have inv:
    "typesafe_base.StateInvariant ep_nonvacuous demo_env_mem3d demo_state_mem3d demo_state_mem3d demo_cd"
    using typesafe_nonvacuous.TypeSafe_Statements[OF ts st fi] .
  show ?thesis
    using inv .
qed

text \<open>Concrete evaluator output for the memory example.\<close>

value \<open>demo_state_mem3d\<close>
value \<open>Memory demo_state_mem3d\<close>
value \<open>Stack demo_state_mem3d\<close>
value \<open>Denvalue demo_env_mem3d\<close>
value \<open>accessStore demo_mem3d_stack_loc (Stack demo_state_mem3d)\<close>
value \<open>accessStore (hash demo_mem3d_root (STR ''0'')) (Memory demo_state_mem3d)\<close>

end
