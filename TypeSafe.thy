theory TypeSafe
  imports TypeSafe_Expressions
begin

context typesafe_base
begin

lemma diffTypeDiffLoc:
  assumes "st' = st\<lparr>Stack := updateStore l v (Stack st), Gas:=g\<rparr>"
    and "v' \<noteq> v"
    and "accessStore l1 (Stack st') = Some v'"
  shows "l1 \<noteq> l" using assms notNoneUpdate by fastforce

lemma stackSingleUpdate:
  assumes "st' = st\<lparr>Stack := updateStore l v (Stack st), Gas:=g\<rparr>"
  shows "\<forall>nl \<noteq>l. accessStore nl (Stack st) = accessStore nl (Stack st')"
proof (intros)
  fix nl
  assume a1:"nl \<noteq> l"
  then have "accessStore nl (updateStore l v (Stack st)) = accessStore nl (Stack st)"
    unfolding updateStore_def by (simp add: accessStore_def)
  then show "accessStore nl (Stack st) = accessStore nl (Stack st')"  using assms by simp     
qed

lemma updateOneType:
  assumes "st' = st\<lparr>Stack := updateStore l v (Stack st), Gas:=g\<rparr>"
    and "v' \<noteq> v"
  shows "accessStore l1 (Stack st') = Some v' \<Longrightarrow> accessStore l1 (Stack st) = Some v'" 
proof - 
  assume a1:"accessStore l1 (Stack st') = Some v'"
  then have "l1 \<noteq> l" using diffTypeDiffLoc[of st' g l v st v' l1] assms by simp
  then show "accessStore l1 (Stack st) = Some v'" using stackSingleUpdate[of st' g l v st] assms a1 by simp
qed


lemma typeSafeLocExists:
  assumes "TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "(t, l) |\<in>| fmran (Denvalue ev)"
    and "l = Stackloc loc"
    and "unique_locations (Denvalue ev)"
    and "balanceTypes (Accounts st)"
  shows "\<exists>val. accessStore loc (Stack st) = Some(val)"
proof -
  have a10:"TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd  = (unique_locations (Denvalue ev) \<and>
     balanceTypes (Accounts st) \<and>
     (\<forall>t l. (t, l) |\<in>| fmran (Denvalue ev) \<longrightarrow>
            (case l of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st) of None \<Rightarrow> False
               | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
               | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
               | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st) stloc | _ \<Rightarrow> False)
               | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st (Address ev)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st (Address ev)) | _ \<Rightarrow> False))))" 
    using assms TypeSafe_def typeCompat_def by simp
  then show ?thesis
  proof(cases "accessStore loc (Stack st)")
    case None
    then have "False" using a10 assms by force
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis using a10 assms by simp
  qed
qed

lemma typeConConvert:
  assumes "local.expr ex env cd (st) g' = Normal ((KValue v, Value t2), g)"
    and "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "convert t2 t' v = Some (v)"
    and "fullyInitialised env (Accounts st) (Stack st)"
  shows "typeCon t' v"
proof -
  have "Memory (st) = Memory st" by simp
  moreover have "Storage (st) = Storage st" by simp
  moreover have "Accounts (st) = Accounts st" by simp
  moreover have "Stack st = Stack (st)" by simp
  ultimately have "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"  using assms(2)  by metis
  then have a10:"typeCon t2 v" using exprTypeconInduct(3) assms(1,4) by force
  then show "typeCon t' v" using a10 assms(3) typeSafeConvert by simp
qed


text \<open>If you have an SCon memory and lexp returns something in that SCon memory the type must be the same\<close>

lemma lexpStorage:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "lexp lv env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage (STValue t')),g')"
    and "fullyInitialised env (Accounts st) (Stack st)"

obtains (1) 
  "((type.Storage (STValue t'), Storeloc locChanged) |\<in>| fmran (Denvalue env))"
| (2) l t
where "((type.Storage t, Storeloc l) |\<in>| fmran (Denvalue env))"
  and "(TypedStoSubpref locChanged l t \<and>  CompStoType t (STValue t') l locChanged)"

| (3) l' t l
where "((type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env))"
  and "accessStore l (Stack st) = Some (KStoptr l')"
  and "(TypedStoSubpref locChanged l' t \<and>  CompStoType t (STValue t') l' locChanged)"
proof (cases lv)
  case (Id x1)
  then have "lexp (Id x1) env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage (STValue t')), g')" using assms(2) by simp
  then have "Denvalue env $$ x1 = Some (type.Storage (STValue t'), Storeloc locChanged) " 
    using Id lexp.simps(1)[of x1 env cd "(st\<lparr>Gas := g\<rparr>)" g] by (auto split:option.splits denvalue.splits)
  then show ?thesis by (simp add: "1" fmranI)
next
  case (Ref x21 x22)
  then have *: "lexp (Ref x21 x22) env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage (STValue t')), g')" using assms(2) by simp
  then show ?thesis 
  proof(cases "Denvalue env $$ x21")
    case None
    then show ?thesis using * lexp.simps(2) Ref by simp
  next
    case (Some a)
    then obtain tp loc where adef:"a = (type.Storage tp, loc)" using * lexp.simps(2) Ref by (cases a; (auto split: result.splits type.splits denvalue.splits option.splits stackvalue.splits))
    then have b6:"(type.Storage tp, loc) |\<in>| fmran (Denvalue env)" using Some by (simp add: fmranI)

    then show ?thesis
    proof(cases loc)
      case (Stackloc x1)
      then show ?thesis 
      proof(cases "accessStore x1 (Stack st)")
        case None
        then show ?thesis using * Ref Stackloc lexp.simps(2)[of x21 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g] Some adef by simp
      next
        case some2:(Some a)
        then obtain x4 where x4def:"a = KStoptr x4" using * Ref Stackloc lexp.simps(2)[of x21 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g] Some adef some2 by (cases a; auto)
        then obtain l'' t'' where  b20:"ssel tp x4 x22 env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((l'', t''), g')" 
          using Stackloc Some Ref * lexp.simps(2) adef some2 by (auto split: result.splits type.splits)
        have b10:"SCon tp x4 (Storage st (Address env))" using assms b6 some2 Stackloc x4def unfolding TypeSafe_def typeCompat_def by fastforce
        then have b30:"locChanged = l'' \<and> (STValue t') =  t''" using * lexp.simps(2) Ref adef Stackloc b20 some2 x4def Some Ref b6 by simp

        then show ?thesis 
        proof(cases x22)
          case Nil
          then have b25:"tp = t'' \<and> x4 = l''" using b20 ssel.simps(1) by simp
          then have b30:"locChanged = l'' \<and> (STValue t') =  t''" using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 by simp
          then show ?thesis using b6 3 b25  Stackloc some2 x4def by auto
        next
          case (Cons a list)
          then have b10:"(CompStoType tp t'' x4 l'')" 
            using exprTypeconInduct(2)[of tp x4 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g l'' t'' g'] assms 
            using b10 b20 some2 x4def unfolding fullyInitialised_def by simp
          have b30:"l'' = locChanged  \<and> (STValue t') =  t''" using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 by simp
          then have "CompStoType tp (STValue t') x4 l''" using b10 by simp
          then show ?thesis using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 b10 b30 3
            using CompStoType_imps_TypedStoSubpref by blast
        qed
      qed
    next
      case (Storeloc x2)
      then have b10:"SCon tp x2 (Storage st (Address env))" using assms b6 unfolding TypeSafe_def typeCompat_def by force
      then obtain l'' t'' where  b20:"ssel tp x2 x22 env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((l'', t''), g')" 
        using Storeloc Some Ref * lexp.simps(2) adef by (auto split: result.splits type.splits)
      then show ?thesis 
      proof(cases x22)
        case Nil
        then have b25:"tp = t'' \<and> x2 = l''" using b20 ssel.simps(1) by simp
        then have b30:"locChanged = l'' \<and> (STValue t') =  t''" using * lexp.simps(2) Ref adef Storeloc b20  Some Ref b6 by simp
        then show ?thesis using b6 1 adef Some Ref * b25 b20 by (simp add: Storeloc)
      next
        case (Cons a list)
        then have b10:"CompStoType tp t'' x2 l''" 
          using exprTypeconInduct(2)[of tp x2 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g l'' t'' g'] assms 
          using b10 b20 Storeloc unfolding fullyInitialised_def by simp
        have b30:"l'' = locChanged  \<and> (STValue t') =  t''" using * lexp.simps(2) Ref adef Storeloc b20  Some Ref b6 by simp
        then have "CompStoType tp (STValue t') x2 l''" using b10 by simp
        then show ?thesis using b30 b6 2 adef Some Ref * b10 b20 Storeloc 
          using CompStoType_imps_TypedStoSubpref by blast
      qed
    qed
  qed
qed

lemma typeSafe_storeloc_scon_from_denvalue:
  assumes ts: "TypeSafe env acc sk mem sto cd"
    and inDen: "(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
  shows "SCon tp i (sto (Address env))"
  using sameStoLocTSafe[OF ts] inDen by blast

lemma fi_contract_var_to_denvalue_storeloc:
  assumes fi: "fullyInitialised env acc sk"
    and addrEq: "Address e = Address env"
    and typedE: "Type (acc (Address e)) = Some (atype.Contract (Contract e))"
    and epLookup: "ep $$ Contract e = Some (ct, dud)"
    and ctVar: "ct $$ i = Some (Var tp)"
  shows "Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
proof -
  obtain c ct_fi dud_fi where
      fiType: "Type (acc (Address env)) = Some (atype.Contract c)"
    and fiCon: "Contract env = c"
    and fiEp: "ep $$ c = Some (ct_fi, dud_fi)"
    and fiMap: "(\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id)))"
    and fiLoc: "(\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
    and fiPtr: "(\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env) \<and> accessStore l sk = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t l' p))"
    using fi unfolding fullyInitialised_def by blast
  have cEq: "Contract e = Contract env"
  proof -
    have "Type (acc (Address env)) = Some (atype.Contract (Contract e))"
      using typedE addrEq by simp
    moreover have "Type (acc (Address env)) = Some (atype.Contract (Contract env))"
      using fiType fiCon by simp
    ultimately show ?thesis by simp
  qed
  have epEnv: "ep $$ Contract env = Some (ct, dud)"
    using epLookup cEq by simp
  have epEnvFi: "ep $$ Contract env = Some (ct_fi, dud_fi)"
    using fiEp fiCon by simp
  have ctEq: "ct = ct_fi"
    using epEnv epEnvFi by auto
  have "ct_fi $$ i = Some (Var tp)"
    using ctVar ctEq by simp
  then show ?thesis
    using fiMap by blast
qed

lemma fiPtr_parent_from_fullyInitialised:
  assumes fi: "fullyInitialised env acc sk"
    and inDen: "(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env)"
    and ptr: "accessStore l sk = Some (KStoptr p)"
  shows "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t l' p"
  using fi inDen ptr unfolding fullyInitialised_def by blast

lemma fi_denvalue_storeloc_to_contract_var:
  assumes fi: "fullyInitialised env acc sk"
    and epLookup: "ep $$ Contract env = Some (ct, dud)"
    and inDen: "(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
  shows "ct $$ i = Some (Var tp)"
proof -
  obtain c ct_fi dud_fi where
      fiType: "Type (acc (Address env)) = Some (atype.Contract c)"
    and fiCon: "Contract env = c"
    and fiEp: "ep $$ c = Some (ct_fi, dud_fi)"
    and fiMap: "(\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id)))"
    and fiLoc: "(\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
    and fiPtr: "(\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env) \<and> accessStore l sk = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t l' p))"
    using fi unfolding fullyInitialised_def by blast
  have epEnvFi: "ep $$ Contract env = Some (ct_fi, dud_fi)"
    using fiEp fiCon by simp
  have ctEq: "ct = ct_fi"
    using epLookup epEnvFi by auto
  obtain id where idDef: "Denvalue env $$ id = Some (type.Storage tp, Storeloc i)"
    using inDen by blast
  then have "id = i" using fiLoc by blast
  then have denI: "Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
    using idDef by simp
  then have "ct_fi $$ i = Some (Var tp)"
    using fiMap by blast
  then show ?thesis using ctEq by simp
qed

lemma safeContract_field_scon_from_typeCompat:
  assumes ts: "TypeSafe env acc sk mem sto cd"
    and fi: "fullyInitialised env acc sk"
    and addrEq: "Address e = Address env"
    and typedE: "Type (acc (Address e)) = Some (atype.Contract (Contract e))"
    and epLookup: "ep $$ Contract e = Some (ct, dud)"
    and ctVar: "ct $$ i = Some (Var tp)"
  shows "SCon tp i (sto (Address env))"
proof -
  have denLookup: "Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
    using fi_contract_var_to_denvalue_storeloc[OF fi addrEq typedE epLookup ctVar] .
  have inDen: "(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
    using denLookup by (simp add: fmranI)
  show ?thesis
    using typeSafe_storeloc_scon_from_denvalue[OF ts inDen] .
qed

lemma safeContract_other_address_preserved:
  assumes sc: "safeContract acc sto"
    and stoEq: "\<forall>a. a \<noteq> a0 \<longrightarrow> sto' a = sto a"
    and addNe: "Address e \<noteq> a0"
    and typedE: "Type (acc (Address (e::environment))) = Some (atype.Contract (Contract e))"
    and epLookup: "ep $$ Contract e = Some (ct, dud)"
    and ctVar: "ct $$ i = Some (Var tp)"
  shows "SCon tp i (sto' (Address e))"
proof -
  have "SCon tp i (sto (Address e))"
    using sc typedE epLookup ctVar unfolding safeContract_def by blast
  moreover have "sto' (Address e) = sto (Address e)"
    using stoEq addNe by blast
  ultimately show ?thesis by simp
qed

lemma copy_dest_scon_from_rel:
  assumes copyStep: "copy p l x t (Storage st (Address env)) = Some s"
    and tEq: "t' = STArray x t"
    and rootSCon: "SCon (STArray x t) l (Storage st (Address env))"
    and srcSCon: "SCon (STArray x t) p (Storage st (Address env))"
    and denSub: "(if TypedStoSubpref stloc lsrc tsrc then CompStoType tsrc tp'' lsrc stloc
                 else if TypedStoSubpref lsrc stloc tp'' then CompStoType tp'' tsrc stloc lsrc else True)"
    and paInf: "(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
    and rel: "CompStoType tsrc (STArray x t) lsrc l"
  shows "SCon (STArray x t) l s"
proof (cases "p = l")
  case pIsL: True
  then show ?thesis
    using copy_same_Scon copyStep tEq rootSCon by (metis copy_def)
next
  case pNotl: False
  then show ?thesis
  proof (cases "p = stloc")
    case True
    then have j1:"(if TypedStoSubpref p lsrc tsrc then CompStoType tsrc (STArray x t) lsrc p
                   else if TypedStoSubpref lsrc p (STArray x t) then CompStoType (STArray x t) tsrc p lsrc else True)"
      using denSub paInf by fastforce
    then have j2:"\<not>TypedStoSubpref p l (STArray x t) \<and> \<not>TypedStoSubpref l p (STArray x t)"
      using comp_stotype_same_type_same_loc j1 pNotl rel 
      by (metis CompStoType_imps_TypedStoSubpref CompStoType_same_type_same_depth CompStoType_trns NotReachablePrnt_imps_notReachableChild NotRelatedPrnt_imps_notRelatedChild
          same_depth_imp_neg_TypedStoSubpref)
    moreover have "\<forall>subL. TypedStoSubpref subL l (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL p (STArray x t)"
      using NotRelatedPrnt_imps_notRelatedChild[of p l "(STArray x t)" "(STArray x t)"] j2 by blast
    moreover have "\<forall>subL. TypedStoSubpref subL p (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL l (STArray x t)"
      using j2 NotRelatedPrnt_imps_notRelatedChild by blast
    ultimately show ?thesis
      using copy_notSub_Scon copyStep tEq rootSCon srcSCon by (metis  (lifting) copy_def)
  next
    case False
    then have j1:"CompStoType tp'' (STArray x t) stloc p" using paInf by simp
    show ?thesis
    proof (cases "TypedStoSubpref stloc lsrc tsrc")
      case True
      then have "CompStoType tsrc tp'' lsrc stloc" using denSub by simp
      then have j5:"CompStoType tsrc (STArray x t) lsrc p"
        using CompStoType_trns j1 False by blast
      have j10:"CompStoType tsrc (STArray x t) lsrc l" using rel .
      then have j20:"lsrc \<noteq> l \<and> lsrc \<noteq> p" using pNotl j5 False
        using CompStoType_sameLoc_sameType comp_stotype_same_type_same_loc by blast
      then have j2:"\<not>TypedStoSubpref p l (STArray x t) \<and> \<not>TypedStoSubpref l p (STArray x t)"
        using CompStoType_same_type_same_depth j5 j10 pNotl same_depth_imp_neg_TypedStoSubpref by blast
      moreover have "\<forall>subL. TypedStoSubpref subL l (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL p (STArray x t)"
        using NotRelatedPrnt_imps_notRelatedChild[of p l "(STArray x t)" "(STArray x t)"] j2 by blast
      moreover have "\<forall>subL. TypedStoSubpref subL p (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL l (STArray x t)"
        using j2 NotRelatedPrnt_imps_notRelatedChild by blast
      ultimately show ?thesis
        using copy_notSub_Scon copyStep tEq rootSCon srcSCon by (metis (lifting) copy_def)
    next
      case f2: False
      then show ?thesis
      proof (cases "TypedStoSubpref lsrc stloc tp''")
        case True
        then have j5:"CompStoType tp'' tsrc stloc lsrc" using denSub f2 by auto
        have j10:"CompStoType tp'' (STArray x t) stloc p" using j1 by simp
        have j11:"CompStoType tp'' (STArray x t) stloc l" using CompStoType_trns j5 rel by blast
        then have j2:"\<not>TypedStoSubpref p l (STArray x t) \<and> \<not>TypedStoSubpref l p (STArray x t)"
          using CompStoType_same_type_same_depth j10 pNotl same_depth_imp_neg_TypedStoSubpref by blast
        moreover have "\<forall>subL. TypedStoSubpref subL l (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL p (STArray x t)"
          using NotRelatedPrnt_imps_notRelatedChild[of p l "(STArray x t)" "(STArray x t)"] j2 by blast
        moreover have "\<forall>subL. TypedStoSubpref subL p (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL l (STArray x t)"
          using j2 NotRelatedPrnt_imps_notRelatedChild by blast
        ultimately show ?thesis
          using copy_notSub_Scon copyStep tEq rootSCon srcSCon by (metis  (lifting) copy_def)
      next
        case False
        then have j2:"\<not>TypedStoSubpref p l (STArray x t) \<and> \<not>TypedStoSubpref l p (STArray x t)"
          using CompStoType_imps_TypedStoSubpref NotRelatedPrnt_imps_notRelatedChild f2 j1 rel
          by (meson NotReachablePrnt_imps_notReachableChild)
        moreover have "\<forall>subL. TypedStoSubpref subL l (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL p (STArray x t)"
          using NotRelatedPrnt_imps_notRelatedChild[of p l "(STArray x t)" "(STArray x t)"] j2 by blast
        moreover have "\<forall>subL. TypedStoSubpref subL p (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL l (STArray x t)"
          using j2 NotRelatedPrnt_imps_notRelatedChild by blast
        ultimately show ?thesis
          using copy_notSub_Scon copyStep tEq rootSCon srcSCon by (metis  (lifting) copy_def)
      qed
    qed
  qed
qed



lemma originalMConStillMCon:
  assumes "MCon struct (Memory st) x3"
    and "(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
    and "\<forall>locs.  \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) t' \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs (Memory st')" 
  shows " MCon struct (Memory st') x3" using assms(1)
proof(induction struct arbitrary: x3)
  case (MTArray x1 struct)
  have mcexp:"\<forall>i<x1.
(case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) of None \<Rightarrow> False 
| Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct (Memory st) loc2 | MTValue Types \<Rightarrow> False))" 
    using MTArray(2) unfolding MCon.simps by simp

  have "\<forall>i<x1.
(case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False 
| Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct (Memory st') loc2 | MTValue Types \<Rightarrow> False))" 
  proof(intros)
    fix i assume h1:"i<x1"
    show "case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False 
| Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases "struct")
      case mta1:(MTArray x11 x12)
      then obtain v where vdef: "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer v)" using h1 mcexp 
        using MTArray.prems(1) MConArrayPointers by blast
      then have vdef2:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer v)" using   assms(2) assms(3,4) 
        by (metis  nat_le_linear option.distinct(1))
      have "MCon struct (Memory st) v" using vdef mcexp h1 mta1 by fastforce                     
      then have "MCon struct (Memory st') v" using MTArray.IH[of v]  
        by simp
      then show ?thesis using mta1 h1 vdef vdef2 by simp
    next
      case (MTValue x2)
      then obtain v where vdef: "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue v)" using h1 mcexp 
        using MCon_sub_MTVal_imps_val MTArray.prems(1) by presburger
      then have vdef2:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st')  = Some (MValue v)" using assms 
        by (metis  nat_le_linear  option.distinct(1))
      have "MCon struct (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using vdef mcexp h1 MTValue by auto
      then show ?thesis using MTValue vdef vdef2 h1 by auto 
    qed
  qed

  moreover have "x3 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
    using MCon_imps_Some MTArray.prems LSubPrefL2_def assms(2) not_None_eq by blast
  moreover have " \<not> TypedMemSubPref x3 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) t'" using assms 
    by (metis (no_types, opaque_lifting) MCon_imps_Some MTArray.prems LSubPrefL2_def Not_Sub_More_Specific le_refl neg_MemLSubPrefL2_imps_TypedMemSubPref not_Some_eq)
  moreover have "((\<exists>p. accessStore x3 (Memory st') = Some (MPointer p)) \<or> accessStore x3 (Memory st') = None)" 
    using  allocateSameAccess MTArray.prems    calculation assms
    by (metis  MCon.simps(2)) 

  ultimately show ?case unfolding MCon.simps 
    by (metis MTArray.prems(1) MCon.simps(2))
next
  case (MTValue x')
  then show ?case using   assms 
    by (metis Option.option.simps(4) le_eq_less_or_eq   MCon.simps(1))
qed


lemma mselReturnAlwaysHash:
  assumes"msel True t l'' x22 env cd st g = Normal ((l, t'), g')" 
    and "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "MCon t (Memory st) l''"
    and "fullyInitialised env (Accounts st) (Stack st)"
  shows "\<exists>prnt i len arr len' arr'. t= MTArray len arr \<and>  l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)  \<and> arr' = t' \<and> i < len' \<and> MCon (MTArray len' arr') (Memory st) prnt
                        \<and> (prnt = l'' \<and> len = len' \<and> arr' = arr  \<or> CompMemType (Memory st) len arr  (MTArray len' arr') l'' prnt) " using assms(1,3)
proof(induction "x22" arbitrary: t l'' g)
  case Nil
  then show ?case using msel.simps by simp
next
  case (Cons a x22)
  show ?case  using Cons(2)
  proof(cases rule: msel.elims )
    case (1 uv uw ux uy uz g)
    then show ?thesis by blast
  next
    case (2 vb vc vd ve vf vg g)
    then show ?thesis by auto
  next
    case (3 al t loc x env cd st g)
    then obtain kv b g4'  where a20: "local.expr x env cd st g = Normal ((KValue kv, Value (TUInt b)), g4')"
      and a30: "less (TUInt b) (TUInt b256) kv (ShowL\<^sub>i\<^sub>n\<^sub>t (int al)) = Some ((ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), TBool)"
      using  msel.simps(3) by (simp split: result.split_asm prod.split_asm types.split_asm type.split_asm if_split_asm stackvalue.split_asm option.split_asm memoryvalue.split_asm)
    then have b2:"(hash loc kv, t) = (l, t')" using 3 by simp
    have a50: "checkUInt b kv" using exprTypeconInduct(3) 3(1) assms(2) a20 typeCon.simps(2)[of b "extractValueType (KValue kv)"] extractValueType.simps(1)[of kv] 
      using "3"(4,5,6) using assms(4)  by force
    then have a60:"ReadL\<^sub>i\<^sub>n\<^sub>t(kv) < int al " using a20 a30 less_def plift.simps(2)[of "(<)" b b256 kv "(ShowL\<^sub>i\<^sub>n\<^sub>t (int al))"] Read_ShowL_id[of "(int al)"] unfolding createBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    then have a62:"0\<le>ReadL\<^sub>i\<^sub>n\<^sub>t(kv)" and a65:"(ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) = kv" using a50 checkUInt_def[of b kv] by simp+
    have a64:"(ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))) = kv" using ShowLnat_ReadLint_inverse a62 a50 unfolding checkUInt_def by simp
    then have a70:"(nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) \<in> {0..al-1}" using a60 a62 by simp
    have "loc = l''" using 3 by simp
    moreover have "(nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) < al" using a70 
      by (simp add: a60 a62 nat_less_iff)
    ultimately show ?thesis using b2 a64 a70 "3"(1) prod.inject 
      by (metis Cons.prems(2))

  next
    case (4 al t'' loc x y ys env cd st g'')
    then obtain kv b g4' ptr where a20: "local.expr x env cd st g'' = Normal ((KValue kv, Value (TUInt b)), g4')"
      and a30: "less (TUInt b) (TUInt b256) kv (ShowL\<^sub>i\<^sub>n\<^sub>t (int al)) = Some ((ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), TBool)"
      and a40:"accessStore (hash loc kv) (if True then Memory st else cd) = Some (MPointer ptr)"
      using  msel.simps(3) by (simp split: result.split_asm prod.split_asm types.split_asm type.split_asm if_split_asm stackvalue.split_asm option.split_asm memoryvalue.split_asm)
    have a50: "checkUInt b kv" using exprTypeconInduct(3) 4(1) assms(2) a20 typeCon.simps(2)[of b "extractValueType (KValue kv)"] extractValueType.simps(1)[of kv] 
      using "4"(4,5,6) using assms(4) by force
    then have a60:"ReadL\<^sub>i\<^sub>n\<^sub>t(kv) < int al " using a20 a30 less_def plift.simps(2)[of "(<)" b b256 kv "(ShowL\<^sub>i\<^sub>n\<^sub>t (int al))"] Read_ShowL_id[of "(int al)"] unfolding createBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    then have a62:"0\<le>ReadL\<^sub>i\<^sub>n\<^sub>t(kv)" and a65:"(ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) = kv" using a50 checkUInt_def[of b kv] by simp+
    have a64:"(ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))) = kv" using ShowLnat_ReadLint_inverse a62 a50 unfolding checkUInt_def by simp
    then have a70:"(nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) \<in> {0..al-1}" using a60 a62 by simp
    have tdef:"t = MTArray al t''" using 4 by simp
    then have mc:" MCon t'' (Memory st) ptr" using Cons.prems a40 
      by (metis "4"(2,6) MCon_imps_sub_Mcon a60 a62 a64 nat_less_iff)

    then have mse:"msel True t'' ptr (y # ys) env cd st g4' = Normal ((l, t'), g')" using 4 a20 a30 a40  by simp
    then have "\<exists>prnt i len arr len' arr'.
       t'' = MTArray len arr \<and>
       l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = t' \<and> MCon (MTArray len' arr') (Memory st) prnt \<and> (prnt = ptr \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt )" using Cons.IH[of t'' ptr g4'] 4(4,5,6,7,3) a64  mc by blast
    then obtain prnt i len arr len' arr' where defs:"t'' = MTArray len arr \<and>
       l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = t' \<and> MCon (MTArray len' arr') (Memory st) prnt \<and> (prnt = ptr \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt )" by blast

    have a6:"(case t' of MTArray l' ar' \<Rightarrow> \<exists>p. accessStore l (if True then Memory st else cd) = Some (MPointer p) 
                            \<and> CompMemType (if True then Memory st else cd) len arr t' ptr p 
          | MTValue val \<Rightarrow> CompMemType (if True then Memory st else cd) len arr t' ptr l )" 
      using exprTypeconInduct(1)[of True t'' ptr "(y # ys)" env cd st g4' l t' g'] mse mc assms(2) 4 defs 
      using assms(4) unfolding fullyInitialised_def by simp

    then show ?thesis 
    proof(cases "prnt = ptr")
      case True
      have notComp:"\<not>CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt" 
      proof
        assume in1:"CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt"
        show False
        proof(cases "arr")
          case (MTArray x11 x12)
          then have "(\<exists>i<len. \<exists>l. accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer l) \<and> 
                    (l = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType (Memory st) x11 x12 (MTArray len' arr') l prnt))" 
            using in1 CompMemType.simps(2)[of "Memory st" len x11 x12 "(MTArray len' arr')" ptr prnt] by auto
          moreover have " MCon (MTArray len (MTArray x11 x12)) (Memory st) ptr" using mc defs MTArray by simp
          ultimately show ?thesis using True in1 mc defs 
            by (metis BothMConImpsNotCompMemType)
        next
          case (MTValue x2)
          then show ?thesis using in1 True by simp
        qed
      qed

      then have lenIslen':"len = len'" using defs mc a6 notComp by simp
      then have arrIsarr':"arr' = arr" using defs mc a6 notComp by blast

      then have notSame:"ptr \<noteq> l''" using defs mc 4 
        using Cons.prems(2) MConSubTypes CompMemJustType.simps(2) by blast
      have "CompMemType (Memory st) al (MTArray len arr) (MTArray len' arr') loc prnt " 
        using CompMemType.simps(2)[of "Memory st" al len arr "(MTArray len' arr')"  loc prnt] a40  True defs lenIslen' arrIsarr' 
        by (metis a60 a62 a64 nat_less_iff)
      moreover have "arr' = t'" using defs by simp
      ultimately show ?thesis using tdef True defs notSame 
        using "4"(6,2) by blast
    next
      case False
      then have "CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt" using defs by auto
      then show ?thesis 
        by (smt (verit, ccfv_SIG) "4"(2,6)
            \<open>\<exists>prnt i len arr len' arr'. t'' = MTArray len arr \<and> l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = t' \<and> MCon (MTArray len' arr') (Memory st) prnt \<and> (prnt = ptr \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt)\<close>
            a40 a60 a62 a64 nat_less_iff CompMemType.simps(2) tdef)
    qed
  qed
qed

lemma lexpIndexMem:
  assumes "lexp lv env cd st g = Normal ((LMemloc l, type.Memory t'), g')"
    and "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "fullyInitialised env (Accounts st) (Stack st)"

obtains (1) x21 x22 tp tParent l' l'' prnt  len' arr' i
where  "lv = Ref x21 x22"
  and "(tp, Stackloc l') |\<in>| fmran (Denvalue env)"
  and "accessStore l' (Stack st) = Some (KMemptr l'')"
  and "tp = type.Memory tParent"
  and "MCon tParent (Memory st) l''"
  and "accessTypeStore l (Memory st) = Some (t')"
  and "(\<exists>len arr. tParent = MTArray len arr \<and> 
      (case t' of MTArray l' ar' \<Rightarrow>
          \<exists>p. accessStore l (Memory st)  = Some (MPointer p) \<and> CompMemType (Memory st) len arr t' l'' p 
      | MTValue val \<Rightarrow> CompMemType (Memory st) len arr t' l'' l )
\<and>     l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = t' \<and> MCon (MTArray len' arr') (Memory st) prnt \<and> (prnt = l'' \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') l'' prnt))"
proof(cases lv)
  case (Id x1)
  then show ?thesis using assms(1) lexp.simps(1)[of x1] by (auto split:option.splits denvalue.splits)
next
  case (Ref x21 x22)
  then obtain tp l' where tpdef:"Denvalue env $$ x21 = Some (tp, Stackloc l')" 
    using assms(1) lexp.simps(2)[of x21 x22 env cd "st"]  
    by (auto split:option.splits denvalue.splits type.splits result.splits)
  then have parentIn:"( tp, Stackloc l') |\<in>| fmran (Denvalue env)" using fmranI by metis
  then obtain l'' where access:"accessStore l' (Stack st) = Some (KMemptr l'')" 
    using Ref assms(1) lexp.simps(2)[of x21 x22 env cd "st"]  tpdef
    by (auto split:option.splits denvalue.splits type.splits result.splits stackvalue.splits)
  then obtain t where tdef:"tp = type.Memory t" using access tpdef Ref assms(1) lexp.simps(2)[of x21 x22 env cd "st"]  
    by (auto split:option.splits denvalue.splits type.splits result.splits stackvalue.splits)
  then have msel12:"msel True t l'' x22 env cd st g = Normal ((l, t'), g')" using access tpdef Ref assms(1) lexp.simps(2)[of x21 x22 env cd "st"]  
    by (auto split:option.splits denvalue.splits type.splits result.splits stackvalue.splits prod.splits)
  have " MCon t (Memory st) l''" 
    using access assms(2) parentIn sameMemTSafe tdef by blast
  then obtain prnt i len arr len' arr' where a1:"
     t = MTArray len arr \<and> l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> arr' = t' \<and> i < len' \<and> MCon (MTArray len' arr') (Memory st) prnt 
    \<and> (prnt = l'' \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') l'' prnt)" 
    using mselReturnAlwaysHash[OF msel12  assms(2)] assms(3)  unfolding fullyInitialised_def by blast

  have mconP:"MCon t (Memory st) l''" using tpdef access tdef assms(2)
    by (meson assms(2) fmranI sameMemTSafe)
  have "x22 \<noteq> []" using msel12 msel.simps by auto
  then have a6:"(\<exists>len arr.
       t = MTArray len arr \<and>
       (case t' of
        MTArray l' ar' \<Rightarrow>
          \<exists>p. accessStore l (Memory st) = Some (MPointer p) \<and>
              CompMemType (Memory st) len arr t' l'' p 
        | MTValue val \<Rightarrow> CompMemType (Memory st) len arr t' l'' l ))" 
    using exprTypeconInduct(1)[of True t l'' x22 env cd "st" g l t' g'] assms(2) mconP msel12 assms(3)  unfolding fullyInitialised_def 
    by presburger

  have "((case t of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr
       | MTValue val \<Rightarrow> accessTypeStore l'' (Memory st) = Some (MTValue val)))" 
    using assms(2) unfolding TypeSafe_def denvalueTypeCorrectness_def 
    using parentIn tdef access 
    using a6 by fastforce
  then have a10:"(\<forall>i<len. accessTypeStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)" using a1 by simp

  have co:" (\<forall>locs tp.
      accessTypeStore locs (Memory st) = Some tp \<longrightarrow>
      (case accessStore locs (Memory st) of None \<Rightarrow> False
       | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st) p \<and> tp = MTArray len arr 
                            \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
                           ))" 
    using assms(2) unfolding TypeSafe_def subPrefixStructuralConsistency_def by blast

  have "accessTypeStore l (Memory st) = Some t'" 
  proof(cases "prnt = l'' \<and> len = len' \<and> arr' = arr ")
    case True
    then show ?thesis using a1 a10 by blast
  next
    case False
    then have cmp:"CompMemType (Memory st) len arr (MTArray len' arr') l'' prnt" using a1 by blast
    have accTT:"\<forall>i<len'. accessTypeStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr'" 
      using CompMemTypeSubIndexes[OF cmp ] a1 assms(2) unfolding TypeSafe_def 
      using a10 mconP by argo
    then show ?thesis using a1 by simp
  qed

  then show ?thesis using msel12 1[OF Ref parentIn access tdef mconP, of prnt i len' arr' ] a1 a6 by blast
qed

lemma lexpStorageG:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"

and "lexp lv env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage t'),g')"
and "fullyInitialised env (Accounts st) (Stack st)"

obtains (1) 
  "((type.Storage t', Storeloc locChanged) |\<in>| fmran (Denvalue env))"
| (2) l t
where "((type.Storage t, Storeloc l) |\<in>| fmran (Denvalue env))"
  and "(TypedStoSubpref locChanged l t \<and>  CompStoType t t' l locChanged)"

| (3) l' t l
where "((type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env))"
  and "accessStore l (Stack st) = Some (KStoptr l')"
  and "(TypedStoSubpref locChanged l' t \<and>  CompStoType t t' l' locChanged)"
proof (cases lv)
  case (Id x1)
  then have "lexp (Id x1) env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage ( t')), g')" using assms(2) by simp
  then have "Denvalue env $$ x1 = Some (type.Storage ( t'), Storeloc locChanged) " 
    using Id lexp.simps(1)[of x1 env cd "(st\<lparr>Gas := g\<rparr>)" g] by (auto split:option.splits denvalue.splits)
  then show ?thesis by (simp add: "1" fmranI)
next
  case (Ref x21 x22)
  then have *: "lexp (Ref x21 x22) env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage ( t')), g')" using assms(2) by simp
  then show ?thesis 
  proof(cases "Denvalue env $$ x21")
    case None
    then show ?thesis using * lexp.simps(2) Ref by simp
  next
    case (Some a)
    then obtain tp loc where adef:"a = (type.Storage tp, loc)" using * lexp.simps(2) Ref by (cases a; (auto split: result.splits type.splits denvalue.splits option.splits stackvalue.splits))
    then have b6:"(type.Storage tp, loc) |\<in>| fmran (Denvalue env)" using Some by (simp add: fmranI)

    then show ?thesis
    proof(cases loc)
      case (Stackloc x1)
      then show ?thesis 
      proof(cases "accessStore x1 (Stack st)")
        case None
        then show ?thesis using * Ref Stackloc lexp.simps(2)[of x21 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g] Some adef by simp
      next
        case some2:(Some a)
        then obtain x4 where x4def:"a = KStoptr x4" using * Ref Stackloc lexp.simps(2)[of x21 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g] Some adef some2 by (cases a; auto)
        then obtain l'' t'' where  b20:"ssel tp x4 x22 env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((l'', t''), g')" 
          using Stackloc Some Ref * lexp.simps(2) adef some2 by (auto split: result.splits type.splits)
        have b10:"SCon tp x4 (Storage st (Address env))" using assms b6 some2 Stackloc x4def unfolding TypeSafe_def typeCompat_def by fastforce
        then have b30:"locChanged = l'' \<and> ( t') =  t''" using * lexp.simps(2) Ref adef Stackloc b20 some2 x4def Some Ref b6 by simp

        then show ?thesis
        proof(cases x22)
          case Nil
          then have b25:"tp = t'' \<and> x4 = l''" using b20 ssel.simps(1) by simp
          then have b30:"locChanged = l'' \<and> ( t') =  t''" using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 by simp
          then show ?thesis using b6 3 b25  Stackloc some2 x4def 
            using CompStoType_sameLocNdTyp TypedStoSubpref_sameLoc by auto
        next
          case (Cons a list)
          then have b10:"CompStoType tp t'' x4 l''" 
            using exprTypeconInduct(2)[of tp x4 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g l'' t'' g'] assms 
            unfolding fullyInitialised_def using b10 b20 some2 x4def by simp
          have b30:"l'' = locChanged  \<and> (t') =  t''" using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 by simp
          then have "CompStoType tp (t') x4 l''" using b10 by simp
          then show ?thesis using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 b10 b30 3 
            using CompStoType_imps_TypedStoSubpref by blast
        qed
      qed
    next
      case (Storeloc x2)
      then have b10:"SCon tp x2 (Storage st (Address env))" using assms b6 unfolding TypeSafe_def typeCompat_def by force
      then obtain l'' t'' where  b20:"ssel tp x2 x22 env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((l'', t''), g')" 
        using Storeloc Some Ref * lexp.simps(2) adef by (auto split: result.splits type.splits)
      then show ?thesis 
      proof(cases x22)
        case Nil
        then have b25:"tp = t'' \<and> x2 = l''" using b20 ssel.simps(1) by simp
        then have b30:"locChanged = l'' \<and> (t') =  t''" using * lexp.simps(2) Ref adef Storeloc b20  Some Ref b6 by simp
        then show ?thesis using b6 1 adef Some Ref * b25 b20 by (simp add: Storeloc)
      next
        case (Cons a list)
        then have b10:"CompStoType tp t'' x2 l''" 
          using exprTypeconInduct(2)[of tp x2 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g l'' t'' g'] b20 assms 
          unfolding fullyInitialised_def using b10 b20 Storeloc by simp
        have b30:"l'' = locChanged  \<and> (t') =  t''" using * lexp.simps(2) Ref adef Storeloc b20  Some Ref b6 by simp
        then have "CompStoType tp (t') x2 l''" using b10 by simp
        then show ?thesis using b30 b6 2 adef Some Ref * b10 b20 Storeloc 
          using CompStoType_imps_TypedStoSubpref by blast
      qed
    qed
  qed
qed


definition allStoresSCon::"(address \<Rightarrow> storageT) \<Rightarrow> bool"
  where "allStoresSCon stoN =  (\<forall>e ct t' l'. ep $$ Contract e = Some ct 
\<and> (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue (e::environment))  \<longrightarrow> (SCon t' l' (stoN (Address (e::environment)))))"


definition StateInvariant :: "environment \<Rightarrow> state \<Rightarrow> state \<Rightarrow> calldataT \<Rightarrow> bool" where
  "StateInvariant ev st_orig st_curr cd \<equiv>
     TypeSafe ev (Accounts st_curr) (Stack st_curr) (Memory st_curr) (Storage st_curr) cd \<and>
     fullyInitialised ev (Accounts st_curr) (Stack st_curr) \<and>
     (\<forall>locs t. accessTypeStore locs (Memory st_orig) = Some t \<longrightarrow> accessTypeStore locs (Memory st_curr) = Some t) \<and>
(\<forall>locs v. accessStore locs (Memory st_orig) = Some (MPointer v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st_curr) = Some (MPointer v'))) \<and>
(\<forall>locs v. accessStore locs (Memory st_orig) = Some (MValue v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st_curr) = Some (MValue v'))) \<and>
(\<forall>i loc. i < Toploc (Memory st_orig) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> 
                      accessStore loc (Memory st_orig) = None \<longrightarrow> accessStore loc (Memory st_curr) = None) \<and>
  Toploc (Memory st_orig) \<le> Toploc (Memory st_curr)
    "


lemma cpm2m_sublocations_toploc:
  assumes ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'"
    and accessLGen:"\<exists>ptr. accessStore l mem' = Some (MPointer ptr) \<and> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<and> MCon (MTArray x t) mem' ptr"
    and nonLocChanged2:"\<forall>locs. locs \<noteq> l \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<longrightarrow> accessStore locs mem = accessStore locs mem'"
    and selfPoint2:"\<forall>l1 l2. LSubPrefL2 l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))
                        \<and> accessStore l1 mem' = Some (MPointer l2) \<longrightarrow> l2 = l1 \<and> l1 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
  shows "\<forall>len' arr' locs stl1.
                \<not> LSubPrefL2 stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<longrightarrow>
                TypedMemSubPrefPtrs mem' len' arr' locs stl1
              \<longrightarrow> TypedMemSubPrefPtrs mem len' arr' locs stl1"
proof intros
  fix len' arr' locs stl1
  have BT3:"\<forall>locs tp x t. \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<longrightarrow> \<not>CompMemType mem' x t tp (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs
                                                                    \<and> \<not>TypedMemSubPrefPtrs mem' x t (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs"
    using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def SubPtrs_top selfPoint2
    by blast

  assume asm3:"TypedMemSubPrefPtrs mem' len' arr' locs stl1"
    and "\<not> LSubPrefL2 stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
  then show "TypedMemSubPrefPtrs mem len' arr' locs stl1"
  proof(induction arr' arbitrary: len' locs)
    case (MTArray x1 arr')
    obtain i'' ptr where ptrDef:"i''<len' \<and> accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) mem' = Some (MPointer ptr)
            \<and> (ptr = stl1 \<or> TypedMemSubPrefPtrs mem' x1 arr' ptr stl1)"
      using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
    then have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems(2)
      using BT3 accessLGen
      by (metis (no_types, lifting) memoryvalue.inject(2) SubPtrs_top selfPoint2 option.inject)
    then have sameAccess:"accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) mem' = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) mem"
      using MTArray.prems MemLSubPrefL2_specific_imps_general SubPtrs_top nonLocChanged2 selfPoint2
      by (metis (no_types, lifting))
    then show ?case
    proof(cases "ptr = stl1")
      case True
      then show ?thesis using sameAccess
        using ptrDef by force
    next
      case False
      then show ?thesis using ptrDef sameAccess
        using MTArray.IH
        using MTArray.prems(2) by auto
    qed
  next
    case (MTValue x)
    then show ?case by simp
  qed
qed

lemma cpm2m_subPrefixPersist:
  assumes "subPrefixStructuralConsistency mo"
    and "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) mo = None"
    and "SomeValSomeTyp mo"
    and sameTypeAccess:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))  \<longrightarrow>
                         accessTypeStore locs (mo) = accessTypeStore locs m"
    and lessThan:"lessThanTopLocs mo"
    and sameTypeAccess2:" \<forall>locs.  \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))  \<longrightarrow>
       accessTypeStore locs (mo) = accessTypeStore locs m"
    and tps:"\<forall>destl'.
     TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t) \<longrightarrow>
     (\<exists>stt. CompMemType m x t stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) destl' \<and>
           (case stt of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
            | MTValue pval \<Rightarrow> accessTypeStore destl' m = Some (MTValue pval)))"
    and MCondest:" MCon (MTArray x t) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (mo)))"
    and selfPoint:"\<forall>l l'. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
    and tps2:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some t"
    and nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))
                  \<longrightarrow> accessStore locs (mo) = accessStore locs m" 
    and a32:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t) \<longrightarrow> accessStore locs mo = accessStore locs m"
  shows "subPrefixStructuralConsistency (m)" unfolding subPrefixStructuralConsistency_def
proof intros
  fix locs tp
  assume in1:"accessTypeStore locs m = Some tp"
  show "case accessStore locs m of None \<Rightarrow> False
 | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp
 | Some (MPointer p) \<Rightarrow>
     \<exists>len arr.
        MCon tp m p \<and>
        tp = MTArray len arr \<and>
        (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) "
  proof(cases " locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) ")
    case True
    then have "accessStore locs mo = None"
      by (simp add: assms(2))
    then have "accessTypeStore locs mo = None"
      using assms(3) unfolding SomeValSomeTyp_def by force
    then have "accessTypeStore locs m = None" using sameTypeAccess True by simp
    then show ?thesis using in1 by simp
  next
    case notTop:False
    then show ?thesis 
    proof(cases "LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))")
      case True
      then have "accessStore locs mo = None " 
        using lessThan unfolding lessThanTopLocs_def by blast
      then have "accessTypeStore locs mo = None" 
        using assms(3) unfolding SomeValSomeTyp_def by force
      then have "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t)" 
        using sameTypeAccess2 in1 by auto
      then obtain stt where sttDef:"( CompMemType m x t stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) locs \<and>
        (case stt of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
         | MTValue pval \<Rightarrow> accessTypeStore locs m = Some (MTValue pval)))" using tps by blast
      then have mcLocs: "MCon stt m locs" 
        using CompTypeRemainsMCon MCondest by blast
      then show ?thesis 
      proof(cases stt)
        case (MTArray x11 x12)

        then have mi:"t = MTArray x11 x12 \<and> (\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs)) \<or>
                  (\<exists>midP subL subA i. CompMemType m x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) midP \<and>
                    accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)" 
          using CompMemType_imps_Mid[of m x t x11 x12 "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))" locs] sttDef by simp

        then show ?thesis 
        proof(cases "t = MTArray x11 x12 \<and> (\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs))")
          case True
          then obtain i where idef:"i<x \<and> accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs)" 
            by blast
          then have isTop:"locs = (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
            using selfPoint by auto
          then have tpDef:"t = tp" using tps2 in1 idef by simp
          have "accessStore locs m = Some (MPointer locs)"
            using MCondest idef isTop by blast
          moreover have "\<exists>len arr.
                 MCon tp m locs \<and>
                 tp = MTArray len arr \<and>
                 (\<forall>i<len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) \<and>
                 (\<forall>v. accessStore locs m = Some (MPointer v) \<longrightarrow> accessTypeStore locs m = Some (MTArray len arr))" 
            using tpDef mcLocs True MTArray 
            using in1 sttDef by fastforce
          ultimately show ?thesis using in1 MTArray mcLocs tps2 by auto
        next
          case False
          then have prefPtrs_imps_Pref:"\<forall>l. TypedMemSubPrefPtrs m x t (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) l 
                                    \<longrightarrow> TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t)"
            using selfPoint_imps_TypedMemSubPref[of " (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))" x t m ] selfPoint by blast

          then obtain midP subL subA i
            where mid: "(CompMemType m x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) midP \<and>
                    accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
            using mi False by auto
          then have locD:"locs = (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint  
            using CompMemType_imps_in_GetAllMemoryLocations_ptr MCondest memSet_selfPoint by blast
          then obtain st2 where st2D:"(CompMemType m x t st2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) midP \<and>
         (case st2 of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
          | MTValue pval \<Rightarrow> accessTypeStore midP m = Some (MTValue pval)))" using mid tps
            using CompMemTypeSameLocsSameType CompMemType_imps_TypedMemSubPrefPtrs prefPtrs_imps_Pref by blast
          then have "st2 = (MTArray subL subA)" using mid CompMemTypeSameLocsSameType MCondest by blast 
          then have " \<forall>i<subL. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some subA" using st2D by simp
          then have tpDef:"MTArray x11 x12 = tp" using in1 locD mid by simp
          moreover have "\<exists>len arr.
                         MCon tp m locs \<and>
                         tp = MTArray len arr \<and>
                         (\<forall>i<len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) "
            using tpDef mcLocs True MTArray in1 sttDef by auto
          ultimately show ?thesis using mid locD by simp
        qed
      next
        case (MTValue x2)
        then obtain v where isVal:"accessStore locs m = Some (MValue v)" using mcLocs 
          using MConAccessSame.simps(1) SameMCon_imps_MConAccessSame by blast
        have "\<exists>val. MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp" 
          using mcLocs in1 sttDef MTValue by simp
        then show ?thesis using isVal by simp
      qed
    next
      case False
      then have sameAccT:"accessTypeStore locs mo = accessTypeStore locs m"
        using sameTypeAccess by blast
      have sameAcc:"accessStore locs mo = accessStore locs m" 
        using False nonLocChanged by metis
      obtain a where acc1:"accessStore locs mo = Some a" 
        using assms(3) sameAccT unfolding TypeSafe_def SomeValSomeTyp_def using in1 by auto
      then have old:"(case accessStore locs mo of
      Some (MValue v) \<Rightarrow> \<exists>val. MCon tp mo locs \<and> tp = MTValue val \<and> accessTypeStore locs mo = Some tp
   | Some (MPointer p) \<Rightarrow>
       \<exists>len arr.
          MCon tp mo p \<and>
          tp = MTArray len arr \<and>
          (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mo = Some arr))" 
        using assms(1) in1 sameAccT unfolding subPrefixStructuralConsistency_def by fastforce
      then show ?thesis 
      proof(cases a)
        case (MValue x1)

        then show ?thesis using sameAccT acc1 old MValue a32 in1 MCon.simps sameAcc
          by (auto split:option.splits memoryvalue.splits)
      next
        case (MPointer x2)

        then have oo:"\<exists>len arr.
          MCon tp mo x2 \<and>
          tp = MTArray len arr \<and>
          (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mo = Some arr) "
          using old acc1 by simp
        then have subs:"\<not> LSubPrefL2  (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) x2 \<and>\<not> LSubPrefL2 x2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) "
          using assms unfolding TypeSafe_def 
          by (meson AllPtrsNotTop2 TypeSafe_def le_refl)
        have "MCon tp mo x2" using oo by simp
        then have "MCon tp m x2" 
          using lessThanTop_topChange_MCon subs nonLocChanged lessThan by simp

        then have "\<exists>len arr.
     MCon tp m x2 \<and>
     tp = MTArray len arr \<and>
     (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) " 
          using oo subs nonLocChanged by (simp add: Mutual_NonSub_SpecificNonSub sameTypeAccess)
        then show ?thesis  using MPointer sameAcc acc1  
          by (smt (verit, ccfv_SIG) memoryvalue.simps(6) Option.option.simps(5))
      qed
    qed
  qed
qed

lemma cpm2m_singleLChange:
  assumes "MCon struct m x3"
  assumes structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 m = Some (MTValue val))"
    and "updateStore l (MPointer tloc) m = m'"
    and lOld2:"\<exists>p. accessStore l m = Some (MPointer p)"
    and accl:"accessTypeStore l (m) = Some (MTArray x t)"
    and MCondest2:"MCon (MTArray x t) m' (tloc)"
    and subPrefM:"subPrefixStructuralConsistency (m)"
    and NonChangeM'm:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs m = accessStore locs m'"
  shows "MCon struct m' x3"
  using assms(1,2)
proof(induction struct arbitrary:x3)
  case (MTArray x11 x12)
  have accessL:"accessStore l m' = Some (MPointer tloc)" 
    using assms unfolding updateStore_def accessStore_def by auto
  have oldexp:"(\<forall>i<x11.
          case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow>
              (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 m (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
          | Some (MPointer loc2) \<Rightarrow>
              (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 m loc2 | MTValue val \<Rightarrow> False)) \<and>
      (\<exists>p. accessStore x3 m = Some (MPointer p) \<or> accessStore x3 m = None)" 
    using  MTArray.prems(1) unfolding MCon.simps by simp

  then have subs:"(\<forall>i<x11. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some x12)"
    using structss MTArray by simp

  have "(\<forall>i<x11.
          case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow>
              (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 m' (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
          | Some (MPointer loc2) \<Rightarrow>
              (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 m' loc2 | MTValue val \<Rightarrow> False))"
  proof(intros)
    fix i assume idef:"i<x11"
    then consider (val1) val typw where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MValue val) 
                              \<and> x12 = MTValue typw 
                              \<and> MCon x12 m (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
      | (ptr1) ptr l1 a1 where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer ptr) 
                            \<and> x12 = MTArray l1 a1  
                            \<and> MCon x12 m ptr"
      using oldexp 
      by (metis MCon_imps_sub_Mcon MTArray.prems(1) mtypes.distinct(1) gr_implies_not0 mcon_accessStore nat_neq_iff)
    then show "case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
| Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 m' (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 m' loc2 | MTValue val \<Rightarrow> False)"
    proof(cases)
      case val1
      then show ?thesis 
      proof(cases "(hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
        case True
        then show ?thesis using True lOld2 val1 by simp
      next
        case False
        then have sameACC:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m'"
          using assms unfolding updateStore_def accessStore_def by auto
        then have "MCon x12 m' (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
          using val1  unfolding MCon.simps by auto
        then show ?thesis using val1 sameACC by simp
      qed
    next
      case ptr1
      then have "\<forall>i<x11. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some x12" using subs by simp

      then show ?thesis
      proof(cases "(hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
        case True
        then have "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer (tloc))" 
          using assms unfolding updateStore_def accessStore_def by auto

        moreover have "x12 = MTArray x t" using subs True idef MTArray.prems calculation accl by auto
        moreover have "MCon x12 m' (tloc)" using calculation MCondest2 by blast
        ultimately show ?thesis 
          by (simp add: ptr1)
      next
        case False
        then have "case x12 of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)
                  | MTValue val \<Rightarrow> accessTypeStore ptr m = Some (MTValue val)" 
          using subPrefM unfolding subPrefixStructuralConsistency_def using MTArray.prems
          using ptr1 idef by fastforce
        then have "MCon x12 m' ptr" 
          using MTArray.IH[of ptr] ptr1 by blast
        then show ?thesis 
          using False NonChangeM'm ptr1 by auto
      qed
    qed
  qed
  then show ?case using MTArray.prems(1) unfolding MCon.simps 
    by (metis NonChangeM'm accessL)
next
  case (MTValue x2)
  then show ?case
  proof(cases "x3 = l")
    case True
    then show ?thesis using accl 
      using MTValue.prems(2) by auto
  next
    case False
    then have "accessStore x3 m = accessStore x3 (m')"
      using assms unfolding updateStore_def accessStore_def by auto
    then show ?thesis using MTValue unfolding MCon.simps by simp
  qed
qed



lemma TypeSafe_Statements:
  assumes "TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd" 
    and normal:"stmt smt ev cd st = Normal((),st')"
    and inits:"fullyInitialised ev (Accounts st) (Stack st)"
  shows  "StateInvariant ev st st' cd"
  using assms(1,2,3)
proof (induction arbitrary: st' rule:stmt.induct)
  case (1 e cd st)
  have *:"st' = st\<lparr>Gas := (state.Gas st) - costs SKIP e cd st\<rparr>" using 1 skip by simp
  moreover have "Stack st = Stack st'" using * by simp
  moreover have memSame:"Memory st' = Memory st" using * by simp
  moreover have "Storage st' = Storage st" using * by simp
  moreover have "Accounts st' = Accounts st" using * by simp
  moreover have "WrittenMem_between (Memory st) (Memory st') = {}" using calculation unfolding WrittenMem_between_def by simp
  moreover have "ReachableMem e (Stack st') (Memory st') = ReachableMem e (Stack st) (Memory st)" unfolding ReachableMem.simps using calculation by metis

  ultimately show ?case using assms 1 * unfolding StateInvariant_def fullyInitialised_def  by auto
next
  case (2 lv ex env cd st)
  then show ?case 
  proof (cases rule:assign[OF 2(2)])
    case (1 v t2 g l2 t' g' v')
    show "StateInvariant env st st' cd" unfolding StateInvariant_def TypeSafe_def 
    proof (intros)
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd" unfolding typeCompat_def
      proof intros
        fix t l assume a10:"(t, l) |\<in>| fmran (Denvalue env)"
        show "case l of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)"
        proof (split denvalue.split, intros)
          fix loc assume a20:"l = Stackloc loc"
          show "case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
          proof (cases "loc = l2") 
            case False
            show ?thesis
            proof (split option.split, intros)
              assume a30:"accessStore loc (Stack st') = None"
              then have "accessStore loc (Stack st) = None" using 1(4) False by (simp add:stackSingleUpdate)
              then show False using a30 a20 a10 assms False "2.prems"(1) unfolding TypeSafe_def typeCompat_def  by force
            next
              fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
              then have a40:"accessStore loc (Stack st) = Some x2" using 1(4) False by (simp add:stackSingleUpdate)
              then have a50:"(Memory st) = (Memory st')" using 1(4) by simp
              then have a60:"(Storage st) = (Storage st')" using 1(4) by simp
              show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                    | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                    | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                    | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
                using a10 a20 a30 a40 a50 a60 "2.prems"(1) unfolding TypeSafe_def typeCompat_def by (cases x2; cases t; force)
            qed
          next 
            case sameLoc:True
            show ?thesis
            proof (split option.split, intros)
              assume a30:"accessStore loc (Stack st') = None"
              then show False using a20 a10 assms(1) sameLoc 1(4) notNoneUpdate[of st' g' loc "KValue v'" ] by simp
            next
              fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
              show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
              proof(cases "x2")
                case (KValue x1)
                then have a40:"unique_locations (Denvalue env)" using 2(1) typeSafeUnique by simp
                then have "(Value t', l2) = (t, loc)" using  a40 a20 1(2) lexpStackloc_imps_inDen a10 sameLoc 
                    uniqueLocs[of env "(t,l)" "(Value t', Stackloc l2)"] by simp
                then have True:"Value t' = t" by simp
                then have a40:"v' = v" using convertSame[of t2 t' v v'] 1(3) by simp
                moreover have "typeCon t' v" using a40 1 2(1) 2(3) 
                  by (simp add: typeConConvert)
                moreover have "x1 = v" 
                  using sameLoc a30 a40 KValue 1(4) notNoneUpdate[of st' g' l2 "(KValue x1)"  ] notNoneUpdate[of st' g' l2 "(KValue v')"  ] by simp
                ultimately have "typeCon t' x1" by simp
                then show ?thesis using True KValue by auto
              next
                case (KCDptr x2)
                then show ?thesis using a30 "1"(4) by (simp add:sameLoc)
              next
                case (KMemptr x3)
                then show ?thesis using a30 "1"(4) by (simp add:sameLoc)
              next
                case (KStoptr x4)
                then show ?thesis using a30 "1"(4) by (simp add:sameLoc)
              qed
            qed
          qed

        next
          fix x2 assume a20:"l = Storeloc x2"
          then have "(Storage st' (Address env)) = (Storage st (Address env))" using 1(4) by simp
          then show "case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st' (Address env)) | _ \<Rightarrow> False"  
            using a10 a20  "2.prems"(1) unfolding TypeSafe_def typeCompat_def by (cases t; force)
        qed
      qed
    next
      show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by auto
    next
      have "(Accounts st) = Accounts(st')" using 1(4) by simp
      then show "balanceTypes (Accounts st')" using balanceTypes_def balanceTypes_def 2(1) typeSafeAccounts by simp
    next
      show " compPointers (Stack st')  (Denvalue env)" unfolding compPointers_def
      proof(intros)
        fix tp1 tp2 l1 l22 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
       (type.Storage tp2, l22) |\<in>| fmran (Denvalue env) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l22 = Storeloc stl2)"
        then have 10:"accessStore l1' (Stack st) = Some (KStoptr stl1) \<or> l1 = Storeloc stl1" using 1(4) 2(1) updateOneType[of st' g' l2 "(KValue v')" st "(KStoptr stl1)" l1' ] by auto
        then have 20:"accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l22 = Storeloc stl2" using a1 1(4) 2(1) updateOneType[of st' g' l2 "(KValue v')" st "(KStoptr stl2)" l2' ] by auto
        have "Storage st' (Address env) = (Storage st (Address env))" using a1 1(4) 2(1) updateOneType[of st' g' l2 "(KValue v')" st "(KStoptr stl2)" l2' ] by auto
        then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"  
          using 2(1) a1 10 20 unfolding TypeSafe_def compPointers_def by blast
      qed
    next
      show "svalueTypes (Svalue env)" using svalueTypes_def typeSafeSvalue 2(1) by simp
    next
      have "(Storage st') = (Storage st)" using 1(4) by simp
      then show "safeContract (Accounts st') (Storage st')" using 2(1) 1(4) unfolding safeContract_def TypeSafe_def 
        by fastforce
    next
      have a10:"Toploc (Stack st') = Toploc (Stack st)" using 1(4) unfolding updateStore_def by simp
      then have "(Value t', Stackloc l2) |\<in>| fmran (Denvalue env)"  using 2(1) 1(2) lexpStackloc_imps_inDen by simp
      then have a20:"\<exists>val. accessStore l2 (Stack st) = Some val" using typeSafeLocExists 2(1) TypeSafe_def by blast
      then have a30:"(\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                     \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))" 
        using 2(1) unfolding TypeSafe_def  lessThanTopLocs_def by simp
      then have a40:"(\<forall>tloc loc. Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                      \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))" 
        using a10 by simp
      show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume *:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then show "accessStore loc (Stack st') = None"
        proof(cases "loc = l2")
          case True
          then show ?thesis using * a10 
            by (metis a20 a30 option.distinct(1)) 
        next
          case False
          then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 1(4) unfolding updateStore_def accessStore_def by simp
          then show ?thesis using 2(1) a40 * a10 False a30 by simp
        qed
      next 
        fix loc y 
        assume *:" accessStore loc (Stack st') = Some y "
        show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        proof(cases "loc = l2")
          case True
          then show ?thesis using *a10 a20 a30 by simp
        next
          case False
          then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 1(4) unfolding updateStore_def accessStore_def by simp
          then show ?thesis using * 2(1) a40 by simp
        qed
      qed
    next
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def using 1 by auto
    next 
      show "lessThanTopLocs (Memory st')" using 2(1) unfolding TypeSafe_def using 1 by auto
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by auto
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 1 by simp
    next 
      have "Accounts st'= Accounts st" using 1 by auto
      then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 1(4) unfolding fullyInitialised_def updateStore_def accessStore_def by auto
    next 
      have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using 1(4) unfolding updateStore_def accessStore_def by auto
      show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
      proof intros
        fix t l ptr_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "(case t of
         MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
        moreover have "Memory st = Memory st'" using 1(4) by simp
        ultimately show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          by metis
      qed
    next
      show "subPrefixStructuralConsistency (Memory st')"
        using 2(1) 1(4) unfolding TypeSafe_def by simp
    next
      show "SomeValSomeTyp (Memory st') " using 2(1) unfolding TypeSafe_def using 1(4) by auto
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 1 by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using 1 by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using 1 by simp
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 1 by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 1 by simp
    qed
  next
    case subcase2:(2 v t2 g locationChanged t' g' v')
    then have tpCon:"typeCon t2 (extractValueType (KValue v)) \<and> (\<exists>xx. KValue v = KValue xx)" 
      using exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KValue v" "Value t2" g] 
      using "2.prems"(1) 2(3) unfolding fullyInitialised_def by force
    then have tcon:"typeCon t' v'" using typeSafeConvert[of t2 "(extractValueType (KValue v))" t' ] subcase2(3) 
      by (metis convertSame extractValueType.simps(1))
    have stacksSame:"Stack st = Stack st'" using subcase2(4) by simp
    have accessStoreSt:"Storage st' (Address env) $$ locationChanged = Some v'" using subcase2 by simp
    then have scont':"SCon (STValue t') locationChanged (Storage st' (Address env))" 
      using SCon.simps(1)[of t' locationChanged "Storage st' (Address env)"] accessStorage_def tcon by simp
    have nonLocChanged:"\<forall>l. l \<noteq> locationChanged \<longrightarrow> Storage st' (Address env) $$ l = Storage st (Address env) $$ l"  using subcase2 by simp
    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros
      show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by simp
    next
      have "compPointers (Stack st)  (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
      show "compPointers (Stack st')  (Denvalue env)" unfolding compPointers_def  using "2.prems"(1) compPointers_def stacksSame typeSafeCompPointers by force

    next
      show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
      proof intros
        fix e ct dud i tp
        assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
                 ep $$ Contract (e::environment) = Some (ct, dud) \<and>
                 ct $$ i = Some (Var tp)"
        have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp
        show "SCon tp i (Storage st' (Address e))"
        proof (cases "Address e = Address env")
          case False
          have stoEq:"\<forall>a. a \<noteq> Address env \<longrightarrow> Storage st' a = Storage st a"
            using subcase2(4) by simp
          have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using * subcase2(4) by simp
          have epOld:"ep $$ Contract e = Some (ct, dud)"
            using * by simp
          have ctOld:"ct $$ i = Some (Var tp)"
            using * by simp
          show ?thesis
            using safeContract_other_address_preserved[OF scOld stoEq False typedOld epOld ctOld] .
        next
          case addrEq:True
          obtain c where **:"Type (Accounts st (Address env)) = Some (atype.Contract c) \<and> Contract env = c"
            using 2(3) unfolding fullyInitialised_def using 2 by blast
          have cEq:"Contract e = Contract env"
            using * ** addrEq subcase2(4) by auto
          have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using * subcase2(4) by simp
          have epOld:"ep $$ Contract e = Some (ct, dud)"
            using * by simp
          have ctOld:"ct $$ i = Some (Var tp)"
            using * by simp
          have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
            using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
          have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
            using denI by (simp add: fmranI)
          have oldSCon:"SCon tp i (Storage st (Address env))"
            using safeContract_field_scon_from_typeCompat[OF 2(1) 2(3) addrEq typedOld epOld ctOld] .
          have uniq:"unique_locations (Denvalue env)"
            using 2(1) typeSafeUnique by simp
          have epEnv:"ep $$ Contract env = Some (ct, dud)"
            using epOld cEq by simp
          show ?thesis
          proof(cases rule:lexpStorage[OF 2(1) subcase2(2) 2(3)])
            case 1
            then have inDenChanged:"(type.Storage (STValue t'), Storeloc locationChanged) |\<in>| fmran (Denvalue env)" by simp
            show ?thesis
            proof(cases "i = locationChanged")
              case True
              have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage (STValue t'), Storeloc locationChanged)"
                using uniqueLocs[OF uniq inDenI inDenChanged] True by simp
              then have tpEq:"tp = STValue t'" by simp
              show ?thesis using scont' True tpEq by (simp add: addrEq)
            next
              case False
              have ctChanged:"ct $$ locationChanged = Some (Var (STValue t'))"
                using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenChanged] .
              have n1:"\<not>TypedStoSubpref locationChanged i tp"
                and n2:"\<not>TypedStoSubpref i locationChanged (STValue t')"
                using methodVarsNoPref False epOld ctOld ctChanged by blast+
              have relChanged:"TypedStoSubpref locationChanged locationChanged (STValue t')
                               \<and> CompStoType (STValue t') (STValue t') locationChanged locationChanged"
                by simp
              show ?thesis
                using singleLocChanged_nonchanged_SCon[OF nonLocChanged False oldSCon n1 n2 relChanged] 
                by (simp add: addrEq)
            qed
          next
            case sub2:(2 l t)
            have inDenL:"(type.Storage t, Storeloc l) |\<in>| fmran (Denvalue env)" using sub2 by simp
            have relL:"TypedStoSubpref locationChanged l t \<and> CompStoType t (STValue t') l locationChanged" using sub2 by simp
            show ?thesis
            proof(cases "i = l")
              case True
              have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage t, Storeloc l)"
                using uniqueLocs[OF uniq inDenI inDenL] True by simp
              then have tpEq:"tp = t" by simp
              have comp:"CompStoType tp (STValue t') i locationChanged"
                using relL tpEq True by simp
              show ?thesis using SCon_value_write_imps_SCon[OF comp oldSCon scont' nonLocChanged]
                by (simp add: addrEq)
            next
              case False
              have ctL:"ct $$ l = Some (Var t)"
                using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenL] by simp
              have n1:"\<not>TypedStoSubpref l i tp"
                and n2:"\<not>TypedStoSubpref i l t"
                using methodVarsNoPref False epOld ctOld ctL by blast+
              have iNeChanged:"i \<noteq> locationChanged"
              proof
                assume "i = locationChanged"
                then have "TypedStoSubpref i l t" using relL by simp
                then show False using n2 by contradiction
              qed
              show ?thesis
                using singleLocChanged_nonchanged_SCon[OF nonLocChanged iNeChanged oldSCon n1 n2 relL]
                by (simp add: addrEq)
            qed
          next
            case (3 l' t l)
            have inDenStk:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env)" using 3 by simp
            have ptrL:"accessStore l (Stack st) = Some (KStoptr l')" using 3 by simp
            have rel0:"TypedStoSubpref locationChanged l' t \<and> CompStoType t (STValue t') l' locationChanged" using 3 by simp
            obtain tprnt lprnt where
                inDenPr:"(type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue env)"
              and compPr:"CompStoType tprnt t lprnt l'"
              using fiPtr_parent_from_fullyInitialised[OF 2(3) inDenStk ptrL] by blast
            have compPr2:"CompStoType tprnt (STValue t') lprnt locationChanged"
              using compPr rel0 CompStoType_trns by blast
            have relPr:"TypedStoSubpref locationChanged lprnt tprnt \<and> CompStoType tprnt (STValue t') lprnt locationChanged"
              using compPr2 CompStoType_imps_TypedStoSubpref by blast
            show ?thesis
            proof(cases "i = lprnt")
              case True
              have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage tprnt, Storeloc lprnt)"
                using uniqueLocs[OF uniq inDenI inDenPr] True by simp
              then have tpEq:"tp = tprnt" by simp
              have comp:"CompStoType tp (STValue t') i locationChanged"
                using compPr2 tpEq True by simp
              show ?thesis using SCon_value_write_imps_SCon[OF comp oldSCon scont' nonLocChanged]
                by (simp add: addrEq)
            next
              case False
              have ctPr:"ct $$ lprnt = Some (Var tprnt)"
                using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenPr] .
              have n1:"\<not>TypedStoSubpref lprnt i tp"
                and n2:"\<not>TypedStoSubpref i lprnt tprnt"
                using methodVarsNoPref False epOld ctOld ctPr by blast+
              have iNeChanged:"i \<noteq> locationChanged"
              proof
                assume "i = locationChanged"
                then have "TypedStoSubpref i lprnt tprnt" using relPr by simp
                then show False using n2 by contradiction
              qed
              show ?thesis
                using singleLocChanged_nonchanged_SCon[OF nonLocChanged iNeChanged oldSCon n1 n2 relPr]
                by (simp add: addrEq)
            qed
          qed
        qed
      qed
    next
      have "Accounts st' = Accounts st" using subcase2(4) by simp
      then show "balanceTypes (Accounts st')"  using 2(1)  unfolding TypeSafe_def balanceTypes_def by simp
    next 
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have "Stack st = Stack st'" using subcase2(4) by simp
      then show "lessThanTopLocs (Stack st')" using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    next
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd" unfolding typeCompat_def
      proof intros
        fix t l 
        assume inDen:"(t, l) |\<in>| fmran (Denvalue env)"
        then show "case l of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False
               | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
               | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
               | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
               | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)"
        proof (cases l)
          case (Stackloc loc)
          then have "l \<noteq> Storeloc locationChanged" by simp
          then have same:"accessStore loc (Stack st) = accessStore loc (Stack st')" using subcase2(4) by simp
          then show ?thesis 
          proof(cases "accessStore loc (Stack st')")
            case None
            then show ?thesis using same 2(1) inDen Stackloc unfolding TypeSafe_def typeCompat_def by fastforce
          next
            case (Some a)
            have samemem:"(Memory st) = Memory st'" using subcase2(4) by simp
            then show ?thesis
            proof(cases a)
              case (KValue x1)
              then show ?thesis using Some same 2(1) inDen Stackloc unfolding TypeSafe_def typeCompat_def by fastforce
            next
              case (KCDptr x2)
              then show ?thesis using Some same 2(1) inDen Stackloc unfolding TypeSafe_def typeCompat_def samemem by fastforce
            next
              case (KMemptr x3)
              then show ?thesis using Some same 2(1) inDen Stackloc unfolding TypeSafe_def typeCompat_def samemem by fastforce
            next
              case (KStoptr x4)
              then have a20:"accessStore loc (Stack st) = Some (KStoptr x4)" using same Some by simp
              have a25:"(case l of
              Stackloc loc \<Rightarrow>
                (case accessStore loc (Stack st) of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st) stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st (Address env)) | _ \<Rightarrow> False))
              | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st (Address env)) | _ \<Rightarrow> False))" 
                using 2(1) unfolding TypeSafe_def typeCompat_def using inDen by simp
              then obtain struct where a30:"t = type.Storage struct" using a20 Stackloc by (simp split:type.splits)
              then have a40:"SCon struct x4 (Storage st (Address env))" using a25 a20 Stackloc by (simp split:type.splits)
              have tCont2v:"typeCon t2 v" using subcase2(1) extractValueType.simps 2(1) 
                using exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KValue v" "Value t2" g] 
                using 2(3) unfolding fullyInitialised_def 
                by (simp)
              have "v' = v" using  convertSame[of t2 t' v v'] subcase2(3) by simp
              then have tCont'v:"typeCon t' v" using typeSafeConvert[of t2 v t'] subcase2(3) tCont2v by simp
              have "SCon struct x4 (Storage st' (Address env))" using a40 a30 inDen
              proof(cases "TypedStoSubpref locationChanged x4 struct")
                case subloc:True
                have compPtr:"(\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
                        (type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
                        (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
                        (l1 = Stackloc l1' \<and> accessStore l1' (Stack st) = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) 
                        \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
                        (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
                  using 2(1)  unfolding TypeSafe_def compPointers_def  by auto
                then show ?thesis 
                proof(cases rule:lexpStorage[OF 2(1) subcase2(2) 2(3)])
                  case 11:1
                  then have b40:"CompStoType struct (STValue t') x4 locationChanged" 
                    using inDen Stackloc Some KStoptr a20  a30   compPtr subloc by metis
                  then show ?thesis
                    using SCon_value_write_imps_SCon[OF _ a40 scont' nonLocChanged] by blast
                next
                  case (2 l'' t'')
                  have c3:"\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow>  Storage st' (Address env) $$ l = Storage st (Address env) $$ l" 
                    by (metis TypedStoSubpref_sameLoc nonLocChanged)
                  have b40:"if TypedStoSubpref x4 l'' t'' then CompStoType t'' struct l'' x4
                                  else if TypedStoSubpref l'' x4 struct then CompStoType struct t'' x4 l'' 
                                    else True"
                    using compPtr inDen Stackloc Some KStoptr a20  a30 2  by blast
                  then show ?thesis using subloc 2
                  proof(cases "x4 = l''")
                    case True
                    then have stt:"struct = t''" using b40 
                      using CompStoType_sameLoc_sameType TypedStoSubpref_sameLoc by auto
                    then show ?thesis 
                    proof(cases "l'' = locationChanged")
                      case t4:True
                      then show ?thesis using  stt True scont' 
                        using "2"(2) CompStoType_sameLoc_sameType by blast
                    next
                      case False
                      have c0:"CompStoType struct (STValue t') x4 locationChanged" using 2(2) True stt by simp
                      then have "\<exists>y. hash l'' y = locationChanged" using subloc "2"(2) TypedStoSubpref_b False by auto
                      then obtain i'' where c1:"(hash x4 i'' = locationChanged)" using CompStoType_imps_subloc False True by blast
                      then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 by blast 
                    qed
                  next
                    case x4Dif:False
                    then show ?thesis
                    proof(cases "TypedStoSubpref x4 l'' t''")
                      case d5:True
                      then have d7:"CompStoType t'' struct l'' x4" using b40 by simp
                      have d9:"CompStoType t'' (STValue t') l'' locationChanged" using 2(2) by simp
                      have d10:"CompStoType struct (STValue t') x4 locationChanged" using CompStoType_subloc_type_transfer[of t'' t' l'' locationChanged struct x4] subloc d7 d9 by blast
                      then have d11:"\<exists>x. hash l'' x = x4" using TypedStoSubpref_b x4Dif d5 by auto
                      then show ?thesis 
                      proof(cases "l'' = locationChanged")
                        case True
                        then obtain i'' where d11:"hash locationChanged i'' = x4" using d11 by auto
                        then show ?thesis using subloc using TypedStoSubpref_hashes by auto
                      next
                        case False
                        then have "\<exists>x. hash l'' x = locationChanged" using 2(2) TypedStoSubpref_b by auto
                        then have "\<exists>x. hash l'' x = x4" using d11 using hash_suffixes_associative by auto
                        then show ?thesis
                        proof(cases "x4 = locationChanged")
                          case True
                          then have "struct = (STValue t')" using d10 by (simp add: CompStoType_sameLoc_sameType)
                          then show ?thesis using True scont' by auto
                        next
                          case False
                          then obtain i'' where d11:"hash x4 i'' = locationChanged" 
                            using subloc False TypedStoSubpref_b[of locationChanged x4 struct] by blast
                          then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 d10 by blast
                        qed
                      qed
                    next
                      case f5:False
                      then show ?thesis
                      proof(cases "TypedStoSubpref l'' x4 struct")
                        case True
                        then have d5:"TypedStoSubpref l'' x4 struct"  by simp
                        then have d7:"CompStoType struct t'' x4 l''" using b40 f5 by simp
                        then have d10:"\<exists>x. hash x4 x = l''" using TypedStoSubpref_b x4Dif d5 by auto
                        then show ?thesis 
                        proof(cases "l'' = locationChanged")
                          case True
                          then obtain i'' where d11:"hash x4 i'' = locationChanged" using d10 by auto
                          then have d15:"t'' = STValue t'" using 2(2) CompStoType_sameLoc_sameType True by auto
                          then have c0:"CompStoType struct (STValue t') x4 locationChanged" using 2(2) d15 d7 by fastforce
                          then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 d11 by blast 
                        next
                          case False
                          then have "\<exists>x. hash l'' x = locationChanged" using 2(2) TypedStoSubpref_b by auto
                          then have "\<exists>x. hash x4 x = locationChanged" using d10 using hash_suffixes_associative by auto
                          then obtain i'' where d11:"hash x4 i'' = locationChanged" by auto
                          then have "CompStoType struct (STValue t') x4 locationChanged" using CompStoType_trns 2(2)  d7 by blast
                          then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 by blast
                        qed
                      next
                        case False
                        have "x4 \<noteq> locationChanged" using 2(2) f5 by blast
                        then show ?thesis using  a40 False f5 2(2) singleLocChanged_nonchanged_SCon 
                          using nonLocChanged by blast
                      qed
                    qed
                  qed
                next
                  case (3 l'' t'' l)
                  have c3:"\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow>  Storage st' (Address env) $$ l = Storage st (Address env) $$ l" 
                    by (metis TypedStoSubpref_sameLoc nonLocChanged)
                  then have b40:"if TypedStoSubpref x4 l'' t'' then CompStoType t'' struct l'' x4
                                  else if TypedStoSubpref l'' x4 struct then CompStoType struct t'' x4 l'' 
                                    else True"
                    using compPtr inDen Stackloc Some KStoptr a20  a30 3  by blast
                  then show ?thesis using subloc 2
                  proof(cases "x4 = l''")
                    case True
                    then have stt:"struct = t''" using b40 
                      using CompStoType_sameLoc_sameType TypedStoSubpref_sameLoc by auto
                    then show ?thesis 
                    proof(cases "l'' = locationChanged")
                      case t4:True
                      then show ?thesis using  stt True scont' 
                        using "3"(3) CompStoType_sameLoc_sameType by blast
                    next
                      case False
                      have c0:"CompStoType struct (STValue t') x4 locationChanged" using 3(3) True stt by simp
                      then have "\<exists>y. hash l'' y = locationChanged" using subloc 3(3) TypedStoSubpref_b False by auto
                      then obtain i'' where c1:"(hash x4 i'' = locationChanged)" using CompStoType_imps_subloc False True by blast
                      then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 by blast 
                    qed
                  next
                    case x4Dif:False
                    then show ?thesis
                    proof(cases "TypedStoSubpref x4 l'' t''")
                      case d5:True
                      then have d7:"CompStoType t'' struct l'' x4" using b40 by simp
                      have d9:"CompStoType t'' (STValue t') l'' locationChanged" using 3(3) by simp
                      have d10:"CompStoType struct (STValue t') x4 locationChanged" using CompStoType_subloc_type_transfer[of t'' t' l'' locationChanged struct x4] subloc d7 d9 by blast
                      then have d11:"\<exists>x. hash l'' x = x4" using TypedStoSubpref_b x4Dif d5 by auto
                      then show ?thesis 
                      proof(cases "l'' = locationChanged")
                        case True
                        then obtain i'' where d11:"hash locationChanged i'' = x4" using d11 by auto
                        then show ?thesis using subloc using TypedStoSubpref_hashes by auto
                      next
                        case False
                        then have "\<exists>x. hash l'' x = locationChanged" using 3(3) TypedStoSubpref_b by auto
                        then have "\<exists>x. hash l'' x = x4" using d11 using hash_suffixes_associative by auto
                        then show ?thesis
                        proof(cases "x4 = locationChanged")
                          case True
                          then have "struct = (STValue t')" using d10 by (simp add: CompStoType_sameLoc_sameType)
                          then show ?thesis using True scont' by auto
                        next
                          case False
                          then obtain i'' where d11:"hash x4 i'' = locationChanged" 
                            using subloc False TypedStoSubpref_b[of locationChanged x4 struct] by blast
                          then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 d10 by blast
                        qed
                      qed
                    next
                      case f5:False
                      then  show ?thesis 
                      proof(cases "TypedStoSubpref l'' x4 struct")
                        case True
                        then have d5:"TypedStoSubpref l'' x4 struct"  by simp
                        then have d7:"CompStoType struct t'' x4 l''" using b40 f5 by simp
                        then have d10:"\<exists>x. hash x4 x = l''" using TypedStoSubpref_b x4Dif d5 by auto
                        then show ?thesis 
                        proof(cases "l'' = locationChanged")
                          case True
                          then obtain i'' where d11:"hash x4 i'' = locationChanged" using d10 by auto
                          then have d15:"t'' = STValue t'" using 3(3) CompStoType_sameLoc_sameType True by auto
                          then have c0:"CompStoType struct (STValue t') x4 locationChanged" using 3(3) d15 d7 by fastforce
                          then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 d11 by blast 
                        next
                          case False
                          then have "\<exists>x. hash l'' x = locationChanged" using 3(3) TypedStoSubpref_b by auto
                          then have "\<exists>x. hash x4 x = locationChanged" using d10 using hash_suffixes_associative by auto
                          then obtain i'' where d11:"hash x4 i'' = locationChanged" by auto
                          then have "CompStoType struct (STValue t') x4 locationChanged" using CompStoType_trns 3(3)  d7 by blast
                          then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 by blast
                        qed
                      next
                        case False
                        have "x4 \<noteq> locationChanged" using  f5 
                          using "3"(3) by auto
                        then show ?thesis using  a40 False f5 3(3) singleLocChanged_nonchanged_SCon 
                          using nonLocChanged by blast
                      qed
                    qed
                  qed
                qed
              next
                case f1:False
                then show ?thesis using a40
                proof(induction struct arbitrary:x4)
                  case (STArray x1 struct)
                  have b10:"\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st (Address env))" 
                    using STArray(3) using SCon.simps(2)[of x1 struct x4 "(Storage st (Address env))"] by auto
                  have b20:"\<forall>i<x1. \<not> TypedStoSubpref locationChanged (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct 
                                    \<and> locationChanged \<noteq> hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)" 
                    using STArray(2) TypedStoSubpref.simps(2)[of locationChanged x4 x1 struct] 
                    using TypedStoSubpref_sameLoc by auto
                  then have b30:"\<forall>i<x1. \<not> TypedStoSubpref locationChanged (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct " by auto
                  have " (\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st' (Address env)))" 
                  proof(intros)
                    fix i assume b40: "i<x1"
                    then have "\<not>TypedStoSubpref locationChanged (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct" using b30 by auto
                    then show "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st' (Address env))" using STArray(1)[of "(hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b30 b10 b40 by simp
                  qed
                  then show ?case using SCon.simps(2)[of x1 struct x4 "Storage st' (Address env)"] by simp
                next
                  case (STMap x1 struct)
                  then have " (\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (Storage st (Address env)))" using SCon.simps(3)[of x1 struct x4 "(Storage st (Address env))"] by simp
                  moreover have "(\<forall>i. \<not>typeCon x1 i \<or> \<not>TypedStoSubpref locationChanged (hash x4 i) struct \<and> locationChanged \<noteq> hash x4 i)" 
                    using STMap(2) TypedStoSubpref.simps(3)[of locationChanged x4 x1 struct] 
                    using TypedStoSubpref_sameLoc by auto
                  ultimately show ?case  using STMap(1) by auto
                next
                  case (STValue x)
                  then have c5:"(x4 \<noteq> locationChanged \<or> STValue t' \<noteq> STValue x)" using Subpref.simps(1)[of  x x4 "STValue t'" locationChanged] by auto
                  then show ?case 
                  proof(cases "x4 \<noteq> locationChanged")
                    case True
                    then have c10:"Storage st' (Address env) $$ x4 = Storage st (Address env) $$ x4" using subcase2 nonLocChanged by auto
                    then have " SCon (STValue x) x4 (Storage st (Address env))" using STValue by blast
                    then show ?thesis using c10 
                      by (simp add: accessStorage_def)
                  next
                    case False
                    then have "x4 = locationChanged" by simp
                    then have "STValue t' = STValue x" using subcase2  Stackloc KStoptr inDen lexpStorage[of env st cd lv g locationChanged t' g'] Some f1 2(1) a20 a30 
                      by (metis STValue.prems(1) TypedStoSubpref.simps(1))
                    then show ?thesis using False c5 by auto
                  qed
                qed
              qed
              then show ?thesis using Stackloc inDen KStoptr Some a30 subcase2 by simp
            qed
          qed
        next
          case (Storeloc x2)
          then have a20:"case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address env)) | _ \<Rightarrow> False" 
            using 2(1) unfolding TypeSafe_def typeCompat_def using inDen by force
          then obtain struct where a30:"t = type.Storage struct" using a20 Storeloc by (simp split:type.splits)
          then have a40:"SCon struct x2 (Storage st (Address env))" using a20 Storeloc by (simp split:type.splits)
          have tCont2v:"typeCon t2 v" using subcase2(1) extractValueType.simps 2(1) 
            using exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KValue v" "Value t2" g] 
            using 2(3) unfolding fullyInitialised_def by (simp)
          have "v' = v" using  convertSame[of t2 t' v v'] subcase2(3) by simp
          then have tCont'v:"typeCon t' v" using typeSafeConvert[of t2 v t'] subcase2(3) tCont2v by simp
          have "SCon struct x2 (Storage st' (Address env))" using a40 a30 inDen
          proof(cases "TypedStoSubpref locationChanged x2 struct")
            case subloc:True
            have compPtr:"(\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
                        (type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
                        (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
                        (l1 = Stackloc l1' \<and> accessStore l1' (Stack st) = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) 
                        \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
                        (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
              using 2(1)  unfolding TypeSafe_def compPointers_def by auto
            then show ?thesis 
            proof(cases rule:lexpStorage[OF 2(1) subcase2(2) 2(3)])
              case 1
              then have b40:"CompStoType struct (STValue t') x2 locationChanged" 
                using inDen Storeloc a20 a30 1 compPtr subloc by metis
              then show ?thesis
                using SCon_value_write_imps_SCon[OF _ a40 scont' nonLocChanged] by blast
            next
              case (2 l'' t'')
              have c3:"\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow>  Storage st' (Address env) $$ l = Storage st (Address env) $$ l" 
                by (metis TypedStoSubpref_sameLoc nonLocChanged)
              then have b40:"if TypedStoSubpref x2 l'' t'' then CompStoType t'' struct l'' x2
                                  else if TypedStoSubpref l'' x2 struct then CompStoType struct t'' x2 l'' 
                                    else True"
                using compPtr inDen Storeloc a20 a30 2  by blast
              then show ?thesis using subloc 2
              proof(cases "x2 = l''")
                case True
                then have stt:"struct = t''" using b40 
                  using CompStoType_sameLoc_sameType TypedStoSubpref_sameLoc by auto
                then show ?thesis 
                proof(cases "l'' = locationChanged")
                  case t4:True
                  then show ?thesis using  stt True scont' 
                    using "2"(2) CompStoType_sameLoc_sameType by blast
                next
                  case False
                  have c0:"CompStoType struct (STValue t') x2 locationChanged" using 2(2) True stt by simp
                  then have "\<exists>y. hash l'' y = locationChanged" using subloc "2"(2) TypedStoSubpref_b False by auto
                  then obtain i'' where c1:"(hash x2 i'' = locationChanged)" using CompStoType_imps_subloc False True by blast
                  then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 by blast 
                qed
              next
                case x4Dif:False
                then show ?thesis
                proof(cases "TypedStoSubpref x2 l'' t''")
                  case d5:True
                  then have d7:"CompStoType t'' struct l'' x2" using b40 by simp
                  have d9:"CompStoType t'' (STValue t') l'' locationChanged" using 2(2) by simp
                  have d10:"CompStoType struct (STValue t') x2 locationChanged" using CompStoType_subloc_type_transfer[of t'' t' l'' locationChanged struct x2] subloc d7 d9 by blast
                  then have d11:"\<exists>x. hash l'' x = x2" using TypedStoSubpref_b x4Dif d5 by auto
                  then show ?thesis 
                  proof(cases "l'' = locationChanged")
                    case True
                    then obtain i'' where d11:"hash locationChanged i'' = x2" using d11 by auto
                    then show ?thesis using subloc using TypedStoSubpref_hashes by auto
                  next
                    case False
                    then have "\<exists>x. hash l'' x = locationChanged" using 2(2) TypedStoSubpref_b by auto
                    then have "\<exists>x. hash l'' x = x2" using d11 using hash_suffixes_associative by auto
                    then show ?thesis
                    proof(cases "x2 = locationChanged")
                      case True
                      then have "struct = (STValue t')" using d10 by (simp add: CompStoType_sameLoc_sameType)
                      then show ?thesis using True scont' by auto
                    next
                      case False
                      then obtain i'' where d11:"hash x2 i'' = locationChanged" 
                        using subloc False TypedStoSubpref_b[of locationChanged x2 struct] by blast
                      then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 d10 by blast
                    qed
                  qed
                next
                  case f5:False
                  then show ?thesis 
                  proof(cases "TypedStoSubpref l'' x2 struct")
                    case True
                    then have d5:"TypedStoSubpref l'' x2 struct" by simp
                    then have d7:"CompStoType struct t'' x2 l''" using b40 f5 by simp
                    then have d10:"\<exists>x. hash x2 x = l''" using TypedStoSubpref_b x4Dif d5 by auto
                    then show ?thesis 
                    proof(cases "l'' = locationChanged")
                      case True
                      then obtain i'' where d11:"hash x2 i'' = locationChanged" using d10 by auto
                      then have d15:"t'' = STValue t'" using 2(2) CompStoType_sameLoc_sameType True by auto
                      then have c0:"CompStoType struct (STValue t') x2 locationChanged" using 2(2) d15 d7 by fastforce
                      then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 d11 by blast 
                    next
                      case False
                      then have "\<exists>x. hash l'' x = locationChanged" using 2(2) TypedStoSubpref_b by auto
                      then have "\<exists>x. hash x2 x = locationChanged" using d10 using hash_suffixes_associative by auto
                      then obtain i'' where d11:"hash x2 i'' = locationChanged" by auto
                      then have "CompStoType struct (STValue t') x2 locationChanged" using CompStoType_trns 2(2)  d7 by blast
                      then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 by blast
                    qed
                  next
                    case False
                    have "x2 \<noteq> locationChanged" using 2(2) f5 by blast
                    then show ?thesis using  a40 False f5 2(2) singleLocChanged_nonchanged_SCon 
                      using nonLocChanged by blast
                  qed

                qed
              qed
            next
              case (3 l'' t'' l)
              have c3:"\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow>  Storage st' (Address env) $$ l = Storage st (Address env) $$ l" 
                by (metis TypedStoSubpref_sameLoc nonLocChanged)
              then have b40:"if TypedStoSubpref x2 l'' t'' then CompStoType t'' struct l'' x2
                                  else if TypedStoSubpref l'' x2 struct then CompStoType struct t'' x2 l'' 
                                    else True"
                using compPtr inDen Storeloc a20  a30 3  by blast
              then show ?thesis using subloc 2
              proof(cases "x2 = l''")
                case True
                then have stt:"struct = t''" using b40 
                  using CompStoType_sameLoc_sameType TypedStoSubpref_sameLoc by auto
                then show ?thesis 
                proof(cases "l'' = locationChanged")
                  case t4:True
                  then show ?thesis using  stt True scont' 
                    using "3"(3) CompStoType_sameLoc_sameType by blast
                next
                  case False
                  have c0:"CompStoType struct (STValue t') x2 locationChanged" using 3(3) True stt by simp
                  then have "\<exists>y. hash l'' y = locationChanged" using subloc 3(3) TypedStoSubpref_b False by auto
                  then obtain i'' where c1:"(hash x2 i'' = locationChanged)" using CompStoType_imps_subloc False True by blast
                  then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 by blast 
                qed
              next
                case x4Dif:False
                then show ?thesis
                proof(cases "TypedStoSubpref x2 l'' t''")
                  case d5:True
                  then have d7:"CompStoType t'' struct l'' x2" using b40 by simp
                  have d9:"CompStoType t'' (STValue t') l'' locationChanged" using 3(3) by simp
                  have d10:"CompStoType struct (STValue t') x2 locationChanged" using CompStoType_subloc_type_transfer[of t'' t' l'' locationChanged struct x2] subloc d7 d9 by blast
                  then have d11:"\<exists>x. hash l'' x = x2" using TypedStoSubpref_b x4Dif d5 by auto
                  then show ?thesis 
                  proof(cases "l'' = locationChanged")
                    case True
                    then obtain i'' where d11:"hash locationChanged i'' = x2" using d11 by auto
                    then show ?thesis using subloc using TypedStoSubpref_hashes by auto
                  next
                    case False
                    then have "\<exists>x. hash l'' x = locationChanged" using 3(3) TypedStoSubpref_b by auto
                    then have "\<exists>x. hash l'' x = x2" using d11 using hash_suffixes_associative by auto
                    then show ?thesis
                    proof(cases "x2 = locationChanged")
                      case True
                      then have "struct = (STValue t')" using d10 by (simp add: CompStoType_sameLoc_sameType)
                      then show ?thesis using True scont' by auto
                    next
                      case False
                      then obtain i'' where d11:"hash x2 i'' = locationChanged" 
                        using subloc False TypedStoSubpref_b[of locationChanged x2 struct] by blast
                      then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 d10 by blast
                    qed
                  qed
                next
                  case f5:False
                  then show ?thesis 
                  proof(cases "TypedStoSubpref l'' x2 struct")
                    case True
                    then have d5:"TypedStoSubpref l'' x2 struct" by simp
                    then have d7:"CompStoType struct t'' x2 l''" using b40 f5 by simp
                    then have d10:"\<exists>x. hash x2 x = l''" using TypedStoSubpref_b x4Dif d5 by auto
                    then show ?thesis 
                    proof(cases "l'' = locationChanged")
                      case True
                      then obtain i'' where d11:"hash x2 i'' = locationChanged" using d10 by auto
                      then have d15:"t'' = STValue t'" using 3(3) CompStoType_sameLoc_sameType True by auto
                      then have c0:"CompStoType struct (STValue t') x2 locationChanged" using 3(3) d15 d7 by fastforce
                      then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 d11 by blast 
                    next
                      case False
                      then have "\<exists>x. hash l'' x = locationChanged" using 3(3) TypedStoSubpref_b by auto
                      then have "\<exists>x. hash x2 x = locationChanged" using d10 using hash_suffixes_associative by auto
                      then obtain i'' where d11:"hash x2 i'' = locationChanged" by auto
                      then have "CompStoType struct (STValue t') x2 locationChanged" using CompStoType_trns 3(3)  d7 by blast
                      then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 by blast
                    qed                
                  next
                    case False
                    have "x2 \<noteq> locationChanged" using 3(3) f5 by blast
                    then show ?thesis using  a40 False f5 3(3) singleLocChanged_nonchanged_SCon 
                      using nonLocChanged by blast
                  qed   
                qed
              qed
            qed
          next
            case f1:False
            then show ?thesis using a40
            proof(induction struct arbitrary:x2)
              case (STArray x1 struct)
              have b10:"\<forall>i<x1. SCon struct (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st (Address env))" 
                using STArray(3) using SCon.simps(2)[of x1 struct x2 "(Storage st (Address env))"] by auto
              have b20:"\<forall>i<x1. \<not> TypedStoSubpref locationChanged (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct 
                                    \<and> locationChanged \<noteq> hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)" 
                using STArray(2) TypedStoSubpref.simps(2)[of locationChanged x2 x1 struct] 
                using TypedStoSubpref_sameLoc by auto
              then have b30:"\<forall>i<x1. \<not> TypedStoSubpref locationChanged (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct " by auto
              have " (\<forall>i<x1. SCon struct (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st' (Address env)))" 
              proof(intros)
                fix i assume b40: "i<x1"
                then have "\<not>TypedStoSubpref locationChanged (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct" using b30 by auto
                then show "SCon struct (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st' (Address env))" using STArray(1)[of "(hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b30 b10 b40 by simp
              qed
              then show ?case using SCon.simps(2)[of x1 struct x2 "Storage st' (Address env)"] by simp
            next
              case (STMap x1 struct)
              then have " (\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x2 i) (Storage st (Address env)))" using SCon.simps(3)[of x1 struct x2 "(Storage st (Address env))"] by simp
              moreover have "(\<forall>i. \<not>typeCon x1 i \<or> \<not>TypedStoSubpref locationChanged (hash x2 i) struct \<and> locationChanged \<noteq> hash x2 i)" 
                using STMap(2) TypedStoSubpref.simps(3)[of locationChanged x2 x1 struct] 
                using TypedStoSubpref_sameLoc by auto
              ultimately show ?case  using STMap(1) by auto
            next
              case (STValue x)
              then have c5:"(x2 \<noteq> locationChanged \<or> STValue t' \<noteq> STValue x)" using Subpref.simps(1)[of  x x2 "STValue t'" locationChanged] by auto
              then show ?case 
              proof(cases "x2 \<noteq> locationChanged")
                case True
                then have c10:"Storage st' (Address env) $$ x2 = Storage st (Address env) $$ x2" using subcase2 nonLocChanged by auto
                then have " SCon (STValue x) x2 (Storage st (Address env))" using STValue by blast
                then show ?thesis using c10 
                  by (simp add: accessStorage_def)
              next
                case False
                then have "x2 = locationChanged" by simp
                then have "STValue t' = STValue x" using subcase2  Storeloc  inDen lexpStorage[of env st cd lv g locationChanged t' g'] f1 2(1) a20 a30 
                  by (metis STValue.prems(1) TypedStoSubpref.simps(1))
                then show ?thesis using False c5 by auto
              qed
            qed
          qed
          then show ?thesis 
            using Storeloc a30 by auto
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using subcase2 by auto
    next 
      show "lessThanTopLocs cd" using 2 unfolding TypeSafe_def by simp
    next 
      have "Memory st = Memory st'" using subcase2(4) by simp
      then show "lessThanTopLocs (Memory st')" using 2 unfolding TypeSafe_def by simp
    next
      have "envAddressesWellFormed env" using 2 unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+

    next 
      show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using subcase2 by simp
    next 
      have "Accounts st'= Accounts st" using subcase2 by auto
      then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) subcase2(4) unfolding fullyInitialised_def updateStore_def accessStore_def by auto
    next 
      have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using subcase2(4) unfolding updateStore_def accessStore_def by auto
      show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
      proof intros
        fix t l ptr_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "(case t of
         MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
        moreover have "Memory st = Memory st'" using subcase2(4) by simp
        ultimately show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr) 
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          by metis
      qed
    next
      show "subPrefixStructuralConsistency (Memory st')"
        using 2(1) subcase2(4) unfolding TypeSafe_def by simp
    next
      show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def  using subcase2(4) by simp
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using subcase2 by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using subcase2 by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using subcase2 by simp
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using subcase2 by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using subcase2 by simp
    qed

  next
    case (3 v t g l t' g' v')
    have sameStack:"Stack st' = Stack st" using 3(4) by auto
    have sameStorage:"Storage st'  = Storage st " using 3 by auto
    have sameAccounts:"Accounts st = Accounts st'" using 3 by simp
    have temp:"TypeSafe env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd" 
      using 2(1) by simp
    have ttt:"fullyInitialised env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 2(3) unfolding fullyInitialised_def by simp
    show ?thesis 
    proof(cases rule:lexpIndexMem[OF 3(2) temp ttt])
      case lInfo:(1 x21 x22 tp tParent l' l'' prnt len' arr' i)

      have nonLocChanged:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs  (Memory st) = accessStore locs  (Memory st')" 
        using 3 unfolding updateStore_def accessStore_def by simp

      have TCsrc:"typeCon t (extractValueType (KValue v)) \<and> (\<exists>xx. KValue v = KValue xx)"
        using 2(1) 3(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KValue v" "Value t" g] 
        using 2(3) unfolding fullyInitialised_def
        by (auto split:type.splits if_splits )


      obtain len subT where tParentType:"tParent = MTArray len subT" using lInfo by blast
      then have compType:"CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len subT (MTValue t') l'' l" 
        and lsublocs:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = (MTValue t') \<and> MCon (MTArray len' arr') (Memory (st)) prnt" 
        and lsublocs3:"(prnt = l'' \<and> len = len' \<and> arr' = subT \<or> CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt)"
        using lInfo 3(3) by fastforce+

      then have lsublocs2:" CompMemType (Memory (st)) len' arr' (MTValue t') prnt l" 
        using 3(3) CompMemType.simps(2) by auto
      then have bb9:"\<forall>subT subloc. CompMemType (Memory (st)) len' arr' subT prnt subloc \<and> subloc = l
                                  \<longrightarrow> subT = (MTValue t')" 
        using CompMemTypeSameLocsSameType lsublocs by blast

      have mconPrnt:"MCon (MTArray len' (MTValue t')) (Memory st) prnt" using lsublocs by auto
      have ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'" using lsublocs by auto

      have t6:"(type.Memory tParent,  Stackloc l') |\<in>| fmran (Denvalue env)" using lInfo by blast
      have t7:" MCon (MTArray len subT) (Memory (st)) l''" using lInfo 
        using tParentType by auto
      then have mconlOld:"MCon (MTValue t') (Memory st) l" using 3(3) lInfo 
        using CompTypeRemainsMCon lsublocs lsublocs2 by blast
      have "MCon (MTArray len' arr') (Memory st) prnt" using lsublocs3 
        using lsublocs by blast
      then have mcPrntNew:"MCon (MTArray len' arr') (Memory st') prnt" 
      proof -
        have lenNotZero:"len' \<noteq> 0" using lsublocs by auto
        have prntNotL:"prnt \<noteq> l" using ldef 
          by (metis hash_inequality)
        then have p2:"(\<exists>p. accessStore prnt (Memory st') = Some (MPointer p)) \<or> accessStore prnt (Memory st') = None" 
          using mconPrnt lenNotZero nonLocChanged by simp
        have "\<forall>i<len'.
            (case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case arr' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon arr' (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case arr' of MTArray len' arr'a \<Rightarrow> MCon arr' (Memory st') loc2 | MTValue Types \<Rightarrow> False)) 
           " 
        proof(intros)
          fix i1 assume in1:"i1<len'"
          show "case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') of None \<Rightarrow> False 
          | Some (MValue val) \<Rightarrow> (case arr' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon arr' (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)))
          | Some (MPointer loc2) \<Rightarrow> (case arr' of MTArray len' arr'a \<Rightarrow> MCon arr' (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
          proof(cases "i1 = i")
            case True
            then have "(hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) = l" using ldef by simp
            then have ac:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = Some((MValue v'))" using 3 by simp
            have "MCon  (MTValue t') (Memory st) (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1))" 
              using \<open>hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1) = l\<close> lsublocs mconlOld by auto
            then have "typeCon t' v'" unfolding MCon.simps 
              by (metis "3"(3) TCsrc convertSame extractValueType.simps(1) typeSafeConvert)
            then show ?thesis 
              by (simp add: \<open>accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = Some (MValue v')\<close> lsublocs)
          next
            case False
            then have sameAC:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st)" using ldef nonLocChanged in1 
              by (metis Read_Show_nat'_id hash_never_equal_sufix)
            then obtain ptr where ptrDef:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st) = Some (MValue ptr)" using in1 
              using  lsublocs MCon_sub_MTVal_imps_val by blast
            then have ptrMC:"case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) of None \<Rightarrow> False | Some (MValue xa) \<Rightarrow> typeCon t' xa | Some (MPointer t) \<Rightarrow> False" 
              using in1 mconPrnt unfolding MCon.simps
              using lsublocs mconlOld MCon.simps(1) by blast
            then show ?thesis using sameAC 
              using in1 lsublocs ptrDef by force
          qed
        qed
        then show ?thesis using lenNotZero p2 by simp
      qed

      have "(type.Memory (MTArray len subT), Stackloc l') |\<in>| fmran (Denvalue env) \<and> accessStore l' (Stack st) = Some (KMemptr l'')"
        using lInfo(2,3,4) tParentType by simp


      have cmpO_imps_new:"\<forall>x11 x12 stl2 dt prnt.  CompMemType (Memory st) x11 x12 dt stl2 prnt
            \<longrightarrow> CompMemType (Memory st') x11 x12 dt stl2 prnt"
      proof intros
        fix x11 x12 stl2 dt prnt
        assume "CompMemType (Memory st) x11 x12 dt stl2 prnt"
        then show "CompMemType (Memory st') x11 x12 dt stl2 prnt"
        proof(induction x12 arbitrary:x11 stl2)
          case (MTArray x1 x12)
          then obtain ii ll where iiDef: "ii<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll) 
                    \<and> (ll = prnt \<and> MTArray x1 x12 = dt \<or> CompMemType (Memory st) x1 x12 dt ll prnt)" 
            unfolding CompMemType.simps by blast
          then show ?case 
          proof(cases "ll = prnt")
            case True
            then show ?thesis using MTArray.prems iiDef 
              by (metis MCon_sub_MTVal_imps_val MTArray.IH memoryvalue.distinct(1) lsublocs nonLocChanged option.inject CompMemType.simps(2))
          next
            case False
            then show ?thesis 
              by (metis MCon_sub_MTVal_imps_val MTArray.IH memoryvalue.distinct(1) iiDef lsublocs nonLocChanged option.inject CompMemType.simps(2))
          qed
        next
          case (MTValue x)
          then show ?case unfolding CompMemType.simps by simp
        qed

      qed

      have nToO_neg:"\<forall>x11 x12 stl2 prnt . \<not>TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<longrightarrow> \<not>TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
      proof intros
        fix x11 x12 stl2 prnt
        assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt" 
        show "\<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
        proof
          assume in2:"TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
          then show False using in1
          proof(induction x12 arbitrary:x11 stl2)
            case (MTArray x1 x12)
            then obtain ii ll where iiDef:"ii<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll) \<and> (ll = prnt \<or> TypedMemSubPrefPtrs (Memory st) x1 x12 ll prnt)" 
              unfolding TypedMemSubPrefPtrs.simps by blast
            then show ?case 
            proof(cases "ll = prnt")
              case True
              then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using iiDef mconlOld by auto
              then show ?thesis using True iiDef nonLocChanged 
                using MTArray.prems(2) by auto
            next
              case False
              then show ?thesis using MTArray iiDef 
                by (metis MCon_sub_MTVal_imps_val memoryvalue.distinct(1) lsublocs nonLocChanged option.inject TypedMemSubPrefPtrs.simps(2))
            qed
          next
            case (MTValue x)
            then show ?case by simp
          qed
        qed
      qed


      have nToO:"\<forall>len2 arr2 stl2 stl1. TypedMemSubPrefPtrs (Memory st') len2 arr2 stl2 stl1 \<longrightarrow> TypedMemSubPrefPtrs (Memory st) len2 arr2 stl2 stl1"
      proof intros
        fix len2 arr2 stl2 stl1
        assume "TypedMemSubPrefPtrs (Memory st') len2 arr2 stl2 stl1"
        then show "TypedMemSubPrefPtrs (Memory st) len2 arr2 stl2 stl1 "
        proof(induction arr2 arbitrary:len2 stl2)
          case (MTArray x1 arr2)
          then obtain ii ll where iidef:"ii<len2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll) \<and>
                                     (ll = stl1 \<or> TypedMemSubPrefPtrs (Memory st') x1 arr2 ll stl1)"
            unfolding TypedMemSubPrefPtrs.simps by auto
          then show ?case 
          proof(cases "ll = stl1")
            case True
            then show ?thesis 
              by (metis MCon_sub_MTVal_imps_val memoryvalue.distinct(1) iidef lsublocs mcPrntNew nonLocChanged option.inject TypedMemSubPrefPtrs.simps(2))
          next
            case False
            then show ?thesis 
              by (metis MCon_sub_MTVal_imps_val MTArray.IH memoryvalue.distinct(1) iidef lsublocs mcPrntNew nonLocChanged option.inject TypedMemSubPrefPtrs.simps(2))
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed


      have mcl:"MCon (MTValue t') (Memory st') l" using mconlOld 3(4) 
        using CompTypeRemainsMCon cmpO_imps_new lsublocs2 mcPrntNew by blast

      show ?thesis unfolding TypeSafe_def StateInvariant_def
      proof intros 
        show "AddressTypes (Accounts st')" using 2(1) 3 unfolding TypeSafe_def by simp
      next 
        show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
      next 
        have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
        then show "compPointers (Stack st') (Denvalue env)"  using sameStack  sameStorage by simp
      next 
        show "safeContract (Accounts st') (Storage st')" using sameStorage sameAccounts using 2(1) unfolding TypeSafe_def safeContract_def by auto
      next 
        show "balanceTypes (Accounts st')" using 3 using 2(1) unfolding TypeSafe_def by simp
      next 
        have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
      next 
        show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
      next 
        have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
          using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
        have **:"Toploc (Stack st) = Toploc (Stack st')" using 3 unfolding updateStore_def by auto
        show "lessThanTopLocs (Stack st')"  unfolding lessThanTopLocs_def
        proof intros

          fix tloc loc 
          assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
          then show "accessStore loc (Stack st') = None" using *  
            by (simp add: sameStack)
        next 
          fix loc y 
          assume h1:" accessStore loc (Stack st') = Some y"
          then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** * 
            by (metis sameStack)
        qed
      next 
        show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
      next
        have a12:"Toploc (Memory st) = Toploc (Memory st')" using 3 unfolding updateStore_def by auto
        have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
        have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
        show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def 
        proof intros
          fix tloc loc 
          assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then have b20:"Toploc (Memory st) \<le> tloc" using a12 tloc a12 
            by force

          then show "accessStore loc (Memory st') = None " 
            by (metis MCon_imps_Some a15 b10 lessThanSome_imps_Locs lessThanSome_imps_Locs2 lessThanTopLocs_def linorder_not_less mconlOld nonLocChanged)
        next 
          fix loc y 
          assume "accessStore loc (Memory st') = Some y "
          then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" 
            by (metis MConAccessSame.simps(1) SameMCon_imps_MConAccessSame a12 a15 lessThanTopLocs_def mconlOld nonLocChanged)
        qed
      next 
        show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
          unfolding typeCompat_def 
        proof intros
          fix tLook lLook
          assume inDen:" (tLook, lLook) |\<in>| fmran (Denvalue env)"
          show " case lLook of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case tLook of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case tLook of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case tLook of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case tLook of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case tLook of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
          proof(cases lLook)
            case (Stackloc x1)
            then show ?thesis 
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc by force
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1')
                then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some  by force
              next
                case (KCDptr x2)
                then show ?thesis  using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by force
              next
                case (KMemptr x3)
                then obtain struct where stT: "tLook = type.Memory struct" using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some 
                  by (cases tLook; fastforce)
                have structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
       | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
                  using 2(1) inDen KMemptr Some Stackloc stT 3(4)
                  unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
                then have structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))" 
                  by (metis (no_types, lifting) )
                have mcold:"MCon struct (Memory st) x3" using stT
                  by (metis "2.prems"(1) KMemptr Some Stackloc inDen sameMemTSafe sameStack)
                then have "MCon struct (Memory st') x3" using structss
                proof(induction struct arbitrary:x3)
                  case (MTArray x11 x12)
                  have oldexp:"(\<forall>i<x11.
                        case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) of None \<Rightarrow> False
                        | Some (MValue val) \<Rightarrow>
                            (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                        | Some (MPointer loc2) \<Rightarrow>
                            (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st) loc2 | MTValue val \<Rightarrow> False)) \<and>
                    (\<exists>p. accessStore x3 (Memory st) = Some (MPointer p) \<or> accessStore x3 (Memory st) = None)" 
                    using  MTArray.prems(1) unfolding MCon.simps by simp
                  then have notL:"x3 \<noteq> l" using lInfo(7) by auto
                  then have conc1:"(\<exists>p. accessStore x3 (Memory st') = Some (MPointer p) \<or> accessStore x3 (Memory st') = None)"
                    using 3(4) oldexp unfolding accessStore_def updateStore_def by simp

                  then have subs:"(\<forall>i<x11. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12)"
                    using structss MTArray by simp

                  have "(\<forall>i<x11.
                        case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                        | Some (MValue val) \<Rightarrow>
                            (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                        | Some (MPointer loc2) \<Rightarrow>
                            (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st') loc2 | MTValue val \<Rightarrow> False))"
                  proof(intros)
                    fix i assume idef:"i<x11"
                    then consider (val1) val typw where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue val) 
                                            \<and> x12 = MTValue typw 
                                            \<and> MCon x12 (Memory st)  (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
                      | (ptr1) ptr l1 a1 where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr) 
                                          \<and> x12 = MTArray l1 a1  
                                          \<and> MCon x12 (Memory st)  ptr"
                      using oldexp 
                      by (metis MCon_imps_sub_Mcon MTArray.prems(1) mtypes.distinct(1) gr_implies_not0 mcon_accessStore nat_neq_iff)
                    then show "case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
         | Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
         | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st') loc2 | MTValue val \<Rightarrow> False)"
                    proof(cases)
                      case val1
                      then show ?thesis 
                      proof(cases "(hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
                        case True
                        then have "x12 = (MTValue t')" using subs lInfo(6) idef by auto
                        then show ?thesis using 3(4) True 
                          unfolding updateStore_def accessStore_def using idef mcl by simp
                      next
                        case False
                        then have sameACC:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st')"
                          using 3(4)unfolding updateStore_def accessStore_def by simp
                        then have "MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
                          using val1 unfolding MCon.simps by auto
                        then show ?thesis using val1 sameACC by simp
                      qed
                    next
                      case ptr1
                      then have notl:"(hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> l" using mconlOld unfolding MCon.simps by auto

                      have " case x12 of MTArray len arr \<Rightarrow>
      (\<forall>i<len. accessTypeStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
    | MTValue val \<Rightarrow> accessTypeStore ptr (Memory st) = Some (MTValue val)" 
                        using 2(1) unfolding TypeSafe_def subPrefixStructuralConsistency_def using MTArray.prems
                        using ptr1 idef by fastforce
                      then have "MCon x12 (Memory st') ptr" 
                        using MTArray.IH[of ptr] ptr1 by blast
                      then show ?thesis using ptr1 notl 3(4) unfolding accessStore_def updateStore_def  by simp
                    qed
                  qed
                  then show ?case using conc1 MTArray.prems(1) unfolding MCon.simps by simp
                next
                  case (MTValue x2)
                  then show ?case
                  proof(cases "x3 = l")
                    case True
                    then have "x2 = t'" using lInfo(6) structss MTValue by simp
                    then show ?thesis using lInfo  MTValue True 
                      using CompTypeRemainsMCon cmpO_imps_new lsublocs2 mcPrntNew by blast
                  next
                    case False
                    then have "accessStore x3 (Memory st) = accessStore x3 (Memory st')"
                      using 3(4) unfolding updateStore_def accessStore_def by simp
                    then show ?thesis using mcold MTValue unfolding MCon.simps by simp
                  qed
                qed

                then show ?thesis using sameStorage inDen sameStack Stackloc Some KMemptr stT by simp
              next
                case (KStoptr x4)
                then show ?thesis  using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by (cases tLook; force)
              qed
            qed
          next
            case (Storeloc x2)
            then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen 
              by (metis denvalue.simps(6))
          qed
        qed
        then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using sameStack by auto
      next 
        have "Accounts st'= Accounts st" using 3 by auto
        then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) 3 unfolding fullyInitialised_def  by auto
      next 

        have sameStack:"Stack st = Stack st'" using 3 by simp
        have oldL:"\<exists>v''. accessStore l (Memory (st\<lparr>Gas := g\<rparr>)) = Some (MValue v'')" using lInfo 
          using MCon_sub_MTVal_imps_val by blast
      next 
        have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
          using 3(4) unfolding updateStore_def accessStore_def by auto
        have cc1:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
          using 3(4) unfolding updateStore_def accessTypeStore_def by simp
        show "denvalueTypeCorrectness env (Stack st') (Memory st')"
          unfolding denvalueTypeCorrectness_def  
        proof intros
          fix t l ptr_loc sub_loc
          assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
          then have old:"(
        (case t of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val)))"
            using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast

          then show "case t of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr) 
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"  

          proof(cases t)
            case (MTArray x11 x12)
            then have o2:" \<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12"
              using old by simp
            then have conc1:"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12)" using cc1 by simp
            then show ?thesis using MTArray cc1 old 3(4) by auto
          next
            case (MTValue x2)
            then show ?thesis using cc1 old by simp
          qed
        qed
      next 
        have cc1:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
          using 3(4) unfolding updateStore_def accessTypeStore_def by simp
        have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))" 
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
        show "SomeValSomeTyp (Memory st')" unfolding SomeValSomeTyp_def 
        proof intros
          fix locs
          show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
          proof(cases "locs = l")
            case True
            then have "accessStore locs (Memory st') = Some (MValue v')" 
              using 3 unfolding updateStore_def accessStore_def by simp
            moreover have "\<exists>v. accessStore locs (Memory st) = Some v "
              using mconlOld True old by auto
            ultimately show ?thesis using old cc1  by simp
          next
            case False
            then have "accessStore locs (Memory st) = accessStore locs (Memory st')"
              using 3 unfolding updateStore_def accessStore_def by simp
            then show ?thesis using cc1 old by metis
          qed
        qed

      next
        have old:"subPrefixStructuralConsistency (Memory st)"
          using 2(1) unfolding TypeSafe_def by blast
        show "subPrefixStructuralConsistency (Memory st')" 
          unfolding subPrefixStructuralConsistency_def
        proof intros
          fix locs tp
          assume in1:"accessTypeStore locs (Memory st') = Some tp"
          have allTyp:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using 3 unfolding updateStore_def accessTypeStore_def by auto
          have notNo:"accessStore locs (Memory st) \<noteq> None" 
          proof -
            have "accessTypeStore locs (Memory st) = Some tp"
              using in1 allTyp by simp
            then have "\<exists>v. accessStore locs (Memory st) = Some v"
              using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by simp
            then show ?thesis by simp
          qed
          then have old':"(case accessStore locs (Memory st) of  Some (MValue v) \<Rightarrow>
            \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
        | Some (MPointer p) \<Rightarrow>
            \<exists>len arr.
               MCon tp (Memory st) p \<and>
               tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr))" 
            using old in1 allTyp unfolding subPrefixStructuralConsistency_def by fastforce
          then consider (val) v val' where "accessStore locs (Memory st) = Some (MValue v) 
                                            \<and> MCon tp (Memory st) locs \<and> tp = MTValue val' 
                                            \<and> accessTypeStore locs (Memory st) = Some tp"
            | (ptr) p len arr where "accessStore locs (Memory st) = Some (MPointer p) \<and>
                                     MCon tp (Memory st) p \<and> tp = MTArray len arr \<and> 
                                     (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)"
            using notNo by (auto split:option.splits memoryvalue.splits)

          then show "case accessStore locs (Memory st') of None \<Rightarrow> False
       | Some (MValue v) \<Rightarrow>
           \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
       | Some (MPointer p) \<Rightarrow>
           \<exists>len arr.
              MCon tp (Memory st') p \<and>
              tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)" 
          proof(cases)
            case val
            then show ?thesis 
            proof(cases "locs = l")
              case True
              then have "tp = (MTValue t')" using lInfo(6) allTyp in1 by simp
              moreover have "\<exists>v''. accessStore locs (Memory st') = Some (MValue v'')" 
                using True mcl MCon_sub_MTVal_imps_val lsublocs mcPrntNew by presburger
              ultimately show ?thesis using mcl lInfo(6) allTyp val True by fastforce
            next
              case False
              then show ?thesis using val nonLocChanged allTyp by auto
            qed
          next
            case ptr
            then have notlLocs:"locs \<noteq> l" 
              using mconlOld by force
            have cc1:"(\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)" 
              using ptr allTyp by simp
            have "MCon (MTArray len arr) (Memory st) p" using ptr by blast

            then have "MCon (MTArray len arr) (Memory st') p" using cc1
            proof(induction arr arbitrary:len p)
              case (MTArray x11 x12)
              have oldexp:"(\<forall>i<len. \<exists>val.
         accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) =  Some (MPointer val) \<and>
             MCon (MTArray x11 x12) (Memory st) val)" 
                using  MTArray.prems(1) MCon.simps(2)[of len "MTArray x11 x12" "Memory st" p] 
                by (meson CompMemType.simps(2) CompTypeRemainsMCon MConArrayPointers)


              then have subs:"\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MTArray x11 x12)"
                using  MTArray by simp

              have "(\<forall>i<len. \<exists>val.
         accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') =  Some (MPointer val) \<and>
             (MCon (MTArray x11 x12) (Memory st') (val)))"
              proof(intros)
                fix i assume idef:"i<len"

                then show "\<exists>val. accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer val) \<and>
                            MCon (MTArray x11 x12) (Memory st') val" 
                proof(cases "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
                  case True
                  then show ?thesis using mconlOld oldexp idef by auto
                next
                  case False
                  then have sameACC:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st')"
                    using 3(4)unfolding updateStore_def accessStore_def by simp
                  then obtain val where mcc:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) =  Some (MPointer val) 
                                        \<and> MCon (MTArray x11 x12) (Memory st) val" 
                    using oldexp unfolding MCon.simps using idef by blast
                  then have "accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') =  Some (MPointer val) "
                    using sameACC by simp
                  have "\<forall>i<x11. accessTypeStore (hash val (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12" 
                    using 2(1) subs allTyp idef mcc unfolding TypeSafe_def subPrefixStructuralConsistency_def 
                    by force
                  then have "MCon (MTArray x11 x12) (Memory st') val" 
                    using MTArray.IH[of x11 val] mcc idef allTyp by simp
                  then show ?thesis using mcc sameACC idef oldexp by simp
                qed
              qed

              moreover have "(\<exists>p'. accessStore p (Memory st') = Some (MPointer p') \<or> accessStore p (Memory st') = None)"
              proof - 
                have "p \<noteq> l" using mconlOld MTArray.prems(1) MCon.simps(2)[of len _ "Memory st" p] by auto
                then show ?thesis using nonLocChanged MTArray.prems(1) MCon.simps(2)[of len _ "Memory st" p] by simp
              qed
              moreover have "0 < len" using MTArray.prems(1) MCon.simps(2)[of len _ "Memory st" p] by simp
              ultimately show ?case using nonLocChanged MCon.simps(2)[of len _ "Memory st'" p] by auto
            next
              case (MTValue x2)
              have oldexp:"(\<forall>i<len. \<exists>val.
         accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) =  Some (MValue val) \<and>
             (MCon (MTValue x2) (Memory st) (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))))" 
                using  MTValue.prems(1) MCon.simps(2)[of len "MTValue x2" "Memory st" p] 
                by (auto split:option.splits memoryvalue.splits mtypes.splits)

              then have subs:"\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MTValue x2)"
                using  MTValue by simp


              have "(\<forall>i<len. \<exists>val.
         accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') =  Some (MValue val) \<and>
             (MCon (MTValue x2) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))))"
              proof(intros)
                fix i assume idef:"i<len"

                then show "\<exists>val. accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MValue val) \<and>
                                 MCon (MTValue x2) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
                proof(cases "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
                  case True
                  then have "(MTValue x2) = (MTValue t')" using subs lInfo(6) idef allTyp by auto
                  then show ?thesis using 3(4) True 
                    unfolding updateStore_def accessStore_def using idef mcl by simp
                next
                  case False
                  then have sameACC:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st')"
                    using 3(4)unfolding updateStore_def accessStore_def by simp
                  then have "MCon (MTValue x2) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
                    using oldexp unfolding MCon.simps 
                    using idef by force
                  then show ?thesis using sameACC idef oldexp by metis
                qed
              qed

              moreover have "(\<exists>p'. accessStore p (Memory st') = Some (MPointer p') \<or> accessStore p (Memory st') = None)"
              proof - 
                have "p \<noteq> l" using mconlOld MTValue(1) MCon.simps(2)[of len "MTValue x2" "Memory st" p] by auto
                then show ?thesis using nonLocChanged MTValue(1) MCon.simps(2)[of len "MTValue x2" "Memory st" p] by simp
              qed
              moreover have "0 < len" using MTValue(1) MCon.simps(2)[of len "MTValue x2" "Memory st" p] by simp
              ultimately show ?case using nonLocChanged MCon.simps(2)[of len "MTValue x2" "Memory st'" p] by auto
            qed
            then show ?thesis using ptr nonLocChanged notlLocs allTyp by auto
          qed
        qed
      next 
        show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
          using 3(4) unfolding updateStore_def accessTypeStore_def by simp
      next 
        show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
          using 3(4)  
          by (metis MConAccessSame.simps(1) memoryvalue.distinct(1) SameMCon_imps_MConAccessSame mconlOld nonLocChanged option.inject)
      next
        show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
          by (metis MCon_sub_MTVal_imps_val lInfo(7) mcPrntNew nonLocChanged)
      next
        show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
          by (metis MCon_sub_MTVal_imps_val accessStore_def fmdom_notI fmlookup_dom_iff lsublocs nonLocChanged)
      next 
        have a12:"Toploc (Memory st) = Toploc (Memory st')" using 3 unfolding updateStore_def by auto
        then show "Toploc (Memory st) \<le> Toploc (Memory st')" by simp
      qed
    qed

  next
    case (4 p x t g l g' p' m t' st'')
    have nonChangedStack:"\<forall>loc. loc \<noteq> l \<longrightarrow> accessStore loc (Stack st) = accessStore loc (Stack st')" using 4 unfolding accessStore_def updateStore_def by auto
    have accessLStack:"accessStore l (Stack st') = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 4 unfolding accessStore_def updateStore_def by auto
    have sameStorage:"Storage st'  = Storage st " using 4 by auto
    have lInDen:"(type.Memory t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[of lv env cd _ _ l ] 4(2) by simp
    have nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
      using 4(6) unfolding cpm2m_def using  cpm2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]   cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd " (snd (allocate (Memory st)))" ]  
      by fastforce
    have a30:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
      using  4(6) unfolding cpm2m_def using cpm2mSingleChange2[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]  by fastforce
    have selfPoint:"\<forall>l l'. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l" 
      using  4(6) unfolding cpm2m_def using cpm2mSelfPointers[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ] by blast
    have mInStd:"m = Memory st'" using 4 by simp

    have p'MCon:"MCon t' (Memory st) p'" using 2 4(4) unfolding TypeSafe_def typeCompat_def using lInDen by (auto split:denvalue.splits option.splits stackvalue.splits type.splits)

    have MConsrc:"MCon (MTArray x t) cd (extractValueType (KCDptr p)) \<and> (\<exists>xx. KCDptr p = KCDptr xx) \<and> 
            (\<exists>stloc tp'' pa.
            (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KCDptr pa) \<and>
            (tp'' = (MTArray x t) \<and> KCDptr p = KCDptr pa \<or>
             (\<exists>len arr. extractValueType (KCDptr p) \<noteq> pa \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x t) pa (extractValueType (KCDptr p)))))"
      using 2(1) 4(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KCDptr p" "Calldata (MTArray x t)" g] 
        2(3) unfolding fullyInitialised_def by (auto split:type.splits if_splits )
    have "(\<exists>p. accessStore p' (Memory st) = Some (MPointer p)) \<or> accessStore p' (Memory st) = None" using p'MCon 4(3) 
      by (metis MCon.simps(2))
    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
    then have MCondest:" MCon (MTArray x t) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using  4(6) unfolding cpm2m_def
      using MCon_cpm2m[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] MConsrc extractValueType.simps(2) by metis
    have selfPoint2:"\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> accessStore l (Memory st') = Some (MPointer l') \<longrightarrow> l' = l" using selfPoint limitSt1 limitSt 
        "4"(6) a30 accessPrePost1 allocateSameAccess cpm2m_def eq_imp_le hash_inequality not_Some_eq 
      by (metis mInStd)

    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                            \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros 
      show "AddressTypes (Accounts st')" using 2(1) 4 unfolding TypeSafe_def by simp
    next 
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      show "compPointers (Stack st') (Denvalue env)"  unfolding compPointers_def
      proof(intros)
        fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
        then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
          using a0 nonChangedStack accessLStack sameStorage compPointers_def 
          by (smt (verit) stackvalue.distinct(11) compPointers_def option.inject)
      qed
    next 
      have "Accounts st = Accounts st'" using 4 by simp
      then show "safeContract (Accounts st') (Storage st')" using sameStorage using 2(1) unfolding TypeSafe_def safeContract_def by auto
    next 
      show "balanceTypes (Accounts st')" using 4 using 2(1) unfolding TypeSafe_def by simp
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 4 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')"  unfolding lessThanTopLocs_def
      proof intros

        fix tloc loc 
        assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
        then show "accessStore loc (Stack st') = None" using *  
          by (metis "4"(4) nonChangedStack not_None_eq)
      next 
        fix loc y 
        assume h1:" accessStore loc (Stack st') = Some y"
        then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** * 
          by (metis "4"(4) nonChangedStack)        
      qed
    next 
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      have a10:"Toploc (snd (allocate (Memory st))) = Toploc m" using cpm2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 4(6) mInStd unfolding cpm2m_def by fastforce
      have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
      have a20:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
        using 4(6) unfolding cpm2m_def using  cpm2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m ]   
          cpm2m_def[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd "(snd (allocate (Memory st)))" ] by fastforce
      then have a30: "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m" 
        by (metis allocateSameAccess)
      have st'IsM:"Memory st' = m" using 4 by simp
      have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
      show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def 
      proof intros
        fix tloc loc 
        assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have b20:"Toploc (Memory st) \<le> tloc" using a10 tloc st'IsM by simp
        have "\<not>LSubPrefL2 loc p'" 
        proof(rule ccontr)
          assume c10:"\<not> \<not> LSubPrefL2 loc p'"
          then have c20: "LSubPrefL2 loc p'" by simp
          then have c30:"LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using b10  MemLSubPrefTransitive by auto
          then show False
          proof -
            have "MCon t' (Memory st) p'" using 4(4) 2(1) unfolding TypeSafe_def typeCompat_def using lInDen by fastforce
            then obtain x i where c40: "accessStore p' (Memory st) = Some x \<or> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using MCon_imps_Some by blast
            then show ?thesis
            proof(cases "accessStore p' (Memory st) = Some x")
              case True
              then show ?thesis using lessThanSome_imps_Locs[of "(state.Memory st)" p' x tloc] c30 a15 b20 by simp
            next
              case False
              then have "accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using c40 by simp
              then show ?thesis using lessThanSome_imps_Locs2  c30 a15 b20 by fastforce
            qed
          qed
        qed
        then show "accessStore loc (Memory st') = None " using b10 b20 a20 a10 st'IsM a15 a30 
          by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive antisym_conv2 hash_inequality hash_suffixes_associative hashesIntSame lessThanTopLocs_def order_less_le_trans tloc)

      next 
        fix loc y 
        assume "accessStore loc (Memory st') = Some y "
        then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" 
          by (metis a10 a15 a30 lessThanTopLocs_def order_less_trans st'IsM tloc)
      qed
    next 
      show ns:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t'' l'
        assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"
        show " case l' of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t'' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t'' of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False )
              | Some (KMemptr stloc) \<Rightarrow> (case t'' of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t'' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t'' of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases l')
          case (Stackloc x1)
          then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using accessLStack nonChangedStack by fastforce
          then show ?thesis 
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(3) stackvalue.simps(17) option.inject)
          next
            case (KCDptr x2)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) accessLStack nonChangedStack unfolding TypeSafe_def  typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(7) stackvalue.simps(18) option.inject)
          next
            case (KMemptr x3)
            then have "\<exists>struct. t'' = type.Memory struct" 
            proof(cases "x1 = l")
              case True
              have "accessStore l (Stack st) = Some (KMemptr p')" using 4(4) by simp
              then show ?thesis using Stackloc adef  inDen Stackloc 2(1) KMemptr True unfolding TypeSafe_def typeCompat_def by (cases t'';force+) 
            next
              case False
              then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" using accessLStack nonChangedStack by simp
              then show ?thesis using Stackloc adef  inDen Stackloc 2(1) KMemptr unfolding TypeSafe_def typeCompat_def by (cases t'';force+) 
            qed
            then obtain struct where structdef:"t'' = type.Memory struct" by blast


            have "MCon struct (Memory st') x3" 
            proof(cases "x1 = l")
              case True
              then have "x3 = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 4 KMemptr adef unfolding accessStore_def updateStore_def by auto
              moreover have "(MTArray x t) = struct" 
                by (metis "2.prems"(1) "4"(3) Stackloc True type.inject(3) fst_conv inDen lInDen snd_conv TypeSafe_def
                    structdef unique_locations_def)
              ultimately show ?thesis using MCondest 4 Stackloc True inDen lInDen mInStd structdef by metis
            next
              case False
              then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" using accessLStack nonChangedStack by simp
              then have "accessStore x1 (Stack st) = Some (KMemptr x3)" using adef KMemptr by simp
              then have mgh:"MCon struct (Memory st) x3" using inDen KMemptr Stackloc adef structdef 2(1) unfolding TypeSafe_def typeCompat_def by force
              then show ?thesis using originalMConStillMCon[OF mgh limitSt ] mInStd allocateSameAccess a30  by (metis nonLocChanged)

            qed

            then show ?thesis  using structdef KMemptr Stackloc adef  inDen Stackloc 2(1) unfolding TypeSafe_def by simp

          next
            case (KStoptr x4)  
            then show ?thesis using Stackloc adef sameStorage  inDen Stackloc KStoptr 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def apply(cases t'') 
              apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(3) type.simps(17) lInDen old.prod.inject snd_eqD uniqueLocs)
              apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(7) type.simps(18) lInDen old.prod.inject snd_eqD uniqueLocs)

              apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(11) stackvalue.simps(20) type.simps(19) option.inject)

              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(11) type.simps(20) lInDen prod.inject snd_conv uniqueLocs)
          qed

        next
          case (Storeloc x2)
          then show ?thesis using sameStorage inDen 2(1) unfolding TypeSafe_def typeCompat_def by (cases t''; force)
        qed
      qed

    next 
      have accSame:"Accounts st'= Accounts st" using 4 by auto
      from "2.prems"(3) 
      obtain c_fi ct_fi dud_fi where fi:"
           Type (Accounts st (Address env)) = Some (atype.Contract c_fi) \<and>
           Contract env = c_fi \<and>
           ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
           (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id))) \<and>
           (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
           (\<forall>t'' l'' p''.
               (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st) = Some (KStoptr p'') \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''))"
        unfolding fullyInitialised_def by blast
      have fiPtrs':"\<forall>t'' l'' p''.
               (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st') = Some (KStoptr p'') \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p'')"
      proof (intro allI impI)
        fix t'' l'' p''
        assume in1:"(type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env)\<and>accessStore l'' (Stack st') = Some (KStoptr p'')"
        then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''"
          using 4 fi unfolding accessStore_def updateStore_def 
          by (metis "2.prems"(1) type.distinct(11) accessStore_def lInDen nonChangedStack prod.inject snd_eqD typeSafeUnique uniqueLocs)
      qed
      show "fullyInitialised env  (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fi fiPtrs' accSame by metis

    next 
      have a20':"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
        using 4(6) unfolding cpm2m_def using  cpm2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m ]   
          cpm2m_def[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd "(snd (allocate (Memory st)))" ] by fastforce
      then have a30': "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m" 
        by (metis allocateSameAccess)
      have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
      have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc (Memory st')" 
        using cpm2mTopLocSame 4(6) cpm2m_def mInStd MCondest 
        by (metis (no_types, lifting) MCon.simps(2))
    next 
      show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
      proof(intros)
        fix t2 l2 ptr_loc sub_loc
        assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"

        show "case t2 of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
 
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        proof(cases "ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
          case False
          then have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
            using nonChangedStack * 4(5) unfolding accessStore_def updateStore_def 
            by (metis stackvalue.inject(3) accessLStack accessStore_def option.inject)
          then have mcOld:"MCon t2 (Memory st) ptr_loc" using * by (metis "2.prems"(1) sameMemTSafe)
          then have old:"(case t2 of MTArray len arr \<Rightarrow>
 (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
            using sameACC 2(1) * unfolding TypeSafe_def denvalueTypeCorrectness_def by fastforce

          have inDenvalue:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env)" using * by simp
          have lims:"\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) ptr_loc"
            using typeSafe_noDenElementOverToploc_mem[OF 2(1) inDenvalue] * sameACC 
            using LSubPrefL2_def MemLSubPrefTransitive by metis

          then show ?thesis
          proof(cases t2)
            case (MTArray x11 x12)
            have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) 
                                          \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
              using lims mInStd 4(6) unfolding cpm2m_def 
              by (metis allocateTypeSameAccess cpm2mSingleChange_Typed cpm2m_def)
            have nonLocChanged_TypedSafe2:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) 
                                          \<longrightarrow> accessStore loc (Memory st') = accessStore loc (Memory st)"
              using lims mInStd 4(6) cpm2mSingleChange unfolding cpm2m_def 
              by (metis allocateSameAccess  cpm2m_def)
            have "\<forall>i. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
              using lims Mutual_NonSub_SpecificNonSub by blast
            then show ?thesis using old MTArray nonLocChanged_TypedSafe nonLocChanged_TypedSafe2 lims by simp
          next
            case (MTValue x2)
            have "\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using lims by simp
            then have "accessTypeStore ptr_loc (Memory st') = accessTypeStore ptr_loc (Memory st)"
              by (metis "4"(6) allocateTypeSameAccess cpm2mSingleChange_Typed cpm2m_def mInStd)
            then show ?thesis using MTValue old by simp
          qed
        next
          case True
          then have newLocation:"l2 = l \<and> t2 = (MTArray x t)"
            using lInDen accessLStack * 
            by (metis "2.prems"(1) "4"(3) LSubPrefL2_def Pair_inject type.inject(3) nonChangedStack snd_eqD typeSafeUnique typeSafe_noDenElementOverToploc_mem
                unique_locations_def)
          then have l2IsL:"l2 = l" using newLocation by simp
          then have conc0:"ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using * 4(5,7) by auto
          have conc1:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t" 
            using 4(6) unfolding cpm2m_def 
            using cpm2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m]
              mInStd by simp
          have nonLocChanged_TypedSafe2:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                          \<longrightarrow> accessStore loc (Memory st') = accessStore loc (Memory st)"
            using mInStd 4(6)  unfolding cpm2m_def 
            by (metis allocateSameAccess cpm2mSingleChange cpm2m_def)
          then show ?thesis using conc1 conc0 newLocation 
            using LSubPrefL2_def limitSt by fastforce

        qed
      qed
    next 
      have old:"subPrefixStructuralConsistency (Memory st)"
        using 2(1) unfolding TypeSafe_def by simp
      have none:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st) = None" 
        by (simp add: \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame)
      have lessT:"lessThanTopLocs (Memory st)" using 2(1) unfolding TypeSafe_def by simp
      have someV:"SomeValSomeTyp (Memory st)" 
        using 2(1) unfolding TypeSafe_def by simp
      have nonCha:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow>
             accessStore locs (Memory st) = accessStore locs (Memory st')" 
        using a30 allocateSame mInStd by presburger
      have index:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t" 
        using "4"(6) cpm2m_TypeCompChangeIndexs cpm2m_def mInStd by auto
      have subs:"\<forall>destl'.
     TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow>
     (\<exists>stt. CompMemType (Memory st') x t stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) destl' \<and>
            (case stt of
             MTArray parent_len parent_arr \<Rightarrow>
               \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' (Memory st') = Some (MTValue pval)))" 
        using cpm2m_TypeCompChange  "4"(6) cpm2m_def mInStd by simp
      have subT:"\<forall>locs.
       \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
       accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using "4"(6) mInStd unfolding cpm2m_def using cpm2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m] 
          allocateTypeSameAccess by metis
      have subT2:"\<forall>locs.
       \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
       accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using "4"(6) mInStd unfolding cpm2m_def using cpm2mSingleChange2_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m] 
          allocateTypeSameAccess by metis
      show "subPrefixStructuralConsistency (Memory st')"
        using cpm2m_subPrefixPersist[OF old none someV subT lessT subT2 subs _ _ index _ nonCha] MCondest mInStd selfPoint nonLocChanged 
        by (metis (no_types, lifting) "4"(6) allocateSame cpm2mSingleChange cpm2m_def)
    next 
      have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))" 
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      have somesome:"\<forall>destl'. TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow> (\<exists>t. accessStore destl' m = Some t) = (\<exists>tt. accessTypeStore destl' m = Some tt)"
        using 4(6) unfolding cpm2m_def using cpm2m_TypeCompChange_somesome[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 
        by simp
      have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')" 
        using  4(6) unfolding cpm2m_def using cpm2mSingleChange2_typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]  
          mInStd allocateTypeSameAccess by metis
      show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def 
      proof intros
        fix locs
        show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
        proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)")
          case True
          then have "(\<exists>t. accessStore locs m = Some t) = (\<exists>tt. accessTypeStore locs m = Some tt)" 
            using somesome by simp
          then show ?thesis using mInStd by simp
        next
          case False
          then have "accessStore locs (Memory st) = accessStore locs (Memory st')" 
            using a30 mInStd allocateSameAccess by metis
          moreover have "accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using a30T False by simp
          ultimately show ?thesis using old by metis
        qed
      qed
      fix locs t' 
      assume in1:"accessTypeStore locs (Memory st) = Some t'"
      show "accessTypeStore locs (Memory st') = Some t'"
      proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)")
        case True
        then show ?thesis using 2(1) in1 unfolding TypeSafe_def lessThanTopLocs_def 
          by (metis Suc_n_not_le_n neg_MemLSubPrefL2_imps_TypedMemSubPref not_less_eq_eq old option.distinct(1))
      next
        case False
        then show ?thesis using  in1 4(6) unfolding cpm2m_def using cpm2mSingleChange2_typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]  
            mInStd allocateTypeSameAccess by metis
      qed
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        by (metis allocateSameAccess limitSt mInStd nonLocChanged option.discI verit_comp_simplify1(2))
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        by (metis allocateSameAccess limitSt mInStd nonLocChanged option.distinct(1) order_eq_refl)
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"

        by (metis LSubPrefL2_def MemLSubPrefTransitive Read_Show_nat'_id allocateSame hash_flatten_right hash_inequality mInStd nat_less_le nonLocChanged)
    next 
      have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
      have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc (Memory st')" 
        using cpm2mTopLocSame 4(6) cpm2m_def mInStd MCondest 
        by (metis (no_types, lifting) MCon.simps(2))
      then show "Toploc (Memory st) \<le> Toploc (Memory st')" using tloc by simp
    qed
  next
    case (5 p x t g l t' g' p' s)
    obtain t''' where t''Def:"t' = STArray x t''' " using 5(4) 
      by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
    have sameStack:"(Stack st) = (Stack st')" using 5 unfolding accessStore_def updateStore_def by auto
    have sameMemory:"Memory st' = Memory st " using 5 by auto
    have lInDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" 
      using lexpStackloc_imps_inDen[of lv env cd ] 5(2) by simp
    have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs p' \<or> locs = p' \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s" 
      using 5(5) unfolding cpm2s_def using  cpm2sSingleChange[of p p' t cd "(Storage st (Address env))" x s]  
      by fastforce
    have a30:" \<forall>locs t' t''.
       cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t') \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s" 
      using  5(5) unfolding cpm2s_def using cpm2sSingleChange2[of p  "p'" t cd "(Storage st (Address env))" x s ]  by simp
    then have a35:"\<forall>locs t''. locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t''') \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))" 
      using 5 t''Def by auto
    have mInStd:"s = Storage st' (Address env)" using 5 by simp

    have p'MCon:"SCon t' p' (Storage st (Address env))" using 2 5 unfolding TypeSafe_def typeCompat_def using lInDen 
      by (auto split:denvalue.splits option.splits stackvalue.splits type.splits)

    have MConsrc:"MCon (MTArray x t) cd (extractValueType (KCDptr p)) \<and> (\<exists>xx. KCDptr p = KCDptr xx) \<and> 
            (\<exists>stloc tp'' pa.
            (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KCDptr pa) \<and>
            (tp'' = (MTArray x t) \<and> KCDptr p = KCDptr pa \<or>
             (\<exists>len arr. extractValueType (KCDptr p) \<noteq> pa \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x t) pa (extractValueType (KCDptr p)))))"
      using 2(1) 5(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KCDptr p" "Calldata (MTArray x t)" g] 
        2(3) unfolding fullyInitialised_def
      by (auto split:type.splits if_splits )

    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
    then have SCondest:"SCon (STArray x t''') p' s" using  5 unfolding cpm2s_def
      using MCon_cpm2s[of p p' t cd "(Storage st (Address env))" x s t'''] t''Def MConsrc extractValueType.simps(2) by metis
    then have SCondest2:"SCon (STArray x t''') p' (Storage st' (Address env))" 
      by (simp add: mInStd)
    then have SCondest3:"SCon t' p' (Storage st' (Address env))" 
      by (simp add: mInStd t''Def)

    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                            \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros 
      show "AddressTypes (Accounts st')" using 2(1) 5 unfolding TypeSafe_def by simp
    next 
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have a0:" compPointers (Stack st)  (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      show "compPointers (Stack st') (Denvalue env)"  unfolding compPointers_def 
      proof(intros)
        fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
        then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
        proof(cases "TypedStoSubpref stl2 stl1 tp1")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case f1:False
          then show ?thesis 
          proof(cases "TypedStoSubpref stl1 stl2 tp2")
            case True
            then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
          next
            case False
            then show ?thesis using f1 by simp
          qed
        qed
      qed
    next 
      have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp 
      show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
      proof intros
        fix e ct dud i tp
        assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
                 ep $$ Contract (e::environment) = Some (ct, dud) \<and>
                 ct $$ i = Some (Var tp)"
        show "SCon tp i (Storage st' (Address e))"
        proof (cases "Address e = Address env")
          case False
          then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 5 by simp
          moreover have "SCon tp i (Storage st (Address e))"
            using * scOld 5 unfolding safeContract_def 
            by fastforce
          ultimately show ?thesis by simp
        next
          case addrEq:True
          have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using * 5 by simp
          have epOld:"ep $$ Contract e = Some (ct, dud)"
            using * by simp
          have ctOld:"ct $$ i = Some (Var tp)"
            using * by simp
          have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
            using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
          have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
            using denI by (simp add: fmranI)
          have oldSConE:"SCon tp i (Storage st (Address e))"
            using scOld typedOld epOld ctOld unfolding safeContract_def by blast
          have oldSCon:"SCon tp i (Storage st (Address env))"
            using oldSConE addrEq by simp
          have cmpPtr:"(if TypedStoSubpref p' i tp then CompStoType tp t' i p'
                         else if TypedStoSubpref i p' t' then CompStoType t' tp p' i else True)"
            using 2(1) 5(3) inDenI lInDen t''Def unfolding TypeSafe_def compPointers_def by blast
          have newSCon:"SCon tp i (Storage st' (Address env))"
            using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
          show ?thesis using newSCon addrEq by simp
        qed
      qed
    next 
      show "balanceTypes (Accounts st')" using 5 using 2(1) unfolding TypeSafe_def by simp
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 5 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')"  using sameStack * ** unfolding lessThanTopLocs_def by auto
    next 
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def 
        by (simp add: limitSt limitSt1)
    next 
      show tcN:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def 
      proof intros
        fix t'' l'
        assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

        show "case l' of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t'' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t'' of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False )
                | Some (KMemptr stloc) \<Rightarrow> (case t'' of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t'' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t'' of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases l')
          case (Stackloc x1)
          then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
          then show ?thesis 
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack  unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
          next
            case (KCDptr x2)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def  typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
          next
            case (KMemptr x3)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
          next
            case (KStoptr x4)  
            then obtain struct where structDef: "t'' = type.Storage struct" using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
              by (cases t''; fastforce)

            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t'''), Stackloc l) |\<in>| fmran (Denvalue env) \<and>
              (l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4) \<or> l' = Storeloc x4) \<and>
              (accessStore l (Stack st) = Some (KStoptr p')) \<longrightarrow>
              (if TypedStoSubpref p' x4 struct then CompStoType struct  (STArray x t''') x4 p'
               else if TypedStoSubpref x4 p'  (STArray x t''') then CompStoType  (STArray x t''') struct p' x4 else True))" 
              using 2(1) 5(3) lInDen inDen Stackloc structDef KStoptr unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref p' x4 struct then CompStoType struct  (STArray x t''') x4 p'
             else if TypedStoSubpref x4 p'  (STArray x t''') then CompStoType  (STArray x t''') struct p' x4 else True)"
              using  5(3) lInDen inDen Stackloc structDef KStoptr  t''Def
              by (simp add: adef sameStack)

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Stackloc adef inDen Stackloc 2(1) sameStack structDef KStoptr 
              by fastforce

            have cmpStoPtr3:"(if TypedStoSubpref p' x4 struct then CompStoType struct t' x4 p'
              else if TypedStoSubpref x4 p' t' then CompStoType t' struct p' x4 else True)"
              using cmpStoPtr2 t''Def by blast
            have "SCon struct x4 (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpStoPtr3 SCondest2 SCondest3 SConx4Old t''Def a35] .
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack KStoptr structDef by simp
          qed

        next
          case (Storeloc x2)
          then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc  inDen  2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t'''), Stackloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Storeloc x2) \<and>
              (accessStore l (Stack st) = Some (KStoptr p')) \<longrightarrow>
              (if TypedStoSubpref p' x2 struct then CompStoType struct  (STArray x t''') x2 p'
               else if TypedStoSubpref x2 p'  (STArray x t''') then CompStoType  (STArray x t''') struct p' x2 else True)" 
            using 2(1) 5(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref p' x2 struct then CompStoType struct  (STArray x t''') x2 p'
               else if TypedStoSubpref x2 p'  (STArray x t''') then CompStoType  (STArray x t''') struct p' x2 else True)"
            using  5(3) lInDen inDen Storeloc structDef t''Def by (simp add: sameStack)

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
            by fastforce

          have cmpStoPtr3:"(if TypedStoSubpref p' x2 struct then CompStoType struct t' x2 p'
            else if TypedStoSubpref x2 p' t' then CompStoType t' struct p' x2 else True)"
            using cmpStoPtr2 t''Def by fastforce
          have "SCon struct x2 (Storage st' (Address env))"
            using SCon_update_array_subloc_cases[OF cmpStoPtr3 SCondest2 SCondest3 SConx4Old t''Def a35] .
          then show ?thesis using Storeloc  inDen  2(1) sameStack Storeloc structDef by simp
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd"
        using sameStack by auto

    next 

      have accSame:"Accounts st'= Accounts st" using 5 by auto
      from "2.prems"(3) 
      obtain c_fi ct_fi dud_fi where fi:"
           Type (Accounts st (Address env)) = Some (atype.Contract c_fi) \<and>
           Contract env = c_fi \<and>
           ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
           (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id))) \<and>
           (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
           (\<forall>t'' l'' p''.
               (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st) = Some (KStoptr p'') \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''))"
        unfolding fullyInitialised_def by blast
      have fiPtrs':"\<forall>t'' l'' p''.
               (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st') = Some (KStoptr p'') \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p'')"
      proof (intro allI impI)
        fix t'' l'' p''
        assume in1:"(type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env)\<and>accessStore l'' (Stack st') = Some (KStoptr p'')"
        then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''"
          using 5 fi unfolding accessStore_def updateStore_def 
          using "2.prems"(1) type.distinct(11) accessStore_def lInDen  prod.inject snd_eqD typeSafeUnique uniqueLocs
          by simp
      qed
      show "fullyInitialised env  (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fi fiPtrs' accSame by metis
    next
      have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using 5(6) unfolding updateStore_def accessStore_def by auto
      have sameMem:"Memory st = Memory st'" using 5(6) by simp
      show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
      proof intros
        fix t l ptr_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "(case t of
         MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
        then show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr) 
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          using sameMem by metis
      qed
    next
      have sameMem:"Memory st = Memory st'" using 5(6) by simp
      show "subPrefixStructuralConsistency (Memory st')"
        using 2(1) sameMem unfolding TypeSafe_def  by simp
    next
      show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 5(6) by simp
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t "
        using 5(6) by auto
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using 5(6) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using 5(6) by simp
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 5(6) by auto
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 5(6) by simp
    qed
  next
    case (6 p x t g l t' g' s)
    obtain t''' where t''Def:"t' = STArray x t''' " using 6(3) 
      by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
    have sameStack:"(Stack st) = (Stack st')" using 6 unfolding accessStore_def updateStore_def by auto
    have sameMemory:"Memory st' = Memory st " using 6 by auto
    have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s" 
      using 6(4) unfolding cpm2s_def using  cpm2sSingleChange[of p l t cd "(Storage st (Address env))" x s]  
      by fastforce
    have a30:" \<forall>locs t' t''.
       cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t') \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s" 
      using  6(4) unfolding cpm2s_def using cpm2sSingleChange2[of p  "l" t cd "(Storage st (Address env))" x s ]  by simp
    then have a35:"\<forall>locs t''. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t''') \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))" 
      using 6 t''Def by auto
    have mInStd:"s = Storage st' (Address env)" using 6 by simp

    have MConsrc:"MCon (MTArray x t) cd (extractValueType (KCDptr p)) \<and> (\<exists>xx. KCDptr p = KCDptr xx) \<and> 
            (\<exists>stloc tp'' pa.
            (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KCDptr pa) \<and>
            (tp'' = (MTArray x t) \<and> KCDptr p = KCDptr pa \<or>
             (\<exists>len arr. extractValueType (KCDptr p) \<noteq> pa \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x t) pa (extractValueType (KCDptr p)))))"
      using 2(1) 6(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KCDptr p" "Calldata (MTArray x t)" g] 
        2(3) unfolding fullyInitialised_def
      by (auto split:type.splits if_splits )

    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
    then have SCondest:"SCon (STArray x t''') l s" using  6 unfolding cpm2s_def
      using MCon_cpm2s[of p l t cd "(Storage st (Address env))" x s t'''] t''Def MConsrc extractValueType.simps(2) by metis
    then have SCondest2:"SCon (STArray x t''') l (Storage st' (Address env))" 
      by (simp add: mInStd)
    then have SCondest3:"SCon t' l (Storage st' (Address env))" 
      by (simp add: mInStd t''Def)

    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                            \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros 
      show "AddressTypes (Accounts st')" using 2(1) 6 unfolding TypeSafe_def by simp
    next 
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have a0:" compPointers (Stack st)  (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      show "compPointers (Stack st') (Denvalue env)"  unfolding compPointers_def 
      proof(intros)
        fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
        then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
        proof(cases "TypedStoSubpref stl2 stl1 tp1")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case f1:False
          then show ?thesis 
          proof(cases "TypedStoSubpref stl1 stl2 tp2")
            case True
            then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
          next
            case False
            then show ?thesis using f1 by simp
          qed
        qed
      qed
    next 
      have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp 
      show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
      proof intros
        fix e ct dud i tp
        assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
                 ep $$ Contract (e::environment) = Some (ct, dud) \<and>
                 ct $$ i = Some (Var tp)"
        show "SCon tp i (Storage st' (Address e))"
        proof (cases "Address e = Address env")
          case False
          then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 6 by simp
          moreover have "SCon tp i (Storage st (Address e))"
            using * scOld 6 unfolding safeContract_def by fastforce
          ultimately show ?thesis by simp
        next
          case addrEq:True
          have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using * 6 by simp
          have epOld:"ep $$ Contract e = Some (ct, dud)"
            using * by simp
          have ctOld:"ct $$ i = Some (Var tp)"
            using * by simp
          have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
            using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
          have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
            using denI by (simp add: fmranI)
          have oldSConE:"SCon tp i (Storage st (Address e))"
            using scOld typedOld epOld ctOld unfolding safeContract_def by blast
          have oldSCon:"SCon tp i (Storage st (Address env))"
            using oldSConE addrEq by simp
          have uniq:"unique_locations (Denvalue env)"
            using 2(1) typeSafeUnique by simp
          have epEnv:"ep $$ Contract env = Some (ct, dud)"
            using epOld addrEq 
            using "2.prems"(3) fullyInitialised_def typedOld by auto
          show ?thesis
          proof(cases rule:lexpStorageG[OF 2(1) 6(2) 2(3)])
            case lInDen:1
            have inDenL:"(type.Storage t', Storeloc l) |\<in>| fmran (Denvalue env)"
              using lInDen by simp
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using 2(1) 6(3) inDenI inDenL unfolding TypeSafe_def compPointers_def by blast
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          next
            case sub2:(2 l''' t)
            have inDenL:"(type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env)" using sub2 by simp
            have relL:"TypedStoSubpref l l''' t \<and> CompStoType t t' l''' l" using sub2 by simp
            show ?thesis
            proof(cases "i = l'''")
              case True
              have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage t, Storeloc l''')"
                using uniqueLocs[OF uniq inDenI inDenL] True by simp
              then have tpEq:"tp = t" by simp
              have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                            else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
                using relL tpEq True by simp
              have newSCon:"SCon tp i (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
              show ?thesis using newSCon addrEq by simp
            next
              case False
              have ctL:"ct $$ l''' = Some (Var t)"
                using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenL] .
              have nPrnt1:"\<not>TypedStoSubpref i l''' t"
                and nPrnt2:"\<not>TypedStoSubpref l''' i tp"
                using methodVarsNoPref False epOld ctOld ctL by blast+
              have n1:"\<not>TypedStoSubpref l i tp"
                using NotRelatedPrnt_imps_notRelatedChild[OF nPrnt1 nPrnt2] relL by blast
              have n2:"\<not>TypedStoSubpref i l t'"
                using NotReachablePrnt_imps_notReachableChild nPrnt1 nPrnt2 relL by blast
              have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                            else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
                using n1 n2 by simp
              have newSCon:"SCon tp i (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
              show ?thesis using newSCon addrEq by simp
            qed
          next
            case sub3:(3 l' t l'')
            have inDenStk:"(type.Storage t, Stackloc l'') |\<in>| fmran (Denvalue env)" using sub3 by simp
            have ptrL:"accessStore l'' (Stack st) = Some (KStoptr l')" using sub3 by simp
            have rel0:"TypedStoSubpref l l' t \<and> CompStoType t t' l' l" using sub3 by simp
            obtain tprnt lprnt where
                inDenPr:"(type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue env)"
              and compPr:"CompStoType tprnt t lprnt l'"
              using fiPtr_parent_from_fullyInitialised[OF 2(3) inDenStk ptrL] by blast
            have compPr2:"CompStoType tprnt t' lprnt l"
              using compPr rel0 CompStoType_trns by blast
            have relPr:"TypedStoSubpref l lprnt tprnt \<and> CompStoType tprnt t' lprnt l"
              using compPr2 CompStoType_imps_TypedStoSubpref by blast
            show ?thesis
            proof(cases "i = lprnt")
              case True
              have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage tprnt, Storeloc lprnt)"
                using uniqueLocs[OF uniq inDenI inDenPr] True by simp
              then have tpEq:"tp = tprnt" by simp
              have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                            else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
                using compPr2 tpEq True 
                by (metis True tpEq compPr2 relPr)
              have newSCon:"SCon tp i (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
              show ?thesis using newSCon addrEq by simp
            next
              case False
              have ctPr:"ct $$ lprnt = Some (Var tprnt)"
                using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenPr] .
              have nPrnt1:"\<not>TypedStoSubpref i lprnt tprnt"
                and nPrnt2:"\<not>TypedStoSubpref lprnt i tp"
                using methodVarsNoPref False epOld ctOld ctPr by blast+
              have n1:"\<not>TypedStoSubpref l i tp"
                using NotRelatedPrnt_imps_notRelatedChild[OF nPrnt1 nPrnt2] relPr by blast
              have n2:"\<not>TypedStoSubpref i l t'"
                using NotReachablePrnt_imps_notReachableChild nPrnt1 nPrnt2 relPr by blast
              have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                            else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
                using n1 n2 by simp
              have newSCon:"SCon tp i (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
              show ?thesis using newSCon addrEq by simp
            qed
          qed
        qed
      qed
    next 
      show "balanceTypes (Accounts st')" using 6 using 2(1) unfolding TypeSafe_def by simp
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 6 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')"  using sameStack * ** unfolding lessThanTopLocs_def by auto
    next 
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def 
        by (simp add: limitSt limitSt1)
    next 
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t'' l'
        assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

        show "case l' of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t'' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t'' of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False )
                | Some (KMemptr stloc) \<Rightarrow> (case t'' of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t'' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t'' of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases l')
          case (Stackloc x1)
          then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
          then show ?thesis 
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack  unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
          next
            case (KCDptr x2)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def  typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
          next
            case (KMemptr x3)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
          next
            case (KStoptr x4)  
            then obtain struct where structDef: "t'' = type.Storage struct" using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
              by (cases t''; fastforce)

            have "SCon struct x4 (Storage st' (Address env))" 
            proof(cases rule:lexpStorageG[OF 2(1) 6(2) 2(3)])
              case lInDen:1
              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage (STArray x t'''), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) 
                 \<longrightarrow>
                (if TypedStoSubpref l x4 struct then CompStoType struct  (STArray x t''') x4 l
                 else if TypedStoSubpref x4 l  (STArray x t''') then CompStoType  (STArray x t''') struct l x4 else True)" 
                using 2(1) 6(3) lInDen inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l x4 struct then CompStoType struct  (STArray x t''') x4 l
                 else if TypedStoSubpref x4 l  (STArray x t''') then CompStoType  (STArray x t''') struct l x4 else True)"
                using  6(3) lInDen inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce

              have cmpStoPtr3:"(if TypedStoSubpref l x4 struct then CompStoType struct t' x4 l
                else if TypedStoSubpref x4 l t' then CompStoType t' struct l x4 else True)"
                using cmpStoPtr2 t''Def by fastforce
              have "SCon struct x4 (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpStoPtr3 SCondest2 SCondest3 SConx4Old t''Def a35] .
              then show ?thesis by simp
            next
              case sub2:(2 l''' t)
              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) 
                 \<longrightarrow>
                (if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
                 else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)" 
                using 2(1) 6(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
                 else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
                using  6(3) sub2 inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce
              have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

              have "SCon struct x4 (Storage st' (Address env))" 
              proof(cases "TypedStoSubpref l''' x4 struct")
                case True
                then have "CompStoType struct t x4 l'''" using cmpStoPtr2 by simp
                then have "CompStoType struct (STArray x t''') x4 l" using sub2 
                  using CompStoType_trns t''Def by blast
                then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                  by blast
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref x4 l''' t")
                  case True
                  then have "l''' \<noteq> x4" using f1 
                    using TypedStoSubpref_sameLoc by auto
                  then show ?thesis 
                  proof(cases "l = x4")
                    case t5:True
                    then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                    moreover have "CompStoType t t' l''' x4" using t5 sub2 by auto
                    ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                      by simp
                    then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                  next
                    case False
                    then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def  True by simp                
                    then show ?thesis 
                    proof(cases "CompStoType t' struct l x4 ")
                      case True
                      then show ?thesis 
                        using SCon_imps_sublocs SCondest3 by blast
                    next
                      case False
                      then show ?thesis 
                        by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x4\<close> a35 scl''' sub2(2) t''Def)
                    qed
                  qed
                next
                  case False                                                             
                  then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
                  then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
                  have notSame:"x4 \<noteq> l" using False sub2 by blast
                  have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20  by blast
                  have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False sub2 t''Def asm10 asm20 by blast
                  show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
                qed
              qed

              then show ?thesis by simp
            next
              case sub3:(3 l''' t l'''')
              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t, Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) \<and> accessStore l'''' (Stack st) = Some (KStoptr l''')
                 \<longrightarrow>
                (if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
                 else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)" 
                using 2(1) 6(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
                 else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
                using  6(3) sub3 inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce
              have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def  using sub3 by fastforce

              have "SCon struct x4 (Storage st' (Address env))" 
              proof(cases "TypedStoSubpref l''' x4 struct")
                case True
                then have "CompStoType struct t x4 l'''" using cmpStoPtr2 by simp
                then have "CompStoType struct (STArray x t''') x4 l" using sub3 
                  using CompStoType_trns t''Def by blast
                then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                  by blast
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref x4 l''' t")
                  case True
                  then have "l''' \<noteq> x4" using f1 
                    using TypedStoSubpref_sameLoc by auto
                  then show ?thesis
                  proof(cases "l = x4")
                    case t5:True
                    then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                    moreover have "CompStoType t t' l''' x4" using t5 sub3 by auto
                    ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                      by simp
                    then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                  next
                    case False
                    then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def  True by simp                
                    then show ?thesis 
                    proof(cases "CompStoType t' struct l x4 ")
                      case True
                      then show ?thesis 
                        using SCon_imps_sublocs SCondest3 by blast
                    next
                      case False
                      then show ?thesis 
                        by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x4\<close> a35 scl''' sub3(3) t''Def)
                    qed
                  qed
                next
                  case False                                                             
                  then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                  then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                  have notSame:"x4 \<noteq> l" using False sub3 by blast
                  have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20  by blast
                  have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False sub3 t''Def asm10 asm20 by blast
                  show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
                qed
              qed
              then show ?thesis by simp
            qed
            then show ?thesis using Stackloc  inDen  2(1) sameStack KStoptr adef structDef by simp
          qed
        next
          case (Storeloc x2)
          then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc  inDen  2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have "SCon struct x2 (Storage st' (Address env))" 
          proof(cases rule:lexpStorageG[OF 2(1) 6(2) 2(3)])
            case lInDen:1
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t'''), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Storeloc x2) 
               \<longrightarrow>
              (if TypedStoSubpref l x2 struct then CompStoType struct  (STArray x t''') x2 l
               else if TypedStoSubpref x2 l  (STArray x t''') then CompStoType  (STArray x t''') struct l x2 else True)" 
              using 2(1) 6(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l x2 struct then CompStoType struct  (STArray x t''') x2 l
               else if TypedStoSubpref x2 l  (STArray x t''') then CompStoType  (STArray x t''') struct l x2 else True)"
              using  6(3) lInDen inDen Storeloc structDef t''Def sameStack by simp

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce

            have cmpStoPtr3:"(if TypedStoSubpref l x2 struct then CompStoType struct t' x2 l
              else if TypedStoSubpref x2 l t' then CompStoType t' struct l x2 else True)"
              using cmpStoPtr2 t''Def by fastforce
            have "SCon struct x2 (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpStoPtr3 SCondest2 SCondest3 SConx4Old t''Def a35] .
            then show ?thesis by simp
          next
            case sub2:(2 l''' t)
            have cmpStoPtr:"(
                (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env) )
                 \<longrightarrow>
                (if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
                 else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)" 
              using 2(1) 6(3) inDen  Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
                 else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
              using  6(3) sub2 inDen Storeloc  structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce
            have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

            have "SCon struct x2 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref l''' x2 struct")
              case True
              then have "CompStoType struct t x2 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t''') x2 l" using sub2 
                using CompStoType_trns t''Def by blast
              then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x2 l''' t")
                case True
                then have "l''' \<noteq> x2" using f1 
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x2")
                  case t5:True
                  then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                  moreover have "CompStoType t t' l''' x2" using t5 sub2 by auto
                  ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                    by simp
                  then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                next
                  case False
                  then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def  True by simp                
                  then show ?thesis 
                  proof(cases "CompStoType t' struct l x2 ")
                    case True
                    then show ?thesis 
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis 
                      by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x2\<close> a35 scl''' sub2(2) t''Def)
                  qed
                qed
              next
                case False                                                             
                then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
                then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x2 \<noteq> l" using False sub2 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20  by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False sub2 t''Def asm10 asm20 by blast
                show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
              qed
            qed

            then show ?thesis by simp
          next
            case sub3:(3 l''' t l'''')
            have cmpStoPtr:"(
                (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t, Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
                 accessStore l'''' (Stack st) = Some (KStoptr l'''))
                 \<longrightarrow>
                (if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
                 else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)" 
              using 2(1) 6(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
                 else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
              using  6(3) sub3 inDen Storeloc structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce
            have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

            have "SCon struct x2 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref l''' x2 struct")
              case True
              then have "CompStoType struct t x2 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t''') x2 l" using sub3 
                using CompStoType_trns t''Def by blast
              then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x2 l''' t")
                case True
                then have "l''' \<noteq> x2" using f1 
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x2")
                  case t5:True
                  then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                  moreover have "CompStoType t t' l''' x2" using t5 sub3 by auto
                  ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                    by simp
                  then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                next
                  case False
                  then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def  True by simp                
                  then show ?thesis 
                  proof(cases "CompStoType t' struct l x2 ")
                    case True
                    then show ?thesis 
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis 
                      by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x2\<close> a35 scl''' sub3(3) t''Def)
                  qed
                qed
              next
                case False                                                             
                then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x2 \<noteq> l" using False sub3 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20  by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False sub3 t''Def asm10 asm20 by blast
                show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
              qed
            qed
            then show ?thesis by simp
          qed


          then show ?thesis using Storeloc  inDen  2(1) sameStack Storeloc structDef by simp
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using sameStack by simp

    next 
      have "Accounts st'= Accounts st" using 6 by auto
      then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) 6 unfolding fullyInitialised_def  by auto
    next
      have ss:"Stack st = Stack st' \<and> Memory st = Memory st'" using 6 by simp
      have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using 6(5) unfolding updateStore_def accessStore_def by auto
      have sameMem:"Memory st = Memory st'" using 6(5) by simp
      show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
      proof intros
        fix t l ptr_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "(case t of
         MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
        then show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          using sameMem by metis
      qed
    next
      have sameMem:"Memory st = Memory st'" using 6(5) by simp
      show "subPrefixStructuralConsistency (Memory st')"
        using 2(1) sameMem unfolding TypeSafe_def by simp
    next
      show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 6(5) by auto
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 6(5) by auto
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using 6(5) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using 6(5) by simp
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using 6(5) by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 6(5) by auto
    qed

  next
    case (7 p x t g l t' g' m m')
    have temp:"TypeSafe env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd" 
      using 2(1) by simp
    have ttt:"fullyInitialised env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 2(3) unfolding fullyInitialised_def by simp
    then show ?thesis
    proof(cases rule:lexpIndexMem[OF 7(2) temp ttt])
      case lInfo:(1 x21 x22 tp tParent l' l'' prnt len' arr' i)
      have nonChangedStack:"\<forall>loc. loc \<noteq> l \<longrightarrow> accessStore loc (Stack st) = accessStore loc (Stack st')" using 7 unfolding accessStore_def updateStore_def by auto
      have sameStack:"(Stack st') = Stack st" using 7 unfolding accessStore_def updateStore_def by auto
      have sameStorage:"Storage st'  = Storage st " using 7 by auto
      have nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))\<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
        using 7(4) unfolding cpm2m_def using  cpm2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]   cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd " (snd (allocate (Memory st)))" ]  
        by fastforce
      have a30:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
        using  7(4) unfolding cpm2m_def using cpm2mSingleChange2[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]  by fastforce
      have a32:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m"  
        by (metis a30 allocateSameAccess)
      have selfPoint:"\<forall>l l'. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l \<and> l \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        using   7(4) unfolding cpm2m_def using cpm2mSelfPointers[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ] 
        by (metis LSubPrefL2_def hash_inequality hash_suffixes_associative TypedMemSubPref.simps(2) typedPrefix_imp_SubPref)

      have sameTypeAccess:" \<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))  \<longrightarrow>
       accessTypeStore locs (Memory st) = accessTypeStore locs m" 
        using  7(4) unfolding cpm2m_def 
        using cpm2mSingleChange_Typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]  
          allocateTypeSameAccess by metis

      have sameTypeAccess2:" \<forall>locs.  \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))  \<longrightarrow>
       accessTypeStore locs (Memory st) = accessTypeStore locs m" 
        using  7(4) unfolding cpm2m_def 
        using cpm2mSingleChange2_typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]  
          allocateTypeSameAccess by metis

      have mInStd:"m' = Memory st'" using 7 by simp
      have NonChangeM'm:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs m = accessStore locs m'" 
        using 7(5) unfolding accessStore_def updateStore_def by auto
      have NonChangeM'mT:"\<forall>locs. accessTypeStore locs m = accessTypeStore locs m'"
        using 7(5) unfolding accessStore_def updateStore_def accessTypeStore_def by auto
      then have nonLocChanged3:"\<forall>locs. locs \<noteq>l \<and> \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) 
                                \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
        using a32 mInStd NonChangeM'm by auto

      have accessL:"accessStore l m' = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 7(5) unfolding accessStore_def updateStore_def by auto

      have MConsrc:"MCon (MTArray x t) cd (extractValueType (KCDptr p)) \<and> (\<exists>xx. KCDptr p = KCDptr xx) \<and> 
            (\<exists>stloc tp'' pa.
            (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KCDptr pa) \<and>
            (tp'' = (MTArray x t) \<and> KCDptr p = KCDptr pa \<or>
             (\<exists>len arr. extractValueType (KCDptr p) \<noteq> pa \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x t) pa (extractValueType (KCDptr p)))))"
        using 2(1) 7(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KCDptr p" "Calldata (MTArray x t)" g] 
        using 2(3) unfolding fullyInitialised_def
        by (auto split:type.splits if_splits )

      have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" 
        using allocateSameAccess by blast
      ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
      then have MCondest:" MCon (MTArray x t) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 7(4) unfolding cpm2m_def
        using MCon_cpm2m[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 
          MConsrc extractValueType.simps(2) by metis
      have lIs:"\<exists>x. accessStore l (Memory st) = Some x" using lInfo by (auto split:option.splits)
      then have lOld:"\<exists>p. accessStore l (Memory st) = Some (MPointer p)" using lInfo 7 by force
      then have l_not_toploc_orSub:"\<not>LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        using limitSt by fastforce 
      then have lOld2:"\<exists>p. accessStore l m = Some (MPointer p)" using lOld 
        by (simp add: allocateSame nonLocChanged)


      have tps:"\<forall>destl'.
     TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow>
     (\<exists>stt. CompMemType m x t stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) destl' \<and>
           (case stt of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
            | MTValue pval \<Rightarrow> accessTypeStore destl' m = Some (MTValue pval)))" 
        using 7(4) unfolding cpm2m_def
        using cpm2m_TypeCompChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m]  by simp

      have tps2:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some t"
        using 7(4) unfolding cpm2m_def
        using cpm2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 
        by blast

      have selfPoint2:"\<forall>l1 l2. LSubPrefL2 l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) 
                        \<and> accessStore l1 (Memory st') = Some (MPointer l2) \<longrightarrow> l2 = l1 \<and> l1 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        by (metis NonChangeM'm a30 allocateSame l_not_toploc_orSub limitSt linorder_le_cases mInStd option.distinct(1)
            selfPoint)

      obtain len subT where tParentType:"tParent = MTArray len subT" using lInfo by blast
      then obtain p'' where lOrigin:"accessStore l (Memory (st)) = Some (MPointer p'')" 
        and  compType:"CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len subT (MTArray x t) l'' p''" 
        and lsublocs:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = (MTArray x t) \<and> MCon (MTArray len' arr') (Memory (st)) prnt" 
        and lsublocs3:"(prnt = l'' \<and> len = len' \<and> arr' = subT \<or> CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt)"
        using lInfo 7(3) by force
      then have lsublocs2:" CompMemType (Memory (st)) len' arr' (MTArray x t) prnt p''" 
        using "7"(3) CompMemType.simps(2) by blast

      then have bb9:"\<forall>subT subloc. CompMemType (Memory (st)) len' arr' subT prnt subloc \<and> subloc = p''
                                  \<longrightarrow> subT = (MTArray x t)" 
        using CompMemTypeSameLocsSameType lsublocs by blast

      have mconPrnt:"MCon (MTArray len' (MTArray x t)) (Memory st) prnt" using lsublocs by auto
      have ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'" using lsublocs by auto

      have t6:"(type.Memory tParent,  Stackloc l') |\<in>| fmran (Denvalue env)" using lInfo by blast
      have t7:" MCon (MTArray len subT) (Memory (st)) l''" using lInfo 
        using tParentType by auto
      then have t8:"\<not> LSubPrefL2 l'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt limitSt1 typeSafe_noDenElementOverToploc_mem[OF 2(1) t6] lInfo(3) by simp
      have comptype2:"CompMemType m len subT (MTArray x t) l'' p''" using 
          cpm2mCompMemTypeOld_imps_CompMemType[of "(Memory (st\<lparr>Gas := g\<rparr>))" len subT "(MTArray x t)" l'' p'' "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" m ] 
          compType nonLocChanged limitSt t7 t8 allocateSame by auto
      have t10:"CompMemType (Memory st) len subT (MTArray x t) l'' p''"
        using 
          cpm2mCompMemTypeOld_imps_CompMemType[of "(Memory (st\<lparr>Gas := g\<rparr>))" len subT "(MTArray x t)" l'' p'' "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" m ] 
          compType nonLocChanged limitSt t7 t8 allocateSame by auto
      then have mconlOld:"MCon (MTArray x t) (Memory st) p''" using 7(3) lInfo lOrigin by force

      have den:"(type.Memory (MTArray len subT), Stackloc l') |\<in>| fmran (Denvalue env)
              \<and> accessStore l' (Stack st) = Some (KMemptr l'')" using lInfo tParentType by simp
      have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                          \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
      proof -
        have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs m"
          using 7(4,5,6) cpm2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
            cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd " (snd (allocate (Memory st)))" ] by simp
        then have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs m'"
          using 7(6,5) unfolding accessTypeStore_def updateStore_def by force
        then show "\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
          using allocateTypeSameAccess mInStd by metis
      qed


      have nonLocChanged2:"\<forall>locs. locs \<noteq> l \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')" 
        using 7 nonLocChanged LSubPrefL2_def NonChangeM'm mInStd allocateSame by metis
      have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                          \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto
      have MCondest2:" MCon (MTArray x t) (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) " using 7 MCondest 
        by (smt (verit, best) LSubPrefL2_def MemLSubPrefTransitive NonChangeM'm MCon_mem_preserved_disjoint_update l_not_toploc_orSub mInStd selfPoint)
      have bb:"\<forall>locs tp. CompMemType (Memory st) len subT tp l'' locs \<longrightarrow> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      proof intros
        fix locs tp 
        assume asm1:"CompMemType (Memory st) len subT tp l'' locs"
        then have a2:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using t7
        proof(induction subT arbitrary:len l'')
          case (MTArray x1 subT)
          then show ?case 
            using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def limitSt limitSt1 subPtrs_nonTop by blast
        next
          case (MTValue x)
          then show ?case 
            by (metis (no_types, lifting) CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def limitSt limitSt1 subPtrs_nonTop)
        qed
        then show " locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" by simp
        show "\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) " using a2 by simp
      qed

      have nonLocChanged22:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) 
                            \<longrightarrow> accessStore locs (Memory st) = accessStore locs m" using nonLocChanged 
        by (simp add: allocateSame)

      have prntMconNew:"MCon (MTArray len' (MTArray x t)) (Memory st') prnt"
      proof - 
        have " \<forall>i<len'.
             (case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x t) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x t of MTArray len' arr' \<Rightarrow> MCon (MTArray x t) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
        proof intros
          fix i' assume asm1:"i'<len'"
          then obtain ptr where ptrDef': "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some(MPointer ptr)
                                  " and ptrDef'2:"MCon (MTArray x t) (Memory st) ptr"
            using mconPrnt by (metis MConArrayPointers MCon_imps_sub_Mcon bot_nat_0.not_eq_extremum not_less_zero)

          show "case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x t) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x t of MTArray len' arr' \<Rightarrow> MCon (MTArray x t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)" 
          proof(cases "i' = i")
            case True
            then show ?thesis 
              using MCondest2 accessL ldef mInStd by force
          next
            case False
            then have "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st')" using ldef 
              by (metis hashesIntSame limitSt nle_le nonLocChanged2 option.distinct(1) ptrDef')
            then have same:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st') =  Some(MPointer ptr)" using ptrDef' by simp
            have notPrnt:"ptr \<noteq> prnt" 
              using MConSubTypes mconPrnt ptrDef' CompMemJustType.simps(2) ptrDef'2 by blast

            have locRule:"\<forall>ct locs ints. CompMemType (Memory st) len' (MTArray x t) ct prnt locs \<longrightarrow> locs \<noteq> prnt \<and> hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t ints) \<noteq> l"  
              using BothMConImpsNotCompMemType CompTypeRemainsMCon mconPrnt ldef  ShowLNatDot hash_injective by metis
            have "CompMemType (Memory st) len' (MTArray x t) (MTArray x t)  prnt ptr" using ptrDef' asm1 by auto
            then have "MCon (MTArray x t) (Memory st') ptr" using ptrDef'2 locRule 
            proof(induction t arbitrary: x ptr len' prnt)
              case (MTArray x11 x12)
              have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTArray x11 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x11 x12) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTArray x11 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x11 x12) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
              proof intros
                fix i'' assume "i''<x"
                then obtain ptr' where ptr'Def:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st) = Some(MPointer ptr')
                                                \<and> MCon (MTArray x11 x12) (Memory st) ptr'" using  MTArray.prems(2)
                  by (metis MConArrayPointers MCon_imps_sub_Mcon  neq0_conv not_less_zero)
                have "ptr \<noteq> prnt" using MTArray.prems by blast
                then have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems ShowLNatDot hash_injective by blast
                then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st) = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st')" 
                  by (metis less_or_eq_imp_le limitSt nonLocChanged2 option.discI ptr'Def)
                then have same2:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some(MPointer ptr')" using ptr'Def by simp

                have "MCon (MTArray x11 x12) (Memory st) ptr'" using ptr'Def by blast
                moreover have "CompMemType (Memory st) x (MTArray x11 x12) (MTArray x11 x12) ptr ptr'" using ptr'Def 
                  using \<open>i'' < x\<close> by auto
                moreover have "\<forall>ct locs ints. CompMemType (Memory st) x (MTArray x11 x12) ct ptr locs \<longrightarrow> locs \<noteq> ptr \<and> hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t ints) \<noteq> l" 
                  by (metis BothMConImpsNotCompMemType CompTypeRemainsMCon MTArray.prems(1,2,3) compMemTypes_trns)
                ultimately have "MCon (MTArray x11 x12) (Memory st') ptr'" using MTArray.IH[of x x11 ptr ptr'] by blast
                then show "(case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTArray x11 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x11 x12) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
               | Some (MPointer loc2) \<Rightarrow> (case MTArray x11 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x11 x12) (Memory st') loc2 | MTValue Types \<Rightarrow> False))" 
                  using ptrDef' same2 by auto
              qed

              moreover have xNotZero:"x>0" using MTArray.prems(2) 
                using bot_nat_0.not_eq_extremum by fastforce
              moreover have "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
              proof(cases "ptr = l")
                case True
                then have " accessStore ptr (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 7 by auto
                then show ?thesis by blast
              next
                case False
                then have pdef:"(\<exists>p. accessStore ptr (Memory st) = Some (MPointer p)) \<or> accessStore ptr (Memory st) = None" 
                  using MTArray.prems(2) MCon.simps(2)[of x _ "Memory st" ptr] xNotZero by simp
                then have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt1 limitSt 
                  by (metis (no_types, lifting) MCon_imps_Some MTArray.prems(2) LSubPrefL2_def Not_Sub_More_Specific le_refl option.distinct(1))
                then have "accessStore ptr (Memory st) =accessStore ptr (Memory st') " using False nonLocChanged2 by simp
                then show ?thesis using pdef by simp
              qed
              ultimately show ?case using MCon.simps(2)[of x "MTArray x11 x12" "Memory st'" ptr]  by simp
            next
              case (MTValue x2)
              have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case MTValue x2 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x2) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x2 of MTArray len' arr' \<Rightarrow> MCon (MTValue x2) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
              proof intros
                fix i'' assume "i''<x"
                then obtain val where oldDef:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st) = Some(MValue val)
                                                \<and> MCon (MTValue x2) (Memory st) (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))" using MTValue ptrDef' 
                  by (meson MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
                have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l " using MTValue ldef ShowLNatDot hash_injective by blast
                then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st) = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st')" 
                  by (metis less_or_eq_imp_le limitSt nonLocChanged2 option.discI oldDef)
                then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some(MValue val)" using oldDef by simp
                then show "case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
                       | Some (MValue val) \<Rightarrow> (case MTValue x2 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x2) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
                       | Some (MPointer loc2) \<Rightarrow> (case MTValue x2 of MTArray len' arr' \<Rightarrow> MCon (MTValue x2) (Memory st') loc2 | MTValue Types \<Rightarrow> False)" 
                  using oldDef by auto
              qed
              moreover have xNotZero:"x>0" using MTValue(2) 
                using bot_nat_0.not_eq_extremum by fastforce
              moreover have "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
              proof(cases "ptr = l")
                case True
                then have " accessStore ptr (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 7 by auto
                then show ?thesis by blast
              next
                case False
                then have pdef:"(\<exists>p. accessStore ptr (Memory st) = Some (MPointer p)) \<or> accessStore ptr (Memory st) = None" 
                  using MTValue(2) MCon.simps(2)[of x _ "Memory st" ptr] xNotZero by simp
                then have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt1 limitSt 
                  by (metis (no_types, lifting) MCon_imps_Some MTValue(2) LSubPrefL2_def Not_Sub_More_Specific le_refl option.distinct(1))
                then have "accessStore ptr (Memory st) =accessStore ptr (Memory st') " using False nonLocChanged2 by simp
                then show ?thesis using pdef by simp
              qed

              ultimately show ?case using MCon.simps(2)[of x "MTValue x2" "Memory st'" ptr] by simp
            qed
            then show ?thesis using same asm1 by simp
          qed
        qed

        moreover have "len' > 0" using mconPrnt 
          using ldef by auto
        moreover have "prnt \<noteq> l" using ldef 
          by (metis hash_inequality)
        moreover have "(\<exists>p. accessStore prnt (Memory st') = Some (MPointer p)) \<or> accessStore prnt (Memory st') = None"
        proof(cases "LSubPrefL2 prnt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
          case True
          then show ?thesis 
            by (metis LSubPrefL2_def Not_Sub_More_Specific l_not_toploc_orSub ldef)
        next
          case False
          then show ?thesis using nonLocChanged2 calculation mconPrnt by simp
        qed
        ultimately show ?thesis using MCon.simps(2)[of len' "MTArray x t" "Memory st'" prnt] mconPrnt  nonLocChanged2 ldef by simp
      qed


      then have l''Top'':"CompMemType (Memory (st)) len subT (MTArray x t) l'' p''" using  lsublocs3 lsublocs 
        using compMemTypes_trns lsublocs2 by blast


      have aaa:"\<forall>sT sL. CompMemType (Memory (st)) len subT sT l'' sL \<and> sL \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 sL (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> MCon (MTArray len subT) (Memory (st)) l''
                            \<longrightarrow>  CompMemType m len subT sT l'' sL"
      proof(intros)
        fix sT sL
        assume asm1: " CompMemType (Memory st) len subT sT l'' sL \<and> sL \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 sL (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> MCon (MTArray len subT) (Memory (st)) l''"
        then show " CompMemType m len subT sT l'' sL"
        proof(induction subT arbitrary: len l'')
          case (MTArray x1 subT)
          obtain i'' ptr where i''Def:"(i''<len \<and> accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some (MPointer ptr) \<and> (ptr = sL \<and> MTArray x1 subT = sT \<or> CompMemType (Memory st) x1 subT sT ptr sL))"
            using MTArray.prems unfolding CompMemType.simps by auto
          then have "accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m" using MTArray.prems 
            by (metis Read_Show_nat'_id antisym_conv1 limitSt nonLocChanged22 option.distinct(1) readLintNotEqual)

          then show ?case 
          proof(cases "ptr = sL")
            case True
            then have "MTArray x1 subT = sT" using i''Def MTArray.prems 
              by (meson BothMConImpsNotCompMemType CompTypeRemainsMCon MCon_imps_sub_Mcon)
            then show ?thesis using True i''Def 
              using \<open>accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m\<close> by force
          next
            case False
            then have "CompMemType m x1 subT sT ptr sL" using MTArray.IH[of x1 ptr] using i''Def MTArray.prems by force
            then show ?thesis 
              by (metis \<open>accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m\<close> i''Def CompMemType.simps(2))
          qed
        next
          case (MTValue x)
          then show ?case 
            by auto
        qed
      qed


      have BT3:"\<forall>locs tp x t. \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> \<not>CompMemType (Memory (st')) x t tp (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) locs 
                                                                    \<and> \<not>TypedMemSubPrefPtrs (Memory (st')) x t (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) locs" 
        using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def SubPtrs_top selfPoint2 by blast

      have accessLGen:"\<exists>ptr. accessStore l (Memory st') = Some (MPointer ptr) 
                      \<and> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> MCon (MTArray x t) (Memory st') ptr " 
        using MCondest2 accessL  mInStd
        by (simp add: LSubPrefL2_def )

      

      have notTopSublocs_inv:"\<forall>dloc1 x11 x12 stl1 i. \<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> TypedMemSubPrefPtrs (Memory st') x11 x12 stl1 dloc1
                            \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x11 x12 stl1 dloc1"
      proof intros
        fix dloc1 x11 x12 stl1
        assume "\<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> TypedMemSubPrefPtrs (Memory st') x11 x12 stl1 dloc1"
        then have asm3:"\<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
          and asm4:"TypedMemSubPrefPtrs (Memory st') x11 x12 stl1 dloc1" by simp+
        show "TypedMemSubPrefPtrs (Memory st) x11 x12 stl1 dloc1 " using asm3 asm4
        proof(induction x12 arbitrary:x11 stl1)
          case (MTArray x1 x12)
          obtain i'' ptr where ptrDef:"i''<x11 \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some (MPointer ptr)
                    \<and> (ptr = dloc1 \<or> TypedMemSubPrefPtrs (Memory st') x1 x12 ptr dloc1)"
            using MTArray.prems(2) unfolding TypedMemSubPrefPtrs.simps by auto
          then have notl:"(hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using  MTArray.prems(1)
            by (metis BT3 LSubPrefL2_def memoryvalue.inject(2) accessL mInStd option.inject)
          have notSub:"\<not>LSubPrefL2 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
            using SubPtrs_top asm3 ptrDef selfPoint2 by blast
          have sameAccess:"accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st)"
            using notl notSub nonLocChanged2 by auto
          then show ?case
          proof(cases "ptr = dloc1")
            case True
            then show ?thesis using sameAccess ptrDef by force
          next
            case False
            then show ?thesis using MTArray.IH sameAccess ptrDef
              by (metis asm3 TypedMemSubPrefPtrs.simps(2))
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have subPrefM:"subPrefixStructuralConsistency (m)"
        using cpm2m_subPrefixPersist[OF _ _ _ sameTypeAccess _ sameTypeAccess2  tps MCondest] 
          \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame
          nonLocChanged a32 tps2 selfPoint 2(1) unfolding TypeSafe_def by metis


      show ?thesis unfolding TypeSafe_def StateInvariant_def
      proof intros 
        show "AddressTypes (Accounts st')" using 2(1) 7 unfolding TypeSafe_def by simp
      next 
        show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
      next 
        have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
        then show "compPointers (Stack st')  (Denvalue env)"  using sameStack  sameStorage by simp
      next 
        show "safeContract (Accounts st') (Storage st')" using sameStorage 7 using 2(1) unfolding TypeSafe_def safeContract_def by auto
      next 
        show "balanceTypes (Accounts st')" using 7 using 2(1) unfolding TypeSafe_def by simp
      next 
        have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
      next 
        show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
      next 
        have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
          using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
        have **:"Toploc (Stack st) = Toploc (Stack st')" using 7 unfolding updateStore_def by auto
        show "lessThanTopLocs (Stack st')"  unfolding lessThanTopLocs_def
        proof intros

          fix tloc loc 
          assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
          then show "accessStore loc (Stack st') = None" using *  
            by (simp add: sameStack)
        next 
          fix loc y 
          assume h1:" accessStore loc (Stack st') = Some y"
          then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** * 
            by (metis sameStack)
        qed
      next 
        show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
      next
        have a10:"Toploc (snd (allocate (Memory st))) = Toploc m" 
          using cpm2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 7(4) mInStd unfolding cpm2m_def by fastforce
        then have a12:"Toploc m = Toploc m'" using 7(5) unfolding updateStore_def by auto
        have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
        have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
        show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def 
        proof intros
          fix tloc loc 
          assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then have b20:"Toploc (Memory st) \<le> tloc" using a10 tloc a12 
            using mInStd by force

          then show "accessStore loc (Memory st') = None " 
            by (metis (no_types, lifting)  LSubPrefL2_def MemLSubPrefTransitive NonChangeM'm \<open>\<exists>x. accessStore l (Memory st) = Some x\<close> a10 a12 allocateSame antisym_conv2 b10 hash_inequality
                hash_suffixes_associative hashesIntSame limitSt mInStd nonLocChanged option.discI order_less_le_trans tloc)
        next 
          fix loc y 
          assume "accessStore loc (Memory st') = Some y "
          then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" 
            by (metis NonChangeM'm \<open>\<exists>x. accessStore l (Memory st) = Some x\<close> a10 a12 allocateSameAccess limitSt1 mInStd nonLocChanged order_less_trans tloc)
        qed
      next 
        show " typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
          unfolding typeCompat_def
        proof intros
          fix tLook lLook
          assume inDen:" (tLook, lLook) |\<in>| fmran (Denvalue env)"
          show " case lLook of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case tLook of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case tLook of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False )
                | Some (KMemptr stloc) \<Rightarrow> (case tLook of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case tLook of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case tLook of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
          proof(cases lLook)
            case (Stackloc x1)
            then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack nonChangedStack by fastforce
            then show ?thesis 
            proof(cases "a")
              case (KValue x1)
              then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack nonChangedStack unfolding TypeSafe_def typeCompat_def
                by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
            next
              case (KCDptr x2)
              then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack nonChangedStack unfolding TypeSafe_def  typeCompat_def
                by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
            next
              case (KMemptr x3)
              then have "\<exists>struct. tLook = type.Memory struct" using Stackloc adef  inDen Stackloc 2(1) KMemptr sameStack unfolding TypeSafe_def typeCompat_def  by (cases tLook;force+) 
              then obtain struct where structdef:"tLook = type.Memory struct" by blast

              then have mcOld:"MCon struct (Memory st) x3" using 2(1) unfolding TypeSafe_def typeCompat_def
                using Stackloc adef inDen KMemptr sameStack by (auto split:type.splits denvalue.splits stackvalue.splits option.splits)
              then have mcM:"MCon struct m x3" using PreExistMconNotChangeByToploc  limitSt limitSt1 nonLocChanged22 
                by auto
              have structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
                using 2(1) inDen KMemptr Stackloc structdef adef 7(6)
                unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
              then have structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))" 
                by (metis (no_types, lifting))
              have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                          \<longrightarrow> accessTypeStore loc m = accessTypeStore loc (Memory st)"
              proof -
                have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs m"
                  using 7(4,5,6) cpm2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
                    cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd " (snd (allocate (Memory st)))" ] by simp
                then show "\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore loc m = accessTypeStore loc (Memory st)"
                  using allocateTypeSameAccess mInStd by metis
              qed

              then have "accessTypeStore x3 (Memory st) = accessTypeStore x3 m" 
                using limitSt limitSt1 mcOld 
                by (metis AllPtrsNotTop2 lessThanTopLocs_def nat_le_linear)
              moreover have eq2:"\<forall>i::nat. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)"
                using nonLocChanged_TypedSafe limitSt limitSt1 mcOld AllPtrsNotTop2 lessThanTopLocs_def 
                by (metis MemLSubPrefL2_specific_imps_general nat_le_linear)
              ultimately have structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 m = Some (MTValue val))"  using structss by presburger

              have "accessTypeStore l (Memory st) = Some (MTArray x t)" 
                using lInfo 7 nonLocChanged by auto
              then have accl:"accessTypeStore l (m) = Some (MTArray x t)" 
                using nonLocChanged_TypedSafe 
                using l_not_toploc_orSub by auto
              have "MCon struct (Memory st') x3" 
                using cpm2m_singleLChange[OF mcM structss _ _ _ MCondest2 subPrefM] 7(5) mInStd 
                by (metis NonChangeM'm accl lOld2)

              then show ?thesis  using structdef KMemptr Stackloc adef  inDen Stackloc 2(1) unfolding TypeSafe_def  typeCompat_def by simp

            next
              case (KStoptr x4)  
              then show ?thesis using Stackloc adef sameStorage  inDen Stackloc KStoptr 2(1) nonChangedStack sameStack unfolding TypeSafe_def  typeCompat_def
                apply(cases tLook) by fastforce+
            qed

          next
            case (Storeloc x2)
            then show ?thesis using sameStorage inDen 2(1) unfolding TypeSafe_def typeCompat_def by (cases tLook; force)
          qed
        qed
        then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using sameStack by simp
      next 
        have "Accounts st'= Accounts st" using 7 by auto
        then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) 7 unfolding fullyInitialised_def  by auto
      next 
        have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
        have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc m" 
          using cpm2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 7(4) mInStd unfolding cpm2m_def by fastforce
        then have topmm':"Toploc m = Toploc m'" using 7(5) unfolding updateStore_def by auto
        then have topm'st':"Toploc m' = Toploc (Memory st')" using mInStd by blast

        then have "{l. Toploc (Memory st) \<le> l \<and> l < Suc (Toploc (Memory st))} = {(Toploc (Memory st))}" by auto
        then have "{l. Toploc (Memory st) \<le> l \<and> l < (Toploc m)} = {(Toploc (Memory st))}" using topLocEq mInStd unfolding allocate_def by auto
        then have topLocSet:"{(ShowL\<^sub>n\<^sub>a\<^sub>t l) |l. Toploc (Memory st) \<le> l \<and> l < Toploc m} = {ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))}" 
          by (smt (verit, best) Collect_cong mem_Collect_eq singleton_conv2)
        have "\<forall>l. l \<in> WrittenMem_between (Memory st) (m) \<longrightarrow> TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) " 
          using WrittenMem_between_def mInStd a30 selfPoint a32 by blast
        then have "\<forall>l''. l'' \<in> WrittenMem_between (Memory st) (m') \<longrightarrow> TypedMemSubPref l'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> l'' = l" 
          using NonChangeM'm  WrittenMem_between_def by fastforce
        then have cc0:"\<forall>l''. l'' \<in> WrittenMem_between (Memory st) (Memory st') \<longrightarrow> TypedMemSubPref l'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> l'' = l" using mInStd by simp
        moreover have aloccated:"\<forall>x'. x'\<in> (AllocatedMem_between (Memory st) m) \<longleftrightarrow> TypedMemSubPref x' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        proof intros 
          fix x'
          show "(x' \<in> AllocatedMem_between (Memory st) m) = (TypedMemSubPref x' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))"
          proof
            assume " x' \<in> AllocatedMem_between (Memory st) m"
            then have "x' \<in> {(ShowL\<^sub>n\<^sub>a\<^sub>t l) |l. Toploc (Memory st) \<le> l \<and> l < Toploc m} \<union> fset (fmdom (Mapping m) |-| fmdom (Mapping (Memory st)))"
              unfolding AllocatedMem_between_def by simp
            then have "x' \<in> ({(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))} \<union> fset (fmdom (Mapping m) |-| fmdom (Mapping (Memory st))))" 
              using topLocSet by simp
            then  show "TypedMemSubPref x' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
              using a30  accessStore_def allocateSame fminus_iff fmlookup_dom_iff 
              by (metis Un_iff empty_iff insert_iff)
          next 
            assume *:"TypedMemSubPref x' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"

            then show "x' \<in> AllocatedMem_between (Memory st) m"  
            proof(cases "x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
              case True
              then show ?thesis unfolding AllocatedMem_between_def using topLocSet by simp
            next
              case False
              then have "accessStore x' (Memory st) = None" using limitSt typedPrefix_imp_SubPref * by blast

              moreover have "\<exists>v. accessStore x' m = Some v" using * MCondest selfPoint MCon_imps_TypedMemSubPref_Some False by blast

              ultimately have "x' \<in> fset (fmdom (Mapping m) |-| fmdom (Mapping (Memory st)))" using a30 
                by (simp add: accessStore_def fmlookup_dom_iff)
              then show ?thesis using AllocatedMem_between_def by auto
            qed
          qed
        qed
        moreover have "accessStore l m = accessStore l (Memory st)" 
          using l_not_toploc_orSub nonLocChanged22 by fastforce
        moreover obtain vv where vvdef:"accessStore l m = Some vv" using calculation lIs by auto
        moreover have lIn22:"l |\<in>| fmdom (Mapping m)" using fmdomI calculation(4)  accessStore_def by metis
        moreover have "accessStore l m' = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using fmdomI 7(5) by auto
        moreover have "l |\<in>| fmdom (Mapping m')" using calculation(6) fmdomI 
          by (metis accessStore_def)
      next 
        show "denvalueTypeCorrectness env (Stack st') (Memory st')" 
          unfolding denvalueTypeCorrectness_def
        proof intros
          fix t2 l2 ptr_loc
          assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"
          have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
            using nonChangedStack * 7(5,6) unfolding accessStore_def updateStore_def by simp


          show "case t2 of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr) 
                           | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          proof(cases t2)
            case (MTArray x11 x12)

            have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12)" 
              using sameACC 2(1) * unfolding TypeSafe_def denvalueTypeCorrectness_def using MTArray by force

            have conc0:"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12)"
            proof - 
              have o:"\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12" using old' by blast
              then have "\<forall>i<x11. \<exists>v. accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some v"
                using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by auto
              then have "\<forall>i<x11. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
                using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by fastforce
              then show ?thesis using nonLocChanged_TypedSafe o by simp
            qed

            then show ?thesis using MTArray by simp
          next
            case (MTValue x2)
            then show ?thesis using sameACC 2(1) * unfolding TypeSafe_def denvalueTypeCorrectness_def 
              by (metis (no_types, lifting) mtypes.simps(6) nonLocChanged_TypedSafe stackDenvalLimits)
          qed
        qed
      next 
        show "subPrefixStructuralConsistency (Memory st')" 
          unfolding subPrefixStructuralConsistency_def
        proof intros
          fix locs tp
          assume in1:" accessTypeStore locs (Memory st') = Some tp "
          have sameTy:"\<forall>locs. accessTypeStore locs m = accessTypeStore locs (Memory st') "
            using mInStd by (metis NonChangeM'mT)
          then have in2:"accessTypeStore locs m = Some tp " using in1 by simp
          show "case accessStore locs (Memory st') of None \<Rightarrow> False
                | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
                | Some (MPointer p) \<Rightarrow>
                   \<exists>len arr.
                      MCon tp (Memory st') p \<and>
                      tp = MTArray len arr \<and>
                      (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
          proof(cases "locs = l")
            case True
            have "accessTypeStore l (Memory st) = Some (MTArray x t)" 
              using lInfo 7 nonLocChanged by auto
            then have accl:"accessTypeStore l (m) = Some (MTArray x t)" 
              using nonLocChanged_TypedSafe l_not_toploc_orSub 
              using sameTypeAccess by auto
            then have tpDef:"tp = MTArray x t" 
              using sameTy True in1 by simp
            then have ptr:"accessStore locs (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" 
              using mInStd True by (metis accessL)
            have sameAccm:"accessStore l m = accessStore l (Memory st)" 
              using l_not_toploc_orSub nonLocChanged22 by fastforce
            moreover have " MCon tp (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"   
              using MCondest2 tpDef by blast
            moreover have "(\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t)"
              using tpDef ptr subPrefM sameAccm accl unfolding subPrefixStructuralConsistency_def 
              using sameTy tps2 by presburger
            moreover have "
           (\<forall>v. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st') = Some (MPointer v) 
                  \<longrightarrow> accessTypeStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st') = Some (MTArray x t))" 
              using LSubPrefL2_def selfPoint2 by blast
            ultimately show ?thesis using True tpDef ptr by auto
          next
            case False
            then have sameACC:"accessStore locs m = accessStore locs (Memory st')" 
              using mInStd NonChangeM'm by simp
            then have in3:"(case accessStore locs m of None \<Rightarrow> False | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp
        | Some (MPointer p) \<Rightarrow>
            \<exists>len arr.
               MCon tp m p \<and>
               tp = MTArray len arr \<and>
               (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) )" 
              using subPrefM in2 unfolding subPrefixStructuralConsistency_def by blast
            then show ?thesis 
            proof(cases "accessStore locs m")
              case None
              then show ?thesis using in3 sameACC by simp
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (MValue x1)
                then obtain val where " MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp"
                  using in3 Some by auto
                moreover have "MCon tp (Memory st') locs" using sameACC calculation by auto
                ultimately show ?thesis using sameACC Some MValue sameTy
                  by (auto split:option.splits)
              next
                case (MPointer x2)
                have "accessTypeStore l (Memory st) = Some (MTArray x t)" 
                  using lInfo 7 nonLocChanged by auto
                then have accl:"accessTypeStore l (m) = Some (MTArray x t)" 
                  using nonLocChanged_TypedSafe l_not_toploc_orSub 
                  using sameTypeAccess by auto
                then obtain len arr where s:"MCon tp m x2 \<and> tp = MTArray len arr \<and>
                           (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)"
                  using Some in3 MPointer by auto
                then have mcM:"MCon tp m x2" by auto
                then have "MCon tp (Memory st') x2" 
                  using cpm2m_singleLChange[OF mcM _ _ _ _ MCondest2 subPrefM, of l] 
                    7(5) accl mInStd s NonChangeM'm accessL lOld2 
                  by simp
                moreover have "(\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
                  using s sameTy by simp

                ultimately show ?thesis using Some MPointer sameACC sameTy s
                  by (auto split:option.splits)
              qed
            qed
          qed
        qed

      next 
        have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))" 
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
        have somesome:"\<forall>destl'. TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) 
              \<longrightarrow> (\<exists>t. accessStore destl' m = Some t) = (\<exists>tt. accessTypeStore destl' m = Some tt)"
          using 7(4) unfolding cpm2m_def using cpm2m_TypeCompChange_somesome[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 
          by simp
        have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) 
                  \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs m" 
          using  7(4) unfolding cpm2m_def using cpm2mSingleChange2_typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]  
            mInStd allocateTypeSameAccess by metis
        show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def 
        proof intros
          fix locs
          show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
          proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)")
            case True
            then have ss:"(\<exists>t. accessStore locs m = Some t) = (\<exists>tt. accessTypeStore locs m = Some tt)" 
              using somesome by simp
            then show ?thesis 
            proof(cases "locs = l")
              case True
              then show ?thesis using lInfo NonChangeM'mT accessL mInStd ss 
                using lIs l_not_toploc_orSub nonLocChanged22 by auto
            next
              case False
              then show ?thesis using ss NonChangeM'mT NonChangeM'm mInStd by simp
            qed
          next
            case False
            then have acc1:"accessStore locs (Memory st) = accessStore locs m" 
              using a30 mInStd allocateSameAccess by metis
            have acc2:"accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
              using a30T False mInStd NonChangeM'mT by simp
            show ?thesis
            proof(cases "locs = l")
              case True
              then show ?thesis using lInfo acc2 accessL mInStd by force
            next
              case False
              then have "accessStore locs m = accessStore locs (Memory st')"
                using mInStd NonChangeM'm by auto
              then show ?thesis using old acc1 acc2 by metis
            qed
          qed
        qed
      next 
        fix locs t2
        assume acc1:"accessTypeStore locs (Memory st) = Some t2"
        then have someSome:"\<exists>v. accessStore locs (Memory st) = Some v"
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by simp
        have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) 
                  \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs m" 
          using  7(4) unfolding cpm2m_def using cpm2mSingleChange2_typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]  
            mInStd allocateTypeSameAccess by metis

        show "accessTypeStore locs (Memory st') = Some t2"
        proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)")
          case True
          then show ?thesis 
          proof(cases "locs = l")
            case True
            then show ?thesis using l_not_toploc_orSub  
              by (metis NonChangeM'mT a30T acc1 mInStd typedPrefix_imp_SubPref)
          next
            case False
            then show ?thesis using  NonChangeM'mT a30T typedPrefix_imp_SubPref acc1 NonChangeM'm mInStd someSome 
              by (metis less_or_eq_imp_le limitSt option.distinct(1))
          qed
        next
          case False
          have acc2:"accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using a30T False mInStd NonChangeM'mT by simp
          show ?thesis
          proof(cases "locs = l")
            case True
            then show ?thesis using lInfo acc2 accessL mInStd acc1 by argo
          next
            case False
            then have "accessStore locs m = accessStore locs (Memory st')"
              using mInStd NonChangeM'm by auto
            then show ?thesis using acc1 acc2 by metis
          qed
        qed
      next 
        show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
          by (metis accessL le_refl limitSt mInStd nonLocChanged2 option.distinct(1))
      next
        show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
          by (metis memoryvalue.distinct(1) lOld le_refl limitSt nonLocChanged2 not_None_eq option.inject)
      next
        fix i loc 
        assume a1:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
          and a2:"accessStore loc (Memory st) = None"
        then have "loc \<noteq> l" using lOld by auto
        moreover have "\<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using a1 
          by (metis (no_types, opaque_lifting) LSubPrefL2_def MemLSubPrefTransitive hash_flatten_right hash_inequality hashesIntSame nless_le)
        ultimately show " accessStore loc (Memory st') = None" using a2 nonLocChanged2 by simp
      next 
        have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
        moreover have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc m" 
          using cpm2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 7(4) mInStd unfolding cpm2m_def by fastforce
        moreover have topmm':"Toploc m = Toploc m'" using 7(5) unfolding updateStore_def by auto
        moreover have topm'st':"Toploc m' = Toploc (Memory st')" using mInStd by blast
        ultimately show "Toploc (Memory st) \<le> Toploc (Memory st')" by simp
      qed
    qed
  next
    case (8 p x t g l t' g')
    then have stackChanged:"\<forall>l'. l' \<noteq> l \<longrightarrow> accessStore l' (Stack st) = accessStore l' (Stack st')" unfolding updateStore_def accessStore_def by simp
    have t'InDen:"(type.Memory t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[OF 8(2)] by blast
    then have lDen:"\<forall>t'. (t', Stackloc l) |\<in>| fmran (Denvalue env) \<longrightarrow> t'= (type.Memory (MTArray x t))" using 8 2(1) unfolding TypeSafe_def unique_locations_def by auto

    have pOrigin:"MCon (MTArray x t) (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) (extractValueType (KMemptr p)) \<and>
        (\<exists>xx. KMemptr p = KMemptr xx) \<and>
        (\<exists>stloc tp'' pa.
            (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pa) \<and>
            (tp'' = (MTArray x t) \<and> KMemptr p = KMemptr pa \<or>
             (\<exists>len arr.
                 extractValueType (KMemptr p) \<noteq> pa \<and>
                 tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pa (extractValueType (KMemptr p)))))" 
      using 2(1) 8(1) 2(3) using
        exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KMemptr p" "type.Memory (MTArray x t)" g] 
      by (auto split:type.splits if_splits )
    then obtain pParent pParentT pParentPtr where 
      pOrigin:"MCon (MTArray x t) (Memory (st)) (extractValueType (KMemptr p)) \<and>(type.Memory pParentT, Stackloc pParent) |\<in>| fmran (Denvalue env) \<and>
            accessStore pParent (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pParentPtr) \<and>
            (pParentT = (MTArray x t) \<and> KMemptr p = KMemptr pParentPtr \<or>
             (\<exists>len arr.
                 extractValueType (KMemptr p) \<noteq> pParentPtr \<and>
                 pParentT = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pParentPtr (extractValueType (KMemptr p))))"
      using pOrigin      by force
    have pMCon:"MCon (MTArray x t) (Memory st) p" using pOrigin by force

    have storageSame:"(Storage st' (Address env)) = (Storage st (Address env))" using 8 by simp
    have memorySame:"Memory st = Memory st'" using 8 by simp
    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof (intros)
      show tcN:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof(intros)
        fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
        show "case l' of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof (split denvalue.split, intros)
          fix loc assume a20:"l' = Stackloc loc"
          show "(case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))"
          proof (cases "loc = l")
            case False
            show ?thesis
            proof (split option.split, intros)
              assume a30:"accessStore loc (Stack st') = None"
              then have "accessStore loc (Stack st) = None" using 8(4) False by (simp add:stackSingleUpdate)
              then show False using a30 a20 a10 assms TypeSafe_def False "2.prems"(1) 
                by (metis option.distinct(1) typeSafeLocExists)
            next
              fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
              then have a40:"accessStore loc (Stack st) = Some x2" using 8(4) False by (simp add:stackSingleUpdate)
              then have a50:"(Memory st) = (Memory st')" using 8(4) by simp
              then have a60:"(Storage st) = (Storage st')" using 8(4) by simp
              show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                    | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                    | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                    | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
                using a10 a20 a30 a40 a50 a60 "2.prems"(1) unfolding TypeSafe_def typeCompat_def by (cases x2; cases t; force)
            qed
          next 
            case sameLoc:True
            show ?thesis
            proof (split option.split, intros)
              assume a30:"accessStore loc (Stack st') = None"
              then show False using a20 a10 assms(1) sameLoc 8(4) notNoneUpdate[of st' g' loc "(KMemptr p)" ] by simp
            next
              fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
              then have x2IsP:"x2 = KMemptr p" using 8 sameLoc by auto
              show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                    | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                    | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                    | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
              proof(cases "x2")
                case (KValue x1)

                then show ?thesis using x2IsP by auto
              next
                case (KCDptr x2)
                then show ?thesis using x2IsP by (simp add:sameLoc)
              next
                case (KMemptr x3)
                then show ?thesis  
                  using a10 a20 lDen memorySame pMCon sameLoc x2IsP by fastforce
              next
                case (KStoptr x4)
                then show ?thesis using x2IsP by (simp add:sameLoc)
              qed
            qed
          qed
        next
          fix x2 assume a20:"l' = Storeloc x2"
          then have "(Storage st' (Address env)) = (Storage st (Address env))" using 8(4) by simp
          then show "case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st' (Address env)) | _ \<Rightarrow> False"  
            using a10 a20 "2.prems"(1) unfolding TypeSafe_def  typeCompat_def by (cases t; force)
        qed
      qed
      have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof(intros)
        fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
        show "case l' of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st) of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases l')
          case (Stackloc x1)
          then show ?thesis 
          proof(cases "x1= l")
            case True
            then obtain t''' where tdef:"t = type.Memory t'''" using lDen a10 Stackloc 2(1) by blast
            then have x2IsP:"\<exists>p. accessStore x1 (Stack st) = Some (KMemptr p)" 
            proof(cases "accessStore x1 (Stack st)")
              case None
              then show ?thesis using 8 True  2(1) a10 Stackloc unfolding TypeSafe_def typeCompat_def by force
            next
              case (Some a)
              then show ?thesis using tdef 8 True  2(1) a10 Stackloc  unfolding TypeSafe_def typeCompat_def
                by (cases a, force+ )
            qed
            then show ?thesis using a10 Stackloc lDen memorySame pMCon True tdef x2IsP 2(1) unfolding TypeSafe_def typeCompat_def by force
          next
            case False
            then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" 
              using stackChanged by auto
            then show ?thesis using tcN a10 Stackloc unfolding typeCompat_def by force
          qed
        next
          case (Storeloc x2)
          then show ?thesis using tcN a10 unfolding typeCompat_def by force
        qed
      qed
    next
      show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by auto
    next
      have "(Accounts st) = Accounts(st')" using 8 by simp
      then show "balanceTypes (Accounts st')" using balanceTypes_def balanceTypes_def 2(1) typeSafeAccounts by simp
    next
      have a0:"compPointers (Stack st)  (Denvalue env)" using 2(1) storageSame unfolding TypeSafe_def by simp
      show " compPointers (Stack st')  (Denvalue env)" unfolding compPointers_def
      proof(intros)
        fix tp1 tp2 l1 l22 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
       (type.Storage tp2, l22) |\<in>| fmran (Denvalue env) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l22 = Storeloc stl2)"
        have a2:"(\<forall>x y. x |\<in>| fmran (Denvalue env) \<and> y |\<in>| fmran (Denvalue env) \<and> snd x = snd y \<longrightarrow> x = y)"
          using  2(1) unfolding TypeSafe_def unique_locations_def by simp

        have a3:"l1 \<noteq> Stackloc l \<and> l22 \<noteq> Stackloc l" using a2 t'InDen a1 by auto

        then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
        proof(cases "l1 = Storeloc stl1")
          case t1:True
          then show ?thesis 
          proof(cases "l22 = Storeloc stl2")
            case True
            then show ?thesis using t1 a0 a1 unfolding compPointers_def by blast
          next
            case False
            then have " accessStore l2' (Stack st') =  accessStore l2' (Stack st)" using  stackChanged a3 a1 by simp
            then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
          qed
        next
          case f1:False
          then have l1Same:"accessStore l1' (Stack st') =  accessStore l1' (Stack st)" 
            using stackChanged a3 a1 by simp
          then show ?thesis 
          proof(cases "l22 = Storeloc stl2")
            case True
            then show ?thesis using f1 a0 a1 l1Same unfolding compPointers_def by metis
          next
            case False
            then have "accessStore l2' (Stack st') =  accessStore l2' (Stack st)" 
              using stackChanged a3 a1 by simp
            then show ?thesis using a0 a1 l1Same unfolding compPointers_def by metis
          qed
        qed

      qed
    next
      show "svalueTypes (Svalue env)" using svalueTypes_def typeSafeSvalue 2(1) by simp
    next
      have "(Storage st') = (Storage st)" using 8(4) by simp
      then show "safeContract (Accounts st') (Storage st')" using 2(1) 8 unfolding safeContract_def TypeSafe_def  by auto
    next
      have a10:"Toploc (Stack st') = Toploc (Stack st)" using 8(4) unfolding updateStore_def by simp
      then have a20:"\<exists>val. accessStore l (Stack st) = Some val" using t'InDen typeSafeLocExists 2(1) TypeSafe_def by blast
      then have a30:"(\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                     \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))" 
        using 2(1) unfolding TypeSafe_def  lessThanTopLocs_def by simp
      then have a40:"(\<forall>tloc loc. Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                      \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))" 
        using a10 by simp
      show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume *:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then show "accessStore loc (Stack st') = None"
        proof(cases "loc = l")
          case True
          then show ?thesis using * a10 
            by (metis a20 a30 option.distinct(1)) 
        next
          case False
          then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 8(4) unfolding updateStore_def accessStore_def by simp
          then show ?thesis using 2(1) a40 * a10 False a30 by simp
        qed
      next 
        fix loc y 
        assume *:" accessStore loc (Stack st') = Some y "
        show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        proof(cases "loc = l")
          case True
          then show ?thesis using *a10 a20 a30 by simp
        next
          case False
          then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 8(4) unfolding updateStore_def accessStore_def by simp
          then show ?thesis using * 2(1) a40 by simp
        qed
      qed
    next
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def using 8 by auto
    next 
      show "lessThanTopLocs (Memory st')" using 2(1) unfolding TypeSafe_def using 8 by auto
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by auto
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 8 by simp
    next 
      have "Accounts st'= Accounts st" using 8 by auto
      then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) 8 unfolding fullyInitialised_def accessStore_def updateStore_def  by auto
    next 
      show "denvalueTypeCorrectness env (Stack st') (Memory st')" unfolding denvalueTypeCorrectness_def
      proof intros
        fix tt ll ptr_loc sub_loc
        assume *:"(type.Memory tt, Stackloc ll) |\<in>| fmran (Denvalue env) \<and> accessStore ll (Stack st') = Some (KMemptr ptr_loc)"
        have SameMemory:"(Memory st) = (Memory st')" using 8 by simp
        have old: "denvalueTypeCorrectness env (Stack st) (Memory st)" 
          using 2(1) unfolding TypeSafe_def by blast

        show "case tt of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
 
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val) "
        proof(cases "ll = l")
          case True
          then have isMTAr:"tt = (MTArray x t)" using lDen * by auto
          then have isP:"ptr_loc = p" using 8 * True by simp

          then have old2:"\<forall>sub_loc. (case pParentT of
                          MTArray len arr \<Rightarrow>
                            (\<forall>i<len. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
 
                          | MTValue val \<Rightarrow> accessTypeStore pParentPtr (Memory st) = Some (MTValue val))" 
            using pOrigin old unfolding denvalueTypeCorrectness_def by auto
          have "(\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t)" 
          proof(cases "KMemptr p = KMemptr pParentPtr")
            case True
            then have "pParentT = MTArray x t" using pOrigin by auto
            then have "(\<forall>i<x. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some t)" 
              using old2 by simp
            then have "(\<forall>i<x. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t)" 
              using SameMemory by (auto split:option.splits mtypes.splits)
            then show ?thesis using True isP SameMemory by blast
          next
            case False
            then obtain len arr where pt:"(extractValueType (KMemptr p) \<noteq> pParentPtr \<and> pParentT = MTArray len arr \<and>
         CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pParentPtr
          (extractValueType (KMemptr p)))" using pOrigin by blast
            then have cmpt:" CompMemType (Memory st) len arr (MTArray x t) pParentPtr p" by simp

            have "((case pParentT of MTArray len arr \<Rightarrow> 
(\<forall>i<len. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
         | MTValue val \<Rightarrow> accessTypeStore pParentPtr (Memory st) = Some (MTValue val)))"
              using 2(1) pOrigin unfolding TypeSafe_def denvalueTypeCorrectness_def by auto
            then have pPrntAccT:"\<forall>i<len. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr" 
              using  pt by simp

            then have o2:"(\<forall>locs tp.
        accessTypeStore locs (Memory st) = Some tp \<longrightarrow>
        (case accessStore locs (Memory st) of None \<Rightarrow> False
         | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
         | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st) p \<and> tp = MTArray len arr 
                                \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
                                ))"
              using 2(1) unfolding TypeSafe_def subPrefixStructuralConsistency_def using pt by blast
            have mcPrnt:"MCon (MTArray len arr) (Memory st) pParentPtr" 
              using pt pOrigin 2(1) sameMemTSafe[OF 2(1), of pParentPtr] by auto 

            have conc1:" \<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some t" 
              using CompMemTypeSubIndexes[OF cmpt _ mcPrnt pPrntAccT] 2(1) unfolding TypeSafe_def by simp            
            then show ?thesis 
              by (simp add: isP memorySame) 
          qed

          then show ?thesis using isMTAr 
            using mtypes.simps(5) \<open>\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t\<close> by blast
        next
          case False
          then have "accessStore ll (Stack st) = accessStore ll (Stack st')" using stackChanged by blast
          then have "(case tt of
                      MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
 
                      | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
            using old unfolding denvalueTypeCorrectness_def using * by auto
          then show ?thesis using SameMemory by metis
        qed
      qed
    next
      show "subPrefixStructuralConsistency (Memory st')" using 8 2(1) unfolding TypeSafe_def by simp
    next
      show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 8 by simp
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 2(1) unfolding TypeSafe_def using 8 by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using memorySame by fastforce
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using memorySame by fastforce
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using memorySame by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using memorySame by auto
    qed
  next
    case (9 p x t g l t' g' p' s)

    obtain t''' where t''Def:"t' = STArray x t''' " using 9(3) 
      by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
    have sameStack:"(Stack st) = (Stack st')" using 9 unfolding accessStore_def updateStore_def by auto
    have sameMemory:"Memory st' = Memory st " using 9 by auto
    have lInDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[of lv env cd ] 9(2) by simp
    have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs p' \<or> locs = p' \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s" 
      using 9 unfolding cpm2s_def using  cpm2sSingleChange[of p p' t "Memory st" "(Storage st (Address env))" x s]  
      by fastforce
    have a30:" \<forall>locs t' t''.
       cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t') \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s" 
      using  9(5) unfolding cpm2s_def using cpm2sSingleChange2[of p  "p'" t  "Memory st" "(Storage st (Address env))" x s ]  by simp
    then have a35:"\<forall>locs t''. locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t''') \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))" 
      using 9 t''Def by auto
    have mInStd:"s = Storage st' (Address env)" using 9 by simp

    have p'MCon:"SCon t' p' (Storage st (Address env))" using 2 9 unfolding TypeSafe_def typeCompat_def using lInDen 
      by (auto split:denvalue.splits option.splits stackvalue.splits type.splits)

    have MConsrc:"MCon (MTArray x t) (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) (extractValueType (KMemptr p)) \<and>
        (\<exists>xx. KMemptr p = KMemptr xx) \<and>
        (\<exists>stloc tp'' pa.
            (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pa) \<and>
            (tp'' = (MTArray x t) \<and> KMemptr p = KMemptr pa \<or>
             (\<exists>len arr.
                 extractValueType (KMemptr p) \<noteq> pa \<and>
                 tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pa (extractValueType (KMemptr p)))))"
      using 2(1) 9(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KMemptr p" "type.Memory (MTArray x t)" g] 
        2(3) unfolding fullyInitialised_def
      by (auto split:type.splits if_splits )

    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
    then have SCondest:"SCon (STArray x t''') p' s" using  9 unfolding cpm2s_def
      using MCon_cpm2s[of p p' t  "Memory st" "(Storage st (Address env))" x s t'''] t''Def MConsrc extractValueType.simps(2) by simp
    then have SCondest2:"SCon (STArray x t''') p' (Storage st' (Address env))" 
      by (simp add: mInStd)
    then have SCondest3:"SCon t' p' (Storage st' (Address env))" 
      by (simp add: mInStd t''Def)

    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                            \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros 
      show "AddressTypes (Accounts st')" using 2(1) 9 unfolding TypeSafe_def by simp
    next 
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      show "compPointers (Stack st')  (Denvalue env)"  unfolding compPointers_def 
      proof(intros)
        fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
        then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
        proof(cases "TypedStoSubpref stl2 stl1 tp1")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case f1:False
          then show ?thesis 
          proof(cases "TypedStoSubpref stl1 stl2 tp2")
            case True
            then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
          next
            case False
            then show ?thesis using f1 by simp
          qed
        qed
      qed
    next 
      have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp 

      show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
      proof intros
        fix e ct dud i tp
        assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
                 ep $$ Contract (e::environment) = Some (ct, dud) \<and>
                 ct $$ i = Some (Var tp)"
        show "SCon tp i (Storage st' (Address e))"
        proof (cases "Address e = Address env")
          case False
          then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 9 by simp
          moreover have "SCon tp i (Storage st (Address e))"
            using * scOld 9 unfolding safeContract_def by fastforce
          ultimately show ?thesis by simp
        next
          case addrEq:True
          have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using * 9 by simp
          have epOld:"ep $$ Contract e = Some (ct, dud)"
            using * by simp
          have ctOld:"ct $$ i = Some (Var tp)"
            using * by simp
          have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
            using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
          have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
            using denI by (simp add: fmranI)
          have oldSConE:"SCon tp i (Storage st (Address e))"
            using scOld typedOld epOld ctOld unfolding safeContract_def by blast
          have oldSCon:"SCon tp i (Storage st (Address env))"
            using oldSConE addrEq by simp
          have cmpPtr:"(if TypedStoSubpref p' i tp then CompStoType tp t' i p'
                         else if TypedStoSubpref i p' t' then CompStoType t' tp p' i else True)"
            using 2(1) 9(3) inDenI lInDen t''Def unfolding TypeSafe_def compPointers_def 
            using "9"(4) by blast
          have newSCon:"SCon tp i (Storage st' (Address env))"
            using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
          show ?thesis using newSCon addrEq by simp
        qed
      qed
    next 
      show "balanceTypes (Accounts st')" using 9 using 2(1) unfolding TypeSafe_def by simp
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 9 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')"  using sameStack * ** unfolding lessThanTopLocs_def by auto
    next 
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def 
        by (simp add: limitSt limitSt1)
    next 
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t'' l'
        assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

        show " case l' of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t'' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t'' of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t'' of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t'' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t'' of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases l')
          case (Stackloc x1)
          then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
          then show ?thesis 
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack  unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
          next
            case (KCDptr x2)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def   typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
          next
            case (KMemptr x3)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
          next
            case (KStoptr x4)  
            then obtain struct where structDef: "t'' = type.Storage struct" 
              using Stackloc adef inDen Stackloc 2(1) sameStack 
              unfolding TypeSafe_def typeCompat_def
              by (cases t''; fastforce)

            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t'''), Stackloc l) |\<in>| fmran (Denvalue env) \<and>
              (l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4) \<or> l' = Storeloc x4) \<and>
              (accessStore l (Stack st) = Some (KStoptr p')) \<longrightarrow>
              (if TypedStoSubpref p' x4 struct then CompStoType struct  (STArray x t''') x4 p'
               else if TypedStoSubpref x4 p'  (STArray x t''') then CompStoType  (STArray x t''') struct p' x4 else True))" 
              using 2(1) 9(3) lInDen inDen Stackloc structDef KStoptr unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref p' x4 struct then CompStoType struct  (STArray x t''') x4 p'
             else if TypedStoSubpref x4 p'  (STArray x t''') then CompStoType  (STArray x t''') struct p' x4 else True)"
              using  9(4) lInDen inDen Stackloc structDef KStoptr  t''Def
              by (simp add: adef sameStack)

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Stackloc adef inDen Stackloc 2(1) sameStack structDef KStoptr 
              by fastforce

            have "SCon struct x4 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref p' x4 struct")
              case True
              then have "CompStoType struct (STArray x t''') x4 p'" using cmpStoPtr2 by simp
              then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast

            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x4 p'  (STArray x t''')")
                case True
                then have "CompStoType t' struct p' x4 " using cmpStoPtr2 f1 t''Def by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs by blast

              next
                case False
                have notSame:"x4 \<noteq> p'" using False by auto
                have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> p' " using f1 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs p' (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False by auto
                show ?thesis  using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast      
              qed
            qed
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack KStoptr structDef by simp
          qed

        next
          case (Storeloc x2)
          then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc  inDen  2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t'''), Stackloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Storeloc x2) \<and>
              (accessStore l (Stack st) = Some (KStoptr p')) \<longrightarrow>
              (if TypedStoSubpref p' x2 struct then CompStoType struct  (STArray x t''') x2 p'
               else if TypedStoSubpref x2 p'  (STArray x t''') then CompStoType  (STArray x t''') struct p' x2 else True)" 
            using 2(1) 9(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref p' x2 struct then CompStoType struct  (STArray x t''') x2 p'
               else if TypedStoSubpref x2 p'  (STArray x t''') then CompStoType  (STArray x t''') struct p' x2 else True)"
            using  9(4) lInDen inDen Storeloc structDef t''Def by (simp add: sameStack)

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
            by fastforce

          have "SCon struct x2 (Storage st' (Address env))" 
          proof(cases "TypedStoSubpref p' x2 struct")
            case True
            then have "CompStoType struct (STArray x t''') x2 p'" using cmpStoPtr2 by simp
            then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
              by blast
          next
            case f1:False
            then show ?thesis 
            proof(cases "TypedStoSubpref x2 p'  (STArray x t''')")
              case True
              then have "CompStoType t' struct p' x2 " using cmpStoPtr2 f1 t''Def by simp
              then show ?thesis using SCondest3  SCon_imps_sublocs by blast
            next
              case False
              have notSame:"x2 \<noteq> p'" using False by auto
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> p' " using f1 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs p' (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False by auto
              show ?thesis  using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast      
            qed
          qed
          then show ?thesis using Storeloc  inDen  2(1) sameStack Storeloc structDef by simp
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using sameStack by simp
    next 
      have "Accounts st'= Accounts st" using 9 by auto
      then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) 9 unfolding fullyInitialised_def  by auto
    next 
      have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using 9(6) unfolding updateStore_def accessStore_def by auto
      show "denvalueTypeCorrectness env (Stack st') (Memory st')" 

        unfolding denvalueTypeCorrectness_def  
      proof intros
        fix t l ptr_loc sub_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "(case t of
        MTArray len arr \<Rightarrow>
           (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
        moreover have "Memory st = Memory st'" using 9(6) by simp
        ultimately show "case t of
       MTArray len arr \<Rightarrow>
        (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr) 
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)" 
          by metis 
      qed
    next
      show "subPrefixStructuralConsistency (Memory st')" using 2(1) unfolding TypeSafe_def using 9(6) by auto
    next 
      show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 9(6) by auto
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t "
        using 2(1) unfolding TypeSafe_def using 9(6) by auto
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using 9(6) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using 9(6) by simp
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using 9(6) by simp
    next  
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 9(6) by simp
    qed                       
  next
    case (10 p x t g l t' g' s)

    obtain t''' where t''Def:"t' = STArray x t''' " using 10(3) 
      by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
    have sameStack:"(Stack st) = (Stack st')" using 10 unfolding accessStore_def updateStore_def by auto
    have sameMemory:"Memory st' = Memory st " using 10 by auto
    have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s" 
      using 10(4) unfolding cpm2s_def using  cpm2sSingleChange[of p l t "Memory st" "(Storage st (Address env))" x s]  
      by fastforce
    have a30:" \<forall>locs t' t''.
       cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t') \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s" 
      using  10(4) unfolding cpm2s_def using cpm2sSingleChange2[of p  "l" t "Memory st" "(Storage st (Address env))" x s ]  
      by simp
    then have a35:"\<forall>locs t''. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t''') \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))" 
      using 10 t''Def by auto
    have mInStd:"s = Storage st' (Address env)" using 10 by simp

    have MConsrc:"MCon (MTArray x t) (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) (extractValueType (KMemptr p)) \<and>
        (\<exists>xx. KMemptr p = KMemptr xx) \<and>
        (\<exists>stloc tp'' pa.
            (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pa) \<and>
            (tp'' = (MTArray x t) \<and> KMemptr p = KMemptr pa \<or>
             (\<exists>len arr.
                 extractValueType (KMemptr p) \<noteq> pa \<and>
                 tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pa (extractValueType (KMemptr p)))))"
      using 2(1) 10(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KMemptr p" "type.Memory (MTArray x t)" g] 
      using 2(3) unfolding fullyInitialised_def
      by (auto split:type.splits if_splits )

    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
    then have SCondest:"SCon (STArray x t''') l s" using  10 unfolding cpm2s_def
      using MCon_cpm2s[of p l t "Memory st" "(Storage st (Address env))" x s t'''] t''Def MConsrc extractValueType.simps(2) by auto
    then have SCondest2:"SCon (STArray x t''') l (Storage st' (Address env))" 
      by (simp add: mInStd)
    then have SCondest3:"SCon t' l (Storage st' (Address env))" 
      by (simp add: mInStd t''Def)

    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                            \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros 
      show "AddressTypes (Accounts st')" using 2(1) 10 unfolding TypeSafe_def by simp
    next 
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      show "compPointers (Stack st')  (Denvalue env)"  unfolding compPointers_def 
      proof(intros)
        fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
        then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
        proof(cases "TypedStoSubpref stl2 stl1 tp1")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case f1:False
          then show ?thesis 
          proof(cases "TypedStoSubpref stl1 stl2 tp2")
            case True
            then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
          next
            case False
            then show ?thesis using f1 by simp
          qed
        qed
      qed
    next 
      have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp 

      show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
      proof intros
        fix e ct dud i tp
        assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
                 ep $$ Contract (e::environment) = Some (ct, dud) \<and>
                 ct $$ i = Some (Var tp)"
        show "SCon tp i (Storage st' (Address e))"
        proof (cases "Address e = Address env")
          case False
          then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 10 by simp
          moreover have "SCon tp i (Storage st (Address e))"
            using * scOld 10 unfolding safeContract_def by fastforce
          ultimately show ?thesis by simp
        next
          case addrEq:True
          have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using * 10 by simp
          have epOld:"ep $$ Contract e = Some (ct, dud)"
            using * by simp
          have ctOld:"ct $$ i = Some (Var tp)"
            using * by simp
          have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
            using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
          have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
            using denI by (simp add: fmranI)
          have oldSConE:"SCon tp i (Storage st (Address e))"
            using scOld typedOld epOld ctOld unfolding safeContract_def by blast
          have oldSCon:"SCon tp i (Storage st (Address env))"
            using oldSConE addrEq by simp
          have uniq:"unique_locations (Denvalue env)"
            using 2(1) typeSafeUnique by simp
          have epEnv:"ep $$ Contract env = Some (ct, dud)"
            using epOld addrEq 
            using "2.prems"(3) fullyInitialised_def typedOld by auto
          show ?thesis
          proof(cases rule:lexpStorageG[OF 2(1) 10(2) 2(3)])
            case lInDen:1
            have inDenL:"(type.Storage t', Storeloc l) |\<in>| fmran (Denvalue env)"
              using lInDen by simp
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using 2(1) 10(3) inDenI inDenL unfolding TypeSafe_def compPointers_def by blast
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          next
            case sub2:(2 l''' t)
            have inDenL:"(type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env)" using sub2 by simp
            have relL:"TypedStoSubpref l l''' t \<and> CompStoType t t' l''' l" using sub2 by simp
            show ?thesis
            proof(cases "i = l'''")
              case True
              have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage t, Storeloc l''')"
                using uniqueLocs[OF uniq inDenI inDenL] True by simp
              then have tpEq:"tp = t" by simp
              have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                            else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
                using relL tpEq True by simp
              have newSCon:"SCon tp i (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
              show ?thesis using newSCon addrEq by simp
            next
              case False
              have ctL:"ct $$ l''' = Some (Var t)"
                using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenL] .
              have nPrnt1:"\<not>TypedStoSubpref i l''' t"
                and nPrnt2:"\<not>TypedStoSubpref l''' i tp"
                using methodVarsNoPref False epOld ctOld ctL by blast+
              have n1:"\<not>TypedStoSubpref l i tp"
                using NotRelatedPrnt_imps_notRelatedChild[OF nPrnt1 nPrnt2] relL by blast
              have n2:"\<not>TypedStoSubpref i l t'"
                using NotReachablePrnt_imps_notReachableChild nPrnt1 nPrnt2 relL by blast
              have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                            else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
                using n1 n2 by simp
              have newSCon:"SCon tp i (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
              show ?thesis using newSCon addrEq by simp
            qed
          next
            case sub3:(3 l' t l'')
            have inDenStk:"(type.Storage t, Stackloc l'') |\<in>| fmran (Denvalue env)" using sub3 by simp
            have ptrL:"accessStore l'' (Stack st) = Some (KStoptr l')" using sub3 by simp
            have rel0:"TypedStoSubpref l l' t \<and> CompStoType t t' l' l" using sub3 by simp
            obtain tprnt lprnt where
                inDenPr:"(type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue env)"
              and compPr:"CompStoType tprnt t lprnt l'"
              using fiPtr_parent_from_fullyInitialised[OF 2(3) inDenStk ptrL] by blast
            have compPr2:"CompStoType tprnt t' lprnt l"
              using compPr rel0 CompStoType_trns by blast
            have relPr:"TypedStoSubpref l lprnt tprnt \<and> CompStoType tprnt t' lprnt l"
              using compPr2 CompStoType_imps_TypedStoSubpref by blast
            show ?thesis
            proof(cases "i = lprnt")
              case True
              have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage tprnt, Storeloc lprnt)"
                using uniqueLocs[OF uniq inDenI inDenPr] True by simp
              then have tpEq:"tp = tprnt" by simp
              have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                            else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
                using compPr2 tpEq True 
                using relPr by presburger
              have newSCon:"SCon tp i (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
              show ?thesis using newSCon addrEq by simp
            next
              case False
              have ctPr:"ct $$ lprnt = Some (Var tprnt)"
                using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenPr] .
              have nPrnt1:"\<not>TypedStoSubpref i lprnt tprnt"
                and nPrnt2:"\<not>TypedStoSubpref lprnt i tp"
                using methodVarsNoPref False epOld ctOld ctPr by blast+
              have n1:"\<not>TypedStoSubpref l i tp"
                using NotRelatedPrnt_imps_notRelatedChild[OF nPrnt1 nPrnt2] relPr by blast
              have n2:"\<not>TypedStoSubpref i l t'"
                using NotReachablePrnt_imps_notReachableChild nPrnt1 nPrnt2 relPr by blast
              have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                            else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
                using n1 n2 by simp
              have newSCon:"SCon tp i (Storage st' (Address env))"
                using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
              show ?thesis using newSCon addrEq by simp
            qed
          qed
        qed
      qed
    next 
      show "balanceTypes (Accounts st')" using 10 using 2(1) unfolding TypeSafe_def by simp
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 10 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')"  using sameStack * ** unfolding lessThanTopLocs_def by auto
    next 
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def 
        by (simp add: limitSt limitSt1)
    next 
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t'' l'
        assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

        show " case l' of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t'' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t'' of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t'' of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t'' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t'' of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases l')
          case (Stackloc x1)
          then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
          then show ?thesis 
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack  unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
          next
            case (KCDptr x2)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def   typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
          next
            case (KMemptr x3)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
          next
            case (KStoptr x4)  
            then obtain struct where structDef: "t'' = type.Storage struct" using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
              by (cases t''; fastforce)

            have "SCon struct x4 (Storage st' (Address env))" 
            proof(cases rule:lexpStorageG[OF 2(1) 10(2) 2(3)])
              case lInDen:1
              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage (STArray x t'''), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) 
                 \<longrightarrow>
                (if TypedStoSubpref l x4 struct then CompStoType struct  (STArray x t''') x4 l
                 else if TypedStoSubpref x4 l  (STArray x t''') then CompStoType  (STArray x t''') struct l x4 else True)" 
                using 2(1) 10(3) lInDen inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l x4 struct then CompStoType struct  (STArray x t''') x4 l
                 else if TypedStoSubpref x4 l  (STArray x t''') then CompStoType  (STArray x t''') struct l x4 else True)"
                using  10(3) lInDen inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce

              have "SCon struct x4 (Storage st' (Address env))" 
              proof(cases "TypedStoSubpref l x4 struct")
                case True
                then have "CompStoType struct (STArray x t''') x4 l" using cmpStoPtr2 by simp
                then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                  by blast

              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref x4 l  (STArray x t''')")
                  case True
                  then have "CompStoType t' struct l x4 " using cmpStoPtr2 f1 t''Def by simp
                  then show ?thesis using SCondest3  SCon_imps_sublocs by blast
                next
                  case False
                  have notSame:"x4 \<noteq> l" using False by auto
                  have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 by blast
                  have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False by auto
                  show ?thesis  using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast      
                qed
              qed
              then show ?thesis by simp
            next
              case sub2:(2 l''' t)
              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) 
                 \<longrightarrow>
                (if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
                 else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)" 
                using 2(1) 10(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
                 else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
                using  10(3) sub2 inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce
              have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

              have "SCon struct x4 (Storage st' (Address env))" 
              proof(cases "TypedStoSubpref l''' x4 struct")
                case True
                then have "CompStoType struct t x4 l'''" using cmpStoPtr2 by simp
                then have "CompStoType struct (STArray x t''') x4 l" using sub2 
                  using CompStoType_trns t''Def by blast
                then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                  by blast
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref x4 l''' t")
                  case True
                  then have "l''' \<noteq> x4" using f1 
                    using TypedStoSubpref_sameLoc by auto
                  then show ?thesis 
                  proof(cases "l = x4")
                    case t5:True
                    then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                    moreover have "CompStoType t t' l''' x4" using t5 sub2 by auto
                    ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                      by simp
                    then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                  next
                    case False
                    then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def  True by simp                
                    then show ?thesis 
                    proof(cases "CompStoType t' struct l x4 ")
                      case True
                      then show ?thesis 
                        using SCon_imps_sublocs SCondest3 by blast
                    next
                      case False
                      then show ?thesis 
                        by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x4\<close> a35 scl''' sub2(2) t''Def)
                    qed
                  qed
                next
                  case False                                                             
                  then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
                  then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
                  have notSame:"x4 \<noteq> l" using False sub2 by blast
                  have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20  by blast
                  have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False sub2 t''Def asm10 asm20 by blast
                  show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
                qed
              qed

              then show ?thesis by simp
            next
              case sub3:(3 l''' t l'''')
              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t, Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) \<and> accessStore l'''' (Stack st) = Some (KStoptr l''')
                 \<longrightarrow>
                (if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
                 else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)" 
                using 2(1) 10(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
                 else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
                using  10(3) sub3 inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce
              have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

              have "SCon struct x4 (Storage st' (Address env))" 
              proof(cases "TypedStoSubpref l''' x4 struct")
                case True
                then have "CompStoType struct t x4 l'''" using cmpStoPtr2 by simp
                then have "CompStoType struct (STArray x t''') x4 l" using sub3 
                  using CompStoType_trns t''Def by blast
                then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                  by blast
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref x4 l''' t")
                  case True
                  then have "l''' \<noteq> x4" using f1 
                    using TypedStoSubpref_sameLoc by auto
                  then show ?thesis 
                  proof(cases "l = x4")
                    case t5:True
                    then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                    moreover have "CompStoType t t' l''' x4" using t5 sub3 by auto
                    ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                      by simp
                    then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                  next
                    case False
                    then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def  True by simp                
                    then show ?thesis 
                    proof(cases "CompStoType t' struct l x4 ")
                      case True
                      then show ?thesis 
                        using SCon_imps_sublocs SCondest3 by blast
                    next
                      case False
                      then show ?thesis 
                        by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x4\<close> a35 scl''' sub3(3) t''Def)
                    qed
                  qed
                next
                  case False                                                             
                  then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                  then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                  have notSame:"x4 \<noteq> l" using False sub3 by blast
                  have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20  by blast
                  have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False sub3 t''Def asm10 asm20 by blast
                  show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
                qed
              qed
              then show ?thesis by simp
            qed
            then show ?thesis using Stackloc  inDen  2(1) sameStack KStoptr adef structDef by simp
          qed
        next
          case (Storeloc x2)
          then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc  inDen  2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have "SCon struct x2 (Storage st' (Address env))" 
          proof(cases rule:lexpStorageG[OF 2(1) 10(2) 2(3)])
            case lInDen:1
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t'''), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Storeloc x2) 
               \<longrightarrow>
              (if TypedStoSubpref l x2 struct then CompStoType struct  (STArray x t''') x2 l
               else if TypedStoSubpref x2 l  (STArray x t''') then CompStoType  (STArray x t''') struct l x2 else True)" 
              using 2(1) 10(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l x2 struct then CompStoType struct  (STArray x t''') x2 l
               else if TypedStoSubpref x2 l  (STArray x t''') then CompStoType  (STArray x t''') struct l x2 else True)"
              using  10(3) lInDen inDen Storeloc structDef t''Def sameStack by simp

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce

            have "SCon struct x2 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref l x2 struct")
              case True
              then have "CompStoType struct (STArray x t''') x2 l" using cmpStoPtr2 by simp
              then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast

            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x2 l  (STArray x t''')")
                case True
                then have "CompStoType t' struct l x2 " using cmpStoPtr2 f1 t''Def by simp
                then show ?thesis using SCondest3  SCon_imps_sublocs by blast
              next
                case False
                have notSame:"x2 \<noteq> l" using False by auto
                have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False by auto
                show ?thesis  using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast      
              qed
            qed
            then show ?thesis by simp
          next
            case sub2:(2 l''' t)
            have cmpStoPtr:"(
                (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env) )
                 \<longrightarrow>
                (if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
                 else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)" 
              using 2(1) 10(3) inDen  Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
                 else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
              using  10(3) sub2 inDen Storeloc  structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce
            have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

            have "SCon struct x2 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref l''' x2 struct")
              case True
              then have "CompStoType struct t x2 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t''') x2 l" using sub2 
                using CompStoType_trns t''Def by blast
              then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x2 l''' t")
                case True
                then have "l''' \<noteq> x2" using f1 
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x2")
                  case t5:True
                  then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                  moreover have "CompStoType t t' l''' x2" using t5 sub2 by auto
                  ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                    by simp
                  then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                next
                  case False
                  then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def  True by simp                
                  then show ?thesis 
                  proof(cases "CompStoType t' struct l x2 ")
                    case True
                    then show ?thesis 
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis 
                      by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x2\<close> a35 scl''' sub2(2) t''Def)
                  qed
                qed
              next
                case False                                                             
                then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
                then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x2 \<noteq> l" using False sub2 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20  by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False sub2 t''Def asm10 asm20 by blast
                show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
              qed
            qed

            then show ?thesis by simp
          next
            case sub3:(3 l''' t l'''')
            have cmpStoPtr:"(
                (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t, Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
                 accessStore l'''' (Stack st) = Some (KStoptr l'''))
                 \<longrightarrow>
                (if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
                 else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)" 
              using 2(1) 10(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
                 else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
              using  10(3) sub3 inDen Storeloc structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce
            have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

            have "SCon struct x2 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref l''' x2 struct")
              case True
              then have "CompStoType struct t x2 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t''') x2 l" using sub3 
                using CompStoType_trns t''Def by blast
              then show ?thesis using SCondest2  SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x2 l''' t")
                case True
                then have "l''' \<noteq> x2" using f1 
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x2")
                  case t5:True
                  then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                  moreover have "CompStoType t t' l''' x2" using t5 sub3 by auto
                  ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                    by simp
                  then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                next
                  case False
                  then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def  True by simp                
                  then show ?thesis 
                  proof(cases "CompStoType t' struct l x2 ")
                    case True
                    then show ?thesis 
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis 
                      by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x2\<close> a35 scl''' sub3(3) t''Def)
                  qed
                qed
              next
                case False                                                             
                then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x2 \<noteq> l" using False sub3 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20  by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False sub3 t''Def asm10 asm20 by blast
                show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
              qed
            qed
            then show ?thesis by simp
          qed
          then show ?thesis using Storeloc  inDen  2(1) sameStack Storeloc structDef by simp
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd " using sameStack by simp
    next
      have "Accounts st'= Accounts st" using 10 by auto
      then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) 10 unfolding fullyInitialised_def  by auto
    next 
      have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using 10(5) unfolding updateStore_def accessStore_def by auto
      show "denvalueTypeCorrectness env (Stack st') (Memory st')" 

        unfolding denvalueTypeCorrectness_def  
      proof intros
        fix t l ptr_loc sub_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "(case t of
        MTArray len arr \<Rightarrow>
           (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
        moreover have "Memory st = Memory st'" using 10(5) by simp
        ultimately show "case t of
       MTArray len arr \<Rightarrow>
        (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)" 
          by metis 
      qed
    next
      show "subPrefixStructuralConsistency (Memory st')" using 2(1) unfolding TypeSafe_def using 10(5) by auto
    next 
      show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 10(5) by auto
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t "
        using 2(1) unfolding TypeSafe_def using 10(5) by auto
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using 10(5) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using 10(5) by simp
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 10(5) by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 10(5)by simp
    qed     

  next
    case (11 p x t g l t' g')
    have temp:"TypeSafe env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd" 
      using 2(1) by simp
    have ttt:"fullyInitialised env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 2(3) unfolding fullyInitialised_def by simp
    then show ?thesis
    proof(cases rule:lexpIndexMem[OF 11(2) temp ttt])
      case lInfo:(1 x21 x22 tp tParent l' l'' prnt len' arr' i)
      have sameStack:"(Stack st') = Stack st" using 11 unfolding accessStore_def updateStore_def by auto
      have sameStorage:"Storage st'  = Storage st " using 11 by auto
      have accL:"accessStore l (Memory st') = Some (MPointer p)" using 11(4) by auto
      have nonLocChanged:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs  (Memory st') = accessStore locs  (Memory st)" 
        using 11 unfolding updateStore_def accessStore_def by simp

      have MConsrc:"MCon (MTArray x t) (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) (extractValueType (KMemptr p)) \<and>
        (\<exists>xx. KMemptr p = KMemptr xx) \<and>
        (\<exists>stloc tp'' pa.
            (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pa) \<and>
            (tp'' = (MTArray x t) \<and> KMemptr p = KMemptr pa \<or>
             (\<exists>len arr.
                 extractValueType (KMemptr p) \<noteq> pa \<and>
                 tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pa (extractValueType (KMemptr p)))))"
        using 2(1) 11(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KMemptr p" "type.Memory (MTArray x t)" g] 
        using 2(3) unfolding fullyInitialised_def
        by (auto split:type.splits if_splits )


      then obtain pParent pParentT pParentPtr where 
        pOrigin:"MCon (MTArray x t) (Memory (st)) (extractValueType (KMemptr p)) \<and>(type.Memory pParentT, Stackloc pParent) |\<in>| fmran (Denvalue env) \<and>
            accessStore pParent (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pParentPtr) \<and>
            (pParentT = (MTArray x t) \<and> KMemptr p = KMemptr pParentPtr \<or>
             (\<exists>len arr.
                 extractValueType (KMemptr p) \<noteq> pParentPtr \<and>
                 pParentT = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pParentPtr (extractValueType (KMemptr p))))"
        by force
      then have l:"MCon pParentT (Memory st) pParentPtr" using sameMemTSafe[OF 2(1)] by auto

      have pTAccessOld:"(\<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some t)"
      proof(cases "pParentT = (MTArray x t) \<and> KMemptr p = KMemptr pParentPtr")
        case True
        then show ?thesis using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def 
          using pOrigin by fastforce
      next
        case False
        then obtain l1 a1 where l1Def:"(p \<noteq> pParentPtr \<and> pParentT = MTArray l1 a1
                    \<and> CompMemType (Memory st) l1 a1 (MTArray x t) pParentPtr p)"
          using pOrigin by auto
        then have prntT:" \<forall>i<l1. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some a1"
          using pOrigin using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def 
          by fastforce
        have subPref:"subPrefixStructuralConsistency (Memory st)" 
          using 2(1) unfolding TypeSafe_def by blast
        then show ?thesis using CompMemTypeSubIndexes[OF _  subPref _ prntT] l1Def 
          using l by blast
      qed


      obtain len subT where tParentType:"tParent = MTArray len subT" using lInfo by blast
      then obtain p'' where lOrigin:"accessStore l (Memory (st)) = Some (MPointer p'')" 
        and  compType:"CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len subT (MTArray x t) l'' p''" 
        and lsublocs:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = (MTArray x t) \<and> MCon (MTArray len' arr') (Memory (st)) prnt" 
        and lsublocs3:"(prnt = l'' \<and> len = len' \<and> arr' = subT \<or> CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt)"
        using lInfo 11(3) by force
      then have lsublocs2:" CompMemType (Memory (st)) len' arr' (MTArray x t) prnt p''" 
        using 11(3) CompMemType.simps(2) by blast
      then have bb9:"\<forall>subT subloc. CompMemType (Memory (st)) len' arr' subT prnt subloc \<and> subloc = p''
                                  \<longrightarrow> subT = (MTArray x t)" 
        using CompMemTypeSameLocsSameType lsublocs by blast

      have mconPrnt:"MCon (MTArray len' (MTArray x t)) (Memory st) prnt" using lsublocs by auto
      have ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'" using lsublocs by auto

      have t6:"(type.Memory tParent,  Stackloc l') |\<in>| fmran (Denvalue env)" using lInfo by blast
      have t7:" MCon (MTArray len subT) (Memory (st)) l''" using lInfo 
        using tParentType by auto
      then have mconlOld:"MCon (MTArray x t) (Memory st) p''" using 11(3) lInfo lOrigin by auto

      have mcP:"MCon (MTArray x t) (Memory st) p" using MConsrc by force
      have compP:"\<not>CompMemType (Memory (st)) x t (MTArray len' (MTArray x t)) p prnt" 
        using MCon_subTypes_imps_noPrnt mcP mconPrnt 
        by simp
      have pNotPrnt:"p \<noteq> prnt" using mcP mconPrnt nonLocChanged
        using MConSubTypes CompMemJustType.simps(2) by blast
      have pSubs:"TypedMemSubPrefPtrs (Memory st) len' (MTArray x t) prnt p \<longrightarrow> (\<exists>i'. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some (MPointer p) \<and> i'<len')" 
      proof intros
        assume in1:"TypedMemSubPrefPtrs (Memory st) len' (MTArray x t) prnt p"
        then obtain i2 l2 where i2Def: "i2<len' \<and> accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st) = Some (MPointer l2) \<and> (l2 = p \<or> TypedMemSubPrefPtrs (Memory st) x t l2 p)" 
          unfolding TypedMemSubPrefPtrs.simps by blast
        show "\<exists>i'. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some (MPointer p) \<and> i' < len'"
        proof(cases "l2 = p")
          case True
          then show ?thesis using i2Def by auto
        next
          case False
          then have in2:"TypedMemSubPrefPtrs (Memory st) x t l2 p" using i2Def by simp
          have in3:"\<forall>ta. CompMemJustType t ta \<longrightarrow> \<not> MCon ta (Memory st) p" using MConSubTypes[OF mcP] by blast
          have "MCon (MTArray x t) (Memory st) l2" using i2Def mconPrnt
            using MCon_imps_sub_Mcon by blast

          then show ?thesis using in3 in2
          proof(induction t arbitrary:l2 x)
            case (MTArray x1 t)
            obtain i3 l3 where i3Def:"i3<x \<and> accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i3)) (Memory st) = Some (MPointer l3) 
                                      \<and> (l3 = p \<or> TypedMemSubPrefPtrs (Memory st) x1 t l3 p)"
              using MTArray.prems(3) unfolding TypedMemSubPrefPtrs.simps by auto
            then have mcL3:"MCon (MTArray x1 t) (Memory st) l3" using MTArray.prems(1) 
              using MconSameTypeSameAccessWithTyping by blast
            then have notP:"l3 \<noteq> p" using MTArray.prems(3) 
              using MConSubTypes MTArray.prems(2) CompMemJustType.simps(2) by blast
            have "\<forall>taa. CompMemJustType t taa \<longrightarrow> \<not> MCon taa (Memory st) p" using MTArray.prems by simp
            moreover have "TypedMemSubPrefPtrs (Memory st) x1 t l3 p" using notP i3Def by simp
            ultimately show ?case using MTArray.IH mcL3 by blast
          next
            case (MTValue x')
            then show ?case 
              by (metis CompTypeRemainsMCon TypedMemSubPrefPtrs.simps(1) CompMemJustType.simps(1) CompMemType.simps(1))
          qed
        qed
      qed

      have p''ToPrnt:"\<not>TypedMemSubPrefPtrs (Memory st) x t p'' prnt" 
        by (meson CompMemType_imps_CompMemJustType CompMemType_imps_TypedMemSubPrefPtrs CompTypeRemainsMCon TypedMemSubPrefOneWay lsublocs lsublocs2)
      moreover have p''notprnt:"p'' \<noteq>prnt" using lsublocs2 
        using CompMemType_imps_TypedMemSubPrefPtrs TypedMemSubPrefPtrs_imps_notsame lsublocs by blast
      ultimately have mcP''New:"MCon (MTArray x t) (Memory st') p''" using mconlOld limitedMemoryChange[of "Memory st" x t p'' prnt i ] nonLocChanged 11 ldef by fastforce

      have mcPrnt:"\<exists>t''. MCon t'' (Memory st) prnt \<and> CompMemJustType t'' (MTArray x t) \<and> t'' \<noteq> (MTArray x t)" using mconPrnt by fastforce
      have asf:"\<not>TypedMemSubPrefPtrs (Memory st) x t p prnt"  
      proof
        assume in1:"TypedMemSubPrefPtrs (Memory st) x t p prnt"
        then show False using mcP mcPrnt  
        proof(induction t arbitrary:x p)
          case (MTArray x1 t)
          then obtain i2 l2 where i2Def: "i2<x \<and> accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st) = Some (MPointer l2)
                                             \<and> (l2 = prnt \<or> TypedMemSubPrefPtrs (Memory st) x1 t l2 prnt)"
            unfolding TypedMemSubPrefPtrs.simps  by blast
          then have mcl2:"MCon (MTArray x1 t) (Memory st) l2" using MTArray.prems(2) 
            using MCon_imps_sub_Mcon by blast
          then show ?case 
          proof(cases "l2 = prnt")
            case True
            then have "MCon (MTArray x1 t) (Memory st)  prnt" using mcl2 by simp
            then show ?thesis 
              by (smt (verit) CompMemTypes_asc MConSubTypes MTArray.prems(3) mtypes.exhaust CompMemJustType.simps(1,2))
          next
            case False
            then have "TypedMemSubPrefPtrs (Memory st) x1 t l2 prnt" using i2Def by simp
            then show ?thesis using MTArray.IH[OF _ mcl2] MTArray.prems(3) 
              by (metis CompMemTypes_asc reversable_CompMemJustType_imps_same CompMemJustType.simps(2))
          qed
        next
          case (MTValue x')
          then have "\<exists>i<x. hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i) = prnt" unfolding TypedMemSubPrefPtrs.simps by blast
          then show ?case using MTValue unfolding MCon.simps 
            using lsublocs by fastforce
        qed
      qed

      have mcPNew:"MCon (MTArray x t) (Memory st') p" using mcP asf pNotPrnt
      proof(induction t arbitrary: x p)
        case (MTArray x1 t)
        then have  xnotzero:"x \<noteq> 0" unfolding MCon.simps by simp
        have "\<forall>i<x. (case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False 
                                  | MTValue typ \<Rightarrow> MCon (MTArray x1 t) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)) \<and>
              ((\<exists>p'. accessStore p (Memory st') = Some (MPointer p')) \<or> accessStore p (Memory st') = None)"
        proof(intros)
          fix i2 assume i2Def:"i2<x"
          have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) \<noteq> l" 
          proof
            assume in1':"hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2) = l"
            then have "p = prnt" using ldef ShowLNatDot 
              using hash_injective by blast
            then show False using MTArray.prems(3) by simp
          qed
          then have sameAccess:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st)" using nonLocChanged by simp
          then obtain p2 where p2Def: "accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = Some (MPointer p2) \<and> MCon (MTArray x1 t) (Memory st) p2" using i2Def
            using MTArray.prems by (metis MConArrayPointers MCon_imps_sub_Mcon bot_nat_0.not_eq_extremum xnotzero)
          then have "\<not> TypedMemSubPrefPtrs (Memory st) x1 t p2 prnt" using MTArray.prems 
            using i2Def sameAccess by fastforce
          moreover have "p2 \<noteq> prnt" using MTArray.prems p2Def i2Def 
            by (simp add: sameAccess)
          ultimately have "MCon (MTArray x1 t) (Memory st') p2" using MTArray.IH[of x1 p2] p2Def MTArray.prems by blast
          then show "case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False
       | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)))
       | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)" 
            using p2Def by simp
          show "(\<exists>p'. accessStore p (Memory st') = Some (MPointer p')) \<or> accessStore p (Memory st') = None" 
          proof(cases "p = l")
            case True
            then show ?thesis using 11 by simp
          next
            case False
            then show ?thesis using nonLocChanged using MTArray.prems(1) unfolding MCon.simps 
              using i2Def  sameAccess by simp
          qed
        qed
        then show ?case using MCon.simps(2)[of x "(MTArray x1 t)" "Memory st'" p ]  xnotzero
          by simp
      next
        case (MTValue x')
        then have xnotzero:"x \<noteq> 0" unfolding MCon.simps by simp
        have "\<forall>i<x. (case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow>
                  (case MTValue x' of MTArray l a \<Rightarrow> False
                  | MTValue typ \<Rightarrow> (case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False | Some (MValue xa) \<Rightarrow> typeCon x' xa | Some (MPointer t) \<Rightarrow> False))
              | Some (MPointer loc2) \<Rightarrow>
                  (case MTValue x' of MTArray len' arr' \<Rightarrow> (case accessStore loc2 (Memory st') of None \<Rightarrow> False | Some (MValue xa) \<Rightarrow> typeCon x' xa | Some (MPointer t) \<Rightarrow> False)
                  | MTValue Types \<Rightarrow> False))\<and>
             ((\<exists>p'. accessStore p (Memory st') = Some (MPointer p')) \<or> accessStore p (Memory st') = None)" 
        proof(intros)
          fix i2 assume i2Def:"i2<x"
          then have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) \<noteq> l" using  ldef 
            by (metis MCon_sub_MTVal_imps_val MTValue.prems(1) memoryvalue.distinct(1) lOrigin option.inject)
          then have sameAccess:" accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') =  accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st)" using nonLocChanged by simp
          then show "case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False
       | Some (MValue val) \<Rightarrow>
           (case MTValue x' of MTArray l a \<Rightarrow> False
           | MTValue typ \<Rightarrow> (case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False | Some (MValue xa) \<Rightarrow> typeCon x' xa | Some (MPointer t) \<Rightarrow> False))
       | Some (MPointer loc2) \<Rightarrow>
           (case MTValue x' of MTArray len' arr' \<Rightarrow> (case accessStore loc2 (Memory st') of None \<Rightarrow> False | Some (MValue xa) \<Rightarrow> typeCon x' xa | Some (MPointer t) \<Rightarrow> False)
           | MTValue Types \<Rightarrow> False)" using MTValue(1) i2Def mcon_accessStore xnotzero by (auto split:option.splits memoryvalue.splits mtypes.splits)
          show "(\<exists>p'. accessStore p (Memory st') = Some (MPointer p')) \<or> accessStore p (Memory st') = None" 
          proof(cases "p = l")
            case True
            then show ?thesis using 11 by simp
          next
            case False
            then show ?thesis using nonLocChanged using MTValue(1) unfolding MCon.simps 
              using i2Def  sameAccess by simp
          qed
        qed
        then show ?case unfolding MCon.simps using xnotzero
          by simp
      qed

      have mcPrntNew:"MCon (MTArray len' (MTArray x t)) (Memory st') prnt" 
      proof -
        have lenNotZero:"len' \<noteq> 0" using lsublocs by auto
        have prntNotL:"prnt \<noteq> l" using ldef 
          by (metis hash_inequality)
        then have p2:"(\<exists>p. accessStore prnt (Memory st') = Some (MPointer p)) \<or> accessStore prnt (Memory st') = None" 
          using mconPrnt lenNotZero nonLocChanged by simp
        have "\<forall>i<len'.
           (case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x t) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x t of MTArray len' arr' \<Rightarrow> MCon (MTArray x t) (Memory st') loc2 | MTValue Types \<Rightarrow> False))" 
        proof(intros)
          fix i1 assume in1:"i1<len'"
          show "case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') of None \<Rightarrow> False
         | Some (MValue val) \<Rightarrow> (case MTArray x t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x t) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)))
         | Some (MPointer loc2) \<Rightarrow> (case MTArray x t of MTArray len' arr' \<Rightarrow> MCon (MTArray x t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
          proof(cases "i1 = i")
            case True
            then have "(hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) = l" using ldef by simp
            then have "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = Some(MPointer p)" using 11 by simp
            then show ?thesis using mcPNew by simp
          next
            case False
            then have "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st)" using ldef nonLocChanged in1 
              by (metis Read_Show_nat'_id hash_never_equal_sufix)
            then obtain ptr where ptrDef:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st) = Some (MPointer ptr)" using in1 
              using MConArrayPointers lsublocs by blast
            then have ptrMC:"MCon (MTArray x t) (Memory st) ptr" using in1 mconPrnt 
              using MCon_imps_sub_Mcon by blast
            moreover have sub2:"\<forall>p ta. MCon ta (Memory st) p \<and> CompMemType (Memory st) len' (MTArray x t) ta prnt p \<longrightarrow> p \<noteq> prnt" 
              using MConPtrsMustBeSubLocs2[OF mconPrnt] by auto
            moreover have ptrPrnt:"CompMemType (Memory st) len' (MTArray x t) (MTArray x t)  prnt ptr" using ptrDef in1 by auto
            ultimately have prtNotPrnt:"ptr \<noteq> prnt" by blast
            have sub3:"\<forall>p ta. CompMemType (Memory st) x t ta ptr p \<longrightarrow> p \<noteq> prnt" using ptrPrnt sub2 ptrMC 
              by (metis CompMemType_imps_CompMemJustType CompTypeRemainsMCon MConSubTypes mconPrnt)
            have "MCon (MTArray x t) (Memory st') ptr" using ptrMC sub3 prtNotPrnt
            proof (induction t arbitrary:x ptr)
              case (MTArray x1 t)
              then have xnotZero:"x \<noteq> 0" by fastforce
              have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)) \<and>
                ((\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None)"
              proof intros
                fix i2 assume i2Def:"i2<x"
                have "ptr  \<noteq> prnt" using MTArray.prems by simp
                then have notL:"(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) \<noteq> l" using ldef ShowLNatDot 
                  using hash_injective by blast
                then have sameAccess:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st)" using nonLocChanged by auto
                then obtain ptr2 where ptr2Def: "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = Some (MPointer ptr2) \<and> MCon (MTArray x1 t) (Memory st) ptr2"
                  using MTArray.prems(1) i2Def 
                  by (metis MConArrayPointers MCon_imps_sub_Mcon bot_nat_0.not_eq_extremum xnotZero)
                moreover have "\<forall>p taa. CompMemType (Memory st) x1 t taa ptr2 p \<longrightarrow> p \<noteq> prnt " using MTArray.prems ptr2Def i2Def 
                  by (metis sameAccess CompMemType.simps(2))
                moreover have "ptr2 \<noteq> prnt" using MTArray.prems ptr2Def i2Def 
                  by (metis sameAccess CompMemType.simps(2))
                ultimately show "case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False
                      | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)))
                      | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
                  using MTArray.IH[of x1 ptr2] using ptr2Def by fastforce
                show " (\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None "
                proof(cases "ptr = l")
                  case True
                  then show ?thesis using 11 by simp
                next
                  case False
                  then show ?thesis using nonLocChanged MTArray.prems(1) 
                    using i2Def by fastforce
                qed
              qed
              then show ?case using MCon.simps(2)[of x "MTArray x1 t" "Memory st'" ptr] using xnotZero by simp
            next
              case (MTValue x')
              then have xnotZero:"x \<noteq> 0" by fastforce
              have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') (Memory st') loc2 | MTValue Types \<Rightarrow> False)) \<and>
                ((\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None)"
              proof(intros)
                fix i2 assume i2Def:"i2<x"
                have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) \<noteq> l" using MTValue 
                  by (metis MCon_sub_MTVal_imps_val memoryvalue.distinct(1) i2Def lOrigin option.inject) 
                then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st)" using nonLocChanged by simp
                then show "case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False
         | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)))
         | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
                  using i2Def MTValue 
                  by (metis (lifting) CompTypeRemainsMCon mtypes.distinct(1) mtypes.simps(6) memoryvalue.simps(5) Option.option.simps(5) linorder_less_linear mcon_accessStore not_less_zero
                      CompMemType.simps(1) MCon.simps(1))
                show "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None" 
                proof(cases "ptr = l")
                  case True
                  then show ?thesis using 11 by simp
                next
                  case False
                  then show ?thesis using nonLocChanged MTValue i2Def by auto
                qed
              qed
              then show ?case using MCon.simps(2)[of x "MTValue x'" "Memory st'" ptr] xnotZero by simp
            qed
            then show ?thesis 
              by (simp add: \<open>accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st)\<close> ptrDef)
          qed
        qed

        then show ?thesis using lenNotZero p2 by simp
      qed

      have compmemst':"\<forall>locs lens subTs. CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt 
                            \<and> MCon (MTArray lens subTs) (Memory st) locs 
                          \<longrightarrow> CompMemType (Memory (st')) lens subTs (MTArray len' arr') locs prnt"
      proof intros
        fix locs lens subTs
        assume asm1:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt  \<and> MCon (MTArray lens subTs) (Memory st) locs"
        then have asm5:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt" by blast
        have asm6:"MCon (MTArray lens subTs) (Memory st) locs" using asm1 by blast

        have mconl'':"MCon (MTArray len subT) (Memory st) l''" using  lInfo(5) tParentType  by simp


        then have a10:"CompMemType (Memory st') lens subTs (MTArray len' arr') locs prnt" using asm6 asm5
        proof(induction subTs arbitrary: lens locs)
          case (MTArray x11 x12)

          then obtain iIn lIn where iInDef:"iIn<lens \<and> accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = Some (MPointer lIn) 
                    \<and> (lIn = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType (Memory st) x11 x12 (MTArray len' arr') lIn prnt)"
            unfolding CompMemType.simps by blast
          have same2:" accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) =  accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st)" 
            using MConArrayPointers MTArray.prems(2)  bot_nat_0.not_eq_extremum iInDef le_eq_less_or_eq  nonLocChanged not_less_zero option.discI by metis
          then have mcIn:"MCon (MTArray x11 x12) (Memory st) lIn" using same2 iInDef MTArray.prems
            by (metis MCon_imps_sub_Mcon)
          then show ?case
          proof(cases "lIn = prnt")
            case True
            have "prnt \<noteq> l" using ldef 
              by (metis hash_inequality)
            moreover have "MTArray x11 x12 = MTArray len' arr'" using iInDef True 
              by (metis CompMemType_imps_CompMemJustType MConSubTypes \<open>MCon (MTArray x11 x12) (Memory st) lIn\<close> lsublocs mconPrnt CompMemJustType.simps(2))
            ultimately show ?thesis using True 
              by (metis MConPtrsMustBeSubLocs iInDef lsublocs nonLocChanged CompMemType.simps(2))
          next
            case False
            then have "CompMemType (Memory st) x11 x12 (MTArray len' arr') lIn prnt" using iInDef by blast
            then have cp:"CompMemType (Memory st') x11 x12 (MTArray len' arr') lIn prnt" using MTArray.IH[of x11 lIn] mcIn t7 by simp
            have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) \<noteq> l" 
              by (metis CompMemType_imps_CompMemJustType CompMemTypes_asc MConSubTypes memoryvalue.inject(2) iInDef lOrigin lsublocs mcIn mconlOld option.inject
                  CompMemJustType.simps(2))
            then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st')" 
              by (simp add:  nonLocChanged)
            then have "\<exists>i<lens. \<exists>l. accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer l)
                \<and> (l = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType (Memory st') x11 x12 (MTArray len' arr') l prnt)"
              using False cp iInDef by metis
            then show ?thesis unfolding CompMemType.simps(2) 
              using iInDef by blast
          qed
        next
          case (MTValue x2)
          then show ?case 
            using compType by auto
        qed
        then show "CompMemType (Memory st') lens subTs (MTArray len' arr') locs prnt" by blast
      qed

      have "(type.Memory (MTArray len subT), Stackloc l') |\<in>| fmran (Denvalue env) \<and> accessStore l' (Stack st) = Some (KMemptr l'')"
        using lInfo(2,3,4) tParentType by simp


      have subPNew_imp_old:"\<forall>stl2. TypedMemSubPrefPtrs (Memory st') x t p stl2 \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x t p stl2"
      proof intros
        fix stl2
        assume in1:"TypedMemSubPrefPtrs (Memory st') x t p stl2"
        then show "TypedMemSubPrefPtrs (Memory st) x t p stl2 " using asf pNotPrnt
        proof(induction t arbitrary:x p)
          case (MTArray x1 t)
          obtain iin lin where linDef: "iin<x \<and> accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer lin) 
                                        \<and> (lin = stl2 \<or> TypedMemSubPrefPtrs (Memory st') x1 t lin stl2)" 
            using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
          have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) \<noteq> l" using MTArray.prems(3) ldef ShowLNatDot 
            by (metis hash_injective)
          then have sameAccess:" accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') =  accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st)" using nonLocChanged by simp
          then show ?case 
          proof(cases "lin = stl2")
            case True
            then show ?thesis using MTArray.prems sameAccess linDef by force
          next
            case False
            then have "TypedMemSubPrefPtrs (Memory st') x1 t lin stl2" using linDef by simp
            moreover have "\<not> TypedMemSubPrefPtrs (Memory st) x1 t lin prnt" using MTArray.prems(2) linDef 
              using sameAccess by auto
            moreover have " lin \<noteq> prnt" using MTArray.prems linDef 
              using sameAccess by auto
            ultimately have "TypedMemSubPrefPtrs (Memory st) x1 t lin stl2" 
              using MTArray.IH[of x1 lin] by blast
            then show ?thesis 
              using linDef sameAccess by auto
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have subPOld_imp_new_cmp:"\<forall>stl2 x11 x12. CompMemType (Memory st) x t (MTArray x11 x12) p stl2 \<longrightarrow> CompMemType (Memory st') x t (MTArray x11 x12) p stl2"
      proof intros
        fix stl2  x11 x12
        assume in1:" CompMemType (Memory st) x t (MTArray x11 x12) p stl2"
        then show " CompMemType (Memory st') x t (MTArray x11 x12) p stl2" using asf pNotPrnt
        proof(induction t arbitrary:x p)
          case (MTArray x1 t)
          obtain iin lin where linDef: "iin<x \<and> accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = Some (MPointer lin) 
                                        \<and> (lin = stl2 \<and> MTArray x1 t = MTArray x11 x12 \<or> CompMemType (Memory st) x1 t (MTArray x11 x12) lin stl2)" 
            using MTArray.prems(1) unfolding CompMemType.simps by blast
          have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) \<noteq> l" using MTArray.prems(3) ldef ShowLNatDot 
            by (metis hash_injective)
          then have sameAccess:" accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') =  accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st)" using nonLocChanged by simp
          then show ?case 
          proof(cases "lin = stl2")
            case True
            then show ?thesis using MTArray.prems sameAccess linDef 
              by (metis (mono_tags, lifting) MTArray.IH CompMemType.simps(2) TypedMemSubPrefPtrs.simps(2))
          next
            case False
            then have "CompMemType (Memory st) x1 t (MTArray x11 x12) lin stl2" using linDef by simp
            moreover have "\<not> TypedMemSubPrefPtrs (Memory st) x1 t lin prnt" using MTArray.prems(2) linDef 
              using sameAccess by auto
            moreover have " lin \<noteq> prnt" using MTArray.prems linDef 
              using sameAccess by auto
            ultimately have "CompMemType (Memory st') x1 t (MTArray x11 x12) lin stl2" 
              using MTArray.IH[of x1 lin] by blast
            then show ?thesis 
              using linDef sameAccess by auto
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have prntPNeg:"\<forall>stl2 x11 x12. \<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<longrightarrow> \<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p"
      proof intros
        fix stl2 x11 x12
        assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p"
        show "\<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p "
        proof
          assume in2:"TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p"
          then show False using in1 
          proof(induction x12 arbitrary:x11 stl2)
            case (MTArray x1 t)
            obtain iin lin where linDef: "iin<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = Some (MPointer lin) 
                                        \<and> (lin = p \<or> TypedMemSubPrefPtrs (Memory st) x1 t lin p)" 
              using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
            then show ?case 
            proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) = l")
              case True
              then have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer p)" using linDef 11 unfolding updateStore_def accessStore_def by simp
              then show ?thesis using MTArray.prems(2) linDef by auto
            next
              case False
              then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st')" using nonLocChanged by simp
              then show ?thesis 
              proof(cases "lin = p")
                case True
                then show ?thesis using MTArray.prems(2) linDef sameAccess by auto
              next
                case False
                then have "TypedMemSubPrefPtrs (Memory st) x1 t lin p" using linDef by simp
                then show ?thesis using MTArray linDef sameAccess by auto
              qed
            qed
          next
            case (MTValue x)
            then show ?case by simp
          qed
        qed
      qed

      have subPNeg:"\<forall>stl2. \<not> TypedMemSubPrefPtrs (Memory st') x t p stl2 \<longrightarrow> \<not> TypedMemSubPrefPtrs (Memory st) x t p stl2"
      proof intros
        fix stl2 
        assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x t p stl2"
        show "\<not> TypedMemSubPrefPtrs (Memory st) x t p stl2 "
        proof
          assume in2:" TypedMemSubPrefPtrs (Memory st) x t p stl2"
          then show False using in1 asf pNotPrnt
          proof(induction t arbitrary:x p)
            case (MTArray x1 t)
            obtain iin lin where linDef: "iin<x \<and> accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = Some (MPointer lin) 
                                        \<and> (lin = stl2 \<or> TypedMemSubPrefPtrs (Memory st) x1 t lin stl2)" 
              using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
            then have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) \<noteq> l" using ldef MTArray.prems ShowLNatDot 
              by (metis hash_injective)

            then have sameAccess:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st')" using nonLocChanged by simp
            then show ?thesis 
            proof(cases "lin = stl2")
              case True
              then show ?thesis using MTArray.prems(2) linDef sameAccess by auto
            next
              case False
              then have "TypedMemSubPrefPtrs (Memory st) x1 t lin stl2" using linDef by simp
              then show ?thesis using MTArray linDef sameAccess 
                by (metis TypedMemSubPrefPtrs.simps(2))
            qed
          next
            case (MTValue x)
            then show ?case by simp
          qed
        qed
      qed

      have prntPNeg_2:"\<forall>stl2 x11 x12 dloc1. \<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<and> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 dloc1 
                                    \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 dloc1 "
      proof intros
        fix stl2 x11 x12 dloc1
        assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<and> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 dloc1"
        then show "TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 dloc1"
        proof(induction x12 arbitrary:x11 stl2)
          case (MTArray x1 t)
          obtain iin lin where linDef: "iin<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer lin) 
                                      \<and> (lin = dloc1 \<or> TypedMemSubPrefPtrs (Memory st') x1 t lin dloc1)" 
            using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
          then show ?case 
          proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) = l")
            case True
            then have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer p)" using linDef 11 unfolding updateStore_def accessStore_def by simp
            then show ?thesis using MTArray.prems(1) linDef by auto
          next
            case False
            then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st')" using nonLocChanged by simp
            then show ?thesis 
            proof(cases "lin = dloc1")
              case True
              then show ?thesis using MTArray.prems(1) linDef sameAccess by auto
            next
              case False
              then have "TypedMemSubPrefPtrs (Memory st') x1 t lin dloc1" using linDef by simp
              then show ?thesis using MTArray linDef sameAccess by auto
            qed
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have prntPNeg_sublocs_comp:"\<forall>stl2 x11 x12 dloc1 dt. \<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<and> CompMemType (Memory st) x11 x12 dt stl2 dloc1 
                                    \<longrightarrow> CompMemType (Memory st') x11 x12 dt stl2 dloc1 "
      proof intros
        fix stl2 x11 x12 dloc1 dt
        assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<and> CompMemType (Memory st) x11 x12 dt stl2 dloc1"
        then show "CompMemType (Memory st') x11 x12 dt stl2 dloc1"
        proof(induction x12 arbitrary:x11 stl2)
          case (MTArray x1 t)
          obtain iin lin where linDef: "iin<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = Some (MPointer lin) 
                                      \<and> (lin = dloc1 \<and> MTArray x1 t = dt \<or> CompMemType (Memory st) x1 t dt  lin dloc1)" 
            using MTArray.prems(1) unfolding CompMemType.simps by blast
          then show ?case 
          proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) = l")
            case True
            then have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer p)" using linDef 11 unfolding updateStore_def accessStore_def by simp
            then show ?thesis using MTArray.prems(1) linDef by auto
          next
            case False
            then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st')" using nonLocChanged by simp
            then show ?thesis 
            proof(cases "lin = dloc1")
              case True
              then show ?thesis using MTArray.prems(1) linDef sameAccess 
                using MTArray.IH by auto
            next
              case False
              then have "CompMemType (Memory st) x1 t dt  lin dloc1" using linDef by simp
              then show ?thesis using MTArray linDef sameAccess by auto
            qed
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have pPrntsLim:"\<forall>x11 x12 stl2. CompMemType (Memory st) x11 x12 (MTArray x t) stl2 p \<and> accessStore l (Memory st) \<noteq> Some (MPointer p) \<and> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p \<and>
    MCon (MTArray x11 x12) (Memory st) stl2 \<longrightarrow> CompMemType (Memory st') x11 x12 (MTArray x t) stl2 p"
      proof(intros)
        fix x11 x12 stl2
        assume "CompMemType (Memory st) x11 x12 (MTArray x t) stl2 p \<and>
       accessStore l (Memory st) \<noteq> Some (MPointer p) \<and> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p \<and> MCon (MTArray x11 x12) (Memory st) stl2"
        then show "CompMemType (Memory st') x11 x12 (MTArray x t) stl2 p"
        proof(induction x12 arbitrary: x11 stl2)
          case (MTArray x1 x12)
          obtain inI inL where inDef:"inI<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t inI)) (Memory st) = Some (MPointer inL) 
                              \<and> (inL = p \<or> TypedMemSubPrefPtrs (Memory st) x1 x12 inL p)" 
            using MTArray.prems unfolding TypedMemSubPrefPtrs.simps by blast
          then show ?case 
          proof(cases "inL = p")
            case True
            then show ?thesis 
              by (metis MTArray.prems inDef
                  existingLocation_imps_allLocs_same nonLocChanged CompMemType.simps(2))
          next
            case False
            then have "TypedMemSubPrefPtrs (Memory st) x1 x12 inL p" using inDef by auto
            moreover have "accessStore l (Memory st) \<noteq> Some (MPointer p)" using MTArray.prems by simp
            moreover have "MCon (MTArray x1 x12) (Memory st) inL" using MTArray.prems inDef 
              using MconSameTypeSameAccessWithTyping by blast
            moreover have "CompMemType (Memory st) x1 x12 (MTArray x t) inL p" 
              by (meson False MTArray.prems existingLocation_imps_allLocs inDef)
            ultimately have "CompMemType (Memory st') x1 x12 (MTArray x t) inL p" using MTArray.IH[of x1 inL] by blast
            moreover have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t inI)) (Memory st) = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t inI)) (Memory st')" 
            proof -
              obtain nn :: "nat \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> nat" where
                f1: "\<forall>X1 X4 X5. (\<exists>X7. hash X4 (ShowL\<^sub>n\<^sub>a\<^sub>t X7) = X5 \<and> X7 < X1) \<longrightarrow> hash X4 (ShowL\<^sub>n\<^sub>a\<^sub>t (nn X1 X4 X5)) = X5 \<and> nn X1 X4 X5 < X1"
                by moura
              obtain nna :: "String.literal \<Rightarrow> String.literal \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> nat" and nnb :: "String.literal \<Rightarrow> String.literal \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> nat" where
                f2: "\<forall>l la n m. (TypedMemSubPref l la (MTArray n m) \<or> (\<forall>na. hash la (ShowL\<^sub>n\<^sub>a\<^sub>t na) \<noteq> l 
            \<and> \<not> TypedMemSubPref l (hash la (ShowL\<^sub>n\<^sub>a\<^sub>t na)) m \<or> \<not> na < n)) \<and> ((hash la (ShowL\<^sub>n\<^sub>a\<^sub>t(nna l la n m)) = l 
              \<or> TypedMemSubPref l (hash la (ShowL\<^sub>n\<^sub>a\<^sub>t(nna l la n m))) m) \<and> nna l la n m < n \<or> \<not> TypedMemSubPref l la (MTArray n m))"
                using TypedMemSubPref.simps(2) by moura
              obtain nnc :: "nat \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> nat" where
                f3: "\<forall>s n t m l la. (CompMemType s n (MTValue t) m l la \<or> (\<forall>na. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t na) \<noteq> la \<or> \<not> na < n) 
          \<or> MTValue t \<noteq> m) \<and> ((hash l (ShowL\<^sub>n\<^sub>a\<^sub>t(nnc n l la)) = la \<and> nnc n l la < n) \<and> MTValue t = m \<or> \<not> CompMemType s n (MTValue t) m l la)"
                using f1 CompMemType.simps(1) by moura
              obtain ll :: "String.literal \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> (mtypes, memoryvalue) typedstore \<Rightarrow> String.literal" 
                  and lla :: "String.literal \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> memoryvalue store \<Rightarrow> String.literal" where
                f4: "TypedMemSubPref (ll inL x1 x12 (Memory st)) inL (MTArray x1 x12) \<or> TypedMemSubPref p inL (MTArray x1 x12)"
                by (meson CompMemType_imps_TypedMemSubPrefPtrs \<open>CompMemType (Memory st) x1 x12 (MTArray x t) inL p\<close> selfPoint_imps_TypedMemSubPref)
              obtain tt :: "mtypes \<Rightarrow> types" and nnd :: "mtypes \<Rightarrow> nat" and mm :: "mtypes \<Rightarrow> mtypes" where
                "x12 = MTArray (nnd x12) (mm x12) \<or> x12 = MTValue (tt x12) \<or> 0 = x1"
                by (metis (no_types) \<open>MCon (MTArray x1 x12) (Memory st) inL\<close> bot_nat_0.not_eq_extremum mcon_accessStore)
              then show ?thesis
                using f4 f3 f2 by (metis CompMemType_imps_CompMemJustType MConSubTypes memoryvalue.inject(2) \<open>CompMemType (Memory st) x1 x12 (MTArray x t) inL p\<close> \<open>MCon (MTArray x1 x12) (Memory st) inL\<close> inDef lOrigin less_nat_zero_code mconlOld nonLocChanged option.inject CompMemJustType.simps(2) CompMemType.simps(2))
            qed         
            ultimately show ?thesis using inDef unfolding CompMemType.simps by metis
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed

      qed

      have getToPrntNew_imps_Old:"\<forall>stl2 x11 x12. TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<and> prnt \<noteq> stl2 \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
      proof intros
        fix stl2 x11 x12 
        assume "TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<and> prnt \<noteq> stl2"
        then show "TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
        proof(induction x12 arbitrary:x11 stl2)
          case (MTArray x1 x12)
          obtain ii ll where llDef:"ii<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll) 
                                  \<and> (ll = prnt \<or> TypedMemSubPrefPtrs (Memory st') x1 x12 ll prnt)" 
            using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast

          then show ?case 
          proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) = l")
            case True
            then have "stl2 = prnt" using ldef ShowLNatDot 
              using hash_injective by blast
            then show ?thesis using MTArray.prems(1) by auto
          next
            case False
            then have same:" accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') =  accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
            then show ?thesis  
            proof(cases "ll = prnt")
              case True
              then show ?thesis using same llDef by force
            next
              case False
              then have "TypedMemSubPrefPtrs (Memory st') x1 x12 ll prnt" using llDef by simp
              then show ?thesis using MTArray.IH[of x1 ll] same False llDef by force
            qed
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have prntPrntNeg:"\<forall>stl2 x11 x12. \<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<and> prnt \<noteq> stl2 \<longrightarrow> \<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
      proof intros
        fix stl2 x11 x12
        assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<and> prnt \<noteq> stl2"
        show "\<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt "
        proof
          assume in2:"TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
          then show False using in1 
          proof(induction x12 arbitrary:x11 stl2)
            case (MTArray x1 t)
            obtain iIn lin where linDef: "iIn<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = Some (MPointer lin) 
                                        \<and> (lin = prnt \<or> TypedMemSubPrefPtrs (Memory st) x1 t lin prnt)" 
              using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
            then show ?case 
            proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) = l")
              case True
              then have "stl2 = prnt" using ldef ShowLNatDot 
                using hash_injective by blast
              then show ?thesis using MTArray.prems(2) linDef by simp
            next
              case False
              then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st')" using nonLocChanged by simp
              then show ?thesis 
              proof(cases "lin = prnt")
                case True
                then show ?thesis using MTArray.prems(2) linDef sameAccess by auto
              next
                case False
                then have "TypedMemSubPrefPtrs (Memory st) x1 t lin prnt" using linDef by simp
                then show ?thesis using MTArray linDef sameAccess by auto
              qed
            qed
          next
            case (MTValue x)
            then show ?case by simp
          qed
        qed
      qed


      have prntLim3Neg:"\<forall>x11' x12' stl2 stl1. \<not>TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 \<and> \<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1 \<and>
            stl2 \<noteq> prnt \<and> ( \<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')
            \<longrightarrow> \<not>TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 stl1"
      proof intros
        fix x11' x12' stl2 stl1
        assume "\<not>TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 \<and>
       \<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1 \<and>
       stl2 \<noteq> prnt \<and> (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')"
        then have in1:"\<not>TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1"
          and "\<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1"
          and "stl2 \<noteq> prnt"
          and " (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')" by simp+
        then show "\<not>TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 stl1"
        proof(induction x12' arbitrary:x11' stl2)
          case (MTArray x1 x12')
          then have iiNeg: "\<forall>i<x11'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') \<noteq> Some (MPointer l) 
                                          \<or> (l \<noteq> stl1 \<and> \<not>TypedMemSubPrefPtrs (Memory st') x1 x12' l stl1)"
            unfolding TypedMemSubPrefPtrs.simps by blast
          show ?case 
          proof
            assume "TypedMemSubPrefPtrs (Memory st) x11' (MTArray x1 x12') stl2 stl1"
            then obtain ii ll where iiDef: "ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll) 
                      \<and> (ll = stl1 \<or> TypedMemSubPrefPtrs (Memory st) x1 x12' ll stl1)"
              unfolding TypedMemSubPrefPtrs.simps by blast
            then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray.prems by blast
            then have same:" accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
            show False
            proof(cases "ll = stl1")
              case True
              then show ?thesis using iiDef same iiNeg 
                using MTArray.prems(1) by auto
            next
              case False
              then have s:"TypedMemSubPrefPtrs (Memory st) x1 x12' ll stl1" using iiDef by simp
              have llNotPrnt:"ll \<noteq> prnt"
              proof
                assume *:"ll = prnt"
                then have "MTArray x1 x12' = MTArray len' arr'" using MTArray.prems(4) iiDef by auto
                then show False using s MTArray.prems(2) * by simp
              qed
              then show ?thesis using same  MTArray.IH[OF ] iiDef MTArray.prems(4) 
                by (metis MTArray.prems(1,2) CompMemType.simps(2) TypedMemSubPrefPtrs.simps(2))
            qed
          qed

        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have prntLim4:"\<forall>x11' x12' stl2 stl1  dt. CompMemType (Memory st) x11' x12' dt stl2 stl1 \<and> \<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1 \<and>
            stl2 \<noteq> prnt \<and> ( \<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr') \<and> MCon (MTArray x11' x12') (Memory st) stl2 
            \<longrightarrow> CompMemType (Memory st') x11' x12' dt stl2 stl1"
      proof intros
        fix x11' x12' stl2 stl1 dt
        assume "CompMemType (Memory st) x11' x12' dt stl2 stl1 \<and>
       \<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1 \<and>
       stl2 \<noteq> prnt \<and> (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr') \<and> MCon (MTArray x11' x12') (Memory st) stl2"
        then have in1:"CompMemType (Memory st) x11' x12' dt stl2 stl1"
          and "\<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1"
          and "stl2 \<noteq> prnt"
          and " (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')" 
          and "MCon (MTArray x11' x12') (Memory st) stl2" by blast+
        then show "CompMemType (Memory st') x11' x12' dt stl2 stl1"
        proof(induction x12' arbitrary:x11' stl2)
          case (MTArray x1 x12')
          then obtain ii ll where iiDef: "ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll) 
                      \<and> (ll = stl1 \<and> MTArray x1 x12' = dt \<or> CompMemType (Memory st) x1 x12' dt ll stl1)"
            unfolding CompMemType.simps by blast
          then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray.prems by blast
          then have same:" accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
          then show ?case 
          proof(cases "ll = stl1")
            case True
            then have "MTArray x1 x12' = dt" using iiDef True 
              by (metis MTArray.prems(1,5) existingLocation_imps_allLocs_same)
            then show ?thesis using iiDef same True by force
          next
            case False
            then have s:"CompMemType (Memory st) x1 x12' dt ll stl1" using iiDef by simp
            have llNotPrnt:"ll \<noteq> prnt"
            proof
              assume *:"ll = prnt"
              then have "MTArray x1 x12' = MTArray len' arr'" using MTArray.prems(4) iiDef same by auto
              then show False using s MTArray.prems(2) * same 
                by (simp add: CompMemType_imps_TypedMemSubPrefPtrs)
            qed
            have "MCon (MTArray x1 x12') (Memory st) ll" using MTArray.prems(5) iiDef 
              using MconSameTypeSameAccessWithTyping by blast
            then have "CompMemType (Memory st') x1 x12' dt ll stl1" 
              using MTArray.IH[OF s MTArray.prems(2) llNotPrnt] iiDef MTArray.prems(4,5) by auto
            then show ?thesis using same iiDef by auto
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have prntLim5:"\<forall>x11' x12' stl2 dloc1 dt. TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1 
                        \<and>  (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = dloc1 \<longrightarrow> newt = dt)
                      \<and> stl2 \<noteq> prnt \<and> \<not> TypedMemSubPrefPtrs (Memory st') len' arr' prnt dloc1 
                    \<and> (\<forall>new newt. CompMemType (Memory st') x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')
                      \<longrightarrow> CompMemType (Memory st') x11' x12' dt stl2 dloc1"
      proof intros
        fix x11' x12' stl2 dloc1 dt
        assume " TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1 \<and>
       (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = dloc1 \<longrightarrow> newt = dt) \<and>
       stl2 \<noteq> prnt \<and>
       \<not> TypedMemSubPrefPtrs (Memory st') len' arr' prnt dloc1 \<and> (\<forall>new newt. CompMemType (Memory st') x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')"
        then have " TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1" and
          "(\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = dloc1 \<longrightarrow> newt = dt)"
          and "stl2 \<noteq> prnt"
          and "\<not> TypedMemSubPrefPtrs (Memory st') len' arr' prnt dloc1" 
          and "(\<forall>new newt. CompMemType (Memory st') x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')" by blast+
        then show "CompMemType (Memory st') x11' x12' dt stl2 dloc1"
        proof(induction x12' arbitrary: x11' stl2)
          case (MTArray x1 x12')
          obtain ii ll where iiDef:"ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll) 
                                      \<and> (ll = dloc1 \<or> TypedMemSubPrefPtrs (Memory st') x1 x12' ll dloc1)"
            using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by auto
          then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray.prems(3) by blast
          then have same:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
          then show ?case 
          proof(cases "ll = dloc1")
            case True
            then have "(MTArray x1 x12') = dt" using iiDef MTArray.prems(2) same by auto
            then show ?thesis using iiDef True by force
          next
            case False
            then have cc1:"TypedMemSubPrefPtrs (Memory st') x1 x12' ll dloc1" using iiDef by simp
            have cc2:"\<forall>new newt. CompMemType (Memory st) x1 x12' newt ll new \<and> new = dloc1 \<longrightarrow> newt = dt" using iiDef MTArray.prems(2) same by auto
            have cc3:"ll \<noteq> prnt"
            proof
              assume *:"ll = prnt"
              then have "(MTArray x1 x12') = MTArray len' arr'" using MTArray.prems(5) iiDef by auto
              then show False using MTArray.prems(4) cc1 * by simp
            qed
            have "\<forall>new newt. CompMemType (Memory st') x1 x12' newt ll new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr'" using MTArray.prems(5) same iiDef by force
            then have "CompMemType (Memory st') x1 x12' dt ll dloc1" 
              using MTArray.IH[OF cc1 cc2 cc3 MTArray.prems(4)] MTArray.prems iiDef same  by blast
            then show ?thesis using iiDef same by auto
          qed
        next
          case (MTValue x)
          show ?case using MTValue(1,2) by auto
        qed
      qed

      have prntLim6:"\<forall>x11' x12' stl2 dloc1. \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt\<and> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1\<and> stl2 \<noteq> prnt
              \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 dloc1"
      proof intros
        fix x11' x12' stl2 dloc1
        assume " \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1 \<and> stl2 \<noteq> prnt"
        then show "TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 dloc1 "
        proof(induction x12' arbitrary:x11' stl2)
          case (MTArray x1 x12')
          obtain ii ll where iiDef:"ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll) \<and>
                                         (ll = dloc1 \<or> TypedMemSubPrefPtrs (Memory st') x1 x12' ll dloc1)" 
            using MTArray.prems unfolding TypedMemSubPrefPtrs.simps by blast
          then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray by blast
          then have same:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') =accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
          then show ?case 
          proof(cases "ll = dloc1")
            case True
            then show ?thesis using same iiDef by force
          next
            case False
            then show ?thesis using iiDef same MTArray by auto
          qed
        next
          case (MTValue x)
          then show ?case by auto
        qed
      qed

      have prntLim7:"\<forall>x11' x12' stl2 stl1 dt.(\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = stl1 \<longrightarrow> newt = dt) 
                     \<and> \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> stl2 \<noteq> prnt
                     \<and> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 
                      \<longrightarrow> CompMemType (Memory st') x11' x12' dt stl2 stl1"
      proof intros
        fix x11' x12' stl2 stl1 dt
        assume "(\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = stl1 \<longrightarrow> newt = dt) \<and>
       \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> stl2 \<noteq> prnt \<and> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1"
        then have "(\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = stl1 \<longrightarrow> newt = dt)"
          and "\<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt"
          and "stl2 \<noteq> prnt"
          and "TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1" by blast+
        then show "CompMemType (Memory st') x11' x12' (dt) stl2 stl1"
        proof(induction x12' arbitrary:x11' stl2)
          case (MTArray x1 x12')
          then obtain ii ll where iiDef:"ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll) 
                                        \<and> (ll = stl1 \<or> TypedMemSubPrefPtrs (Memory st') x1 x12' ll stl1)"
            unfolding TypedMemSubPrefPtrs.simps by blast
          then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using MTArray.prems ldef ShowLNatDot hash_injective by blast
          then have same:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') =accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
          then show ?case 
          proof(cases "ll = stl1")
            case True
            then show ?thesis using same MTArray.prems(1) iiDef by force
          next
            case False
            then show ?thesis using same MTArray iiDef 
              by (metis (no_types, opaque_lifting) CompMemType.simps(2) TypedMemSubPrefPtrs.simps(2))
          qed
        next
          case (MTValue x)
          then show ?case by auto
        qed
      qed

      have prntLim8:"\<forall>x11' x12' stl2 stl1. \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 \<and>
                    \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> stl2 \<noteq> prnt
                    \<longrightarrow> \<not> TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 stl1"
      proof intros
        fix x11' x12' stl2 stl1
        assume "\<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 \<and> \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> stl2 \<noteq> prnt"
        then show "\<not> TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 stl1"
        proof(induction x12' arbitrary:x11' stl2)
          case (MTArray x1 x12')

          show ?case 
          proof
            assume *:"TypedMemSubPrefPtrs (Memory st) x11' (MTArray x1 x12') stl2 stl1"
            then obtain ii ll where  iiDef:"ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll) 
                                            \<and> (ll = stl1 \<or> TypedMemSubPrefPtrs (Memory st) x1 x12' ll stl1)"
              unfolding TypedMemSubPrefPtrs.simps by blast
            then have " (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray.prems by blast
            then have same:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st')" using nonLocChanged by simp
            show False
            proof(cases "ll = stl2")
              case True
              then show ?thesis using iiDef same MTArray.prems 
                using MTArray.IH by force
            next
              case False
              then show ?thesis using iiDef same MTArray by auto 
            qed
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed


      show ?thesis unfolding TypeSafe_def StateInvariant_def
      proof intros 
        show "AddressTypes (Accounts st')" using 2(1) 11 unfolding TypeSafe_def by simp
      next 
        show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
      next 
        have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
        then show "compPointers (Stack st')  (Denvalue env)"  using sameStack  sameStorage by simp
      next 
        show "safeContract (Accounts st') (Storage st')" using sameStorage 11  2(1) unfolding TypeSafe_def safeContract_def by auto
      next 
        show "balanceTypes (Accounts st')" using 11 using 2(1) unfolding TypeSafe_def by simp
      next 
        have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
      next 
        show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
      next 
        have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
          using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
        have **:"Toploc (Stack st) = Toploc (Stack st')" using 11 unfolding updateStore_def by auto
        show "lessThanTopLocs (Stack st')"  unfolding lessThanTopLocs_def
        proof intros

          fix tloc loc 
          assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
          then show "accessStore loc (Stack st') = None" using *  
            by (simp add: sameStack)
        next 
          fix loc y 
          assume h1:" accessStore loc (Stack st') = Some y"
          then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** * 
            by (metis sameStack)
        qed
      next 
        show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
      next
        have a12:"Toploc (Memory st) = Toploc (Memory st')" using 11 unfolding updateStore_def by auto
        have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
        have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
        show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def 
        proof intros
          fix tloc loc 
          assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then have b20:"Toploc (Memory st) \<le> tloc" using a12 tloc a12 
            by force

          then show "accessStore loc (Memory st') = None " 
            by (metis a15 b10 lOrigin lessThanSome_imps_Locs lessThanTopLocs_def linorder_not_less nonLocChanged)
        next 
          fix loc y 
          assume "accessStore loc (Memory st') = Some y "
          then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" 
            by (metis a12 a15 lOrigin lessThanTopLocs_def nonLocChanged)
        qed
      next 
        show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
          unfolding typeCompat_def
        proof intros
          fix tLook lLook
          assume inDen:" (tLook, lLook) |\<in>| fmran (Denvalue env)"
          show " case lLook of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case tLook of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case tLook of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False )
                | Some (KMemptr stloc) \<Rightarrow> (case tLook of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case tLook of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case tLook of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
          proof(cases lLook)
            case (Stackloc x1)
            then show ?thesis 
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc by force
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1')
                then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some  by force
              next
                case (KCDptr x2)
                then show ?thesis  using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by force
              next
                case (KMemptr x3)
                then obtain struct where stT: "tLook = type.Memory struct" using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some 
                  by (cases tLook; fastforce)
                have mcOld:"MCon struct (Memory st) x3"
                  using sameStorage inDen sameStack Stackloc Some KMemptr by (metis "2.prems"(1) sameMemTSafe stT)
                have tps:"(case struct of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr
                             | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))" 
                  using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def
                  using inDen sameStack Stackloc Some KMemptr stT by simp
                have nc:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')" using nonLocChanged by simp
                have subt:"subPrefixStructuralConsistency (Memory st)" using 2(1) unfolding TypeSafe_def by simp
                have "accessTypeStore l (Memory st) = Some (MTArray x t)" using lInfo 11 by auto
                then have "MCon struct (Memory st') x3" 
                  using 11(4) cpm2m_singleLChange[OF mcOld tps _ _ _ mcPNew subt nc ] lOrigin 
                  by simp                  
                then show ?thesis using sameStorage inDen sameStack Stackloc Some KMemptr stT by simp
              next
                case (KStoptr x4)
                then show ?thesis  using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by (cases tLook; force)
              qed
            qed
          next
            case (Storeloc x2)
            then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen 
              by (metis denvalue.simps(6))
          qed
        qed
        then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd " using sameStack by simp
      next 
        have "Accounts st'= Accounts st" using 11 by auto
        then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) 11 unfolding fullyInitialised_def  by auto
      next 
        have sameACCT:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
          using 11 lInfo unfolding accessTypeStore_def updateStore_def by auto

        show "denvalueTypeCorrectness env (Stack st') (Memory st') "
          unfolding denvalueTypeCorrectness_def
        proof(intros)
          fix t2 l2 ptr_loc sub_loc
          assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"

          show "case t2 of
         MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr) 
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          proof -
            have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
              using * 11 unfolding accessStore_def updateStore_def by simp
            then have mcOld:"MCon t2 (Memory st) ptr_loc" using * by (metis "2.prems"(1) sameMemTSafe)
            then have old:"(case t2 of
                           MTArray len arr \<Rightarrow>
           (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
 
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
              using sameACC 2(1) * TypeSafe_def denvalueTypeCorrectness_def by auto

            have inDenvalue:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env)" using * by simp 

            then show ?thesis
            proof(cases t2)
              case (MTArray x11 x12)
              then have mcOld:"MCon (MTArray x11 x12) (Memory st) ptr_loc" using mcOld by blast

              then have conc1:"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12)"
                using sameACCT old MTArray by simp
              then show ?thesis using MTArray 
                using lOrigin nonLocChanged old sameACCT by auto
            next 
              case (MTValue x2)
              have "accessTypeStore ptr_loc (Memory st') = Some (MTValue x2)" 
                using MTValue old sameACCT by auto
              then show ?thesis using MTValue by auto
            qed
          qed
        qed
      next 
        have oldSub:"subPrefixStructuralConsistency (Memory st)"
          using 2(1) unfolding TypeSafe_def by simp
        show "subPrefixStructuralConsistency (Memory st')" 
          unfolding subPrefixStructuralConsistency_def
        proof intros
          fix locs tp
          assume in1:" accessTypeStore locs (Memory st') = Some tp "
          have sameTy:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st') "
            using 11 unfolding updateStore_def accessTypeStore_def by auto
          show "case accessStore locs (Memory st') of None \<Rightarrow> False
                | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
                | Some (MPointer p) \<Rightarrow>
                   \<exists>len arr.
                      MCon tp (Memory st') p \<and>
                      tp = MTArray len arr \<and>
                      (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
          proof(cases "locs = l")
            case True
            have actO:"accessTypeStore l (Memory st) = Some (MTArray x t)" 
              using lInfo 11 nonLocChanged by auto
            then have tpDef:"tp = MTArray x t" 
              using sameTy True in1 by simp
            then have ptr:"accessStore locs (Memory st') = Some (MPointer p)" 
              using 11(4) True by simp
            moreover have " MCon tp (Memory st') p"   
              using tpDef mcPNew by fastforce
            moreover have "(\<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t)"
              using sameTy pTAccessOld by simp
            ultimately show ?thesis using True tpDef ptr by auto
          next
            case False
            then have sameACC:"accessStore locs (Memory st) = accessStore locs (Memory st')" 
              using nonLocChanged by simp
            then have in3:"(case accessStore locs (Memory st) of None \<Rightarrow> False | Some (MValue v) 
      \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
        | Some (MPointer p) \<Rightarrow>
            \<exists>len arr.
               MCon tp (Memory st) p \<and>
               tp = MTArray len arr \<and>
               (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) )" 
              using oldSub in1 sameTy unfolding subPrefixStructuralConsistency_def by fastforce
            then show ?thesis 
            proof(cases "accessStore locs (Memory st)")
              case None
              then show ?thesis using in3 sameACC by simp
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (MValue x1)
                then obtain val where " MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp"
                  using in3 Some by auto
                moreover have "MCon tp (Memory st') locs" using sameACC calculation by auto
                ultimately show ?thesis using sameACC Some MValue sameTy
                  by (auto split:option.splits)
              next
                case (MPointer x2)
                have accl:"accessTypeStore l (Memory st) = Some (MTArray x t)" 
                  using lInfo 11 nonLocChanged by auto

                then obtain len arr where s:"MCon tp (Memory st) x2 \<and> tp = MTArray len arr \<and>
                           (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)"
                  using Some in3 MPointer by auto
                then have mcM:"MCon tp (Memory st) x2" by auto
                have lTyp:"accessTypeStore l (Memory st) = Some (MTArray x t)"
                  using lInfo 11 by simp
                then have "MCon tp (Memory st') x2" 
                  using cpm2m_singleLChange[OF mcM _ _ _ lTyp mcPNew oldSub] 
                    11(4) accl s lOrigin nonLocChanged by auto
                moreover have "(\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
                  using s sameTy by simp

                ultimately show ?thesis using Some MPointer sameACC sameTy s
                  by (auto split:option.splits)
              qed
            qed
          qed
        qed

      next

        have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))" 
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
        have sameACCT:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
          using 11 lInfo unfolding accessTypeStore_def updateStore_def by auto

        show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def 
        proof intros
          fix locs
          show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
          proof(cases "locs = l")
            case True
            then have acc:"accessStore l (Memory st') = Some (MPointer p)"
              using 11 by simp
            then have "\<exists>v. accessStore l (Memory st) = Some v" using lOrigin by auto
            then have "\<exists>t. accessTypeStore l (Memory st) = Some t"
              using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by simp
            then show ?thesis using acc sameACCT True by simp
          next
            case False
            then show ?thesis using old sameACCT nonLocChanged by simp
          qed
        qed
      next 
        fix locs t 
        assume a1:"accessTypeStore locs (Memory st) = Some t"
        have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))" 
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
        have sameACCT:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
          using 11 lInfo unfolding accessTypeStore_def updateStore_def by auto

        show "accessTypeStore locs (Memory st') = Some t"
        proof(cases "locs = l")
          case True
          then have "\<exists>t. accessTypeStore l (Memory st) = Some t"
            using 2(1) a1 unfolding TypeSafe_def SomeValSomeTyp_def by simp
          then show ?thesis using sameACCT True a1 by simp
        next
          case False
          then show ?thesis using old sameACCT nonLocChanged a1 by simp
        qed
      next 
        show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
          using accL nonLocChanged by auto
      next
        show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
          by (metis memoryvalue.distinct(1) lOrigin nonLocChanged option.inject)
      next
        show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
          by (metis lOrigin nonLocChanged option.distinct(1))
      next 
        have a12:"Toploc (Memory st) = Toploc (Memory st')" using 11 unfolding updateStore_def by auto
        then show "Toploc (Memory st) \<le> Toploc (Memory st')" by simp
      qed
    qed
  next
    case (12 p x t g l t' g' p' m st'')
    have nonChangedStack:"\<forall>loc. loc \<noteq> l \<longrightarrow> accessStore loc (Stack st) = accessStore loc (Stack st')" using 12 unfolding accessStore_def updateStore_def by auto
    have accessLStack:"accessStore l (Stack st') = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 12 unfolding accessStore_def updateStore_def by auto
    have sameStorage:"Storage st'  = Storage st " using 12 by auto
    have lInDen:"(type.Memory t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[of lv env cd] 12(2) by simp
    have nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
      using 12(6) unfolding cps2m_def using  cps2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m] 
      by simp
    have a30:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> TypedStoSubpref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
      using  12(6) unfolding cps2m_def using cps2mSingleChange2[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m]  by fastforce
    have selfPoint:"\<forall>l l'. l \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> TypedStoSubpref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l" 
      using  12(6) unfolding cps2m_def using cps2mSelfPointers[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ] by blast
    have mInStd:"m = Memory st'" using 12 by simp

    obtain memArr where memArrDef: "t' = MTArray x memArr" using 12(3) cps2mTypeCompatible.simps 
      by (metis mtypes.exhaust)

    have p'MCon:"MCon t' (Memory st) p'" using 2 12(4) unfolding TypeSafe_def typeCompat_def using lInDen by (auto split:denvalue.splits option.splits stackvalue.splits type.splits)

    have MConsrc:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) \<and> (\<exists>xx. KStoptr p = KStoptr xx)"
      using 2(1) 12(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KStoptr p" "type.Storage (STArray x t)" g] 

      using 2(3) unfolding fullyInitialised_def 
      by (auto split:type.splits if_splits )
    have "(\<exists>p. accessStore p' (Memory st) = Some (MPointer p)) \<or> accessStore p' (Memory st) = None" using p'MCon 12(3,4,5) 
      using cps2mTypeCompatible.elims(2) by fastforce

    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
    then have MCondest:"MCon (MTArray x memArr) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using  12(6,3) unfolding cps2m_def
      using cps2m[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m memArr] MConsrc extractValueType.simps(2) memArrDef by simp
    have selfPoint2:"\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> accessStore l (Memory st') = Some (MPointer l') \<longrightarrow> l' = l" using selfPoint limitSt1 limitSt 
        "12"(6) a30 accessPrePost1 allocateSameAccess cpm2m_def eq_imp_le hash_inequality not_Some_eq 
      by (metis cps2mAccessPrePost cps2m_def mInStd)

    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                              \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

    have noC:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
      using allocateSameAccess nonLocChanged mInStd by metis
    have cc:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) t' \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
      using a30 mInStd compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 12(3)] allocateSameAccess
      by (metis (no_types, lifting) "12"(6) cps2mSingleChange cps2m_def)

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros 
      show "AddressTypes (Accounts st')" using 2(1) 12 unfolding TypeSafe_def by simp
    next 
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      show "compPointers (Stack st') (Denvalue env)"  unfolding compPointers_def
      proof(intros)
        fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
         (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
         (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
        then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
          using a0 nonChangedStack accessLStack sameStorage
          by (smt (verit) stackvalue.distinct(11) compPointers_def option.inject)
      qed
    next 
      show "safeContract (Accounts st') (Storage st')" using sameStorage using 12 2(1) unfolding TypeSafe_def safeContract_def by auto
    next 
      show "balanceTypes (Accounts st')" using 12 using 2(1) unfolding TypeSafe_def by simp
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
                (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 12 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')"  unfolding lessThanTopLocs_def
      proof intros

        fix tloc loc 
        assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
        then show "accessStore loc (Stack st') = None" using *  
          by (metis "12"(4) nonChangedStack not_None_eq)
      next 
        fix loc y 
        assume h1:" accessStore loc (Stack st') = Some y"
        then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** * 
          by (metis "12"(4) nonChangedStack)        
      qed
    next 
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      have a10:"Toploc (snd (allocate (Memory st))) = Toploc m" using cps2mTopLocSame 12(6) mInStd unfolding cps2m_def  by blast
      have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp

      have a30: "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m" using nonLocChanged
        by (metis allocateSameAccess)
      have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
      show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def 
      proof intros
        fix tloc loc 
        assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have b20:"Toploc (Memory st) \<le> tloc" using a10 tloc mInStd by simp
        have "\<not>LSubPrefL2 loc p'" 
        proof(rule ccontr)
          assume c10:"\<not> \<not> LSubPrefL2 loc p'"
          then have c20: "LSubPrefL2 loc p'" by simp
          then have c30:"LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using b10  MemLSubPrefTransitive by auto
          then show False
          proof -
            have "MCon t' (Memory st) p'" using 12(4) 2(1) unfolding TypeSafe_def typeCompat_def using lInDen by fastforce
            then obtain x i where c40: "accessStore p' (Memory st) = Some x \<or> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using MCon_imps_Some by blast
            then show ?thesis
            proof(cases "accessStore p' (Memory st) = Some x")
              case True
              then show ?thesis using lessThanSome_imps_Locs[OF a15 True c30] b20 by simp
            next
              case False
              then have "accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using c40 by simp
              then show ?thesis using lessThanSome_imps_Locs2  c30 a15 b20 by fastforce
            qed
          qed
        qed
        then show "accessStore loc (Memory st') = None " using b10 b20 nonLocChanged a10 mInStd a15 a30 
          by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive antisym_conv2 hash_inequality hash_suffixes_associative hashesIntSame lessThanTopLocs_def order_less_le_trans tloc)

      next 
        fix loc y 
        assume "accessStore loc (Memory st') = Some y "
        then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" 
          by (metis a10 a15 a30 lessThanTopLocs_def order_less_trans mInStd tloc)
      qed
    next 
      show ns:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t'' l'
        assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"
        show " case l' of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t'' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t'' of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False )
              | Some (KMemptr stloc) \<Rightarrow> (case t'' of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t'' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t'' of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases l')
          case (Stackloc x1)
          then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using accessLStack nonChangedStack by fastforce
          then show ?thesis 
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(3) stackvalue.simps(17) option.inject)
          next
            case (KCDptr x2)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) accessLStack nonChangedStack unfolding TypeSafe_def  typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(7) stackvalue.simps(18) option.inject)
          next
            case (KMemptr x3)
            then have "\<exists>struct. t'' = type.Memory struct" 
            proof(cases "x1 = l")
              case True
              have "accessStore l (Stack st) = Some (KMemptr p')" using 12(4) by simp
              then show ?thesis using Stackloc adef  inDen Stackloc 2(1) KMemptr True unfolding TypeSafe_def typeCompat_def by (cases t'';force+) 
            next
              case False
              then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" using accessLStack nonChangedStack by simp
              then show ?thesis using Stackloc adef  inDen Stackloc 2(1) KMemptr unfolding TypeSafe_def typeCompat_def by (cases t'';force+) 
            qed
            then obtain struct where structdef:"t'' = type.Memory struct" by blast


            have "MCon struct (Memory st') x3" 
            proof(cases "x1 = l")
              case True
              then have x3Def:"x3 = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 12 KMemptr adef unfolding accessStore_def updateStore_def by auto
              have "(type.Memory struct, Stackloc x1) |\<in>| fmran (Denvalue env)"
                using Stackloc inDen structdef by blast
              then have "t' = struct" using "12"(4) True lInDen "2.prems"(1) 
                unfolding TypeSafe_def unique_locations_def by auto

              then show ?thesis using memArrDef MCondest 12 Stackloc True inDen lInDen mInStd structdef x3Def   unfolding accessStore_def updateStore_def by metis
            next
              case False
              then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" using accessLStack nonChangedStack by simp
              then have "accessStore x1 (Stack st) = Some (KMemptr x3)" using adef KMemptr by simp
              then have mgh:"MCon struct (Memory st) x3" using inDen KMemptr Stackloc adef structdef 2(1) unfolding TypeSafe_def typeCompat_def by force

              then show ?thesis using originalMConStillMCon[OF mgh limitSt noC] cc mInStd allocateSameAccess by metis
            qed
            then show ?thesis  using structdef KMemptr Stackloc adef  inDen Stackloc 2(1) unfolding TypeSafe_def by simp

          next
            case (KStoptr x4)  
            then show ?thesis using Stackloc adef sameStorage  inDen Stackloc KStoptr 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def apply(cases t'') 
              apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(3) type.simps(17) lInDen old.prod.inject snd_eqD uniqueLocs)
              apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(7) type.simps(18) lInDen old.prod.inject snd_eqD uniqueLocs)

              apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(11) stackvalue.simps(20) type.simps(19) option.inject)

              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(11) type.simps(20) lInDen prod.inject snd_conv uniqueLocs)
          qed

        next
          case (Storeloc x2)
          then show ?thesis using sameStorage inDen 2(1) unfolding TypeSafe_def typeCompat_def by (cases t''; force)
        qed
      qed




    next 
      have "Accounts st'= Accounts st" using 12 by auto
      then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) 12 unfolding fullyInitialised_def updateStore_def accessStore_def by auto
    next 

      show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
      proof(intros)
        fix t2 l2 ptr_loc sub_loc
        assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"

        show "case t2 of
         MTArray len arr \<Rightarrow>
           (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        proof(cases "ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
          case False
          then have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
            using nonChangedStack * 12(5) unfolding accessStore_def updateStore_def 
            by (metis stackvalue.inject(3) accessLStack accessStore_def option.inject)
          then have mcOld:"MCon t2 (Memory st) ptr_loc" using * by (metis "2.prems"(1) sameMemTSafe)
          then have old:"(case t2 of
                           MTArray len arr \<Rightarrow>
                             (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
                           | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
            using sameACC 2(1) * TypeSafe_def denvalueTypeCorrectness_def by fastforce

          have inDenvalue:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env)" using * by simp
          have lims:"\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) ptr_loc"
            using typeSafe_noDenElementOverToploc_mem[OF 2(1) inDenvalue] * sameACC False
            using LSubPrefL2_def MemLSubPrefTransitive by metis

          then show ?thesis
          proof(cases t2)
            case (MTArray x11 x12)
            have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12)" using old MTArray by simp

            have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) 
                                          \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
              using lims mInStd 12(6) unfolding cps2m_def 
              by (metis allocateTypeSameAccess cps2mSingleChange_Typed cps2m_def)
            have nonLocChanged_TypedSafe2:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) 
                                          \<longrightarrow> accessStore loc (Memory st') = accessStore loc (Memory st)"
              using lims mInStd 12(6) unfolding cps2m_def 
              by (metis allocateSameAccess cps2mSingleChange cps2m_def)
            have "\<forall>i. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
              using lims Mutual_NonSub_SpecificNonSub by blast
            then have conc0:"\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12" 
              using old' lims nonLocChanged_TypedSafe by auto
            then show ?thesis using MTArray old lims nonLocChanged_TypedSafe2 
              using nonLocChanged_TypedSafe by auto

          next
            case (MTValue x2)
            have "\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using lims by simp
            then have "accessTypeStore ptr_loc (Memory st') = accessTypeStore ptr_loc (Memory st)"
              by (metis "12"(6) allocateTypeSameAccess cps2mSingleChange_Typed cps2m_def mInStd)
            then show ?thesis using MTValue old by simp
          qed
        next
          case True                                         
          then have newLocation:"l2 = l \<and> t2 = (MTArray x memArr)"
            using lInDen accessLStack * memArrDef "2.prems"(1) "12"(3,5,7) LSubPrefL2_def nonChangedStack snd_eqD typeSafeUnique typeSafe_noDenElementOverToploc_mem
              unique_locations_def 
            by (metis Pair_inject type.inject(3))

          then have l2IsL:"l2 = l" using newLocation by simp
          then have conc0:"ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using * 12(5,7) by auto
          have conc1:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some memArr" 
            using 12(3,6) memArrDef unfolding cps2m_def 
            using cps2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m]
              mInStd by blast
          show ?thesis using conc1 conc0 newLocation by simp
        qed
      qed
    next
      have old:"subPrefixStructuralConsistency (Memory st)" using 2(1) unfolding TypeSafe_def by simp
      have noC:"\<forall>locs.
     \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"  
        by (metis (lifting) "12"(6) allocateTypeSameAccess cps2mSingleChange_Typed cps2m_def mInStd)
      have some:"SomeValSomeTyp (Memory st)" using 2(1) unfolding TypeSafe_def by simp
      have less:"lessThanTopLocs (Memory st)" using 2(1) unfolding TypeSafe_def by simp
      have n:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st) = None" using limitSt 
        using \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame by presburger

      have cc:"\<forall>locs.
       \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
       accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')" using memArrDef 
        by (metis (lifting) "12"(3,6) allocateTypeSameAccess compatible_TypedStoSubpref_imps_TypedMemSubPref_neg
            cps2mSingleChange2_Typed cps2m_def mInStd noC)
      have tps:"\<forall>destl'.
     TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
     (\<exists>stt. CompMemType (Memory st') x memArr stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) destl' \<and>
            (case stt of
             MTArray parent_len parent_arr \<Rightarrow>
               \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' (Memory st') = Some (MTValue pval)))"
        using 12(3,6) unfolding cps2m_def
        using cps2m_TypeCompChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m memArr]
          mInStd memArrDef by blast
      have mc:"MCon (MTArray x memArr) (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        using MCondest mInStd by blast
      have conc1:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some memArr" 
        using 12(3,6) memArrDef unfolding cps2m_def 
        using cps2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m]
          mInStd by blast

      have noC2:"\<forall>locs.
       \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
       accessStore locs ((Memory st)) = accessStore locs (Memory st')"  
        using "12"(6) unfolding cps2m_def 
        using cps2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m] 
          mInStd allocateSameAccess by metis
      have nocc2:"\<forall>locs.
       \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
       accessStore locs (Memory st) = accessStore locs (Memory st')"
        using "12"(6) unfolding cps2m_def 
        using cps2mSingleChange2[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m] 
          mInStd allocateSameAccess compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 12(3)]  
        by (metis memArrDef noC2)

      show "subPrefixStructuralConsistency (Memory st')" 
        using cpm2m_subPrefixPersist[OF old n some noC less cc tps mc _ conc1 noC2 nocc2] 
        using selfPoint2 typedPrefix_imp_SubPref by blast
    next 
      have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))" 
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      have somesome:"\<forall>destl'. TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) 
            \<longrightarrow> (\<exists>t. accessStore destl' m = Some t) = (\<exists>tt. accessTypeStore destl' m = Some tt)"
        using 12(6,3) unfolding cps2m_def 
        using cps2m_TypeCompChange_somesome[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m] 
          compatible_TypedStoSubpref_imps_TypedMemSubPref memArrDef by blast
      have a30T:"\<forall>locs.
       locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> TypedStoSubpref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow>
       accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs (Memory st')" 
        using 12(6,3) unfolding cps2m_def using cps2mSingleChange2_Typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]
        using mInStd by blast
      then have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
       accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs (Memory st')" 
        using mInStd allocateTypeSameAccess memArrDef compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 12(3)]  
        by (metis "12"(6) cps2mSingleChange_Typed cps2m_def)

      show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def 
      proof intros
        fix locs
        show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
        proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)")
          case True
          then have "(\<exists>t. accessStore locs m = Some t) = (\<exists>tt. accessTypeStore locs m = Some tt)" 
            using somesome by simp
          then show ?thesis using mInStd by simp
        next
          case False
          then have "accessStore locs (Memory st) = accessStore locs (Memory st')" 
            using a30 mInStd allocateSameAccess 
            by (metis (mono_tags, lifting) "12"(3,6) compatible_TypedStoSubpref_imps_TypedMemSubPref_neg cps2mSingleChange cps2m_def
                memArrDef)
          moreover have "accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using a30T False 
            by (metis allocateTypeSameAccess)
          ultimately show ?thesis using old by metis
        qed
      qed
    next 
      fix locs tt 
      have a30T:"\<forall>locs.
       locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> TypedStoSubpref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow>
       accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs (Memory st')" 
        using 12(6,3) unfolding cps2m_def using cps2mSingleChange2_Typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]
        using mInStd by blast

      assume a1:"accessTypeStore locs (Memory st) = Some tt"
      then have some:"\<exists>v. accessStore locs (Memory st) = Some v"
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by auto
      show "accessTypeStore locs (Memory st') = Some tt " 
      proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)")
        case True
        then show ?thesis using mInStd a1 some 
          by (metis le_refl limitSt option.distinct(1) typedPrefix_imp_SubPref)
      next
        case False

        then have "accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
          using a30T False 
          by (metis \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame allocateTypeSameAccess limitSt neg_LSubPrefL2_imps_neg_TypedStoSubpref
              option.distinct(1) some verit_comp_simplify1(2))
        then show ?thesis using a1 by auto
      qed
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        by (metis allocateSameAccess dual_order.eq_iff limitSt mInStd nonLocChanged not_None_eq)
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        by (metis allocateSameAccess limitSt mInStd nonLocChanged not_None_eq verit_comp_simplify1(2))
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using allocateSameAccess limitSt mInStd nonLocChanged
        by (metis LSubPrefL2_def MemLSubPrefTransitive hash_flatten_right hash_inequality hashesIntSame nat_neq_iff)
    next
      have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
      moreover have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc (Memory st')" 
        using cps2mTopLocSame 12(6) cps2m_def mInStd MCondest 
        by (metis (no_types, lifting))
      ultimately show "Toploc (Memory st) \<le> Toploc (Memory st')" by simp
    qed        
  next
    case (13 p x t g l t' g')
    then have stackChanged:"\<forall>l'. l' \<noteq> l \<longrightarrow> accessStore l' (Stack st) = accessStore l' (Stack st')" unfolding updateStore_def accessStore_def by simp
    have t'InDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[OF 13(2)] by blast
    then have lDen:"\<forall>t'. (t', Stackloc l) |\<in>| fmran (Denvalue env) \<longrightarrow> t'= (type.Storage (STArray x t))" using 13 2(1) unfolding TypeSafe_def unique_locations_def by auto

    have pOrigin:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) \<and>
        (\<exists>xx. KStoptr p = KStoptr xx) \<and>
        (\<exists>stloc tp'' .
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue env) \<and>
            (tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p))))" 
      using 2(1) 13(1) 2(3) using
        exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KStoptr p" "type.Storage (STArray x t)" g] 
      by (auto split:type.splits if_splits )
    obtain pParent pParentT  where 
      pOrigin:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) 
          \<and>(type.Storage pParentT, Storeloc pParent) |\<in>| fmran (Denvalue env) \<and>
            (pParentT = (STArray x t) \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and> CompStoType pParentT (STArray x t) pParent (extractValueType (KStoptr p)))"
      using pOrigin by auto
    have a0: "compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    then have pParentRelations:"(\<forall>tp2 l2  l2'  stl2.
        (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
        
        (l2 = Stackloc l2' \<and> accessStore l2' (Stack (st)) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
        (if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2 else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True))" 
      using compPointers_def pOrigin  by blast
    have pSCon:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st) (Address env))" using pOrigin by force

    have pRelations:"(\<forall>tp2 l2 l2' stl2 . 
    (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and> 
    ((l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some(KStoptr stl2)) \<or> (l2 = Storeloc stl2)) 
     \<longrightarrow>
    (if TypedStoSubpref p stl2 tp2 then CompStoType tp2 (STArray x t) stl2 p 
     else if TypedStoSubpref stl2 p (STArray x t) then CompStoType (STArray x t) tp2 p stl2
     else True))" 
    proof intros 
      fix tp2 l2 l2' stl2
      assume in1:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"

      show "if TypedStoSubpref p stl2 tp2 then CompStoType tp2 (STArray x t) stl2 p else if TypedStoSubpref stl2 p (STArray x t) then CompStoType (STArray x t) tp2 p stl2 else True"
      proof(cases "l2 = Stackloc l2'")
        case StL2:True
        then have mcStl2:"SCon tp2 stl2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using in1 by fastforce

        then have "SCon pParentT pParent (Storage st (Address env))" using pOrigin using 2(1) unfolding TypeSafe_def typeCompat_def by force
        have prnt:" pParentT = STArray x t \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and> CompStoType pParentT (STArray x t) pParent (extractValueType (KStoptr p))"
          using pOrigin by simp
        then have comp:"(if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2 
                      else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True)"
          using pParentRelations in1  StL2 prnt by force 
        then show ?thesis 
        proof(cases "TypedStoSubpref p stl2 tp2")
          case pToStl2:True        

          then show ?thesis 
          proof(cases "pParentT = (STArray x t)")
            case True
            then have cc1:"KStoptr p = KStoptr pParent " using prnt 
              using comp_stotype_same_type_same_loc by blast
            then have cc2:"TypedStoSubpref pParent stl2 tp2" using pToStl2 by auto
            then have "CompStoType tp2 (STArray x t) stl2 p"
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case t2:True
              then show ?thesis using comp 
                by (metis CompStoType_sameLoc_sameType stackvalue.inject(4) True cc1 cc2 typedStoSub_imps_negInv)
            next
              case False
              then have "CompStoType tp2 pParentT stl2 pParent" using comp 
                by (simp add: cc2)
              then show ?thesis 
                using True cc1 by auto
            qed
            then show ?thesis by (simp add: pToStl2)
          next
            case False
            then have cmp:" CompStoType pParentT (STArray x t) pParent p" using prnt by simp
            then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
            then show ?thesis 
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case True
              then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
              have "CompStoType tp2 (STArray x t) stl2 p " using pToStl2 prntStl2  CompStoType_sharedSub cmp by simp
              then show ?thesis using pToStl2 by simp
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                then have "CompStoType tp2 (STArray x t) stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                then show ?thesis using pToStl2 by simp
              next
                case False
                then have "\<not>TypedStoSubpref p stl2 tp2" using f1 cmp tsp NotRelatedPrnt_imps_notRelatedChild[of stl2 pParent pParentT tp2 p]  by simp
                then show ?thesis using f1 pToStl2 cmp by simp
              qed
            qed
          qed
        next
          case f1:False
          then show ?thesis 
          proof(cases " TypedStoSubpref stl2 p (STArray x t)")
            case stl2ToP:True
            have " CompStoType (STArray x t) tp2 p stl2"
            proof(cases "pParentT = (STArray x t)")
              case True
              then have cc1:"KStoptr p = KStoptr pParent " using prnt 
                using comp_stotype_same_type_same_loc by blast
              then have cc2:"TypedStoSubpref stl2 pParent (STArray x t)" using stl2ToP by auto
              then have " CompStoType (STArray x t) tp2 p stl2"
              proof(cases "TypedStoSubpref stl2 pParent pParentT")
                case t2:True
                then have "CompStoType pParentT tp2 pParent stl2" using comp by simp
                then have "CompStoType (STArray x t) tp2 p stl2" using cc1 True  by blast
                then show ?thesis by blast
              next
                case False
                then show ?thesis 
                proof(cases "TypedStoSubpref pParent stl2 tp2")
                  case True
                  then have "CompStoType tp2 pParentT stl2 pParent" using comp False by simp
                  then show ?thesis using True cc1 f1 by auto
                next
                  case f2:False
                  then show ?thesis using False True cc2 by blast
                qed
              qed
              then show ?thesis by blast
            next
              case False
              then have cmp:" CompStoType pParentT (STArray x t) pParent p" using prnt by simp
              then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
              then show ?thesis 
              proof(cases "TypedStoSubpref stl2 pParent pParentT")
                case True
                then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
                then show ?thesis using CompStoType_sharedSub[OF prntStl2 stl2ToP cmp] by simp
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref pParent stl2 tp2")
                  case True
                  then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                  then have "CompStoType tp2 (STArray x t) stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                  then show ?thesis 
                    using CompStoType_sameLocNdTyp CompStoType_sharedSub stl2ToP by blast
                next
                  case False
                  then show ?thesis 
                    using NotReachablePrnt_imps_notReachableChild cmp f1 stl2ToP by blast
                qed
              qed
            qed
            then show ?thesis using f1 by (simp )
          next
            case False
            then show ?thesis 
              using f1 by auto
          qed
        qed

      next
        case f3:False
        then have StL2:"l2 = Storeloc stl2" 
          using in1 by auto

        then have "SCon pParentT pParent (Storage st (Address env))" using pOrigin using 2(1) unfolding TypeSafe_def typeCompat_def by force
        have prnt:" pParentT = STArray x t \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and> CompStoType pParentT (STArray x t) pParent (extractValueType (KStoptr p))"
          using  pOrigin by simp
        then have comp:"(if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2 
                      else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True)"
          using pParentRelations in1  StL2 prnt by force 
        then show ?thesis 
        proof(cases "TypedStoSubpref p stl2 tp2")
          case pToStl2:True        

          then show ?thesis 
          proof(cases "pParentT = (STArray x t)")
            case True
            then have cc1:"KStoptr p = KStoptr pParent " using prnt 
              using comp_stotype_same_type_same_loc by blast
            then have cc2:"TypedStoSubpref pParent stl2 tp2" using pToStl2 by auto
            then have "CompStoType tp2 (STArray x t) stl2 p"
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case t2:True
              then show ?thesis using comp 
                by (metis CompStoType_sameLoc_sameType stackvalue.inject(4) True cc1 cc2 typedStoSub_imps_negInv)
            next
              case False
              then have "CompStoType tp2 pParentT stl2 pParent" using comp 
                by (simp add: cc2)
              then show ?thesis 
                using True cc1 by auto
            qed
            then show ?thesis by (simp add: pToStl2)
          next
            case False
            then have cmp:" CompStoType pParentT (STArray x t) pParent p" using prnt by simp
            then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
            then show ?thesis 
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case True
              then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
              have "CompStoType tp2 (STArray x t) stl2 p " using pToStl2 prntStl2  CompStoType_sharedSub cmp by simp
              then show ?thesis using pToStl2 by simp
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                then have "CompStoType tp2 (STArray x t) stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                then show ?thesis using pToStl2 by simp
              next
                case False
                then have "\<not>TypedStoSubpref p stl2 tp2" using f1 cmp tsp NotRelatedPrnt_imps_notRelatedChild[of stl2 pParent pParentT tp2 p]  by simp
                then show ?thesis using f1 pToStl2 cmp by simp
              qed
            qed
          qed
        next
          case f1:False
          then show ?thesis 
          proof(cases " TypedStoSubpref stl2 p (STArray x t)")
            case stl2ToP:True
            have " CompStoType (STArray x t) tp2 p stl2"
            proof(cases "pParentT = (STArray x t)")
              case True
              then have cc1:"KStoptr p = KStoptr pParent " using prnt 
                using comp_stotype_same_type_same_loc by blast
              then have cc2:"TypedStoSubpref stl2 pParent (STArray x t)" using stl2ToP by auto
              then have " CompStoType (STArray x t) tp2 p stl2"
              proof(cases "TypedStoSubpref stl2 pParent pParentT")
                case t2:True
                then have "CompStoType pParentT tp2 pParent stl2" using comp by simp
                then have "CompStoType (STArray x t) tp2 p stl2" using cc1 True  by blast
                then show ?thesis by blast
              next
                case False
                then show ?thesis 
                proof(cases "TypedStoSubpref pParent stl2 tp2")
                  case True
                  then have "CompStoType tp2 pParentT stl2 pParent" using comp False by simp
                  then show ?thesis using True cc1 f1 by auto
                next
                  case f2:False
                  then show ?thesis using False True cc2 by blast
                qed
              qed
              then show ?thesis by blast
            next
              case False
              then have cmp:" CompStoType pParentT (STArray x t) pParent p" using prnt by simp
              then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
              then show ?thesis 
              proof(cases "TypedStoSubpref stl2 pParent pParentT")
                case True
                then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
                then show ?thesis using CompStoType_sharedSub[OF prntStl2 stl2ToP cmp] by simp
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref pParent stl2 tp2")
                  case True
                  then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                  then have "CompStoType tp2 (STArray x t) stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                  then show ?thesis 
                    using CompStoType_sameLocNdTyp CompStoType_sharedSub stl2ToP by blast
                next
                  case False
                  then show ?thesis 
                    using NotReachablePrnt_imps_notReachableChild cmp f1 stl2ToP by blast
                qed
              qed
            qed
            then show ?thesis using f1 by (simp )
          next
            case False
            then show ?thesis using f1 by auto
          qed
        qed
      qed
    qed

    have storageSame:"(Storage st' (Address env)) = (Storage st (Address env))" using 13 by simp
    have memorySame:"Memory st = Memory st'" using 13 by simp
    show ?thesis unfolding TypeSafe_def StateInvariant_def 
    proof (intros)
      show tcN:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
        show "case l' of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False )" 
        proof (split denvalue.split, intros)
          fix loc assume a20:"l' = Stackloc loc"
          show "case accessStore loc (Stack st') of None \<Rightarrow> False 
          | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
          | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
          | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
          | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
          proof (cases "loc = l") 
            case False
            show ?thesis
            proof (split option.split, intros)
              assume a30:"accessStore loc (Stack st') = None"
              then have "accessStore loc (Stack st) = None" using 13(4) False by (simp add:stackSingleUpdate)
              then show False using a30 a20 a10 assms TypeSafe_def False "2.prems"(1) 
                by (metis option.distinct(1) typeSafeLocExists)
            next
              fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
              then have a40:"accessStore loc (Stack st) = Some x2" using 13(4) False by (simp add:stackSingleUpdate)
              then have a50:"(Memory st) = (Memory st')" using 13(4) by simp
              then have a60:"(Storage st) = (Storage st')" using 13(4) by simp
              show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
                  | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                  | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                  | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
                using a10 a20 a30 a40 a50 a60  "2.prems"(1) unfolding TypeSafe_def typeCompat_def by (cases x2; cases t; force)
            qed
          next 
            case sameLoc:True
            show ?thesis
            proof (split option.split, intros)
              assume a30:"accessStore loc (Stack st') = None"
              then show False using a20 a10 assms(1) sameLoc 13(4) notNoneUpdate[of st' g' loc "(KMemptr p)"] by simp
            next
              fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
              then have x2IsP:"x2 = KStoptr p" using 13 sameLoc by auto
              show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
              | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
              proof(cases "x2")
                case (KValue x1)

                then show ?thesis using x2IsP by auto
              next
                case (KCDptr x2)
                then show ?thesis using x2IsP by (simp add:sameLoc)
              next
                case (KMemptr x3)
                then show ?thesis  using x2IsP by (simp add:sameLoc)
              next
                case (KStoptr x4)
                then show ?thesis using x2IsP a10 a20 lDen storageSame sameLoc 
                  using pSCon by force
              qed
            qed
          qed
        next
          fix x2 assume a20:"l' = Storeloc x2"
          then have "(Storage st' (Address env)) = (Storage st (Address env))" using 13(4) by simp
          then show "case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st' (Address env)) | _ \<Rightarrow> False"  using a10 a20 TypeSafe_def "2.prems"(1) pSCon a10 a20 lDen storageSame 
          proof -
            have "\<And>t d. (t, d) |\<notin>| fmran (Denvalue env) \<or> 
                  (case d of Stackloc l \<Rightarrow> 
                  (case accessStore l (Stack st) of None \<Rightarrow> False 
                  | Some (KValue l) \<Rightarrow> (case t of Value t \<Rightarrow> typeCon t l | _ \<Rightarrow> False) 
                  | Some (KCDptr l) \<Rightarrow> (case t of Calldata m \<Rightarrow> MCon m cd l | _ \<Rightarrow> False) 
                  | Some (KMemptr l) \<Rightarrow> (case t of type.Memory m \<Rightarrow> MCon m (Memory st) l | _ \<Rightarrow> False) 
                  | Some (KStoptr l) \<Rightarrow> (case t of type.Storage s \<Rightarrow> SCon s l (Storage st (Address env)) | _ \<Rightarrow> False)) 
                  | Storeloc l \<Rightarrow> (case t of type.Storage s \<Rightarrow> SCon s l (Storage st (Address env)) | _ \<Rightarrow> False))"
              using "2.prems"(1) TypeSafe_def typeCompat_def by auto
            then show ?thesis
              by (metis (no_types) denvalue.simps(6) a10 a20 storageSame)
          qed 
        qed
      qed
      have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
        show "case l' of
         Stackloc loc \<Rightarrow>
           (case accessStore loc (Stack st) of None \<Rightarrow> False 
            | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
            | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
            | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
            | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
         | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False) " 
        proof(cases l')
          case (Stackloc x1)
          then show ?thesis 
          proof(cases "x1 = l")
            case sameLoc:True
            then show ?thesis 
            proof (cases "accessStore x1 (Stack st)")
              case None
              then show ?thesis using Stackloc a10 assms(1) sameLoc 13(4)  
                by (metis "2.prems"(1) option.distinct(1) typeSafeAllStacklocsExist)
            next
              case (Some a)
              then show ?thesis 
              proof(cases "a")
                case (KValue x1)
                then show ?thesis using a10 Stackloc Some "2.prems"(1) unfolding TypeSafe_def typeCompat_def
                  by fastforce
              next
                case (KCDptr x2)
                then show ?thesis using a10 Stackloc Some "2.prems"(1) unfolding TypeSafe_def typeCompat_def
                  by fastforce
              next
                case (KMemptr x3)
                then show ?thesis using a10 Stackloc Some "2.prems"(1) unfolding TypeSafe_def typeCompat_def  
                  by (metis (lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(19) type.simps(20) sameLoc t'InDen)
              next
                case (KStoptr x4)
                then show ?thesis using a10 Stackloc Some "2.prems"(1) unfolding TypeSafe_def typeCompat_def using lDen storageSame sameLoc 
                  using pSCon by force
              qed
            qed
          next
            case False
            then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" 
              using stackChanged by auto
            then show ?thesis using tcN Stackloc a10 unfolding typeCompat_def by fastforce
          qed
        next
          case (Storeloc x2)
          then show ?thesis using a10 tcN unfolding typeCompat_def by fastforce
        qed
      qed
    next
      show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by auto
    next
      have "(Accounts st) = Accounts(st')" using 13 by simp
      then show "balanceTypes (Accounts st')" using balanceTypes_def balanceTypes_def 2(1) typeSafeAccounts by simp
    next
      have a0:"compPointers (Stack st)(Denvalue env)" using 2(1) storageSame unfolding TypeSafe_def by simp
      show " compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
      proof(intros)
        fix tp1 tp2 l1 l22 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l22) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
     (l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l22 = Storeloc stl2)"
        have a2:"(\<forall>x y. x |\<in>| fmran (Denvalue env) \<and> y |\<in>| fmran (Denvalue env) \<and> snd x = snd y \<longrightarrow> x = y)"
          using  2(1) unfolding TypeSafe_def unique_locations_def by simp

        then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
        proof(cases "l1 = Storeloc stl1")
          case t1:True
          then show ?thesis 
          proof(cases "l22 = Storeloc stl2")
            case True
            then show ?thesis using t1 a0 a1 unfolding compPointers_def by blast
          next
            case False
            then have a4:"l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2)" using a1 by simp
            then show ?thesis 
            proof(cases "l2' = l")
              case True
              then have "stl2 = p" using a4 13 by simp
              then show ?thesis using pRelations a1 a0 t1  True a4 lDen by blast
            next
              case False
              then have " accessStore l2' (Stack st') =  accessStore l2' (Stack st)" using  stackChanged a4 by simp
              then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
            qed
          qed
        next
          case f1:False
          then have a4:"l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1)" using a1 by simp
          then show ?thesis 
          proof(cases "l22 = Storeloc stl2")
            case t1:True
            then show ?thesis
            proof(cases "l1' = l")
              case True
              then have "stl1 = p" using a4 13 by simp
              then show ?thesis using pRelations a1 a0 t1  True a4 lDen 
                by (metis CompStoType_sameLoc_sameType type.inject(4) typedStoSub_imps_negInv)
            next
              case False
              then have " accessStore l1' (Stack st') =  accessStore l1' (Stack st)" using  stackChanged a4 by simp
              then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
            qed
          next
            case False
            then have a4':"l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2)" using a1 by simp
            then show ?thesis 
            proof(cases "l1' = l")
              case True
              then have p1:"stl1 = p" using a4 13 by simp
              then have tp1c:"tp1 = (STArray x t)" using lDen a1 
                using True a4 by auto
              then show ?thesis 
              proof(cases "l2' = l")
                case True
                then have p2:"stl2 = p" using a4' 13 by auto
                then have tp2c:"tp2 = STArray x t" using lDen a1 True a4' by auto
                then show ?thesis using p2 p1 tp1c tp2c by auto
              next
                case False
                then have " accessStore l2' (Stack st') =  accessStore l2' (Stack st)" using  stackChanged a4 by simp
                then show ?thesis 
                  by (metis CompStoType_sameLoc_sameType a1 p1 pRelations tp1c typedStoSub_imps_negInv)
              qed
            next
              case False
              then have same1:" accessStore l1' (Stack st') =  accessStore l1' (Stack st)" using  stackChanged a4 by simp
              then show ?thesis 
              proof(cases "l2' = l")
                case True
                then have p2:"stl2 = p" using a4' 13 by auto
                then have tp2c:"tp2 = STArray x t" using lDen a1 True a4' by auto
                then show ?thesis using same1 pRelations p2 tp2c a1 
                  by metis
              next
                case False
                then have " accessStore l2' (Stack st') =  accessStore l2' (Stack st)" using  stackChanged a4 by simp
                then show ?thesis using a1 a0 same1 
                  using compPointers_def by auto
              qed
            qed
          qed
        qed
      qed
    next
      show "svalueTypes (Svalue env)" using svalueTypes_def typeSafeSvalue 2(1) by simp
    next
      have "(Storage st') = (Storage st)" using 13(4) by simp
      then show "safeContract (Accounts st') (Storage st')" using 2(1) 13 unfolding safeContract_def TypeSafe_def  by auto
    next
      have a10:"Toploc (Stack st') = Toploc (Stack st)" using 13(4) unfolding updateStore_def by simp
      then have a20:"\<exists>val. accessStore l (Stack st) = Some val" using t'InDen typeSafeLocExists 2(1) TypeSafe_def by blast
      then have a30:"(\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                   \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))" 
        using 2(1) unfolding TypeSafe_def  lessThanTopLocs_def by simp
      then have a40:"(\<forall>tloc loc. Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                    \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))" 
        using a10 by simp
      show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume *:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then show "accessStore loc (Stack st') = None"
        proof(cases "loc = l")
          case True
          then show ?thesis using * a10 
            by (metis a20 a30 option.distinct(1)) 
        next
          case False
          then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 13(4) unfolding updateStore_def accessStore_def by simp
          then show ?thesis using 2(1) a40 * a10 False a30 by simp
        qed
      next 
        fix loc y 
        assume *:" accessStore loc (Stack st') = Some y "
        show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        proof(cases "loc = l")
          case True
          then show ?thesis using *a10 a20 a30 by simp
        next
          case False
          then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 13(4) unfolding updateStore_def accessStore_def by simp
          then show ?thesis using * 2(1) a40 by simp
        qed
      qed
    next
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def using 13 by auto
    next 
      show "lessThanTopLocs (Memory st')" using 2(1) unfolding TypeSafe_def using 13 by auto
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by auto
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next
      show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 13 by simp
    next 
      have accSame:"Accounts st'= Accounts st" using 13 by auto
      from "2.prems"(3) obtain c_fi ct_fi dud_fi where fi:"
           Type (Accounts st (Address env)) = Some (atype.Contract c_fi) \<and>
           Contract env = c_fi \<and>
           ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
           (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id))) \<and>
           (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
           (\<forall>t0 l0 p0.
               (type.Storage t0, Stackloc l0) |\<in>| fmran (Denvalue env) \<and> accessStore l0 (Stack st) = Some (KStoptr p0) \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t0 l' p0))"
        unfolding fullyInitialised_def by blast
      have fiPtrs':"\<forall>t'' l'' p''.
               (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st') = Some (KStoptr p'') \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p'')"
      proof (intro allI impI)
        fix t'' l'' p''
        assume in1:"(type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st') = Some (KStoptr p'')"
        then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''"
        proof(cases "l'' = l")
          case True
          then have isST:"t'' = STArray x t" using in1 lDen by blast
          then have isP:"p'' = p" using 13(4) in1 True unfolding accessStore_def updateStore_def by simp
          then have "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' (STArray x t) l' p"
            using pOrigin isST isP by force
          then show ?thesis by (simp add: isP isST)
        next
          case False
          then have sameAcc:"accessStore l'' (Stack st') =accessStore l'' (Stack st)"
            by (simp add: stackChanged)
          then show ?thesis using fi in1 by presburger
        qed
      qed
      show "fullyInitialised env  (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fi fiPtrs' accSame by metis
    next 
      have inDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" using t'InDen by simp
      have denAc:"(\<forall>t l. (t, l) |\<in>| fmran (Denvalue env) \<longrightarrow>
           (case l of
            Stackloc loc \<Rightarrow>
              (case accessStore loc (Stack st) of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow>( case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st) stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st (Address env)) | _ \<Rightarrow> False))
            | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st (Address env)) | _ \<Rightarrow> False)))" using 2(1) unfolding TypeSafe_def typeCompat_def by simp
      have isVal:"\<exists>val. accessStore l (Stack st) = Some (KStoptr val)" 
      proof(cases "accessStore l (Stack st)")
        case None
        then show ?thesis using inDen denAc by fastforce
      next
        case (Some a)
        then show ?thesis 
        proof(cases a)
          case (KValue x1)
          then show ?thesis using inDen denAc Some by fastforce
        next
          case (KCDptr x2)
          then show ?thesis using inDen denAc Some by fastforce
        next
          case (KMemptr x3)
          then show ?thesis using inDen denAc Some by fastforce
        next
          case (KStoptr x4)
          then show ?thesis using inDen denAc Some by simp
        qed
      qed

      have memSame:"Memory st = Memory st'" using 13(4) by simp
      have cc0:"\<forall>l ptr. (accessStore l (Stack st) = Some (KMemptr ptr)) = (accessStore l (Stack st') = Some (KMemptr ptr))" 
      proof intros
        fix l2 ptr
        show " (accessStore l2 (Stack st) = Some (KMemptr ptr)) = (accessStore l2 (Stack st') = Some (KMemptr ptr)) "
        proof
          assume *:"accessStore l2 (Stack st) = Some (KMemptr ptr)"
          then have "l \<noteq> l2" using isVal by auto
          then show "accessStore l2 (Stack st') = Some (KMemptr ptr)" 
            using 13(4) * unfolding updateStore_def accessStore_def by auto
        next 
          assume *:"accessStore l2 (Stack st') = Some (KMemptr ptr)" 
          then have "l \<noteq> l2" using 13(4) by auto
          then show "accessStore l2 (Stack st) = Some (KMemptr ptr) " 
            using * 13(4) unfolding updateStore_def accessStore_def by simp
        qed
      qed
    next
      have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using 13(4) unfolding updateStore_def accessStore_def by auto
      show "denvalueTypeCorrectness env (Stack st') (Memory st')" 

        unfolding denvalueTypeCorrectness_def  
      proof intros
        fix t l ptr_loc sub_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "(case t of
         MTArray len arr \<Rightarrow>
           (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
        moreover have "Memory st = Memory st'" using 13(4) by simp
        ultimately show "case t of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr) 
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)" 
          by metis 
      qed
    next
      show "subPrefixStructuralConsistency (Memory st')"
        using 2(1) unfolding TypeSafe_def using 13(4) by simp
    next
      show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 13(4) by simp
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 2(1) unfolding TypeSafe_def using 13(4) by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using 13(4) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using 13(4) by simp
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 13(4) by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 13(4) by simp
    qed
  next
    case (14 p x t g l t' g' s)
    have sameStack:"(Stack st) = (Stack st')" using 14 unfolding accessStore_def updateStore_def by auto
    have sameMemory:"Memory st' = Memory st " using 14 by auto
    have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s" 
      using 14(4) unfolding copy_def using  copySingleChange[of p l t "(Storage st (Address env))" x s]  
      by fastforce
    have a30:"\<forall>locs t''. \<not> TypedStoSubpref locs l (STArray x t) \<longrightarrow> accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s" 
      using  14(4) unfolding copy_def using copySingleChange2[of p l t "(Storage st (Address env))" x s]  by simp
    then have a35:"\<forall>locs t''. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t) \<longrightarrow>
       accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))" 
      using 14 by auto
    have mInStd:"s = Storage st' (Address env)" using 14 by simp

    obtain stloc tp'' where MConsrc:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) \<and> (\<exists>xx. KStoptr p = KStoptr xx) \<and>
            
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue env) \<and>
            (tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
      using 2(1) 14(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KStoptr p" "type.Storage (STArray x t)" g] 
      using 2(3) 
      by (auto split:type.splits if_splits )

    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto

    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                            \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros 
      show "AddressTypes (Accounts st')" using 2(1) 14 unfolding TypeSafe_def by simp
    next 
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      show "compPointers (Stack st') (Denvalue env)"  unfolding compPointers_def 
      proof(intros)
        fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
        then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
        proof(cases "TypedStoSubpref stl2 stl1 tp1")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case f1:False
          then show ?thesis 
          proof(cases "TypedStoSubpref stl1 stl2 tp2")
            case True
            then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
          next
            case False
            then show ?thesis using f1 by simp
          qed
        qed
      qed
    next 
      have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp 
      show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
      proof intros
        fix e ct dud i tp
        assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
                 ep $$ Contract (e::environment) = Some (ct, dud) \<and>
                 ct $$ i = Some (Var tp)"
        show "SCon tp i (Storage st' (Address e))"
        proof (cases "Address e = Address env")
          case False
          then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 14 by simp
          moreover have "SCon tp i (Storage st (Address e))"
            using * scOld 14 unfolding safeContract_def by fastforce
          ultimately show ?thesis by simp
        next
          case addrEq:True
          have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using * 14 by simp
          have epOld:"ep $$ Contract e = Some (ct, dud)"
            using * by simp
          have ctOld:"ct $$ i = Some (Var tp)"
            using * by simp
          have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
            using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
          have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
            using denI by (simp add: fmranI)
          have oldSConE:"SCon tp i (Storage st (Address e))"
            using scOld typedOld epOld ctOld unfolding safeContract_def by blast
          have oldSCon:"SCon tp i (Storage st (Address env))"
            using oldSConE addrEq by simp
          have newSCon:"SCon tp i (Storage st' (Address env))"
          proof(cases rule:lexpStorageG[OF 2(1) 14(2) 2(3)])
            case lInDen:1
            have cmpStoPtr:"(
              (type.Storage tp, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Storeloc i) 
               \<longrightarrow>
              (if TypedStoSubpref l i tp then CompStoType tp  (STArray x t) i l
               else if TypedStoSubpref i l  (STArray x t) then CompStoType  (STArray x t) tp l i else True)" 
              using 2(1) 14(3) lInDen inDenI unfolding TypeSafe_def compPointers_def by blast
            then have cmpStoPtr2:"(if TypedStoSubpref l i tp then CompStoType tp  (STArray x t) i l
               else if TypedStoSubpref i l  (STArray x t) then CompStoType  (STArray x t) tp l i else True)"
              using 14(3) lInDen inDenI sameStack 
              using "2.prems"(1) compPointers_def typeSafeCompPointers by blast

            have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14 lInDen
                sameStoLocTSafe by blast
            have p:"((if TypedStoSubpref stloc l t' then CompStoType t' tp'' l stloc
               else if TypedStoSubpref l stloc tp'' then CompStoType tp'' t' stloc l else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using lInDen MConsrc by blast
            have denSub:"(if TypedStoSubpref stloc l (STArray x t) then CompStoType (STArray x t) tp'' l stloc
               else if TypedStoSubpref l stloc tp'' then CompStoType tp'' (STArray x t) stloc l else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t' (STArray x t) l l"
              using 14(3) CompStoType_sameLocNdTyp by simp
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3)  h7 h8 denSub paInf ] by auto 
            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )
            show ?thesis
            proof(cases "TypedStoSubpref l i tp")
              case True
              then have "CompStoType tp (STArray x t) i l" 
                by (simp add: cmpStoPtr2)
              then show ?thesis using SCondest2 oldSCon a35 TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref i l  (STArray x t)")
                case True
                then have "CompStoType t' tp l i " using cmpStoPtr2 f1 14(3) by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs by blast
              next
                case False
                have notSame:"i \<noteq> l" using False by auto
                have k7:"\<forall>locs. TypedStoSubpref locs i tp \<longrightarrow> locs \<noteq> l " using f1 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> i" using False by auto
                show ?thesis using sublocs_nonchanged_SCon[OF f1 a35 oldSCon False] by blast
              qed
            qed
          next
            case sub2:(2 l''' t''')
            have cmpStoPtr:"(
                (type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t''', Storeloc l''') |\<in>| fmran (Denvalue env) )
                 \<longrightarrow>
                (if TypedStoSubpref l''' i tp then CompStoType tp t''' i l'''
                 else if TypedStoSubpref i l''' t''' then CompStoType t''' tp l''' i else True)" 
              using 2(1) 14(3) inDenI unfolding TypeSafe_def compPointers_def by blast
            then have cmpStoPtr2:"(if TypedStoSubpref l''' i tp then CompStoType tp t''' i l'''
                 else if TypedStoSubpref i l''' t''' then CompStoType t''' tp l''' i else True)"
              using 14(3) sub2 inDenI sameStack by auto

            have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce
            then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14 sameStoLocTSafe sub2
              using SCon_imps_sublocs by blast
            have p:"((if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
                 else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using sub2 MConsrc by blast
            have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t''' (STArray x t) l''' l" using sub2 14(3) by auto
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )
            show ?thesis
            proof(cases "TypedStoSubpref l''' i tp")
              case True
              then have "CompStoType tp t''' i l'''" using cmpStoPtr2 by simp
              then have "CompStoType tp (STArray x t) i l" using sub2 using CompStoType_trns 14(3) by blast
              then show ?thesis using SCondest2 oldSCon a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref i l''' t'''")
                case True
                then have "l''' \<noteq> i" using f1 using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = i")
                  case t5:True
                  then have "CompStoType t''' tp l''' i" using cmpStoPtr2 f1 14(3) True by simp
                  moreover have "CompStoType t''' t' l''' i" using t5 sub2 by auto
                  ultimately have "t' = tp" using CompStoType_sameLocs_sameType by simp
                  then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
                next
                  case False
                  then have "CompStoType t''' tp l''' i" using cmpStoPtr2 f1 14(3) True by simp
                  then show ?thesis 
                  proof(cases "CompStoType t' tp l i")
                    case True
                    then show ?thesis using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis 
                      by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' tp l''' i\<close> a35 scl''' sub2(2) 14(3))
                  qed
                qed
              next
                case False
                then have asm10:"\<not> TypedStoSubpref l i tp" using NotRelatedPrnt_imps_notRelatedChild[OF False f1] sub2 by blast
                then have asm20:"\<not> TypedStoSubpref i l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"i \<noteq> l" using False sub2 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs i tp \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> i" using False sub2 14(3) asm10 asm20 by blast
                show ?thesis using sublocs_nonchanged_SCon[OF _ a35 oldSCon] asm10 asm20 14(3) by blast
              qed
            qed
          next
            case sub3:(3 l''' t''' l'''')
            have cmpStoPtr:"(
                (type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t''', Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
                 accessStore l'''' (Stack st) = Some (KStoptr l'''))
                 \<longrightarrow>
                (if TypedStoSubpref l''' i tp then CompStoType tp t''' i l'''
                 else if TypedStoSubpref i l''' t''' then CompStoType t''' tp l''' i else True)" 
              using 2(1) 14(3) inDenI unfolding TypeSafe_def compPointers_def by blast
            then have cmpStoPtr2:"(if TypedStoSubpref l''' i tp then CompStoType tp t''' i l'''
                 else if TypedStoSubpref i l''' t''' then CompStoType t''' tp l''' i else True)"
              using 14(3) sub3 inDenI sameStack by auto

            have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce
            then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14 sameStoLocTSafe sub3
              using SCon_imps_sublocs by blast
            have p:"(
                (if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
                 else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using sub3 MConsrc by blast
            have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t''' (STArray x t) l''' l" using sub3 14(3) by auto
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )
            show ?thesis
            proof(cases "TypedStoSubpref l''' i tp")
              case True
              then have "CompStoType tp t''' i l'''" using cmpStoPtr2 by simp
              then have "CompStoType tp (STArray x t) i l" using sub3 using CompStoType_trns 14(3) by blast
              then show ?thesis using SCondest2 oldSCon a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref i l''' t'''")
                case True
                then have "l''' \<noteq> i" using f1 using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = i")                  case t5:True
                  then have "CompStoType t''' tp l''' i" using cmpStoPtr2 f1 14(3) True by simp
                  moreover have "CompStoType t''' t' l''' i" using t5 sub3 by auto
                  ultimately have "t' = tp" using CompStoType_sameLocs_sameType by simp
                  then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
                next
                  case False
                  then have "CompStoType t''' tp l''' i" using cmpStoPtr2 f1 14(3) True by simp
                  then show ?thesis 
                  proof(cases "CompStoType t' tp l i")
                    case True
                    then show ?thesis using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis 
                      by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' tp l''' i\<close> a35 scl''' sub3(3) 14(3))
                  qed
                qed
              next
                case False
                then have asm10:"\<not> TypedStoSubpref l i tp" using NotRelatedPrnt_imps_notRelatedChild[OF False f1] sub3 by blast
                then have asm20:"\<not> TypedStoSubpref i l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"i \<noteq> l" using False sub3 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs i tp \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> i" using False sub3 14(3) asm10 asm20 by blast
                show ?thesis using sublocs_nonchanged_SCon[OF _ a35 oldSCon] asm10 asm20 14(3) by blast
              qed
            qed
          qed
          then show ?thesis using newSCon addrEq by simp
            
        qed
      qed
    next 
      show "balanceTypes (Accounts st')" using 14 using 2(1) unfolding TypeSafe_def by simp
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next 
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 14 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')"  using sameStack * ** unfolding lessThanTopLocs_def by auto
    next 
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def 
        by (simp add: limitSt limitSt1)
    next 
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t'' l'
        assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

        show " case l' of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t'' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t'' of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False )
                | Some (KMemptr stloc) \<Rightarrow> (case t'' of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t'' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t'' of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases l')
          case (Stackloc x1)
          then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
          then show ?thesis 
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack  unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
          next
            case (KCDptr x2)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def   typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
          next
            case (KMemptr x3)
            then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
          next
            case (KStoptr x4)  
            then obtain struct where structDef: "t'' = type.Storage struct" using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
              by (cases t''; fastforce)

            have "SCon struct x4 (Storage st' (Address env))" 
            proof(cases rule:lexpStorageG[OF 2(1) 14(2) 2(3)])
              case lInDen:1
              then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
                  sameStoLocTSafe by blast

              have p:"((if TypedStoSubpref stloc l t' then CompStoType t' tp'' l stloc
                 else if TypedStoSubpref l stloc tp'' then CompStoType tp'' t' stloc l else True))"
                using 2(1) unfolding TypeSafe_def compPointers_def using lInDen MConsrc by blast

              have denSub:"(if TypedStoSubpref stloc l (STArray x t) then CompStoType (STArray x t) tp'' l stloc
                 else if TypedStoSubpref l stloc tp'' then CompStoType tp'' (STArray x t) stloc l else True)"
                using p 14(3) by blast
              have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc 
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))" 
                using MConsrc by simp
              have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
              have rel:"CompStoType t' (STArray x t) l l"
                using 14(3) CompStoType_sameLocNdTyp by simp
              have SCondest:"SCon (STArray x t) l s"
                using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf] by simp

              then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
                by (simp add: mInStd)
              then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
                by (simp add: mInStd )

              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage (STArray x t), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) 
                 \<longrightarrow>
                (if TypedStoSubpref l x4 struct then CompStoType struct  (STArray x t) x4 l
                 else if TypedStoSubpref x4 l  (STArray x t) then CompStoType  (STArray x t) struct l x4 else True)" 
                using 2(1) 14(3) lInDen inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l x4 struct then CompStoType struct  (STArray x t) x4 l
                 else if TypedStoSubpref x4 l  (STArray x t) then CompStoType  (STArray x t) struct l x4 else True)"
                using  14(3) lInDen inDen adef Stackloc KStoptr structDef  sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce

              have "SCon struct x4 (Storage st' (Address env))" 
              proof(cases "TypedStoSubpref l x4 struct")
                case True
                then have "CompStoType struct (STArray x t) x4 l" using cmpStoPtr2 by simp
                then show ?thesis using SCondest2  SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                  by blast
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref x4 l  (STArray x t)")
                  case True
                  then have "CompStoType t' struct l x4 " using cmpStoPtr2 f1 14(3) by simp
                  then show ?thesis using SCondest3  SCon_imps_sublocs by blast
                next
                  case False
                  have notSame:"x4 \<noteq> l" using False by auto
                  have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 by blast
                  have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x4" using False by auto
                  show ?thesis  using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast      
                qed
              qed
              then show ?thesis by simp
            next
              case sub2:(2 l''' t''')
              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t''', Storeloc l''') |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) 
                 \<longrightarrow>
                (if TypedStoSubpref l''' x4 struct then CompStoType struct t''' x4 l'''
                 else if TypedStoSubpref x4 l''' t''' then CompStoType t''' struct l''' x4 else True)" 
                using 2(1) 14(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t''' x4 l'''
                 else if TypedStoSubpref x4 l''' t''' then CompStoType t''' struct l''' x4 else True)"
                using  14(3) sub2 inDen adef Stackloc KStoptr structDef  sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce
              have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce
                  (*BT START: This needs to be revisited, is essentially a generalisation of the proof for SCondest above*)

              then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
                  sameStoLocTSafe sub2 
                using SCon_imps_sublocs by blast

              have p:"(
                (if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
                 else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
                using 2(1) unfolding TypeSafe_def compPointers_def using sub2 MConsrc  by blast

              have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
                 else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
                using p 14(3) by blast
              have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc 
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))" 
                using MConsrc by simp
              have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
              have rel:"CompStoType t''' (STArray x t) l''' l" using sub2 14(3) by auto
              have SCondest:"SCon (STArray x t) l s"
                using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
              then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
                by (simp add: mInStd)
              then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
                by (simp add: mInStd )
                  (*BT END: This needs to be revisited, is essentially a generalisation of the proof for SCondest above*)

              have "SCon struct x4 (Storage st' (Address env))" 
              proof(cases "TypedStoSubpref l''' x4 struct")
                case True
                then have "CompStoType struct t''' x4 l'''" using cmpStoPtr2 by simp
                then have "CompStoType struct (STArray x t) x4 l" using sub2 
                  using CompStoType_trns 14(3) by blast
                then show ?thesis using   SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent SCondest2 by blast
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref x4 l''' t")
                  case True
                  then have "l''' \<noteq> x4" using f1 
                    using TypedStoSubpref_sameLoc by auto
                  then show ?thesis 
                  proof(cases "l = x4")
                    case t5:True
                    then have " CompStoType t''' struct l''' x4" using cmpStoPtr2 f1 14(3) True   
                      using sub2(2) by auto
                    moreover have "CompStoType t''' t' l''' x4" using t5 sub2 by auto
                    ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                      by simp
                    then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                  next
                    case False
                    then show ?thesis 
                    proof(cases "CompStoType t' struct l x4 ")
                      case True
                      then show ?thesis 
                        using SCon_imps_sublocs SCondest3 by blast
                    next
                      case False
                      then show ?thesis 
                        by (smt (verit, ccfv_SIG) "14"(3) NotReachablePrnt_imps_notReachableChild NotRelatedPrnt_imps_notRelatedChild SCon_imps_sublocs 
                            SCon_sub_imps_Parent SCondest2 SConx4Old Scon_NoChange
                            a35 cmpStoPtr2 f1 scl''' sub2(2))
                    qed
                  qed
                next
                  case False
                  show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] 14(3) 
                    by (smt (verit, ccfv_SIG) NotReachablePrnt_imps_notReachableChild NotRelatedPrnt_imps_notRelatedChild SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 a35 cmpStoPtr2 f1 scl'''
                        sub2(2))
                qed
              qed
              then show ?thesis by simp
            next
              case sub3:(3 l''' t''' l'''')
              have cmpStoPtr:"(
                (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t''', Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
                 l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) \<and> accessStore l'''' (Stack st) = Some (KStoptr l''')
                 \<longrightarrow>
                (if TypedStoSubpref l''' x4 struct then CompStoType struct t''' x4 l'''
                 else if TypedStoSubpref x4 l''' t''' then CompStoType t''' struct l''' x4 else True)" 
                using 2(1) 14(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

              then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t''' x4 l'''
                 else if TypedStoSubpref x4 l''' t''' then CompStoType t''' struct l''' x4 else True)"
                using  14(3) sub3 inDen adef Stackloc KStoptr structDef  sameStack by auto

              have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr  inDen  2(1) sameStack structDef  
                by fastforce
              have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

(*BT START: This needs to be revisited, is essentially a generalisation of the proof for SCondest above*)
              then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
                  sameStoLocTSafe sub3
                using SCon_imps_sublocs by blast

              have p:"((if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
                 else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
                using 2(1) unfolding TypeSafe_def compPointers_def using sub3 MConsrc  by blast

              have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
                 else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
                using p 14(3) by blast
              have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc 
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))" 
                using MConsrc by simp
              have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
              have rel:"CompStoType t''' (STArray x t) l''' l" using sub3 14(3) by auto
              have SCondest:"SCon (STArray x t) l s"
                using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
              then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
                by (simp add: mInStd)
              then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
                by (simp add: mInStd )
                  (*BT END: This needs to be revisited, is essentially a generalisation of the proof for SCondest above*)

              have "SCon struct x4 (Storage st' (Address env))" 
              proof(cases "TypedStoSubpref l''' x4 struct")
                case True
                then have "CompStoType struct t''' x4 l'''" using cmpStoPtr2 by simp
                then have "CompStoType struct (STArray x t) x4 l" using sub3 
                  using CompStoType_trns 14(3) by blast
                then show ?thesis using SCondest2  SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                  by blast
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref x4 l''' t'''")
                  case True
                  then have "l''' \<noteq> x4" using f1 
                    using TypedStoSubpref_sameLoc by auto
                  then show ?thesis 
                  proof(cases "l = x4")
                    case t5:True
                    then have " CompStoType t''' struct l''' x4" using cmpStoPtr2 f1 14(3) True by simp
                    moreover have "CompStoType t''' t' l''' x4" using t5 sub3 by auto
                    ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                      by simp
                    then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                  next
                    case False
                    then have " CompStoType t''' struct l''' x4" using cmpStoPtr2 f1 14(3)  True by simp                
                    then show ?thesis 
                    proof(cases "CompStoType t' struct l x4 ")
                      case True
                      then show ?thesis 
                        using SCon_imps_sublocs SCondest3 by blast
                    next
                      case False
                      then show ?thesis 
                        by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' struct l''' x4\<close> a35 scl''' sub3(3) 14(3))
                    qed
                  qed
                next
                  case False                                                             
                  then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                  then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                  have notSame:"x4 \<noteq> l" using False sub3 by blast
                  have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20  by blast
                  have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x4" using False sub3 14(3) asm10 asm20 by blast
                  show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 14(3) by blast
                qed
              qed
              then show ?thesis by simp
            qed
            then show ?thesis using Stackloc  inDen  2(1) sameStack KStoptr adef structDef by simp
          qed
        next
          case (Storeloc x2)
          then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc  inDen  2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have "SCon struct x2 (Storage st' (Address env))" 
          proof(cases rule:lexpStorageG[OF 2(1) 14(2) 2(3)])
            case lInDen:1
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Storeloc x2) 
               \<longrightarrow>
              (if TypedStoSubpref l x2 struct then CompStoType struct  (STArray x t) x2 l
               else if TypedStoSubpref x2 l  (STArray x t) then CompStoType  (STArray x t) struct l x2 else True)" 
              using 2(1) 14(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l x2 struct then CompStoType struct  (STArray x t) x2 l
               else if TypedStoSubpref x2 l  (STArray x t) then CompStoType  (STArray x t) struct l x2 else True)"
              using  14(3) lInDen inDen Storeloc structDef  sameStack by simp

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce

            then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14 lInDen
                sameStoLocTSafe by blast

            have p:"((if TypedStoSubpref stloc l t' then CompStoType t' tp'' l stloc
               else if TypedStoSubpref l stloc tp'' then CompStoType tp'' t' stloc l else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using lInDen MConsrc by blast

            have denSub:"(if TypedStoSubpref stloc l (STArray x t) then CompStoType (STArray x t) tp'' l stloc
               else if TypedStoSubpref l stloc tp'' then CompStoType tp'' (STArray x t) stloc l else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc 
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))" 
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t' (STArray x t) l l"
              using 14(3) CompStoType_sameLocNdTyp by simp
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf ] by simp

            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )

            have "SCon struct x2 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref l x2 struct")
              case True
              then have "CompStoType struct (STArray x t) x2 l" 
                by (simp add: cmpStoPtr2)
              then show ?thesis using SCondest2  SConx4Old a35  TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x2 l  (STArray x t)")
                case True
                then have "CompStoType t' struct l x2 " using cmpStoPtr2 f1 14(3) by simp
                then show ?thesis using SCondest3  SCon_imps_sublocs by blast
              next
                case False
                have notSame:"x2 \<noteq> l" using False by auto
                have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x2" using False by auto
                show ?thesis  using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast      
              qed
            qed
            then show ?thesis by simp
          next
            case sub2:(2 l''' t''')
            have cmpStoPtr:"(
                (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t''', Storeloc l''') |\<in>| fmran (Denvalue env) )
                 \<longrightarrow>
                (if TypedStoSubpref l''' x2 struct then CompStoType struct t''' x2 l'''
                 else if TypedStoSubpref x2 l''' t''' then CompStoType t''' struct l''' x2 else True)" 
              using 2(1) 14(3) inDen  Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t''' x2 l'''
                 else if TypedStoSubpref x2 l''' t''' then CompStoType t''' struct l''' x2 else True)"
              using  14(3) sub2 inDen Storeloc  structDef  sameStack by auto

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce
            have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce
                (*BT START: This needs to be revisited, is essentially a generalisation of the proof for SCondest above*)

            then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
                sameStoLocTSafe sub2 
              using SCon_imps_sublocs by blast

            have p:"((if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
                 else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using sub2 MConsrc  by blast

            have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc 
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))" 
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t''' (STArray x t) l''' l" using sub2 14(3) by auto
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )
                (*BT END: This needs to be revisited, is essentially a generalisation of the proof for SCondest above*)


            have "SCon struct x2 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref l''' x2 struct")
              case True
              then have "CompStoType struct t''' x2 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t) x2 l" using sub2 
                using CompStoType_trns 14(3) by blast
              then show ?thesis using SCondest2  SConx4Old a35 14(3)  TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x2 l''' t'''")
                case True
                then have "l''' \<noteq> x2" using f1 
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x2")
                  case t5:True
                  then have " CompStoType t''' struct l''' x2" using cmpStoPtr2 f1 14(3) True by simp
                  moreover have "CompStoType t''' t' l''' x2" using t5 sub2 by auto
                  ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                    by simp
                  then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                next
                  case False
                  then have " CompStoType t''' struct l''' x2" using cmpStoPtr2 f1 14(3)  True by simp                
                  then show ?thesis 
                  proof(cases "CompStoType t' struct l x2 ")
                    case True
                    then show ?thesis using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis 
                      by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' struct l''' x2\<close> a35 scl''' sub2(2) 14(3))
                  qed
                qed
              next
                case False                                                             
                then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
                then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x2 \<noteq> l" using False sub2 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20  by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x2" using False sub2 14(3) asm10 asm20 by blast
                show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 14(3) by blast
              qed
            qed

            then show ?thesis by simp
          next
            case sub3:(3 l''' t''' l'''')
            have cmpStoPtr:"(
                (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
                (type.Storage t''', Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
                 accessStore l'''' (Stack st) = Some (KStoptr l'''))
                 \<longrightarrow>
                (if TypedStoSubpref l''' x2 struct then CompStoType struct t''' x2 l'''
                 else if TypedStoSubpref x2 l''' t''' then CompStoType t''' struct l''' x2 else True)" 
              using 2(1) 14(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t''' x2 l'''
                 else if TypedStoSubpref x2 l''' t''' then CompStoType t''' struct l''' x2 else True)"
              using  14(3) sub3 inDen Storeloc structDef 14(3) sameStack by auto

            have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc  inDen  2(1) sameStack structDef  
              by fastforce
            have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce
                (*BT START: This needs to be revisited, is essentially a generalisation of the proof for SCondest above*)

            then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
                sameStoLocTSafe sub3
              using SCon_imps_sublocs by blast

            have p:"(
                (if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
                 else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using sub3 MConsrc  by blast

            have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc 
                    \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))" 
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t''' (STArray x t) l''' l" using sub3 14(3) by auto
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))" 
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )
                (*BT END: This needs to be revisited, is essentially a generalisation of the proof for SCondest above*)

            have "SCon struct x2 (Storage st' (Address env))" 
            proof(cases "TypedStoSubpref l''' x2 struct")
              case True
              then have "CompStoType struct t''' x2 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t) x2 l" using sub3 
                using CompStoType_trns 14(3) by blast
              then show ?thesis using SCondest2  SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent 
                by blast
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref x2 l''' t'''")
                case True
                then have "l''' \<noteq> x2" using f1 
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x2")
                  case t5:True
                  then have " CompStoType t''' struct l''' x2" using cmpStoPtr2 f1 14(3) True by simp
                  moreover have "CompStoType t''' t' l''' x2" using t5 sub3 by auto
                  ultimately have "t' = struct"  using  CompStoType_sameLocs_sameType 
                    by simp
                  then show ?thesis using SCondest3  SCon_imps_sublocs t5  by simp
                next
                  case False
                  then have " CompStoType t''' struct l''' x2" using cmpStoPtr2 f1 14(3)  True by simp                
                  then show ?thesis 
                  proof(cases "CompStoType t' struct l x2 ")
                    case True
                    then show ?thesis 
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis 
                      by (smt (verit, best) SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' struct l''' x2\<close> a35 scl''' sub3(3) 14(3))
                  qed
                qed
              next
                case False                                                             
                then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x2 \<noteq> l" using False sub3 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20  by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x2" using False sub3 14(3) asm10 asm20 by blast
                show ?thesis  using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 14(3) by blast
              qed
            qed
            then show ?thesis by simp
          qed


          then show ?thesis using Storeloc  inDen  2(1) sameStack Storeloc structDef by simp
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd " using sameStack by simp
    next 
      have "Accounts st'= Accounts st" using 14 by auto
      then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) unfolding fullyInitialised_def 
        using sameStack by simp
    next 
      have "Stack st = Stack st'" using 14 by simp
      moreover have "Memory st = Memory st'" using 14 by auto
      ultimately show "denvalueTypeCorrectness env (Stack st') (Memory st')" 
        using 2(1) unfolding TypeSafe_def by simp 
    next
      show "subPrefixStructuralConsistency (Memory st')"
        using 2(1) 14 unfolding TypeSafe_def by simp
    next 
      show " SomeValSomeTyp (Memory st') " using 2(1) unfolding TypeSafe_def using 14 by simp
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 2(1) 14 unfolding TypeSafe_def by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using 14 by auto
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using 14 by auto
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 14 by auto
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 14 by auto
    qed
  next
    case (15 p x t g l t' g' m m')
    have temp:"TypeSafe env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd" 
      using 2(1) by simp
    have ttt:"fullyInitialised env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 2(3) unfolding fullyInitialised_def by simp

    then show ?thesis
    proof(cases rule:lexpIndexMem[OF 15(2) temp ttt])
      case lInfo:(1 x21 x22 tp tParent l' l'' prnt len' arr' i)
      have nonChangedStack:"\<forall>loc. loc \<noteq> l \<longrightarrow> accessStore loc (Stack st) = accessStore loc (Stack st')" using 15 unfolding accessStore_def updateStore_def by auto
      have sameStack:"(Stack st') = Stack st" using 15 unfolding accessStore_def updateStore_def by auto
      have sameStorage:"Storage st'  = Storage st " using 15 by auto
      have nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))\<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
        using 15(4) unfolding cps2m_def using  cps2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]   cps2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t "(Storage st (Address env))" " (snd (allocate (Memory st)))" ]  
        by fastforce
      have a30:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> TypedStoSubpref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m" 
        using  15(4) unfolding cps2m_def using cps2mSingleChange2[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]  by fastforce
      then have a32:"\<forall>locs. \<not> TypedStoSubpref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m"   
        by (metis allocateSameAccess nonLocChanged)
      have selfPoint:"\<forall>l l'. l \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> TypedStoSubpref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l" 
        using 15(4) unfolding cps2m_def 
        using cps2mSelfPointers[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ] 
        by blast
      have mInStd:"m' = Memory st'" using 15 by simp
      have NonChangeM'm:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs m = accessStore locs m'" using 15(5) unfolding accessStore_def updateStore_def by auto
      have accessL:"accessStore l m' = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 15(5) unfolding accessStore_def updateStore_def by auto

      have MConsrc:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) \<and> (\<exists>xx. KStoptr p = KStoptr xx)"
        using 2(1) 15(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" ] 2(3)unfolding fullyInitialised_def
        by (auto split:type.splits if_splits )

      obtain memArr where memArrDef: "t' = MTArray x memArr" using 15(3) cps2mTypeCompatible.simps 
        by (metis mtypes.exhaust)

      have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"  
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"  
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" 
        using allocateSameAccess by blast
      ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
      then have MCondest:" MCon (MTArray x memArr) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 15(4,3) unfolding cps2m_def
        using cps2m[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m memArr] 
          MConsrc extractValueType.simps(2) memArrDef by auto
      have "\<exists>x. accessStore l (Memory st) = Some x" using lInfo by (auto split:option.splits)
      then have l_not_toploc_orSub:"\<not>LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        using limitSt by fastforce 

      have selfPoint2:"\<forall>l1 l2. LSubPrefL2 l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) 
                        \<and> accessStore l1 (Memory st') = Some (MPointer l2) \<longrightarrow> l2 = l1 \<and> l1 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        by (metis (no_types, lifting) "15"(4) NonChangeM'm
            \<open>accessStore \<lfloor>Toploc (state.Memory st)\<rfloor> (snd (allocate (state.Memory st))) = None\<close> a32 cps2mSelfPointers cps2m_def
            dual_order.refl l_not_toploc_orSub limitSt mInStd nonLocChanged option.discI)


      obtain len subT where tParentType:"tParent = MTArray len subT" using lInfo by blast
      then obtain p'' where lOrigin:"accessStore l (Memory (st)) = Some (MPointer p'')" 
        and  compType:"CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len subT (MTArray x memArr) l'' p''" 
        and lsublocs:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = (MTArray x memArr) \<and> MCon (MTArray len' arr') (Memory (st)) prnt" 
        and lsublocs3:"(prnt = l'' \<and> len = len' \<and> arr' = subT \<or> CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt)"
        using lInfo 15(3) memArrDef by force
      then have lsublocs2:" CompMemType (Memory (st)) len' arr' (MTArray x memArr) prnt p''" 
        using "15"(3) CompMemType.simps(2) memArrDef by blast

      then have bb9:"\<forall>subT subloc. CompMemType (Memory (st)) len' arr' subT prnt subloc \<and> subloc = p''
                                  \<longrightarrow> subT = (MTArray x memArr)" 
        using CompMemTypeSameLocsSameType lsublocs by blast

      have mconPrnt:"MCon (MTArray len' (MTArray x memArr)) (Memory st) prnt" using lsublocs by auto
      have ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'" using lsublocs by auto

      have t6:"(type.Memory tParent,  Stackloc l') |\<in>| fmran (Denvalue env)" using lInfo by blast
      have t7:" MCon (MTArray len subT) (Memory (st)) l''" using lInfo 
        using tParentType by auto
      then have t8:"\<not> LSubPrefL2 l'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt limitSt1 typeSafe_noDenElementOverToploc_mem[OF 2(1) t6] lInfo(3) by simp
      have comptype2:"CompMemType m len subT (MTArray x memArr) l'' p''" using 
          cpm2mCompMemTypeOld_imps_CompMemType[of "(Memory (st\<lparr>Gas := g\<rparr>))" len subT "(MTArray x memArr)" l'' p'' "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" m ] 
          compType nonLocChanged limitSt t7 t8 allocateSame by auto
      have t10:"CompMemType (Memory st) len subT (MTArray x memArr) l'' p''"
        using 
          cpm2mCompMemTypeOld_imps_CompMemType[of "(Memory (st\<lparr>Gas := g\<rparr>))" len subT "(MTArray x memArr)" l'' p'' "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" m ] 
          compType nonLocChanged limitSt t7 t8 allocateSame by auto
      then have mconlOld:"MCon (MTArray x memArr) (Memory st) p''" using memArrDef 15(3) lInfo lOrigin by auto

      have nonLocChanged2:"\<forall>locs. locs \<noteq> l \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')" 
        using 15 nonLocChanged LSubPrefL2_def NonChangeM'm mInStd allocateSame by metis
      have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env) 
                          \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
        using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto
      have selfPoint_root:"\<forall>l1 l2. TypedStoSubpref l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<and> accessStore l1 m = Some (MPointer l2) \<longrightarrow> l2 = l1"
      proof (intro allI impI)
        fix l1 l2
        assume asm:"TypedStoSubpref l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<and> accessStore l1 m = Some (MPointer l2)"
        have l1_neq:"l1 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
          using asm TypedStoSubpref_imp_LSubPrefL2 hash_inequality 
          using \<open>accessStore \<lfloor>Toploc (state.Memory st)\<rfloor> (snd (allocate (state.Memory st))) = None\<close> nonLocChanged
          by fastforce
        then show "l2 = l1"
          using selfPoint asm by blast
      qed
      have MCondest2:" MCon (MTArray x memArr) (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) " using 15 MCondest memArrDef
        by (smt (verit, ccfv_SIG) LSubPrefL2_def MemLSubPrefTransitive NonChangeM'm MCon_preserved_under_disjoint_location l_not_toploc_orSub mInStd selfPoint_root)

      have bb:"\<forall>locs tp. CompMemType (Memory st) len subT tp l'' locs \<longrightarrow> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
      proof intros
        fix locs tp 
        assume asm1:"CompMemType (Memory st) len subT tp l'' locs"
        then have a2:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using t7
        proof(induction subT arbitrary:len l'')
          case (MTArray x1 subT)
          then show ?case 
            using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def limitSt limitSt1 subPtrs_nonTop by blast
        next
          case (MTValue x)
          then show ?case 
            by (metis (no_types, lifting) CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def limitSt limitSt1 subPtrs_nonTop)
        qed
        then show " locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" by simp
        show "\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) " using a2 by simp
      qed
      have b8:"\<forall>locs tp. CompMemType m len subT tp l'' locs \<longrightarrow> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
      proof intros
        fix locs tp 
        assume asm1:"CompMemType m len subT tp l'' locs"
        then show "locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"  using t7 bb a32
        proof(induction subT arbitrary:len l'')
          case (MTArray x1 subT)
          obtain i' ptr' where i'Def:"i'<len \<and> accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m = Some (MPointer ptr') \<and> (ptr' = locs \<and> MTArray x1 subT = tp \<or> CompMemType m x1 subT tp ptr' locs)" 
            using MTArray.prems(1) unfolding CompMemType.simps by blast
          have "\<not> TypedMemSubPref (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)" 

            by (metis MTArray.prems(2) bot_nat_0.extremum_unique i'Def leI limitSt mcon_accessStore nat_less_le neg_MemLSubPrefL2_imps_TypedMemSubPref not_Some_eq)
          then have "accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m" using MTArray.prems memArrDef 
            by (metis MConArrayPointers allocateSame bot_nat_0.extremum_strict bot_nat_0.not_eq_extremum i'Def le_refl limitSt nonLocChanged option.distinct(1))
          then show ?case 
          proof(cases "ptr' = locs")
            case True
            then show ?thesis 
              using MTArray.prems(3) \<open>accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m\<close> i'Def by auto
          next
            case False
            then have "CompMemType m x1 subT tp ptr' locs" 
              using i'Def by blast
            moreover have "MCon (MTArray x1 subT) (Memory st) ptr'" 
              by (metis MCon_imps_sub_Mcon MTArray.prems(2) \<open>accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m\<close> i'Def)
            moreover have "\<forall>locs tp. CompMemType (Memory st) x1 subT tp ptr' locs \<longrightarrow> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
              using MTArray.prems(3) 
              by (metis (no_types, lifting) CompTypeRemainsMCon MCon_imps_Some LSubPrefL2_def \<open>MCon (MTArray x1 subT) (Memory st) ptr'\<close> Not_Sub_More_Specific le_refl limitSt option.distinct(1))
            ultimately show ?thesis using MTArray.IH[of x1 ptr']  using MTArray.prems by blast
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      have nonLocChanged22:" \<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m" using nonLocChanged 
        by (simp add: allocateSame)
      then have l''mMcon:" MCon (MTArray len subT) m l''" using  t7 bb
      proof(induction subT arbitrary: len l'')
        case (MTArray x1 subT)
        have "\<forall>i<len.
             (case accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTArray x1 subT of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 subT) m (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 subT of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 subT) m loc2 | MTValue Types \<Rightarrow> False))"
        proof(intros)
          fix i assume asm1:"i<len"
          then obtain  ptr' where ptr'def:"accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr')
                          \<and> MCon (MTArray x1 subT) (Memory st) ptr'" using MTArray(3) 
            by (metis MConArrayPointers MCon_imps_sub_Mcon MCon.simps(2))
          have "CompMemType (Memory st) len  (MTArray x1 subT)  (MTArray x1 subT) l'' (ptr')" 
            using ptr'def asm1 by auto
          then have "ptr' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 ptr' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
            using MTArray.prems(3) by blast
          have same:"accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)" using nonLocChanged22 
            by (metis Read_Show_nat'_id antisym_conv1 limitSt option.distinct(1) ptr'def readLintNotEqual)

          have "\<forall>locs tp. CompMemType (Memory st) x1 subT tp ptr' locs \<longrightarrow> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
            using MTArray.prems(3) \<open>CompMemType (Memory st) len (MTArray x1 subT) (MTArray x1 subT) l'' ptr'\<close> compMemTypes_trns by blast
          then have "MCon (MTArray x1 subT) m ptr'" using MTArray.IH[of x1 ptr'] ptr'def 
            using nonLocChanged22 by blast
          then show "(case accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case MTArray x1 subT of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 subT) m (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 subT of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 subT) m loc2 | MTValue Types \<Rightarrow> False))" using same ptr'def 
            by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5))
        qed
        moreover have "len > 0" using MTArray.prems unfolding MCon.simps by blast
        moreover have "(\<exists>p. accessStore l'' m = Some (MPointer p)) \<or> accessStore l'' m = None"
        proof(cases "l'' = l")
          case True
          then show ?thesis 
            using lOrigin l_not_toploc_orSub nonLocChanged22 by auto
        next
          case False
          then have "accessStore (l'' ) (Memory st) = accessStore (l'') (m)" using nonLocChanged22 
            by (metis MConArrayPointers MTArray.prems(2) Read_Show_nat'_id calculation(2) lessThanSome_imps_Locs2 lessThanTopLocs_def limitSt limitSt1 readLintNotEqual)
          then show ?thesis 
            using MTArray.prems(2) calculation(2) by force
        qed
        ultimately show ?case using MCon.simps(2)[of len "MTArray x1 subT" m l''] 
          by simp
      next
        case (MTValue x)
        have "\<forall>i<len.
             (case accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
| Some (MValue val) \<Rightarrow> (case MTValue x of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) m (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) m loc2 | MTValue Types \<Rightarrow> False))"
        proof(intros)
          fix i assume asm1:"i<len"
          then obtain val where ptr':"accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue val)
                          \<and> MCon (MTValue x) (Memory st) (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTValue(2) 
            by (metis MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
          then have " CompMemType (Memory st) len (MTValue x) (MTValue x) l'' (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using asm1 by auto
          then have "(hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
            using MTValue by blast
          then have "accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)" using nonLocChanged22 by auto
          then show "(case accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False | Some (MValue val) \<Rightarrow> 
(case MTValue x of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) m (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) m loc2 | MTValue Types \<Rightarrow> False))" 
            using ptr' asm1 
            by (metis mtypes.simps(6) memoryvalue.simps(5) Option.option.simps(5) MCon.simps(1))
        qed
        moreover have "(\<exists>p. accessStore l'' m = Some (MPointer p)) \<or> accessStore l'' m = None"
        proof(cases "l'' =l")
          case True
          then show ?thesis 
            using lOrigin l_not_toploc_orSub nonLocChanged22 by auto
        next
          case False
          then have "accessStore (l'' ) (Memory st) = accessStore (l'') (m)" using nonLocChanged22  
            by (metis MCon_imps_Some MTValue.prems(2) Read_Show_nat'_id antisym_conv1 lessThanSome_imps_Locs2 lessThanTopLocs_def limitSt limitSt1 option.discI readLintNotEqual)

          then show ?thesis 
            by (metis MTValue.prems(2) MCon.simps(2))
        qed
        moreover have "len > 0" using MTValue by fastforce
        ultimately show ?case using MCon.simps(2)[of len "MTValue x" m l''] by simp
      qed

      have p''mMcon:"MCon (MTArray x memArr) m p''" using mconlOld 
      proof(induction memArr arbitrary:x p'')
        case (MTArray x1 t)
        have samep'':"p'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not>LSubPrefL2 p'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
          by (metis (no_types, lifting) MCon_imps_Some MTArray(2) LSubPrefL2_def Not_Sub_More_Specific le_refl limitSt option.distinct(1))
        have "x > 0" using MTArray 
          using zero_less_iff_neq_zero by force
        moreover have "(\<exists>p. accessStore p'' m = Some (MPointer p)) \<or> accessStore p'' m = None" using MTArray samep'' 
          using nonLocChanged22 calculation(1) by force
        moreover have "\<forall>i<x. (case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
                  | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) m (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) m loc2 | MTValue Types \<Rightarrow> False))" 
        proof(intros)
          fix i assume asm1:"i<x"
          then obtain ptr where ptr':"accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr) \<and> MCon (MTArray x1 t) (Memory st) ptr" using MTArray 
            by (meson MConArrayPointers MCon_imps_sub_Mcon \<open>0 < x\<close>)
          moreover have "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st)"
            using MemLSubPrefL2_specific_imps_general \<open>p'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 p'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))\<close> nonLocChanged22 by metis
          moreover have "accessStore ptr (Memory st) = accessStore ptr (m)"
            using  nonLocChanged22 
            by (metis MCon_imps_Some Read_Show_nat'_id antisym_conv1 calculation(1) lessThanSome_imps_Locs2 lessThanTopLocs_def limitSt limitSt1 option.discI readLintNotEqual)
          moreover have "MCon (MTArray x1 t) m ptr" using MTArray.IH ptr' by blast
          ultimately show "case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
        | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) m (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
         | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) m loc2 | MTValue Types \<Rightarrow> False)" by simp
        qed
        ultimately show ?case using MCon.simps(2)[of x "MTArray x1 t" m p''] by simp
      next
        case (MTValue x')
        have "p'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not>LSubPrefL2 p'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
          by (metis (no_types, lifting) MCon_imps_Some MTValue LSubPrefL2_def Not_Sub_More_Specific le_refl limitSt option.distinct(1))
        then have samep':"accessStore p'' (Memory st) = accessStore p'' m" 
          by (simp add: nonLocChanged22)
        have "\<forall>i<x. (case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
| Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') m (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') m loc2 | MTValue Types \<Rightarrow> False))"
        proof(intros)
          fix i assume asm1:"i<x" 
          then obtain val where "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue val) \<and> MCon (MTValue x') (Memory st) (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTValue 
            by (meson MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
          moreover have "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)" 
            using MemLSubPrefL2_specific_imps_general \<open>p'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 p'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))\<close> nonLocChanged22 by blast
          ultimately show "(case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
                  | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') m (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') m loc2 | MTValue Types \<Rightarrow> False))" 
            by auto
        qed
        moreover have "x > 0" using MTValue 
          using zero_less_iff_neq_zero by force
        moreover have "(\<exists>p. accessStore p'' m = Some (MPointer p)) \<or> accessStore p'' m = None" using MTValue samep' 
          using calculation(2) by auto
        ultimately show ?case using MCon.simps(2)[of x "MTValue x'" m p''] by simp
      qed

      have prntMconNew:"MCon (MTArray len' (MTArray x memArr)) (Memory st') prnt"
      proof - 
        have " \<forall>i<len'.
             (case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x memArr of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x memArr) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x memArr of MTArray len' arr' \<Rightarrow> MCon (MTArray x memArr) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
        proof intros
          fix i' assume asm1:"i'<len'"
          then obtain ptr where ptrDef': "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some(MPointer ptr)
                                  " and ptrDef'2:"MCon (MTArray x memArr) (Memory st) ptr"
            using mconPrnt by (metis MConArrayPointers MCon_imps_sub_Mcon bot_nat_0.not_eq_extremum not_less_zero)

          show "case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x memArr of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x memArr) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x memArr of MTArray len' arr' \<Rightarrow> MCon (MTArray x memArr) (Memory st') loc2 | MTValue Types \<Rightarrow> False)" 
          proof(cases "i' = i")
            case True
            then show ?thesis 
              using MCondest2 accessL ldef mInStd by force
          next
            case False
            then have "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st')" using ldef 
              by (metis hashesIntSame limitSt nle_le nonLocChanged2 option.distinct(1) ptrDef')
            then have same:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st') =  Some(MPointer ptr)" using ptrDef' by simp

            have locRule:"\<forall>ct locs ints. CompMemType (Memory st) len' (MTArray x memArr) ct prnt locs \<longrightarrow> locs \<noteq> prnt \<and> hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t ints) \<noteq> l"  
              using BothMConImpsNotCompMemType CompTypeRemainsMCon mconPrnt ldef  ShowLNatDot hash_injective by metis
            have "CompMemType (Memory st) len' (MTArray x memArr) (MTArray x memArr)  prnt ptr" using ptrDef' asm1 by auto
            then have "MCon (MTArray x memArr) (Memory st') ptr" using ptrDef'2 locRule 
            proof(induction memArr arbitrary: x ptr len' prnt)
              case (MTArray x11 x12)
              have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTArray x11 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x11 x12) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTArray x11 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x11 x12) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
              proof intros
                fix i'' assume "i''<x"
                then obtain ptr' where ptr'Def:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st) = Some(MPointer ptr')
                                                \<and> MCon (MTArray x11 x12) (Memory st) ptr'" using  MTArray.prems(2)
                  by (metis MConArrayPointers MCon_imps_sub_Mcon  neq0_conv not_less_zero)
                have "ptr \<noteq> prnt" using MTArray.prems by blast
                then have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems ShowLNatDot hash_injective by blast
                then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st) = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st')" 
                  by (metis less_or_eq_imp_le limitSt nonLocChanged2 option.discI ptr'Def)
                then have same2:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some(MPointer ptr')" using ptr'Def by simp

                have "MCon (MTArray x11 x12) (Memory st) ptr'" using ptr'Def by blast
                moreover have "CompMemType (Memory st) x (MTArray x11 x12) (MTArray x11 x12) ptr ptr'" using ptr'Def 
                  using \<open>i'' < x\<close> by auto
                moreover have "\<forall>ct locs ints. CompMemType (Memory st) x (MTArray x11 x12) ct ptr locs \<longrightarrow> locs \<noteq> ptr \<and> hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t ints) \<noteq> l" 
                  by (metis BothMConImpsNotCompMemType CompTypeRemainsMCon MTArray.prems(1,2,3) compMemTypes_trns)
                ultimately have "MCon (MTArray x11 x12) (Memory st') ptr'" using MTArray.IH[of x x11 ptr ptr'] by blast
                then show "(case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTArray x11 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x11 x12) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
               | Some (MPointer loc2) \<Rightarrow> (case MTArray x11 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x11 x12) (Memory st') loc2 | MTValue Types \<Rightarrow> False))" 
                  using ptrDef' same2 by auto
              qed

              moreover have xNotZero:"x>0" using MTArray.prems(2) 
                using bot_nat_0.not_eq_extremum by fastforce
              moreover have "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
              proof(cases "ptr = l")
                case True
                then have " accessStore ptr (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 15 by auto
                then show ?thesis by blast
              next
                case False
                then have pdef:"(\<exists>p. accessStore ptr (Memory st) = Some (MPointer p)) \<or> accessStore ptr (Memory st) = None" 
                  using MTArray.prems(2) MCon.simps(2)[of x _ "Memory st" ptr] xNotZero by simp
                then have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt1 limitSt 
                  by (metis (no_types, lifting) MCon_imps_Some MTArray.prems(2) LSubPrefL2_def Not_Sub_More_Specific le_refl option.distinct(1))
                then have "accessStore ptr (Memory st) =accessStore ptr (Memory st') " using False nonLocChanged2 by simp
                then show ?thesis using pdef by simp
              qed
              ultimately show ?case  using MCon.simps(2)[of x "MTArray x11 x12" "Memory st'" ptr]  by simp
            next
              case (MTValue x2)
              have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case MTValue x2 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x2) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x2 of MTArray len' arr' \<Rightarrow> MCon (MTValue x2) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
              proof intros
                fix i'' assume "i''<x"
                then obtain val where oldDef:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st) = Some(MValue val)
                                                \<and> MCon (MTValue x2) (Memory st) (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))" using MTValue ptrDef' 
                  by (meson MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
                have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l " using MTValue ldef ShowLNatDot hash_injective by blast
                then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st) = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))  (Memory st')" 
                  by (metis less_or_eq_imp_le limitSt nonLocChanged2 option.discI oldDef)
                then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some(MValue val)" using oldDef by simp
                then show "case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
                       | Some (MValue val) \<Rightarrow> (case MTValue x2 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x2) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
                       | Some (MPointer loc2) \<Rightarrow> (case MTValue x2 of MTArray len' arr' \<Rightarrow> MCon (MTValue x2) (Memory st') loc2 | MTValue Types \<Rightarrow> False)" 
                  using oldDef by auto
              qed
              moreover have xNotZero:"x>0" using MTValue(2) 
                using bot_nat_0.not_eq_extremum by fastforce
              moreover have "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
              proof(cases "ptr = l")
                case True
                then have " accessStore ptr (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 15 by auto
                then show ?thesis by blast
              next
                case False
                then have pdef:"(\<exists>p. accessStore ptr (Memory st) = Some (MPointer p)) \<or> accessStore ptr (Memory st) = None" 
                  using MTValue(2) MCon.simps(2)[of x _ "Memory st" ptr] xNotZero by simp
                then have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt1 limitSt 
                  by (metis (no_types, lifting) MCon_imps_Some MTValue(2) LSubPrefL2_def Not_Sub_More_Specific le_refl option.distinct(1))
                then have "accessStore ptr (Memory st) =accessStore ptr (Memory st') " using False nonLocChanged2 by simp
                then show ?thesis using pdef by simp
              qed

              ultimately show ?case using MCon.simps(2)[of x "MTValue x2" "Memory st'" ptr] by simp
            qed
            then show ?thesis using same asm1 by simp
          qed
        qed

        moreover have "len' > 0" using mconPrnt 
          using ldef by auto
        moreover have "prnt \<noteq> l" using ldef 
          by (metis hash_inequality)
        moreover have "(\<exists>p. accessStore prnt (Memory st') = Some (MPointer p)) \<or> accessStore prnt (Memory st') = None"
        proof(cases "LSubPrefL2 prnt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
          case True
          then show ?thesis 
            by (metis LSubPrefL2_def Not_Sub_More_Specific l_not_toploc_orSub ldef)
        next
          case False
          then show ?thesis using nonLocChanged2 calculation mconPrnt by simp
        qed
        ultimately show ?thesis using MCon.simps(2)[of len' "MTArray x memArr" "Memory st'" prnt] mconPrnt  nonLocChanged2 ldef by simp
      qed

      have compmemst':"\<forall>locs lens subTs. CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt 
                            \<and> MCon (MTArray lens subTs) (Memory st) locs 
                          \<longrightarrow> CompMemType (Memory (st')) lens subTs (MTArray len' arr') locs prnt \<and> CompMemType (m) lens subTs (MTArray len' arr') locs prnt"
      proof intros
        fix locs lens subTs
        assume asm1:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt  \<and> MCon (MTArray lens subTs) (Memory st) locs"
        then have asm5:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt" by blast
        have asm6:"MCon (MTArray lens subTs) (Memory st) locs" using asm1 by blast
        have asm2:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory (st)) = accessStore locs m"
          using nonLocChanged allocateSame by auto
        have mconl'':"MCon (MTArray len subT) (Memory st) l''" using  lInfo(5) tParentType  by simp

        have a5:"CompMemType m lens subTs (MTArray len' arr') locs prnt" using cpm2mCompMemTypeOld_imps_CompMemType[OF asm5 asm2 ] asm6 limitSt 
          by (metis (no_types, opaque_lifting) MCon_imps_Some LSubPrefL2_def eq_imp_le Not_Sub_More_Specific not_None_eq)
        then have a10:"CompMemType (Memory st') lens subTs (MTArray len' arr') locs prnt \<and> CompMemType m lens subTs (MTArray len' arr') locs prnt" using asm6 
        proof(induction subTs arbitrary: lens locs)
          case (MTArray x11 x12)
          then have "CompMemType m lens (MTArray x11 x12) (MTArray len' arr') locs prnt" using a5 by simp
          then obtain iIn lIn where iInDef:"iIn<lens \<and> accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) m = Some (MPointer lIn) 
                    \<and> (lIn = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType m x11 x12 (MTArray len' arr') lIn prnt)"
            unfolding CompMemType.simps by blast
          have same2:" accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) m =  accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st)" 
            using MConArrayPointers MTArray.prems(2) allocateSame bot_nat_0.not_eq_extremum iInDef le_eq_less_or_eq limitSt nonLocChanged not_less_zero option.discI by metis
          then have mcIn:"MCon (MTArray x11 x12) (Memory st) lIn" using same2 iInDef MTArray.prems
            by (metis MCon_imps_sub_Mcon)
          then show ?case
          proof(cases "lIn = prnt")
            case True
            have "prnt \<noteq> l" using ldef 
              by (metis hash_inequality)
            moreover have "MTArray x11 x12 = MTArray len' arr'" using iInDef True 
              by (metis CompMemType_imps_CompMemJustType MConSubTypes \<open>MCon (MTArray x11 x12) (Memory st) lIn\<close> lsublocs mconPrnt CompMemJustType.simps(2))
            ultimately show ?thesis using True 
              by (metis MConPtrsMustBeSubLocs NonChangeM'm iInDef lsublocs mInStd same2 CompMemType.simps(2))
          next
            case False
            then have "CompMemType m x11 x12 (MTArray len' arr') lIn prnt" using iInDef by blast
            then have cp:"CompMemType (Memory st') x11 x12 (MTArray len' arr') lIn prnt" using MTArray.IH[of x11 lIn] mcIn by blast
            have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) \<noteq> l" 
              by (metis CompMemType_imps_CompMemJustType CompMemTypes_asc MConSubTypes memoryvalue.inject(2) iInDef lOrigin lsublocs mcIn mconlOld option.inject same2
                  CompMemJustType.simps(2))
            then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st')" 
              by (simp add: NonChangeM'm mInStd)
            then have "\<exists>i<lens. \<exists>l. accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer l)
                \<and> (l = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType (Memory st') x11 x12 (MTArray len' arr') l prnt)"
              using False cp iInDef by metis
            then show ?thesis unfolding CompMemType.simps(2) 
              using iInDef by blast
          qed
        next
          case (MTValue x2)
          then show ?case 
            using compType by auto
        qed
        then show "CompMemType (Memory st') lens subTs (MTArray len' arr') locs prnt" by blast
        show "CompMemType m lens subTs (MTArray len' arr') locs prnt " using a10 by simp
      qed

     

      have l''MConst':"\<forall>locs lens subTs. CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt 
                            \<and> MCon (MTArray lens subTs) (Memory st) locs \<and> MCon (MTArray lens subTs) m locs \<longrightarrow> MCon (MTArray lens subTs) (Memory st') locs"
      proof intros

        fix locs lens subTs
        assume asm6:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt \<and> MCon (MTArray lens subTs) (Memory st) locs \<and> MCon (MTArray lens subTs) m locs "
        then have asm7:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt" by simp
        have asm8:"MCon (MTArray lens subTs) (Memory st) locs" using asm6 by blast
        have asm9:"MCon (MTArray lens subTs) m locs " using asm6 by blast
        show "MCon (MTArray lens subTs) (Memory st') locs "
        proof(cases "locs = prnt")
          case True
          then show ?thesis 
            using MConPtrsMustBeSubLocs2 lsublocs lsublocs3 prntMconNew asm8 asm7 by blast
        next
          case False
          then have cpMemo:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt" 
            using asm6 by blast  
          then have asm10:"CompMemType m lens subTs (MTArray len' arr') locs prnt" using compmemst' asm8 by blast
          then have "CompMemType (Memory (st')) lens subTs (MTArray len' arr') locs prnt" using compmemst' 
            using asm8 cpMemo by blast
          have "CompMemType m lens subTs (MTArray x memArr) locs p''" using asm10 compType 
            by (metis allocateSame compMemTypes_trns lOrigin l_not_toploc_orSub lsublocs nonLocChanged CompMemType.simps(2))
          then have "\<forall>locs' loct. CompMemType  m lens subTs loct locs locs' \<and> locs' = p'' \<longrightarrow> loct = (MTArray x memArr)"  
            using p''mMcon  asm9 asm7 
            using CompMemTypeSameLocsSameType by blast
          then show ?thesis using asm9 p''mMcon ldef lOrigin
          proof(induction subTs arbitrary: lens locs)
            case (MTArray x1 subT)
            have "\<forall>i<lens.
             (case accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x1 subT of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 subT) (Memory st') (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 subT of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 subT) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
            proof intros
              fix i'' assume asm1:"i''<lens"
              then obtain ptr where ptrDef:"accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = Some (MPointer ptr) \<and> MCon (MTArray x1 subT) m ptr" using MTArray.prems(2) 
                by (metis MConArrayPointers MconSameTypeSameAccessWithTyping bot_nat_0.not_eq_extremum less_nat_zero_code)

              show "(case accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x1 subT of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 subT) (Memory st') (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 subT of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 subT) (Memory st') loc2 | MTValue Types \<Rightarrow> False))" 
              proof(cases "ptr = p''")
                case True
                then have sameTp:" (MTArray x1 subT) =  (MTArray x memArr)" using MTArray.prems ptrDef asm1 by auto 
                then show ?thesis 
                proof(cases "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) = l")
                  case True
                  then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" 
                    using accessL mInStd by auto
                  then show ?thesis using sameTp  MCondest2 by fastforce
                next
                  case False
                  then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')" 
                    by (simp add: NonChangeM'm mInStd)
                  have "\<forall>locs loct.  CompMemType m x1 subT loct ptr locs \<and> locs = p'' \<longrightarrow> loct = MTArray x memArr" 
                    using CompMemTypeSameLocsSameType ptrDef 
                    using MTArray.prems(1) asm1 CompMemType.simps(2) by blast
                  moreover have "MCon (MTArray x1 subT) (Memory st') ptr" using MTArray.IH[of x1 ptr] MTArray.prems  ptrDef calculation by blast
                  ultimately show ?thesis 
                    by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5) \<open>accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')\<close> ptrDef)
                qed
              next
                case False
                then have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems memoryvalue.inject(2) \<open>accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = Some (MPointer ptr) \<and> MCon (MTArray x1 subT) m ptr\<close>  option.inject

                  by (metis l_not_toploc_orSub nonLocChanged22)
                then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')" 
                  by (simp add: NonChangeM'm mInStd)
                have "\<forall>locs loct.  CompMemType m x1 subT loct ptr locs \<and> locs = p'' \<longrightarrow> loct = MTArray x memArr" 
                  using CompMemTypeSameLocsSameType ptrDef 
                  using MTArray.prems(1) asm1 CompMemType.simps(2) by blast
                moreover have "MCon (MTArray x1 subT) (Memory st') ptr" using MTArray.IH[of x1 ptr] MTArray.prems  ptrDef calculation by blast
                ultimately show ?thesis 
                  by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5) \<open>accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')\<close> ptrDef)
              qed
            qed
            moreover have "lens > 0" using MTArray by force
            moreover have "(\<exists>p. accessStore locs (Memory st') = Some (MPointer p)) \<or> accessStore locs (Memory st') = None"
            proof(cases "locs = l")
              case True
              then show ?thesis 
                using accessL mInStd by auto
            next
              case False
              then have "accessStore locs (Memory st') = accessStore locs m" 
                by (simp add: NonChangeM'm mInStd)
              then show ?thesis using MTArray(3) calculation(2) by simp
            qed

            ultimately show ?case using MCon.simps(2)[of lens "MTArray x1 subT" "Memory st'" locs] by simp
          next
            case (MTValue x')
            have "\<forall>i<lens.
             (case accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') (Memory st') (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
            proof(intros)
              fix i'' assume asm1:"i''<lens"
              then obtain ptr where ptrDef:"accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (m) = Some(MValue ptr) \<and> MCon (MTValue x') m (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i''))" 
                using MCon_sub_MTVal_imps_val MTValue.prems(2) MconSameTypeSameAccessWithTyping by presburger
              then have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" 
                using allocateSame lOrigin l_not_toploc_orSub nonLocChanged by fastforce
              then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (m) = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')" 
                by (simp add: NonChangeM'm mInStd)
              then show "case accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') (Memory st') (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') (Memory st') loc2 | MTValue Types \<Rightarrow> False)" 
                using ptrDef 
                by (metis mtypes.simps(6) memoryvalue.simps(5) Option.option.simps(5) MCon.simps(1))
            qed
            moreover have "lens > 0" using MTValue by fastforce
            moreover have "(\<exists>p. accessStore locs (Memory st') = Some (MPointer p)) \<or> accessStore locs (Memory st') = None"
            proof(cases "locs = l")
              case True
              then show ?thesis 
                using accessL mInStd by auto
            next
              case False
              then have "accessStore locs (Memory st') = accessStore locs m" 
                by (simp add: NonChangeM'm mInStd)
              then show ?thesis using MTValue(2) calculation(2) by simp
            qed
            ultimately show ?case using MCon.simps(2)[of lens "MTValue x'" "Memory st'" locs] by simp
          qed
        qed
      qed
      have mcf:"\<forall>x11 x12 x3. CompMemType (Memory st) x11 x12 (MTArray len subT) x3 l'' \<and> MCon (MTArray x11 x12) (Memory st) x3
            \<longrightarrow> CompMemType m x11 x12 (MTArray len subT) x3 l''"
      proof(intros)
        fix x11 x12 x3
        assume asm3:"CompMemType (Memory st) x11 x12 (MTArray len subT) x3 l'' \<and> MCon (MTArray x11 x12) (Memory st) x3"
        then show "CompMemType m x11 x12 (MTArray len subT) x3 l''"
        proof(induction x12 arbitrary: x11 x3)
          case (MTArray x1 x12)
          then obtain i'' ptr where ptrDef:"(i''<x11 \<and> accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some (MPointer ptr) \<and> (ptr = l'' \<and> MTArray x1 x12 = MTArray len subT \<or> CompMemType (Memory st) x1 x12 (MTArray len subT) ptr l''))" 
            unfolding CompMemType.simps by blast
          then show ?case 
          proof(cases "ptr = l''")
            case True
            then show ?thesis 
              by (metis CompMemType.simps(2) MTArray.prems existingLocation_imps_allLocs_same limitSt nle_le nonLocChanged22 option.discI
                  ptrDef)
          next
            case False
            then have " CompMemType (Memory st) x1 x12 (MTArray len subT) ptr l''" using ptrDef by simp
            moreover have "MCon (MTArray x1 x12) (Memory st) ptr" 
              using MCon_imps_sub_Mcon MTArray.prems ptrDef by blast
            ultimately show ?thesis using MTArray.IH[of x1 ptr] 
              by (metis limitSt nat_le_linear nonLocChanged22 not_Some_eq ptrDef CompMemType.simps(2))
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed

      

      
      have BT3:"\<forall>locs tp x t. \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> \<not>CompMemType (Memory (st')) x t tp (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) locs 
                                                                    \<and> \<not>TypedMemSubPrefPtrs (Memory (st')) x t (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) locs" 
        using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def SubPtrs_top selfPoint2 by blast

      have mconL''New:"MCon (MTArray len subT) (Memory st') l''" using lsublocs3
      proof(cases "prnt = l''")
        case True
        then have notComp:"\<not>CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt" 
          using  lsublocs BothMConImpsNotCompMemType[of len subT "Memory st" l'' "(MTArray len' arr')"] lsublocs3  
          using BothMConImpsNotCompMemType t7 by blast
        then have sameTypes:"len = len' \<and> arr' = subT " using lsublocs3 by simp
        then show ?thesis using prntMconNew True 
          using lsublocs by blast
      next
        case False
        then have "CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt" using lsublocs3 by simp
        then have a:"CompMemType (Memory (st')) len subT (MTArray len' (MTArray x memArr)) l'' prnt" using compmemst'  lsublocs  
          using t7 by blast
        then show ?thesis using False l''MConst' t7  
          using \<open>CompMemType (Memory st) len subT (MTArray len' arr') l'' prnt\<close> l''mMcon by blast
      qed

      have NonChangeM'mT:"\<forall>locs. accessTypeStore locs m = accessTypeStore locs m'"
        using 15(5) unfolding accessStore_def updateStore_def accessTypeStore_def by auto

      have sameTypeAccess:" \<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))  \<longrightarrow>
       accessTypeStore locs (Memory st) = accessTypeStore locs m" 
        using  15(4) unfolding cps2m_def 
        using cps2mSingleChange_Typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]  
          allocateTypeSameAccess by metis

      have sameTypeAccess2:" \<forall>locs.  \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))  \<longrightarrow>
       accessTypeStore locs (Memory st) = accessTypeStore locs m" 
        using  15(4) unfolding cps2m_def 
        using cps2mSingleChange2_Typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]  
          allocateTypeSameAccess memArrDef compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 15(3)]  
        by (metis sameTypeAccess)


      have tps:"\<forall>destl'.
       TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
       (\<exists>stt. CompMemType m x memArr stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) destl' \<and>
           (case stt of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
            | MTValue pval \<Rightarrow> accessTypeStore destl' m = Some (MTValue pval)))" 
        using 15(3,4) memArrDef unfolding cps2m_def
        using cps2m_TypeCompChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m] 
        by simp

      have selfPointMem:"\<forall>l l'.
       TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l" 
        using selfPoint compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 15(3)] memArrDef 
        using selfPoint_root by presburger
      have topIndexType:" \<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some memArr" using memArrDef 
        using "15"(3,4) cps2m_TypeCompChangeIndexs cps2m_def by auto
      have a32Mem:"\<forall>locs.
       \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
       accessStore locs (Memory st) = accessStore locs m" 
        using a32 compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 15(3)] memArrDef 
        using nonLocChanged22 by blast
      have subPrefM:"subPrefixStructuralConsistency (m)"
        using cpm2m_subPrefixPersist[OF _ _ _ sameTypeAccess _ sameTypeAccess2  tps MCondest selfPointMem topIndexType nonLocChanged22 a32Mem] 
          \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame 2(1) 
        unfolding TypeSafe_def by simp

      have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                          \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
      proof -
        have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs m"
          using 15(4,5,6) cps2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]
            cps2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t _ " (snd (allocate (Memory st)))" ] by simp
        then have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs m'"
          using 15(6,5) unfolding accessTypeStore_def updateStore_def by force
        then show "\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
          using allocateTypeSameAccess mInStd by metis
      qed

      have nonLocChanged_MemSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> loc \<noteq> l
                                        \<longrightarrow> accessStore loc (Memory st') = accessStore loc (Memory st)"
        using  mInStd nonLocChanged  allocateSame mInStd 15(5) unfolding updateStore_def accessStore_def
        by (metis accessStore_def nonLocChanged2)

      show ?thesis unfolding TypeSafe_def StateInvariant_def
      proof intros 
        show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 15 by simp
      next 
        show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
      next 
        have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
        then show "compPointers (Stack st') (Denvalue env)"  using sameStack  sameStorage by simp
      next 
        show "safeContract (Accounts st') (Storage st')" using sameStorage 2(1) 15 unfolding TypeSafe_def safeContract_def by auto
      next 
        show "balanceTypes (Accounts st')" using 15 using 2(1) unfolding TypeSafe_def by simp
      next 
        have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
      next 
        show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
      next 
        have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) " 
          using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
        have **:"Toploc (Stack st) = Toploc (Stack st')" using 15 unfolding updateStore_def by auto
        show "lessThanTopLocs (Stack st')"  unfolding lessThanTopLocs_def
        proof intros

          fix tloc loc 
          assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
          then show "accessStore loc (Stack st') = None" using *  
            by (simp add: sameStack)
        next 
          fix loc y 
          assume h1:" accessStore loc (Stack st') = Some y"
          then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** * 
            by (metis sameStack)
        qed
      next 
        show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
      next
        have a10:"Toploc (snd (allocate (Memory st))) = Toploc m" 
          using cps2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m] 15(4) mInStd unfolding cps2m_def by fastforce
        then have a12:"Toploc m = Toploc m'" using 15(5) unfolding updateStore_def by auto
        have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
        have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
        show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def 
        proof intros
          fix tloc loc 
          assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then have b20:"Toploc (Memory st) \<le> tloc" using a10 tloc a12 
            using mInStd by force

          then show "accessStore loc (Memory st') = None " 
            by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive NonChangeM'm \<open>\<exists>x. accessStore l (Memory st) = Some x\<close> a10 a12 allocateSame antisym_conv2 b10 hash_inequality
                hash_suffixes_associative hashesIntSame limitSt mInStd nonLocChanged option.discI order_less_le_trans tloc)
        next 
          fix loc y 
          assume "accessStore loc (Memory st') = Some y "
          then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" 
            by (metis NonChangeM'm \<open>\<exists>x. accessStore l (Memory st) = Some x\<close> a10 a12 allocateSameAccess limitSt1 mInStd nonLocChanged order_less_trans tloc)
        qed
      next 
        show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
          unfolding typeCompat_def
        proof intros
          fix tLook lLook
          assume inDen:" (tLook, lLook) |\<in>| fmran (Denvalue env)"
          show " case lLook of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st') of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case tLook of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case tLook of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False )
                | Some (KMemptr stloc) \<Rightarrow> (case tLook of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case tLook of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case tLook of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
          proof(cases lLook)
            case (Stackloc x1)
            then obtain a where  adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def  using sameStack nonChangedStack by fastforce
            then show ?thesis 
            proof(cases "a")
              case (KValue x1)
              then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack nonChangedStack unfolding TypeSafe_def typeCompat_def
                by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
            next
              case (KCDptr x2)
              then show ?thesis  using Stackloc adef inDen Stackloc 2(1) sameStack nonChangedStack unfolding TypeSafe_def typeCompat_def
                by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5)  stackvalue.simps(18) )
            next
              case (KMemptr x3)
              then have "\<exists>struct. tLook = type.Memory struct" using Stackloc adef  inDen Stackloc 2(1) KMemptr sameStack unfolding TypeSafe_def typeCompat_def  by (cases tLook;force+) 
              then obtain struct where structdef:"tLook = type.Memory struct" by blast

              then have mcOld:"MCon struct (Memory st) x3" using 2(1) unfolding TypeSafe_def typeCompat_def
                using Stackloc adef inDen KMemptr sameStack by (auto split:type.splits denvalue.splits stackvalue.splits option.splits)
              then have mcM:"MCon struct m x3" using PreExistMconNotChangeByToploc  limitSt limitSt1 nonLocChanged22 
                by auto
              have structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
                using 2(1) inDen KMemptr Stackloc structdef adef 15(6)
                unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
              then have structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))" 
                by (metis (no_types, lifting))
              have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                          \<longrightarrow> accessTypeStore loc m = accessTypeStore loc (Memory st)"
              proof -
                have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs m"
                  using 15(4,5,6) cps2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]
                    cps2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t "(Storage st (Address env))" " (snd (allocate (Memory st)))" ] by simp
                then show "\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore loc m = accessTypeStore loc (Memory st)"
                  using allocateTypeSameAccess mInStd by metis
              qed

              then have "accessTypeStore x3 (Memory st) = accessTypeStore x3 m" 
                using limitSt limitSt1 mcOld 
                by (metis AllPtrsNotTop2 lessThanTopLocs_def nat_le_linear)
              moreover have eq2:"\<forall>i::nat. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)"
                using nonLocChanged_TypedSafe limitSt limitSt1 mcOld AllPtrsNotTop2 lessThanTopLocs_def 
                by (metis MemLSubPrefL2_specific_imps_general nat_le_linear)
              ultimately have structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 m = Some (MTValue val))"  using structss by presburger

              have "accessTypeStore l (Memory st) = Some (MTArray x memArr)" 
                using lInfo 15 nonLocChanged memArrDef by simp
              then have accl:"accessTypeStore l (m) = Some (MTArray x memArr)" 
                using nonLocChanged_TypedSafe 
                using l_not_toploc_orSub by auto
              have "MCon struct (Memory st') x3" 
                using cpm2m_singleLChange[OF mcM structss _ _ _ MCondest2 subPrefM] 15(5) mInStd 
                  NonChangeM'm accessL accl memArrDef 
                by (metis lOrigin l_not_toploc_orSub nonLocChanged22)

              then show ?thesis  using structdef KMemptr Stackloc adef  inDen Stackloc 2(1) unfolding TypeSafe_def  typeCompat_def by simp

            next
              case (KStoptr x4)  
              then show ?thesis using Stackloc 
                  adef sameStorage  inDen Stackloc KStoptr 2(1) nonChangedStack sameStack 
                unfolding TypeSafe_def typeCompat_def
                apply(cases tLook) by fastforce+
            qed
          next
            case (Storeloc x2)
            then show ?thesis using sameStorage inDen 2(1) unfolding TypeSafe_def typeCompat_def by (cases tLook; force)
          qed
        qed
        then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd " using sameStack by simp
      next 
        have "Accounts st'= Accounts st" using 15 by auto
        then show "fullyInitialised env  (Accounts st') (Stack st')" using 2(3) unfolding fullyInitialised_def 
          using sameStack by presburger
     next 
        show "denvalueTypeCorrectness env (Stack st') (Memory st') "
          unfolding denvalueTypeCorrectness_def
        proof(intros)
          fix t2 l2 ptr_loc sub_loc
          assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"

          show "case t2 of
         MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          proof -
            have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
              using nonChangedStack * 15(5,6) unfolding accessStore_def updateStore_def by simp
            then have mcOld:"MCon t2 (Memory st) ptr_loc" using * by (metis "2.prems"(1) sameMemTSafe)
            then have old:"(case t2 of
                           MTArray len arr \<Rightarrow>
           (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) 
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
              using sameACC 2(1) * TypeSafe_def denvalueTypeCorrectness_def by fastforce

            have inDenvalue:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env)" using * by simp

            then show ?thesis
            proof(cases t2)
              case (MTArray x11 x12)
              then have mcOld:"MCon (MTArray x11 x12) (Memory st) ptr_loc" using mcOld by blast
              have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12)" 
                using old MTArray by simp

              have conc0:"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12)"
              proof - 
                have o:"\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12" using old' by blast
                then have "\<forall>i<x11. \<exists>v. accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some v"
                  using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by auto
                then have "\<forall>i<x11. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" 
                  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by fastforce
                then show ?thesis using nonLocChanged_TypedSafe o nonLocChanged_MemSafe old' by auto
              qed              
              then show ?thesis using MTArray by auto
            next
              case (MTValue x2)
              have "\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
                using typeSafe_noDenElementOverToploc_mem[OF 2(1) inDenvalue] * sameACC 
                using LSubPrefL2_def MemLSubPrefTransitive by metis
              then have "accessTypeStore ptr_loc (Memory st') = accessTypeStore ptr_loc (Memory st)"
                using "15"(6) allocateTypeSameAccess cpm2mSingleChange_Typed cpm2m_def mInStd 
                using nonLocChanged_TypedSafe by blast
              then show ?thesis using MTValue old by simp
            qed
          qed
        qed
      next
        show "subPrefixStructuralConsistency (Memory st')" 
          unfolding subPrefixStructuralConsistency_def
        proof intros
          fix locs tp
          assume in1:" accessTypeStore locs (Memory st') = Some tp "
          have sameTy:"\<forall>locs. accessTypeStore locs m = accessTypeStore locs (Memory st') "
            using mInStd by (metis NonChangeM'mT)
          then have in2:"accessTypeStore locs m = Some tp " using in1 by simp
          show "case accessStore locs (Memory st') of None \<Rightarrow> False
                | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
                | Some (MPointer p) \<Rightarrow>
                   \<exists>len arr.
                      MCon tp (Memory st') p \<and>
                      tp = MTArray len arr \<and>
                      (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
          proof(cases "locs = l")
            case True
            have "accessTypeStore l (Memory st) = Some (MTArray x memArr)" 
              using lInfo 15 nonLocChanged memArrDef by auto
            then have accl:"accessTypeStore l (m) = Some (MTArray x memArr)" 
              using nonLocChanged_TypedSafe l_not_toploc_orSub 
              using sameTypeAccess by auto
            then have tpDef:"tp = MTArray x memArr" 
              using sameTy True in1 by simp
            then have ptr:"accessStore locs (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" 
              using mInStd True by (metis accessL)
            have sameAccm:"accessStore l m = accessStore l (Memory st)" 
              using l_not_toploc_orSub nonLocChanged22 by fastforce
            moreover have " MCon tp (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"   
              using MCondest2 tpDef by blast
            moreover have "(\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some memArr)"
              using tpDef ptr subPrefM sameAccm accl unfolding subPrefixStructuralConsistency_def 
              using sameTy topIndexType by presburger
            moreover have "
           (\<forall>v. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st') = Some (MPointer v) 
                  \<longrightarrow> accessTypeStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st') = Some (MTArray x memArr))" 
              using LSubPrefL2_def selfPoint2 by blast
            ultimately show ?thesis using True tpDef ptr by auto
          next
            case False
            then have sameACC:"accessStore locs m = accessStore locs (Memory st')" 
              using mInStd NonChangeM'm by simp
            then have in3:"(case accessStore locs m of None \<Rightarrow> False | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp
        | Some (MPointer p) \<Rightarrow>
            \<exists>len arr.
               MCon tp m p \<and>
               tp = MTArray len arr \<and>
               (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) )" 
              using subPrefM in2 unfolding subPrefixStructuralConsistency_def by blast
            then show ?thesis 
            proof(cases "accessStore locs m")
              case None
              then show ?thesis using in3 sameACC by simp
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (MValue x1)
                then obtain val where " MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp"
                  using in3 Some by auto
                moreover have "MCon tp (Memory st') locs" using sameACC calculation by auto
                ultimately show ?thesis using sameACC Some MValue sameTy
                  by (auto split:option.splits)
              next
                case (MPointer x2)
                have "accessTypeStore l (Memory st) = Some (MTArray x memArr)" 
                  using lInfo 15 nonLocChanged memArrDef by auto
                then have accl:"accessTypeStore l (m) = Some (MTArray x memArr)" 
                  using nonLocChanged_TypedSafe l_not_toploc_orSub 
                  using sameTypeAccess by auto
                then obtain len arr where s:"MCon tp m x2 \<and> tp = MTArray len arr \<and>
                           (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)"
                  using Some in3 MPointer by auto
                then have mcM:"MCon tp m x2" by auto
                have lAcc:"updateStore l (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))) m = Memory st'"
                  using 15(5) mInStd by blast
                have "MCon tp (Memory st') x2" 
                  using cpm2m_singleLChange[OF mcM _ lAcc _ accl MCondest2 subPrefM] 
                    mInStd NonChangeM'm accessL lOrigin l_not_toploc_orSub nonLocChanged22 s 
                  by auto

                moreover have "(\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
                  using s sameTy by simp

                ultimately show ?thesis using Some MPointer sameACC sameTy s
                  by (auto split:option.splits)
              qed
            qed
          qed
        qed
      next 
        have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))" 
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
        have somesome:"\<forall>destl'. TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) 
              \<longrightarrow> (\<exists>t. accessStore destl' m = Some t) = (\<exists>tt. accessTypeStore destl' m = Some tt)"
          using 15(3,4) unfolding cps2m_def using cps2m_TypeCompChange_somesome[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m] 
          using memArrDef by blast
        have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) 
                  \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs m" 
          using 15(3,4) unfolding cps2m_def using cps2mSingleChange2_Typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]  
            mInStd allocateTypeSameAccess memArrDef 
          by (metis (no_types, lifting) ext compatible_TypedStoSubpref_imps_TypedMemSubPref_neg cps2mSingleChange_Typed)
        have lIs:"\<exists>x. accessStore l (Memory st) = Some x" using lInfo by (auto split:option.splits)
        show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def 
        proof intros
          fix locs
          show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
          proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)")
            case True
            then have ss:"(\<exists>t. accessStore locs m = Some t) = (\<exists>tt. accessTypeStore locs m = Some tt)" 
              using somesome by simp
            then show ?thesis 
            proof(cases "locs = l")
              case True
              then show ?thesis using lInfo NonChangeM'mT accessL mInStd ss 
                using lIs l_not_toploc_orSub nonLocChanged22 by auto
            next
              case False
              then show ?thesis using ss NonChangeM'mT NonChangeM'm mInStd by simp
            qed
          next
            case False
            then have acc1:"accessStore locs (Memory st) = accessStore locs m" 
              by (metis False memArrDef a32Mem)
            have acc2:"accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
              using a30T False mInStd NonChangeM'mT by simp
            show ?thesis
            proof(cases "locs = l")
              case True
              then show ?thesis using lInfo acc2 accessL mInStd by force
            next
              case False
              then have "accessStore locs m = accessStore locs (Memory st')"
                using mInStd NonChangeM'm by auto
              then show ?thesis using old acc1 acc2 by metis
            qed
          qed
        qed
      next
        fix locs tt
        assume a1:" accessTypeStore locs (Memory st) = Some tt"
        then have some:"\<exists>v. accessStore locs (Memory st) = Some v" 
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
        have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) 
                  \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs m" 
          using 15(3,4) unfolding cps2m_def using cps2mSingleChange2_Typed[of p  "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]  
            mInStd allocateTypeSameAccess memArrDef 
          by (metis (no_types, lifting) ext compatible_TypedStoSubpref_imps_TypedMemSubPref_neg cps2mSingleChange_Typed)
        show " accessTypeStore locs (Memory st') = Some tt"
        proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)")
          case True
          then show ?thesis using some a1 
            by (metis le_refl limitSt option.distinct(1) typedPrefix_imp_SubPref)
        next
          case False
          then have acc1:"accessStore locs (Memory st) = accessStore locs m" 
            using a30 mInStd  
            by (metis False memArrDef a32Mem)
          have acc2:"accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using a30T False mInStd NonChangeM'mT by simp
          show ?thesis
          proof(cases "locs = l")
            case True
            then show ?thesis using lInfo acc2 accessL mInStd a1 by argo
          next
            case False
            then show ?thesis using acc1 acc2 a1 by auto
          qed
        qed
      next 
        show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
          by (metis accessL le_refl limitSt mInStd nonLocChanged2 option.distinct(1))
      next
        show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
          by (metis memoryvalue.distinct(1) lOrigin limitSt nonLocChanged2 option.discI option.inject verit_comp_simplify1(2))
      next
        show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
          using lOrigin limitSt nonLocChanged2 
          by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive Read_Show_nat'_id hash_flatten_right hash_inequality nat_less_le option.distinct(1))
      next 
        have a10:"Toploc (snd (allocate (Memory st))) = Toploc m" 
          using cps2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m] 
            15(4) mInStd unfolding cps2m_def by fastforce
        moreover have a12:"Toploc m = Toploc m'" using 15(5) unfolding updateStore_def by auto
        moreover have tloc:"Toploc (Memory st) < Toploc  (snd (allocate (Memory st)))" unfolding allocate_def by simp
        ultimately show "Toploc (Memory st) \<le> Toploc (Memory st')" 
          using mInStd by auto
      qed
    qed
  next
    case (16 p t g' g l t'' t')
    then have stackChanged:"\<forall>l'. l' \<noteq> l \<longrightarrow> accessStore l' (Stack st) = accessStore l' (Stack st')" unfolding updateStore_def accessStore_def by simp
    have t'InDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[OF 16(2)] by blast
    then have lDen:"\<forall>t'. (t', Stackloc l) |\<in>| fmran (Denvalue env) \<longrightarrow> t'= (type.Storage (STMap t g'))" using 16 2(1) unfolding TypeSafe_def unique_locations_def by auto

    have pOrigin:"SCon (STMap t g') (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) \<and>
        (\<exists>xx. KStoptr p = KStoptr xx) \<and>
        (\<exists>stloc tp'' .
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue env) \<and>
            (tp'' = (STMap t g') \<and> KStoptr p = KStoptr stloc \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STMap t g') stloc (extractValueType (KStoptr p))))" 
      using 2(1) 16(1) 2(3) using
        exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KStoptr p" ] 
      by (auto split:type.splits if_splits )
    obtain pParent pParentT  where 
      pOrigin:"SCon (STMap t g') (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) 
          \<and>(type.Storage pParentT, Storeloc pParent) |\<in>| fmran (Denvalue env) \<and>
            (pParentT = (STMap t g') \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and> CompStoType pParentT (STMap t g') pParent (extractValueType (KStoptr p)))"
      using pOrigin by auto
    have a0: "compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    then have pParentRelations:"(\<forall>tp2 l2  l2'  stl2.
        (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
        
        (l2 = Stackloc l2' \<and> accessStore l2' (Stack (st)) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
        (if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2 else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True))" 
      using compPointers_def pOrigin  by blast
    have pSCon:"SCon (STMap t g') (extractValueType (KStoptr p)) (Storage (st) (Address env))" using pOrigin by force

(*All locations that can get to p must have a parent type of MTArray x t and all locations lower than p similarly*)
    have pRelations:"(\<forall>tp2 l2 l2' stl2 . 
    (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and> 
    ((l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some(KStoptr stl2)) \<or> (l2 = Storeloc stl2)) 
     \<longrightarrow>
    (if TypedStoSubpref p stl2 tp2 then CompStoType tp2 (STMap t g') stl2 p 
     else if TypedStoSubpref stl2 p (STMap t g') then CompStoType (STMap t g') tp2 p stl2
     else True))" 
    proof intros 
      fix tp2 l2 l2' stl2
      assume in1:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"

      show "if TypedStoSubpref p stl2 tp2 then CompStoType tp2 (STMap t g') stl2 p else if TypedStoSubpref stl2 p (STMap t g') then CompStoType (STMap t g') tp2 p stl2 else True"
      proof(cases "l2 = Stackloc l2'")
        case StL2:True

        have "SCon pParentT pParent (Storage st (Address env))" using pOrigin using 2(1) unfolding TypeSafe_def typeCompat_def by force
        have prnt:" pParentT = (STMap t g') \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and> CompStoType pParentT (STMap t g') pParent (extractValueType (KStoptr p))"
          using pOrigin by simp
        then have comp:"(if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2 
                      else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True)"
          using pParentRelations in1 StL2 prnt by force 
        then show ?thesis 
        proof(cases "TypedStoSubpref p stl2 tp2")
          case pToStl2:True        
          then show ?thesis 
          proof(cases "pParentT = (STMap t g')")
            case True
            then have cc1:"KStoptr p = KStoptr pParent " using prnt 
              using comp_stotype_same_type_same_loc by blast
            then have cc2:"TypedStoSubpref pParent stl2 tp2" using pToStl2 by auto
            then have "CompStoType tp2 (STMap t g') stl2 p"
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case t2:True
              then show ?thesis using comp 
                by (metis CompStoType_sameLoc_sameType stackvalue.inject(4) True cc1 cc2 typedStoSub_imps_negInv)
            next
              case False
              then have "CompStoType tp2 pParentT stl2 pParent" using comp 
                by (simp add: cc2)
              then show ?thesis 
                using True cc1 by auto
            qed
            then show ?thesis by (simp add: pToStl2)
          next
            case False
            then have cmp:" CompStoType pParentT (STMap t g') pParent p" using prnt by simp
            then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
            then show ?thesis 
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case True
              then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
              have "CompStoType tp2 (STMap t g') stl2 p " using pToStl2 prntStl2  CompStoType_sharedSub cmp by simp
              then show ?thesis using pToStl2 by simp
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                then have "CompStoType tp2 (STMap t g') stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                then show ?thesis using pToStl2 by simp
              next
                case False
                then have "\<not>TypedStoSubpref p stl2 tp2" using f1 cmp tsp NotRelatedPrnt_imps_notRelatedChild[of stl2 pParent pParentT tp2 p]  by simp
                then show ?thesis using f1 pToStl2 cmp by simp
              qed
            qed
          qed
        next
          case f1:False
          then show ?thesis 
          proof(cases " TypedStoSubpref stl2 p (STMap t g')")
            case stl2ToP:True
            have " CompStoType (STMap t g') tp2 p stl2"
            proof(cases "pParentT = (STMap t g')")
              case True
              then have cc1:"KStoptr p = KStoptr pParent " using prnt 
                using comp_stotype_same_type_same_loc by blast
              then have cc2:"TypedStoSubpref stl2 pParent (STMap t g')" using stl2ToP by auto
              then have " CompStoType (STMap t g') tp2 p stl2"
              proof(cases "TypedStoSubpref stl2 pParent pParentT")
                case t2:True
                then have "CompStoType pParentT tp2 pParent stl2" using comp by simp
                then have "CompStoType (STMap t g') tp2 p stl2" using cc1 True  by blast
                then show ?thesis by blast
              next
                case False
                then show ?thesis 
                proof(cases "TypedStoSubpref pParent stl2 tp2")
                  case True
                  then have "CompStoType tp2 pParentT stl2 pParent" using comp False by simp
                  then show ?thesis using True cc1 f1 by auto
                next
                  case f2:False
                  then show ?thesis using False True cc2 by blast
                qed
              qed
              then show ?thesis by blast
            next
              case False
              then have cmp:" CompStoType pParentT (STMap t g') pParent p" using prnt by simp
              then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
              then show ?thesis 
              proof(cases "TypedStoSubpref stl2 pParent pParentT")
                case True
                then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
                then show ?thesis using CompStoType_sharedSub[OF prntStl2 stl2ToP cmp] by simp
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref pParent stl2 tp2")
                  case True
                  then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                  then have "CompStoType tp2 (STMap t g') stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                  then show ?thesis 
                    using CompStoType_sameLocNdTyp CompStoType_sharedSub stl2ToP by blast
                next
                  case False
                  then show ?thesis 
                    using NotReachablePrnt_imps_notReachableChild cmp f1 stl2ToP by blast
                qed
              qed
            qed
            then show ?thesis using f1 by (simp )
          next
            case False
            then show ?thesis 
              using f1 by auto
          qed
        qed
      next
        case f3:False
        then have StL2:"l2 = Storeloc stl2" 
          using in1 by auto

        then have "SCon pParentT pParent (Storage st (Address env))" using pOrigin using 2(1) unfolding TypeSafe_def typeCompat_def by force
        have prnt:" pParentT = (STMap t g') \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and> CompStoType pParentT (STMap t g') pParent (extractValueType (KStoptr p))"
          using  pOrigin by simp
        then have comp:"(if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2 
                      else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True)"
          using pParentRelations in1  StL2 prnt by force 
        then show ?thesis 
        proof(cases "TypedStoSubpref p stl2 tp2")
          case pToStl2:True        
          then show ?thesis 
          proof(cases "pParentT = (STMap t g')")
            case True
            then have cc1:"KStoptr p = KStoptr pParent " using prnt 
              using comp_stotype_same_type_same_loc by blast
            then have cc2:"TypedStoSubpref pParent stl2 tp2" using pToStl2 by auto
            then have "CompStoType tp2 (STMap t g') stl2 p"
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case t2:True
              then show ?thesis using comp 
                by (metis CompStoType_sameLoc_sameType stackvalue.inject(4) True cc1 cc2 typedStoSub_imps_negInv)
            next
              case False
              then have "CompStoType tp2 pParentT stl2 pParent" using comp 
                by (simp add: cc2)
              then show ?thesis 
                using True cc1 by auto
            qed
            then show ?thesis by (simp add: pToStl2)
          next
            case False
            then have cmp:" CompStoType pParentT (STMap t g') pParent p" using prnt by simp
            then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
            then show ?thesis 
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case True
              then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
              have "CompStoType tp2 (STMap t g') stl2 p " using pToStl2 prntStl2  CompStoType_sharedSub cmp by simp
              then show ?thesis using pToStl2 by simp
            next
              case f1:False
              then show ?thesis 
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                then have "CompStoType tp2 (STMap t g') stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                then show ?thesis using pToStl2 by simp
              next
                case False
                then have "\<not>TypedStoSubpref p stl2 tp2" using f1 cmp tsp NotRelatedPrnt_imps_notRelatedChild[of stl2 pParent pParentT tp2 p]  by simp
                then show ?thesis using f1 pToStl2 cmp by simp
              qed
            qed
          qed
        next
          case f1:False
          then show ?thesis 
          proof(cases " TypedStoSubpref stl2 p (STMap t g')")
            case stl2ToP:True
            have " CompStoType (STMap t g') tp2 p stl2"
            proof(cases "pParentT = (STMap t g')")
              case True
              then have cc1:"KStoptr p = KStoptr pParent " using prnt 
                using comp_stotype_same_type_same_loc by blast
              then have cc2:"TypedStoSubpref stl2 pParent (STMap t g')" using stl2ToP by auto
              then have " CompStoType (STMap t g') tp2 p stl2"
              proof(cases "TypedStoSubpref stl2 pParent pParentT")
                case t2:True
                then have "CompStoType pParentT tp2 pParent stl2" using comp by simp
                then have "CompStoType (STMap t g') tp2 p stl2" using cc1 True  by blast
                then show ?thesis by blast
              next
                case False
                then show ?thesis 
                proof(cases "TypedStoSubpref pParent stl2 tp2")
                  case True
                  then have "CompStoType tp2 pParentT stl2 pParent" using comp False by simp
                  then show ?thesis using True cc1 f1 by auto
                next
                  case f2:False
                  then show ?thesis using False True cc2 by blast
                qed
              qed
              then show ?thesis by blast
            next
              case False
              then have cmp:" CompStoType pParentT (STMap t g') pParent p" using prnt by simp
              then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
              then show ?thesis 
              proof(cases "TypedStoSubpref stl2 pParent pParentT")
                case True
                then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
                then show ?thesis using CompStoType_sharedSub[OF prntStl2 stl2ToP cmp] by simp
              next
                case f1:False
                then show ?thesis 
                proof(cases "TypedStoSubpref pParent stl2 tp2")
                  case True
                  then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                  then have "CompStoType tp2 (STMap t g') stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                  then show ?thesis 
                    using CompStoType_sameLocNdTyp CompStoType_sharedSub stl2ToP by blast
                next
                  case False
                  then show ?thesis 
                    using NotReachablePrnt_imps_notReachableChild cmp f1 stl2ToP by blast
                qed
              qed
            qed
            then show ?thesis using f1 by simp
          next
            case False
            then show ?thesis using f1 by auto
          qed
        qed
      qed
    qed
    have storageSame:"(Storage st' (Address env)) = (Storage st (Address env))" using 16 by simp
    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof (intros)
      show tcN:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
        show "case l' of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof (split denvalue.split, intros)
          fix loc assume a20:"l' = Stackloc loc"
          show "case accessStore loc (Stack st') of None \<Rightarrow> False 
          | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
          | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
          | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
          | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
          proof (cases "loc = l") 

            case False
            show ?thesis
            proof (split option.split, intros)
              assume a30:"accessStore loc (Stack st') = None"
              then have "accessStore loc (Stack st) = None" using 16(4) False by (simp add:stackSingleUpdate)
              then show False using a30 a20 a10 assms TypeSafe_def typeCompat_def False "2.prems"(1) 
                by (metis option.distinct(1) typeSafeLocExists)
            next
              fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
              then have a40:"accessStore loc (Stack st) = Some x2" using 16(4) False by (simp add:stackSingleUpdate)
              then have a50:"(Memory st) = (Memory st')" using 16(4) by simp
              then have a60:"(Storage st) = (Storage st')" using 16(4) by simp
              show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
                  | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                  | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                  | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
                using a10 a20 a30 a40 a50 a60  "2.prems"(1) unfolding TypeSafe_def typeCompat_def by (cases x2; cases t; force)
            qed
          next 
            case sameLoc:True
            show ?thesis
            proof (split option.split, intros)
              assume a30:"accessStore loc (Stack st') = None"
              then show False using a20 a10 assms(1) sameLoc 16(4) notNoneUpdate by simp
            next
              fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
              then have x2IsP:"x2 = KStoptr p" using 16 sameLoc by auto
              show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
              proof(cases "x2")
                case (KValue x1)
                then show ?thesis using x2IsP by auto
              next
                case (KCDptr x2)
                then show ?thesis using x2IsP by (simp add:sameLoc)
              next
                case (KMemptr x3)
                then show ?thesis  using x2IsP by (simp add:sameLoc)
              next
                case (KStoptr x4)
                then show ?thesis using x2IsP a10 a20 lDen storageSame sameLoc 
                  using pSCon by force
              qed
            qed
          qed
        next
          fix x2 assume a20:"l' = Storeloc x2"
          then have "(Storage st' (Address env)) = (Storage st (Address env))" using 16(4) by simp
          then show "case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st' (Address env)) | _ \<Rightarrow> False"  using a10 a20 TypeSafe_def "2.prems"(1) pSCon a10 a20 lDen storageSame 
          proof -
            have "\<And>t d. (t, d) |\<notin>| fmran (Denvalue env) \<or> 
                    (case d of Stackloc l \<Rightarrow> (case accessStore l (Stack st) of None \<Rightarrow> False 
                    | Some (KValue l) \<Rightarrow> (case t of Value t \<Rightarrow> typeCon t l | _ \<Rightarrow> False )
                    | Some (KCDptr l) \<Rightarrow> (case t of Calldata m \<Rightarrow> MCon m cd l | _ \<Rightarrow> False )
                    | Some (KMemptr l) \<Rightarrow> (case t of type.Memory m \<Rightarrow> MCon m (Memory st) l | _ \<Rightarrow> False )
                    | Some (KStoptr l) \<Rightarrow> (case t of type.Storage s \<Rightarrow> SCon s l (Storage st (Address env)) | _ \<Rightarrow> False))
                    | Storeloc l \<Rightarrow> (case t of type.Storage s \<Rightarrow> SCon s l (Storage st (Address env)) | _ \<Rightarrow> False))"
              using "2.prems"(1) unfolding TypeSafe_def typeCompat_def by auto
            then show ?thesis
              by (metis (no_types) denvalue.simps(6) a10 a20 storageSame)
          qed 
        qed
      qed
      have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
        show "case l' of
             Stackloc loc \<Rightarrow>
               (case accessStore loc (Stack st) of None \<Rightarrow> False 
                | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))
             | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address env)) | _ \<Rightarrow> False)" 
        proof(cases "l'")
          case (Stackloc x1)
          then show ?thesis 
          proof(cases "x1 = l")
            case sameLoc:True
            then show ?thesis 
            proof(cases "accessStore x1 (Stack st)")
              case None
              then show ?thesis using Stackloc a10 assms(1) sameLoc 16(4) 
                by (metis "2.prems"(1) option.distinct(1) typeSafeAllStacklocsExist)
            next
              case (Some a)
              then obtain t''' where "t = type.Storage t'''" using lDen a10 Stackloc 2(1) sameLoc by blast
              then have x2IsP:"\<exists>p. a = KStoptr p" using 16 sameLoc  2(1) a10 Stackloc Some  unfolding TypeSafe_def typeCompat_def
                by (cases a, force,simp,fastforce+)
              then show ?thesis using x2IsP a10 Stackloc lDen storageSame sameLoc Some "2.prems"(1) unfolding TypeSafe_def typeCompat_def
                using pSCon by force
            qed
          next
            case False
            then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')"
              using stackChanged by auto
            then show ?thesis using a10 Stackloc tcN unfolding typeCompat_def by force
          qed
        next
          case (Storeloc x2)
          then show ?thesis using a10 tcN unfolding typeCompat_def by force
        qed
      qed
    next
      show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by auto
    next
      have "(Accounts st) = Accounts(st')" using 16 by simp
      then show "balanceTypes (Accounts st')" using balanceTypes_def balanceTypes_def 2(1) typeSafeAccounts by simp
    next
      have a0:"compPointers (Stack st) (Denvalue env)" using 2(1) storageSame unfolding TypeSafe_def by simp
      show " compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
      proof(intros)
        fix tp1 tp2 l1 l22 l1' l2' stl1 stl2
        assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l22) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
     (l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l22 = Storeloc stl2)"
        have a2:"(\<forall>x y. x |\<in>| fmran (Denvalue env) \<and> y |\<in>| fmran (Denvalue env) \<and> snd x = snd y \<longrightarrow> x = y)"
          using  2(1) unfolding TypeSafe_def unique_locations_def by simp

        then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
        proof(cases "l1 = Storeloc stl1")
          case t1:True
          then show ?thesis 
          proof(cases "l22 = Storeloc stl2")
            case True
            then show ?thesis using t1 a0 a1 unfolding compPointers_def by blast
          next
            case False
            then have a4:"l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2)" using a1 by simp
            then show ?thesis 
            proof(cases "l2' = l")
              case True
              then have "stl2 = p" using a4 16 by simp
              then show ?thesis using pRelations a1 a0 t1  True a4 lDen by blast
            next
              case False
              then have " accessStore l2' (Stack st') =  accessStore l2' (Stack st)" using  stackChanged a4 by simp
              then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
            qed
          qed
        next
          case f1:False
          then have a4:"l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1)" using a1 by simp
          then show ?thesis 
          proof(cases "l22 = Storeloc stl2")
            case t1:True
            then show ?thesis
            proof(cases "l1' = l")
              case True
              then have "stl1 = p" using a4 16 by simp
              then show ?thesis using pRelations a1 a0 t1  True a4 lDen 
                by (metis CompStoType_sameLoc_sameType type.inject(4) typedStoSub_imps_negInv)
            next
              case False
              then have " accessStore l1' (Stack st') =  accessStore l1' (Stack st)" using  stackChanged a4 by simp
              then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
            qed
          next
            case False
            then have a4':"l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2)" using a1 by simp
            then show ?thesis 
            proof(cases "l1' = l")
              case True
              then have p1:"stl1 = p" using a4 16 by simp
              then have tp1c:"tp1 = (STMap t g')" using lDen a1 
                using True a4 by auto
              then show ?thesis 
              proof(cases "l2' = l")
                case True
                then have p2:"stl2 = p" using a4' 16 by auto
                then have tp2c:"tp2 = (STMap t g')" using lDen a1 True a4' by auto
                then show ?thesis using p2 p1 tp1c tp2c by auto
              next
                case False
                then have " accessStore l2' (Stack st') =  accessStore l2' (Stack st)" using  stackChanged a4 by simp
                then show ?thesis 
                  by (metis CompStoType_sameLoc_sameType a1 p1 pRelations tp1c typedStoSub_imps_negInv)
              qed
            next
              case False
              then have same1:" accessStore l1' (Stack st') =  accessStore l1' (Stack st)" using  stackChanged a4 by simp
              then show ?thesis 
              proof(cases "l2' = l")
                case True
                then have p2:"stl2 = p" using a4' 16 by auto
                then have tp2c:"tp2 = (STMap t g')" using lDen a1 True a4' by auto
                then show ?thesis using same1 pRelations p2 tp2c a1 
                  by metis
              next
                case False
                then have " accessStore l2' (Stack st') =  accessStore l2' (Stack st)" using  stackChanged a4 by simp
                then show ?thesis using a1 a0 same1 
                  using compPointers_def by auto
              qed
            qed 
          qed
        qed
      qed
    next
      show "svalueTypes (Svalue env)" using svalueTypes_def typeSafeSvalue 2(1) by simp
    next
      have "(Storage st') = (Storage st)" using 16(4) by simp
      then show "safeContract (Accounts st') (Storage st')" using 2(1) 16 unfolding safeContract_def TypeSafe_def  by auto
    next
      have a10:"Toploc (Stack st') = Toploc (Stack st)" using 16(4) unfolding updateStore_def by simp
      then have a20:"\<exists>val. accessStore l (Stack st) = Some val" using t'InDen typeSafeLocExists 2(1) TypeSafe_def by blast
      then have a30:"(\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                   \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))" 
        using 2(1) unfolding TypeSafe_def  lessThanTopLocs_def by simp
      then have a40:"(\<forall>tloc loc. Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                    \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))" 
        using a10 by simp
      show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume *:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then show "accessStore loc (Stack st') = None"
        proof(cases "loc = l")
          case True
          then show ?thesis using * a10 
            by (metis a20 a30 option.distinct(1)) 
        next
          case False
          then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 16(4) unfolding updateStore_def accessStore_def by simp
          then show ?thesis using 2(1) a40 * a10 False a30 by simp
        qed
      next 
        fix loc y 
        assume *:" accessStore loc (Stack st') = Some y "
        show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        proof(cases "loc = l")
          case True
          then show ?thesis using *a10 a20 a30 by simp
        next
          case False
          then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 16(4) unfolding updateStore_def accessStore_def by simp
          then show ?thesis using * 2(1) a40 by simp
        qed
      qed
    next
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def using 16 by auto
    next 
      show "lessThanTopLocs (Memory st')" using 2(1) unfolding TypeSafe_def using 16 by auto
    next 
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by auto
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next 
      show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 16 by simp
    next 
      have accSame:"Accounts st'= Accounts st" using 16 by auto
      from 2(3) obtain c_fi ct_fi dud_fi where fi:"
           Type (Accounts st (Address env)) = Some (atype.Contract c_fi) \<and>
           Contract env = c_fi \<and>
           ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
           (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id))) \<and>
           (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
           (\<forall>t0 l0 p0.
               (type.Storage t0, Stackloc l0) |\<in>| fmran (Denvalue env) \<and> accessStore l0 (Stack st) = Some (KStoptr p0) \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t0 l' p0))"
        unfolding fullyInitialised_def by blast
      have fiPtrs':"\<forall>t''' l''' p'''.
               (type.Storage t''', Stackloc l''') |\<in>| fmran (Denvalue env) \<and> accessStore l''' (Stack st') = Some (KStoptr p''') \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t''' l' p''')"
      proof (intro allI impI)
        fix t''' l''' p'''
        assume in1:"(type.Storage t''', Stackloc l''') |\<in>| fmran (Denvalue env)\<and>accessStore l''' (Stack st') = Some (KStoptr p''') "
        show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t''' l' p'''"
        proof(cases "l''' = l")
          case True
          then have "p''' = p" using 16 in1 unfolding accessStore_def updateStore_def by simp
          then show ?thesis using pOrigin 
            by (metis CompStoType_sameLocNdTyp True type.inject(4) in1 lDen extractValueType.simps(4))
        next
          case False
          then have "accessStore l''' (Stack st') = accessStore l''' (Stack st)" 
            using stackChanged by force
          then show ?thesis using fi in1 
            by presburger
        qed
      qed
      show "fullyInitialised env  (Accounts st') (Stack st')" 
        unfolding fullyInitialised_def using fi fiPtrs' accSame by metis
    next
      have cc0:"\<forall>l ptr_loc.  accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow>  accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using 16(4) unfolding updateStore_def accessStore_def by auto
      show "denvalueTypeCorrectness env (Stack st') (Memory st')" 

        unfolding denvalueTypeCorrectness_def  
      proof intros
        fix t l ptr_loc sub_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
       accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "(case t of
         MTArray len arr \<Rightarrow>
           (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
        moreover have "Memory st = Memory st'" using 16(4) by simp
        ultimately show "case t of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)" 
          by metis 
      qed
    next 
      show "subPrefixStructuralConsistency (Memory st')" using 2(1) unfolding TypeSafe_def  using 16(4) by simp
    next 
      show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def  using 16(4) by simp
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 2(1) unfolding TypeSafe_def  using 16(4) by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using 16(4) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using 16(4) by simp
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 16(4) by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 16(4) by simp
    qed
  qed 
next
  case (3 s1 s2 e cd st)
  show ?case
  proof(cases "state.Gas st > costs (COMP s1 s2) e cd st")
    case True  
    then have a5:"assert Gas (\<lambda>st. costs (COMP s1 s2) e cd st < state.Gas st) st = Normal ((), st)" by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    moreover have sStackSame:"Stack st = Stack sgas" using * by simp
    moreover have sgasSame:"Memory st = Memory sgas" using * by simp
    moreover have "Storage st = Storage sgas" using * by simp
    moreover have "Accounts st = Accounts sgas" using * by simp
    ultimately have a10:"TypeSafe e (Accounts sgas) (Stack sgas) (Memory sgas) (Storage sgas) cd" 
      using 3(3) TypeSafe_def True by simp
    then obtain sts1 where s1:"stmt s1 e cd sgas = Normal ((), sts1)" using 3 * stmt.simps(3) comp by meson
    have fi:"fullyInitialised e (Accounts sgas) (Stack sgas)" using 3(5) unfolding fullyInitialised_def using *  by simp
    then have cc0:"StateInvariant e sgas sts1 cd" using 3(1)[OF a5 a6 a10 s1]   by blast

    then have ts: "TypeSafe e (Accounts sts1) (Stack sts1) (Memory sts1) (Storage sts1) cd"
      using a10 3(1)[of "()" st "()" sgas sts1] a5 a6 * s1  unfolding StateInvariant_def by simp
    then have "stmt s2 e cd sts1 = Normal ((),st')" using 3(4) * s1 using comp by fastforce
    then have cc2:"StateInvariant e sts1 st' cd" using 3(2)[of "()" st "()" sgas "()" "sts1" st'] a5 a6 * s1 ts fi
      using atype_same by (metis cc0 StateInvariant_def)
    then have cc5:"TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd\<and>
  (\<forall>locs t. accessTypeStore locs (Memory sts1) = Some t \<longrightarrow> accessTypeStore locs (Memory st') = Some t)
\<and>(\<forall>i loc. i < Toploc (Memory sts1) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc (Memory sts1) = None \<longrightarrow> accessStore loc (Memory st') = None)"
      unfolding StateInvariant_def by blast
    have cc10:"fullyInitialised e (Accounts st') (Stack st')\<and>
  (\<forall>locs t. accessTypeStore locs (Memory sts1) = Some t \<longrightarrow> accessTypeStore locs (Memory st') = Some t)
\<and> (\<forall>i loc. i < Toploc (Memory sts1) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc (Memory sts1) = None \<longrightarrow> accessStore loc (Memory st') = None)" 
      using cc2 unfolding StateInvariant_def by blast
    then have cc12:"TypeSafe e (Accounts sts1) (Stack sts1) (Memory sts1) (Storage sts1) cd \<and>
    fullyInitialised e (Accounts sts1) (Stack sts1)\<and>
    (\<forall>locs t. accessTypeStore locs (Memory sgas) = Some t \<longrightarrow> accessTypeStore locs (Memory sts1) = Some t) \<and>
(\<forall>i loc. i < Toploc (Memory sgas) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc (Memory sgas) = None \<longrightarrow> accessStore loc (Memory sts1) = None)" 
      using cc0 unfolding StateInvariant_def by simp
    have cc15:"TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd \<and>
  fullyInitialised e (Accounts st') (Stack st') \<and>
  (\<forall>locs t. accessTypeStore locs (Memory sts1) = Some t \<longrightarrow> accessTypeStore locs (Memory st') = Some t)
\<and> (\<forall>i loc. i < Toploc (Memory sts1) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc (Memory sts1) = None \<longrightarrow> accessStore loc (Memory st') = None)" 
      using cc2 unfolding StateInvariant_def by blast
    have tlocs:"Toploc (Memory st) \<le> Toploc (Memory sts1) \<and>  Toploc (Memory sts1) \<le> Toploc (Memory st')" 
      using cc0 cc2 unfolding StateInvariant_def using sgasSame by simp
    then have "(\<forall>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) 
                \<longrightarrow> accessStore loc (Memory st) = None \<longrightarrow> accessStore loc (Memory st') = None)" 
      using sgasSame cc15 cc12 
      by (metis (no_types, lifting) dual_order.strict_trans1)
    then show ?thesis using cc5 cc10 cc15 cc12 unfolding StateInvariant_def 
      using sgasSame 
      using StateInvariant_def cc0 cc2 tlocs by auto
  next
    case False
    then have "assert Gas (\<lambda>st. costs (COMP s1 s2) e cd st < state.Gas st) st = Exception Gas" by simp
    then show ?thesis using 3(4) stmt.simps(3) by simp
  qed
next
  case (4 ex s1 s2 e cd st)
  then show ?case
  proof(cases "state.Gas st> costs (ITE ex s1 s2) e cd st")
    case True
    then have a5:"assert Gas (\<lambda>st. costs (ITE ex s1 s2) e cd st < state.Gas st) st = Normal ((), st)" by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (ITE ex s1 s2) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (ITE ex s1 s2) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    moreover have "Stack st = Stack sgas" using * by simp
    moreover have "Memory st = Memory sgas" using * by simp
    moreover have "Storage st = Storage sgas" using * by simp
    moreover have "Accounts st = Accounts sgas" using * by simp
    ultimately have a10:"TypeSafe e (Accounts sgas) (Stack sgas) (Memory sgas) (Storage sgas) cd" using 4(3) True by simp
    then consider (atrue) g where "expr ex e cd sgas (state.Gas sgas) = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool),g)"
      |(afalse) g where "expr ex e cd sgas (state.Gas sgas) = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool),g)" using * 4(4) stmt.simps(4) 
      by (simp split:if_split_asm result.split_asm prod.split_asm stackvalue.split_asm type.split_asm types.split_asm)
    then show ?thesis
    proof (cases)
      case atrue 
      then obtain g where a20:"expr ex e cd sgas (state.Gas sgas) = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool), g)" by simp
      then obtain s'' where a25:"s'' = sgas\<lparr>Gas:= g\<rparr>" by simp
      moreover have "Stack s'' = Stack sgas" using a25 by simp
      moreover have "Memory s'' = Memory sgas" using a25 by simp
      moreover have "Storage s'' = Storage sgas" using a25 by simp
      moreover have "Accounts s'' = Accounts sgas" using a25 by simp
      ultimately have "TypeSafe e (Accounts s'') (Stack s'') (Memory s'') (Storage s'') cd" using assms 4 True atrue a10 a25 by metis
      moreover have "stmt s1 e cd s'' = Normal((),st')" using * a20 stmt.simps(4) 4(4) a25 by (simp split:if_split_asm result.split_asm prod.split_asm)
      moreover have "fullyInitialised e (Accounts s'') (Stack s'')" using 4(5)  
        using \<open>Accounts s'' = Accounts sgas\<close> \<open>Accounts st = Accounts sgas\<close> 
        by (simp add: \<open>Stack s'' = Stack sgas\<close> \<open>Stack st = Stack sgas\<close>)
      ultimately have "StateInvariant e s'' st' cd" using 4(1)[of "()" st "()" sgas "(KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool)" s'' "(ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True)" s'' st'] a5 a6 a20 a25 
        unfolding StateInvariant_def by simp
      then show ?thesis unfolding StateInvariant_def 
        using \<open>Memory s'' = Memory sgas\<close> \<open>Memory st = Memory sgas\<close> by simp
    next
      case afalse
      then obtain g where a20:"expr ex e cd sgas (state.Gas sgas) = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool), g)" and 
        a21: "expr ex e cd sgas (state.Gas sgas) \<noteq> Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool), g)" by fastforce
      then obtain s'' where a25:"s'' = sgas\<lparr>Gas:= g\<rparr>" by simp
      moreover have "Stack s'' = Stack sgas" using a25 by simp
      moreover have "Memory s'' = Memory sgas" using a25 by simp
      moreover have "Storage s'' = Storage sgas" using a25 by simp
      moreover have "Accounts s'' = Accounts sgas" using a25 by simp
      ultimately have "TypeSafe e (Accounts s'') (Stack s'') (Memory s'') (Storage s'') cd" using assms 4 True afalse a10 a25 by metis
      moreover have "stmt s2 e cd s'' = Normal((),st')" using * a20 a21 stmt.simps(4)[of ex s1 s2 e cd st ] 4(4) a25 by (simp split:if_split_asm result.split_asm prod.split_asm)
      moreover have "fullyInitialised e (Accounts s'') (Stack s'')" using 4(5) unfolding fullyInitialised_def 
        using \<open>Accounts s'' = Accounts sgas\<close> \<open>Accounts st = Accounts sgas\<close> 
        by (simp add: \<open>Stack s'' = Stack sgas\<close> \<open>Stack st = Stack sgas\<close>)
      moreover have "StateInvariant e s'' st' cd" using 4(2)[of "()" st "()" sgas "(KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool)" s'' "(ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False)" s'' st'] 
          a5 a6 a20 a21 a25 calculation by auto
      ultimately show ?thesis 
        unfolding StateInvariant_def 
        using \<open>Memory s'' = Memory sgas\<close> \<open>Memory st = Memory sgas\<close> by auto
    qed
  next
    case False
    then show ?thesis using 4(4) stmt.simps(4) by simp
  qed
next
  case (5 ex s0 e cd st)
  show ?case 
  proof(cases rule:while[OF 5(4)])
    case (1 g st'')
    then have a5:"assert Gas (\<lambda>st. costs (WHILE ex s0) e cd st < state.Gas st) st = Normal ((), st)" by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (WHILE ex s0) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (WHILE ex s0) e cd st\<rparr>) st = Normal ((), sgas)" by simp

    then have a10:"toState (expr ex e cd) sgas
          = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool), (st\<lparr>Gas := g\<rparr>))" using 1 * by auto


    have a20:"TypeSafe e (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd"
      using 5(3) by simp
    have a25:"fullyInitialised e (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 5(5) unfolding fullyInitialised_def by simp
    then have a30:"StateInvariant e (st\<lparr>Gas := g\<rparr>) st'' cd"
      using 5(1)[OF a5 a6 a10 _ _ a20 1(3) ] unfolding StateInvariant_def by simp
    have cc0:"StateInvariant e st'' st' cd"
      using 5(2)[OF a5 a6 a10 _ _ 1(3)  _ 1(4)] a30 unfolding StateInvariant_def  by simp

    then have ts:"TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd \<and>
  fullyInitialised e (Accounts st') (Stack st')" using cc0 unfolding StateInvariant_def by blast
    have "Memory st = Memory (st\<lparr>Gas := g\<rparr>) \<and> Stack st = Stack (st\<lparr>Gas := g\<rparr>)" by simp
    then show ?thesis using ts a30 cc0 unfolding StateInvariant_def by fastforce
  next
    case (2 g)
    then have "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd " 
      by (simp add: "5.prems"(1))
    moreover have "fullyInitialised e (Accounts st') (Stack st')" using 2 
      using "5.prems"(2,3) atype_same fullyInitialised_def by simp
    moreover have "Memory st = Memory st' \<and> Stack st = Stack st'" using 2 by simp
    ultimately show ?thesis unfolding StateInvariant_def by simp
  qed
next
  case (6 i xe e cd st)
  show ?case 
  proof(cases rule:invoke[OF 6(3)])
    case (1 ct fb fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st'')
    then have a5:"assert Gas (\<lambda>st. costs (INVOKE i xe) e cd st < state.Gas st) st = Normal ((), st)" by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    have a10:"option Err (\<lambda>_. ep $$ Contract e) sgas = Normal ((ct, fb), sgas)" using 1(2) by simp
    then have a20:"(case ct $$ i of None \<Rightarrow> throw Err | Some (Method (fp, True, f)) \<Rightarrow> throw Err
     | Some (Method (fp, False, f)) \<Rightarrow> return (fp, f) | Some _ \<Rightarrow> throw Err)
     sgas =  Normal ((fp, f), sgas)" using 1 by auto

   
    have memSGas:"Memory sgas = Memory st" using * by auto
    have a25:"applyf Memory sgas = Normal ((Memory sgas), sgas)" by auto

    obtain x where xDef:"x = ffold_init ct (emptyEnv (Address e) (Contract e) (Sender e) (Svalue e)) (fmdom ct)" by simp

    have tsX:"TypeSafe x (Accounts sgas) emptyStore (Memory sgas) (Storage sgas) emptyTypedStore"  
      using ffoldInitTypeSafe[of "(Accounts sgas)" "(Storage sgas)" "Svalue e" "(Memory sgas)" _ ct fb "Address e" _ _]
      using * 6(2) "6.prems"(3) unfolding TypeSafe_def fullyInitialised_def using 1(2) xDef ffold_init_def by auto
    have cx:"Contract x = Contract e" using xDef by simp
    then have a27:"load False fp xe x emptyTypedStore emptyStore (Memory sgas) e cd (sgas) (state.Gas st - costs (INVOKE i xe) e cd st) =
    Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)" using 1(4) * xDef unfolding ffold_init_def  by simp
    then have a30:"toState (load False fp xe x emptyTypedStore emptyStore (Memory sgas) e cd) sgas =
  Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), sgas\<lparr>Gas := g\<rparr>) " using * 1(5) by auto
    have sameADD:"Address e = Address x" 
      by (simp add: xDef)
    have link:"TypeSafe e\<^sub>l (Accounts sgas) k\<^sub>l m\<^sub>l (Storage sgas) cd\<^sub>l \<and>
    fullyInitialised e\<^sub>l (Accounts sgas) k\<^sub>l \<and>
    (\<not> False \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory sgas) locs \<longrightarrow> MCon tp m\<^sub>l locs) \<and>
     Toploc (Memory sgas) \<le> Toploc m\<^sub>l \<and>
     ncpDenvalueLimit e\<^sub>l e k\<^sub>l (Stack sgas) (Memory sgas) \<and>
     ncpOMemInDMem (Memory sgas) m\<^sub>l \<and> ncpElementsNoSubPref (Memory sgas) m\<^sub>l \<and> ncpNewSelfPoint (Memory sgas) m\<^sub>l)"
    proof - 
      have "(\<forall>locs tp. MCon tp (Memory sgas) locs \<longrightarrow> MCon tp (Memory sgas) locs)" by blast
      moreover have "Toploc (Memory sgas) \<le> Toploc (Memory sgas)" by simp
      moreover have "ncpDenvalueLimit x e emptyStore (Stack sgas) (Memory sgas)" unfolding ncpDenvalueLimit_def accessStore_def emptyStore_def by simp
      moreover have "ncpOMemInDMem (Memory sgas) (Memory sgas)" unfolding ncpOMemInDMem_def by blast
      moreover have "ncpElementsNoSubPref (Memory sgas) (Memory sgas)" using ncpElementsNoSubPref_sameMem 6(2) * by auto
      moreover have "ncpNewSelfPoint (Memory sgas) (Memory sgas)" unfolding ncpNewSelfPoint_def by auto
      moreover have "TypeSafe x (Accounts sgas) emptyStore (Memory sgas) (Storage sgas) emptyTypedStore"  
        using ffoldInitTypeSafe[of "(Accounts sgas)" "(Storage sgas)" "Svalue e" "(Memory sgas)" e ct fb "Address e" _ _]
        using * 6(2) "6.prems"(3) unfolding TypeSafe_def fullyInitialised_def using 1(2) xDef ffold_init_def by auto
      moreover have fiE:"fullyInitialised e (Accounts sgas) (Stack sgas)" 
        by (simp add: "*" "6.prems"(3))
      moreover have "fullyInitialised x (Accounts sgas) emptyStore" 
      proof -
        have addX:"Address x = Address e" by (simp add: xDef)
        have typeX:"Type (Accounts sgas (Address x)) = Some (atype.Contract (Contract x))"
          using fiE addX cx unfolding fullyInitialised_def by force
        have epX:"ep $$ Contract x = Some (ct, fb)" using "1"(2) cx by simp
        have mapX:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue x $$ id = Some (type.Storage v, Storeloc id))"
          using xDef unfolding ffold_init_def
          using ffoldInit_var_storage_mapping_eq[of ct "Address e" "Contract e" "Sender e" "Svalue e" x]
          by blast
        have locX:"\<forall>id v loc. Denvalue x $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
        proof (intro allI impI)
          fix id v loc
          assume hx:"Denvalue x $$ id = Some (type.Storage v, Storeloc loc)"
          have "(Denvalue x $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id)"
            using xDef unfolding ffold_init_def
            using ffoldInitAllLocsStorage[
              of ct "e" "e" "e" "Svalue e" "fmdom ct"
            ] by simp
          then show "id = loc" using hx by simp
        qed
        have ptrX:"\<forall>t l p.
            (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue x) \<and> accessStore l emptyStore = Some (KStoptr p) \<longrightarrow>
            (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue x) \<and> CompStoType t' t l' p)"
          by (simp add: accessStore_def emptyStore_def)
        show ?thesis
          unfolding fullyInitialised_def using typeX epX mapX locX ptrX by blast
      qed
      ultimately show ?thesis using exprTypeconInduct(4)[of False fp xe x emptyTypedStore emptyStore "Memory sgas" e cd "sgas" "(state.Gas st - costs (INVOKE i xe) e cd st)"
            e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g] a27 6(2) * sameADD by auto
    qed
    then have a40:" TypeSafe e\<^sub>l (Accounts (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
     (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Storage (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) cd\<^sub>l" using * by auto

    have typeMstML:"\<forall>locs t. accessTypeStore locs (Memory st) = Some t \<longrightarrow> accessTypeStore locs (m\<^sub>l) = Some t "
    proof intros
      fix locs t 
      assume in1:"accessTypeStore locs (Memory st) = Some t"
      then have "\<exists>v. accessStore locs (Memory st) = Some v" using 6(2) unfolding TypeSafe_def SomeValSomeTyp_def by auto
      then have "\<exists>i. i < Toploc (Memory sgas) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)" 
        using 6(2) unfolding TypeSafe_def lessThanTopLocs_def using memSGas by presburger
      then have "accessTypeStore locs (Memory sgas) = accessTypeStore locs m\<^sub>l"
        using link unfolding ncpOMemInDMem_def by blast
      then show "accessTypeStore locs m\<^sub>l = Some t" using in1 memSGas by auto
    qed


    have a44:"(Address e\<^sub>l) = (Address e)" using xDef a27 
      using emptyEnv_address ffold_init_ad ffold_init_def msel_ssel_expr_load_rexp_gas(4) by presburger
    moreover have a45:"Contract e\<^sub>l = Contract e" using xDef a27  
      using emptyEnv_members ffold_init_contract ffold_init_def msel_ssel_expr_load_rexp_gas(4) by presburger
    ultimately have cc1:"(\<exists>c. Type (Accounts (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address e\<^sub>l)) = Some (atype.Contract c) \<and> Contract e\<^sub>l = c)" 
      using 6(4) unfolding fullyInitialised_def by simp

    have a60:"\<forall>id x'. Denvalue x $$ id = Some x' \<longrightarrow> Denvalue e\<^sub>l $$ id = Some x'" 
      using load_denval_existing_remain(4)[of False fp xe x emptyTypedStore emptyStore "(Memory sgas)" e cd sgas "(state.Gas st - costs (INVOKE i xe) e cd st)" e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g] a27 by blast

    

    have cc3:"(\<forall>t l p.
        (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<longrightarrow>
        accessStore l (Stack (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some (KStoptr p) \<longrightarrow>
        (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p))" 
      using fullyInitialised_def link by auto

    have a50:" fullyInitialised e\<^sub>l (Accounts (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))" using 6(4)
        cc1 fullyInitialised_def link by auto
    have cc10:"applyf Stack (sgas\<lparr>Gas := g\<rparr>) = Normal ((Stack st), sgas\<lparr>Gas := g\<rparr>)" using * by simp
    have IH1:"TypeSafe e\<^sub>l (Accounts st'') (Stack st'') (Memory st'') (Storage st'') cd\<^sub>l \<and> fullyInitialised e\<^sub>l (Accounts st'') (Stack st'')
                \<and>
    (\<forall>locs t. accessTypeStore locs (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some t \<longrightarrow> accessTypeStore locs (Memory st'') = Some t) \<and>
(\<forall>locs v. accessStore locs (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some (MPointer v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st'') = Some (MPointer v'))) \<and>
    (\<forall>locs v. accessStore locs (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some (MValue v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st'') = Some (MValue v'))) \<and>
(\<forall>i loc.
        i < Toploc (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
        accessStore loc (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = None \<longrightarrow> accessStore loc (Memory st'') = None) \<and>
Toploc (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) \<le> Toploc (Memory st'')"
      using 6(1)[OF a5 a6 a10 _ a20 _ xDef a25 a30 _ _ _ cc10 _ a40 1(5) a50]  * unfolding StateInvariant_def by simp
    have cc20:"(Memory st') = (Memory st'') \<and> (Accounts st'') = (Accounts st') \<and> (Storage st'') = (Storage st')" using 1(6) by simp
    have stackOver:"(Stack st') = (Stack st)" using 1(6) by auto

   

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros
      show " AddressTypes (Accounts st')" using IH1 cc20 unfolding TypeSafe_def by auto
    next 
      show "safeContract (Accounts st') (Storage st')" using IH1 cc20 unfolding TypeSafe_def by auto
    next 
      show "unique_locations (Denvalue e)" using 6(2) unfolding TypeSafe_def  by blast
    next 
      show "compPointers (Stack st') (Denvalue e)" using 6(2) unfolding TypeSafe_def using cc20 
        using stackOver by argo
    next 
      show "balanceTypes (Accounts st')" using IH1 cc20 unfolding TypeSafe_def by auto
    next 
      have "envAddressesWellFormed e" using 6(2) unfolding TypeSafe_def by blast
      then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
    next 
      show "svalueTypes (Svalue e)" using 6(2) unfolding TypeSafe_def  by blast
    next 
      show "lessThanTopLocs (Stack st')" using 6(2) 1(6) unfolding TypeSafe_def by simp 
    next 
      show "lessThanTopLocs cd" using 6(2) unfolding TypeSafe_def  by blast
    next 
      show "lessThanTopLocs (Memory st')"  using IH1 cc20 unfolding TypeSafe_def by auto
    next 
      show " typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd"
        unfolding typeCompat_def
      proof intros
        fix tIn lIn
        assume in1:"(tIn, lIn) |\<in>| fmran (Denvalue e)"
        show "case lIn of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case tIn of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case tIn of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case tIn of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case tIn of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case tIn of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address e)) | _ \<Rightarrow> False)"
        proof (split denvalue.split, intros)
          fix x1 assume stackLoc:"lIn = Stackloc x1"
          show "case accessStore x1 (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case tIn of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case tIn of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case tIn of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case tIn of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False)" 
          proof (split option.split,  intros)
            assume "accessStore x1 (Stack st') = None"
            then show False using 6(2) unfolding TypeSafe_def  typeCompat_def using stackOver in1  
              by (metis "6.prems"(1) option.discI stackLoc typeSafeAllStacklocsExist)
          next
            fix x2 assume Some:"accessStore x1 (Stack st') = Some x2"
            then have SomeOld:"accessStore x1 (Stack st) = Some x2" using stackOver by simp
            show "case x2 of KValue val \<Rightarrow> (case tIn of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False) 
          | KCDptr stloc \<Rightarrow> (case tIn of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
          | KMemptr stloc \<Rightarrow> (case tIn of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
          | KStoptr stloc \<Rightarrow> (case tIn of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False)" 
            proof(split stackvalue.split, intros)
              fix x1 assume KValue:"x2 = KValue x1"
              then show "case tIn of Value typ \<Rightarrow> typeCon typ x1 | _ \<Rightarrow> False" 
                using 6(2) unfolding TypeSafe_def  typeCompat_def using stackLoc stackOver in1 Some SomeOld by force
            next 
              fix x2a assume KCDPtr:"x2 = KCDptr x2a"
              then show "case tIn of Calldata struct \<Rightarrow> MCon struct cd x2a | _ \<Rightarrow> False" 
                using 6(2) unfolding TypeSafe_def  typeCompat_def using stackLoc stackOver in1 Some SomeOld by force
            next 
              fix x3 assume KMemPtr:"x2 = KMemptr x3"
              then obtain struct where structDef:"tIn = type.Memory struct" using 6(2) unfolding TypeSafe_def typeCompat_def using in1 stackOver Some stackLoc by (cases tIn; fastforce) 
              then have McOld:"MCon struct (Memory st) x3" using 6(2) unfolding TypeSafe_def typeCompat_def using in1 stackOver Some stackLoc KMemPtr by (cases tIn; fastforce)
              then have "\<exists>x i. accessStore x3 (Memory st) = Some x \<or> accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using  MCon_imps_Some by blast
              moreover have "lessThanTopLocs (Memory st)"using 6(2) unfolding TypeSafe_def by auto
              ultimately obtain tloc where tlocDef: "(tloc<Toploc (Memory st) \<and> LSubPrefL2 x3 (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))"  
                by (meson lessThanTopLocs_def MemLSubPrefL2_specific_imps_general)

              have "(\<forall>locs tp.
      accessTypeStore locs (Memory st) = Some tp \<longrightarrow>
      (case accessStore locs (Memory st) of None \<Rightarrow> False
       | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st) p \<and> tp = MTArray len arr 
\<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)))" 
                using 6(2) unfolding TypeSafe_def subPrefixStructuralConsistency_def using McOld by auto
              have IH1Link:"(\<forall>locs tp.
       accessTypeStore locs (Memory st') = Some tp \<longrightarrow>
       (case accessStore locs (Memory st') of None \<Rightarrow> False
        | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
        | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st') p \<and> tp = MTArray len arr 
\<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)))" 
                using IH1 cc20 unfolding TypeSafe_def subPrefixStructuralConsistency_def by presburger
              have mlFinalLink:"(\<forall>locs t. accessTypeStore locs (m\<^sub>l) = Some t \<longrightarrow> accessTypeStore locs (Memory st') = Some t)"
                using IH1 cc20 by simp
              have linkS:"(\<forall>i loc. i < Toploc (Memory sgas) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> 
                      accessStore loc (Memory sgas) = accessStore loc m\<^sub>l 
                    \<and> accessTypeStore loc (Memory sgas) = accessTypeStore loc m\<^sub>l)" 
                using link unfolding ncpOMemInDMem_def by blast
              then have oldLoadedLink:"accessStore x3 (Memory st) = accessStore x3 m\<^sub>l 
                    \<and> accessTypeStore x3 (Memory st) = accessTypeStore x3 m\<^sub>l" using tlocDef memSGas by simp
              have SameVAccess:"(\<forall>locs v. accessStore locs (m\<^sub>l) = Some (MPointer v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st') = Some (MPointer v'))) \<and>
  (\<forall>locs v. accessStore locs ((m\<^sub>l)) = Some (MValue v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st') = Some (MValue v')))" using IH1 cc20 by auto
              have "MCon struct (Memory st') x3 " 
              proof(cases struct)
                case (MTArray x11 x12)
                then have accTypesOld:"\<forall>i<x11. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12"
                  using 6(2) unfolding TypeSafe_def denvalueTypeCorrectness_def 
                  using in1 Some stackOver KMemPtr structDef stackLoc by fastforce
                then have oldVals:"(\<forall>i<x11.
                                 case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) of None \<Rightarrow> False
                                   | Some (MValue val) \<Rightarrow> case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))
                                   | Some (MPointer loc2) \<Rightarrow> case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st) loc2 | MTValue val \<Rightarrow> False) \<and>
                                   (\<exists>p. accessStore x3 (Memory st) = Some (MPointer p) \<or> accessStore x3 (Memory st) = None)" 
                  using McOld MCon.simps(2)[of x11 x12 "Memory st" x3] MTArray by simp
                have "\<forall>i<x11. case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                             | Some (MValue val) \<Rightarrow> case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))
                             | Some (MPointer loc2) \<Rightarrow> case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st') loc2 | MTValue val \<Rightarrow> False" 
                proof intros
                  fix i 
                  assume in1:"i<x11"

                  then consider (ptr) p x11' x12' where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer p)
                                                  \<and> x12 = MTArray x11' x12'"
                    | (val) v vt where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue v)
                                    \<and> x12 = MTValue vt" using oldVals 
                    by (metis MCon.simps(2) MTArray McOld mcon_accessStore)
                  then show "case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                        | Some (MValue val) \<Rightarrow> case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))
                        | Some (MPointer loc2) \<Rightarrow> case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st') loc2 | MTValue val \<Rightarrow> False "
                  proof(cases)
                    case ptr
                    then obtain t where accNew:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer t)" 
                      using linkS tlocDef memSGas SameVAccess 
                      by (metis LSubPrefL2_def Not_Sub_More_Specific)
                    have "accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MTArray x11' x12')"
                      using accTypesOld ptr in1 by simp
                    then have "accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MTArray x11' x12')" 
                      using mlFinalLink linkS tlocDef memSGas Not_Sub_More_Specific LSubPrefL2_def by metis
                    then have "MCon (MTArray x11' x12') (Memory st') t" using IH1Link accNew by fastforce
                    then show ?thesis using accNew ptr MTArray by simp
                  next
                    case val
                    then have accNew:"\<exists>t. accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MValue t)" 
                      using linkS tlocDef memSGas SameVAccess 
                      by (metis LSubPrefL2_def Not_Sub_More_Specific)
                    have "accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MTValue vt)"
                      using accTypesOld val in1 by simp
                    then have "accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MTValue vt)" 
                      using mlFinalLink linkS tlocDef memSGas Not_Sub_More_Specific LSubPrefL2_def by metis
                    then have "MCon (MTValue vt) (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using IH1Link accNew by fastforce
                    then show ?thesis using MTArray accNew val by auto
                  qed

                qed
                moreover have "(\<exists>p. accessStore x3 (Memory st') = Some (MPointer p) \<or> accessStore x3 (Memory st') = None)" 
                proof -
                  have "\<forall>i loc. i < Toploc m\<^sub>l \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> 
                      accessStore loc m\<^sub>l = None \<longrightarrow> accessStore loc (Memory st') = None" using IH1 cc20 by auto
                  then show ?thesis using oldVals oldLoadedLink SameVAccess tlocDef
                    by (metis dual_order.strict_trans1 link memSGas)
                qed
                ultimately show ?thesis using MTArray McOld by auto
              next
                case (MTValue x2'')
                then have "(case accessStore x3 (Memory st) of None \<Rightarrow> False | Some (MValue t) \<Rightarrow> typeCon x2'' t | Some (MPointer t) \<Rightarrow> False)"
                  using McOld by simp
                then obtain t where accOld:"accessStore x3 (Memory st) = Some (MValue t)" by (auto split:option.splits memoryvalue.splits)
                then have accNew:"\<exists>t. accessStore x3 (Memory st') = Some (MValue t)" using oldLoadedLink SameVAccess by auto
                have "accessTypeStore x3 (Memory st) = Some (MTValue x2'')"
                  using 6(2) unfolding TypeSafe_def denvalueTypeCorrectness_def using in1 Some stackOver KMemPtr structDef MTValue 
                  using stackLoc by force
                then have "accessTypeStore x3 (Memory st') = Some (MTValue x2'')" using mlFinalLink oldLoadedLink by auto
                then have "MCon (MTValue x2'') (Memory st') x3" using IH1Link accNew by force
                then show ?thesis using MTValue by simp
              qed


              then show "case tIn of type.Memory struct \<Rightarrow> MCon struct (Memory st') x3 | _ \<Rightarrow> False" using structDef by simp
            next 
              fix x4 assume KStoPtr:"x2 = KStoptr x4"

              then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                using Some 1 by auto
              then obtain struct where structDef: "tIn = type.Storage struct" 
                using 6(2) unfolding TypeSafe_def typeCompat_def using Some KStoPtr stackLoc in1 Some SomeOld
                by (cases tIn, force,  fastforce, fastforce, auto)
              obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)" 
                using 6(4) using accO in1 unfolding fullyInitialised_def 
                using stackLoc structDef by blast

              then have "SCon tprnt lprnt (Storage st'' (Address e))"
                using IH1 unfolding StateInvariant_def TypeSafe_def safeContract_def 
                using accessStore_def accessStore_updateStore cx a44 a45 
                by (metis (mono_tags, lifting) "6.prems"(3) fi_denvalue_storeloc_to_contract_var fullyInitialised_def)
                
              then have "SCon struct x4 (Storage st'' (Address e))"
                using tprntDef SCon_imps_sublocs by blast
              then show "case tIn of type.Storage struct \<Rightarrow> SCon struct x4 (Storage st' (Address e)) | _ \<Rightarrow> False " 
                using IH1 cc20 stackLoc stackOver in1 Some SomeOld structDef by simp
            qed
          qed
        next 
          fix x2 assume storeLoc:"lIn = Storeloc x2"
          then obtain struct where structDef: "tIn = type.Storage struct" 
            using 6(2) unfolding TypeSafe_def typeCompat_def using in1 
            by (cases tIn, force,  fastforce, fastforce, auto)
          obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x2)" 
            using 6(4) using  in1 unfolding fullyInitialised_def 
            using structDef 
            using CompStoType_sameLocNdTyp storeLoc by auto

          then have "SCon tprnt lprnt (Storage st'' (Address e))"
            using IH1 unfolding StateInvariant_def TypeSafe_def safeContract_def 
            using accessStore_def accessStore_updateStore cx a44 a45 
            by (smt (verit) "6.prems"(3) fmlookup_ran_iff fullyInitialised_def)
            

          then have "SCon struct x2 (Storage st'' (Address e))"
            using tprntDef SCon_imps_sublocs by blast
          then show "case tIn of type.Storage struct \<Rightarrow> SCon struct x2 (Storage st' (Address e)) | _ \<Rightarrow> False " 
            using IH1 cc20 storeLoc stackOver in1 structDef by simp
        qed
      qed    
    next
      show "fullyInitialised e (Accounts st') (Stack st') " using 6(4) 1(6) cc20 unfolding fullyInitialised_def 
        using IH1 \<open>Address e\<^sub>l = Address e\<close> a45 fullyInitialised_def by auto
    next
      show "denvalueTypeCorrectness e (Stack st') (Memory st')" unfolding denvalueTypeCorrectness_def
      proof intros
        fix t l ptr_loc sub_loc
        assume in1:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "accessStore l (Stack st) = Some (KMemptr ptr_loc)" using 1 by simp

        have "(\<forall>tp' locs p i.
       (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore locs k\<^sub>l = Some (KMemptr p) \<and> i < Toploc (Memory sgas) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
       (\<exists>tp'' loc2 p'.
           (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue e) \<and>
           accessStore loc2 (Stack sgas) = Some (KMemptr p') \<and>
           (p' = p \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory sgas) len arr tp' p' p))))" 
          using link unfolding ncpDenvalueLimit_def by blast
        have "(\<forall>t l ptr_loc sub_loc.
       (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore l (Stack st'') = Some (KMemptr ptr_loc) \<longrightarrow>
       (case t of
        MTArray len arr \<Rightarrow>
          (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st'') = Some arr)
        | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st'') = Some (MTValue val)))" 
          using IH1 unfolding TypeSafe_def denvalueTypeCorrectness_def by blast
        have "(case t of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))" 
          using 6(2) in1 1 unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
        then show "case t of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          using IH1 memSGas typeMstML cc20 by (cases t; simp)
      qed
    next
      show "SomeValSomeTyp (Memory st')" 
        using IH1 TypeSafe_def cc20 by auto
    next
      show "subPrefixStructuralConsistency (Memory st')" using IH1 TypeSafe_def cc20 by simp
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t "
        using IH1 cc20 typeMstML memSGas by auto
    next 
      fix locs v 
      assume in1:"accessStore locs (Memory st) = Some (MPointer v)"
      then have "\<exists>i. i < Toploc (Memory sgas) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)" 
        using memSGas 6(2) unfolding TypeSafe_def lessThanTopLocs_def by auto
      then have "accessStore locs (m\<^sub>l) = Some (MPointer v)" 
        using in1 link memSGas unfolding ncpOMemInDMem_def by auto
      then show " \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')" 
        using IH1 cc20 by simp 
    next  
      fix locs v 
      assume in1:"accessStore locs (Memory st) = Some (MValue v)"
      then have "\<exists>i. i < Toploc (Memory sgas) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)" 
        using memSGas 6(2) unfolding TypeSafe_def lessThanTopLocs_def by auto
      then have "accessStore locs (m\<^sub>l) = Some (MValue v)" 
        using in1 link memSGas unfolding ncpOMemInDMem_def by auto
      then show " \<exists>v'. accessStore locs (Memory st') = Some (MValue v')" 
        using IH1 cc20 by simp
    next 
      fix i loc
      assume in1:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        and in2:"accessStore loc (Memory st) = None"
      then have "accessStore loc (m\<^sub>l) = None" 
        using in1 link memSGas unfolding ncpOMemInDMem_def by auto
      moreover have "i < Toploc (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using in1 link memSGas by simp
      ultimately show "accessStore loc (Memory st') = None"
        using IH1 cc20 by auto
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using memSGas link IH1 cc20 by simp
    qed
  qed
next
  case (7 ad i xe val e cd st)
  show ?case
  proof(cases rule:external[OF 7(4)])
    case (1 adv c g ct cn fb' v t g' v' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc st'')
    then obtain cc where ccDef: "c = Contract cc" 
      by (metis Environment.select_convs(2))

    then have a5:"assert Gas (\<lambda>st. costs (EXTERNAL ad i xe val) e cd st < state.Gas st) st =  Normal ((), st)" using 1 by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    obtain expGas where a10:" toState (local.expr ad e cd) sgas = Normal ((KValue adv, Value TAddr), expGas)" using 1(2) a6 * by simp
    then have a20:"(case (KValue adv, Value TAddr) of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err 
                    | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) expGas =
    Normal (adv, expGas)" by simp
    then obtain vd where a30:"assert Err (\<lambda>_. adv \<noteq> Address e) expGas = Normal (vd, expGas)" using 1 by simp
    then have a40:"(case Type (Accounts expGas adv) of None \<Rightarrow> throw Err expGas 
                | Some EOA \<Rightarrow> throw Err expGas 
                | Some (atype.Contract c) \<Rightarrow> return c expGas) = Normal (c, expGas)" using 1 a10 * by auto
    then have a50:"option Err (\<lambda>_. ep $$ c) expGas = Normal ((ct, cn, fb'), expGas)" using 1 by simp
    then have a60:"toState (local.expr val e cd) expGas = Normal ((KValue v, Value t), expGas\<lparr>Gas := g'\<rparr>)" using 1 a10 * by auto
    then have a70:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) 
                    | (KValue v, _) \<Rightarrow> throw Err 
                    | (_, b) \<Rightarrow> throw Err) (expGas\<lparr>Gas := g'\<rparr>) = Normal ((v,t), expGas\<lparr>Gas := g'\<rparr>)" using 1 a10 * by simp
    then have a80:"option Err (\<lambda>_. convert t (TUInt b256) v) (expGas\<lparr>Gas := g'\<rparr>) = Normal (v', expGas\<lparr>Gas := g'\<rparr>)" using 1 by simp
    then obtain loaded where a90:"loaded = ffold_init ct (emptyEnv adv c (Address e) v') (fmdom ct)" using 1(9) by blast
    then have a100:"toState (local.load True fp xe loaded emptyTypedStore emptyStore emptyTypedStore e cd) (expGas\<lparr>Gas := g'\<rparr>) = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), expGas\<lparr>Gas := g''\<rparr>)"
      using 1 * a10 by auto
    then have a110:"option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) (expGas\<lparr>Gas := g''\<rparr>) = Normal (acc, expGas\<lparr>Gas := g''\<rparr>)" 
      using 1 * a10 by auto
    then have a120:"modify (\<lambda>st. st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (expGas\<lparr>Gas := g''\<rparr>) = Normal ((), (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))" 
      using 1 * a10 by auto

    have contractLoaded:"Contract e\<^sub>l = c" using a90 a100 
      using "1"(9) emptyEnv_members ffold_init_contract msel_ssel_expr_load_rexp_gas(4) by presburger
    have addressLoaded: "Address e\<^sub>l = Address loaded" using a90 a100 
      using "1"(9) ffold_init_def msel_ssel_expr_load_rexp_gas(4) by presburger

    have tsInitAcc:"\<forall>x y. TypeSafe loaded acc emptyStore emptyTypedStore (Storage st) emptyTypedStore \<and>
       (Denvalue loaded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue loaded $$ x = Some y \<longrightarrow> (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"  
    proof - 
      have sc:"safeContract acc (Storage st)"
        using 7(3) 1(10) transfer_type_same unfolding TypeSafe_def safeContract_def by fastforce
      have svv':"svalueTypes v'" unfolding svalueTypes_def
        using 1(6,7) 7(3) 7(5) 
        using exprTypeconInduct(3)[of val e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
          typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto
      have bt:"balanceTypes acc" using 1(10) unfolding balanceTypes_def
      proof - 
        have old:"balanceTypes (Accounts (st\<lparr>Gas := g''\<rparr>))" using 7(3) unfolding TypeSafe_def by simp
        have accExp:"(case subBalance (Address e) v' (Accounts (st\<lparr>Gas := g''\<rparr>)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance adv v' x) = Some acc" 
          using 1(10) unfolding transfer_def by blast
        have v'TC: "typeCon (TUInt b256) v'" 
          using  svv' unfolding svalueTypes_def by blast

        show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
        proof
          fix adv'
          show "typeCon (TUInt b256) (Bal (acc adv')) "
          proof(cases "adv' = (Address e)")
            case True
            then have ns:"adv' \<noteq> adv" using 1 by blast
            then have tco:"typeCon (TUInt b256) (Bal ((Accounts (st\<lparr>Gas := g''\<rparr>)) adv'))"
              using True old accExp balanceTypes_def by blast
            have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g''\<rparr>) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))" 
              using transfer_subRead[OF 1(10) _ v'TC ] True ns tco by auto
            then show ?thesis using True 
              by (smt (verit, best) "1"(10,3) checkUInt_def typeCon.simps(2) tco transfer_add transfer_mono transfer_sub transfer_val3)
          next
            case False
            then show ?thesis 
            proof(cases "adv' = adv")
              case True
              then have "typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g''\<rparr>) adv))"
                using True old accExp balanceTypes_def by simp
              then have "Bal (acc adv) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g''\<rparr>) adv))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))" 
                using transfer_addRead[OF 1(10)_ v'TC  ] 1(3) by blast
              then show ?thesis using True 
                using "1"(10,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g''\<rparr>) adv))\<close> checkUInt_def transfer_val1 transfer_val2 by auto
            next
              case f2:False
              then show ?thesis using False transfer_eq[OF 1(10)] old 
                using balanceTypes_def by force
            qed
          qed
        qed
      qed

      have ltp:"lessThanTopLocs emptyTypedStore" using typedEmptyTopLocs by simp
      have tp:"ep $$ Contract cc = Some (ct, cn, fb')" using ccDef 1(5) by simp
      have af1:"addressFormat adv" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by (simp split:option.splits atype.splits)
      have af2:"addressFormat (Address e)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      have af3:"AddressTypes acc" using 1(10) transfer_type_same 7(3) unfolding TypeSafe_def unfolding AddressTypes_def by simp
      have tcAdvAcc:"Type (acc adv) = Some (atype.Contract (Contract cc))"
        using 1(10) a10 * a40 ccDef transfer_type_same by (auto split:option.splits atype.splits result.splits)
      have svt:"SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessStore_def accessTypeStore_def emptyTypedStore_def by auto
      have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      then have " ffold (init ct) (emptyEnv adv (Contract cc) (Address e) v') (fmdom ct) = loaded" using a90 unfolding ffold_init_def using ccDef by simp
      then show ?thesis
        using  ffoldInitTypeSafe[OF sc bt svv' ltp tp af1 af2 af3 sp svt tcAdvAcc,of "(fmdom ct)"]  by simp
    qed

    have tsInit:"\<forall>x y. TypeSafe loaded (Accounts st) emptyStore emptyTypedStore (Storage st) emptyTypedStore \<and>
       (Denvalue loaded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue loaded $$ x = Some y \<longrightarrow> (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
    proof - 
      have "safeContract (Accounts st) (Storage st)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      moreover have svv':"svalueTypes v'" unfolding svalueTypes_def
        using 1(6,7) 7(3) 7(5)
        using exprTypeconInduct(3)[of val e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
          typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto
      moreover have "balanceTypes (Accounts st)" using 7(3) unfolding TypeSafe_def by simp      
      moreover have "lessThanTopLocs emptyStore" using emptyTopLocs by simp
      moreover have "ep $$ Contract cc = Some (ct, cn, fb')" using ccDef 1(5) by simp
      moreover have "addressFormat adv" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by (simp split:option.splits atype.splits)
      moreover have "addressFormat (Sender e)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      moreover have "AddressTypes (Accounts st)" using 7(3) unfolding TypeSafe_def by simp  
      moreover have "SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessTypeStore_def accessStore_def emptyTypedStore_def by simp
      moreover have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      moreover have "Type (acc adv) = Some (atype.Contract (Contract cc))"
        using 1(10) a10 * a40 ccDef transfer_type_same by (auto split:option.splits atype.splits result.splits)

      ultimately show ?thesis 
        using a90 ccDef unfolding ffold_init_def 
        using ffoldInitTypeSafe[of acc "Storage st" v' emptyTypedStore cc ct "(cn,fb')" adv _ " (fmdom ct)"]  
        using TypeSafe_def tsInitAcc by presburger
    qed

    have contractL:"Contract loaded = c" using a90 by simp
    have addressL:"Address loaded = adv" using a90 by simp
    have fi1:"(\<exists>c. Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)" using contractL addressL 1 a10 * a40 by simp
    have "\<exists>dud. ep $$ Contract loaded = Some (ct, dud)" using a50 contractL 1 a10 * by blast
    moreover have "\<forall>id v. (ct $$ id = Some (Var v))  = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))"
      using a90 unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct adv c "Address e" v' loaded]  by blast
    

    have "Type (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address e\<^sub>l)) = Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded))"
      using addressLoaded 1(10) a10 * transfer_type_same by simp
    then have fi3:"(\<exists>c. Type (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address e\<^sub>l)) = Some (atype.Contract c) \<and> Contract e\<^sub>l = c)"
      using contractLoaded fi1 
      using contractL by presburger


    then have tsLoaded:"TypeSafe e\<^sub>l (Accounts (st\<lparr>Gas := g'\<rparr>)) k\<^sub>l m\<^sub>l (Storage (st\<lparr>Gas := g'\<rparr>)) cd\<^sub>l \<and>
    fullyInitialised e\<^sub>l (Accounts (st\<lparr>Gas := g'\<rparr>)) k\<^sub>l" 
    proof - 
      have ld:"load True fp xe loaded emptyTypedStore emptyStore emptyTypedStore e cd (st\<lparr>Gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')" using  1
        using a90 ffold_init_def by presburger

      have "fullyInitialised loaded (Accounts (st\<lparr>Gas := g'\<rparr>)) emptyStore"
      proof -
        obtain c_fi where cfi:
          "Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded)) = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
          using fi1 by blast
        obtain dud_fi where epfi:"ep $$ Contract loaded = Some (ct, dud_fi)"
          using a50 contractL 1 a10 * by blast
        have mapfi:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))"
          using a90 unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct adv c "Address e" v' loaded]
          by blast
        have locfi:"\<forall>id v loc. Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
        proof (intro allI impI)
          fix id v loc
          assume h:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc)"
          have hloc:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
            using tsInit by blast
          then show "id = loc" using h by simp
        qed
        have ptrfi:"\<forall>t l p.
            (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue loaded) \<and> accessStore l emptyStore = Some (KStoptr p) \<longrightarrow>
            (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue loaded) \<and> CompStoType t' t l' p)"
          by (simp add: accessStore_def emptyStore_def)
        show ?thesis using cfi epfi mapfi locfi ptrfi 
          using fullyInitialised_def by blast
      qed
      then show ?thesis
        using *  1(9) 7(3) tsInit 7(5)  using fi1  ld
        using  exprTypeconInduct(4)[of True fp xe loaded emptyTypedStore emptyStore emptyTypedStore e cd "(st\<lparr>Gas := g'\<rparr>)" g' e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'']  
        by simp
    qed


    then have ts1:"TypeSafe e\<^sub>l (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
     (Memory (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Storage (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) cd\<^sub>l"
      using tsInitAcc a10 * 1 unfolding TypeSafe_def by auto

    have fiFinal:"fullyInitialised e\<^sub>l (Accounts(expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))"
    proof -
      from tsLoaded obtain c_fi ct_fi dud_fi where fiOld:"
           Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address e\<^sub>l)) = Some (atype.Contract c_fi) \<and>
           Contract e\<^sub>l = c_fi \<and>
           ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
           (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc id))) \<and>
           (\<forall>id v loc. Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
           (\<forall>t l p.
               (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore l k\<^sub>l = Some (KStoptr p) \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p))"
        unfolding fullyInitialised_def by blast
      have typeNew:"Type (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address e\<^sub>l))
              = Some (atype.Contract c_fi)"
        using fiOld addressLoaded
          \<open>Type (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address e\<^sub>l)) = Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded))\<close>
        by simp
      have ptrNew:"\<forall>t l p.
        (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and>
        accessStore l (Stack (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some (KStoptr p) \<longrightarrow>
        (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p)"
        using fiOld by simp
      show ?thesis
        unfolding fullyInitialised_def using fiOld typeNew ptrNew by blast
    qed

    then have IH1:"StateInvariant e\<^sub>l (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) st'' cd\<^sub>l" 
      using 7(1)[OF a5 a6 a10 a20 a30 a40 a50 _ _ a60 a70 _ a80 a90 1(8) _ _ _ _ a100 _ _ _ a110 _ _ a120 ts1 
          ] 1(11) 1(2) a10 * by fastforce

    have accFinal:"Accounts st' = Accounts st''" using 1 by simp
    have storageFinal:"Storage st' = Storage st''" using 1 by simp

    have SafeC:"safeContract (Accounts st'') (Storage st'')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
    then have "Storage st'' = Storage st'" using 1 by auto
    then have scNew:"\<forall>e ct dud i tp. Type (Accounts st'' (Address e)) = Some (atype.Contract (environment.Contract e)) \<and>  ep $$ Contract (e::environment) = Some (ct, dud) \<and> ct $$ i = Some (Var tp) \<longrightarrow> SCon tp i (Storage st'' (Address e))" 
      using SafeC unfolding safeContract_def by simp
    have acc:"(\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep)"
      using 7(3) unfolding TypeSafe_def AddressTypes_def by blast
    obtain cOld where "Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and> Contract e = cOld" 
      using 7(5) unfolding fullyInitialised_def by simp
    then obtain ctO dudO where ctoDef: "ep $$ Contract e = Some (ctO, dudO)" using acc  
      using "7.prems"(3) typesafe_base.fullyInitialised_def typesafe_base_axioms by blast
    have fi2:"\<forall>id v. (ctO $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))"
      using 7(5) ctoDef unfolding fullyInitialised_def by auto
    have fiLoc:"\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      using 7(5) unfolding fullyInitialised_def by blast

    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def using 1(12) by simp
      next 
        show "safeContract (Accounts st') (Storage st')" using IH1 storageFinal 1 unfolding StateInvariant_def TypeSafe_def by auto
      next 
        show "unique_locations (Denvalue e)" using "7.prems"(1) typeSafeUnique by blast
      next
        have old:" compPointers (Stack st'')  (Denvalue e\<^sub>l)" 
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "compPointers (Stack st') (Denvalue e)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then have a5:"accessStore l1' (Stack st') = accessStore l1' (Stack st)" using 1 by simp
          have a10:"accessStore l2' (Stack st') = accessStore l2' (Stack st)" using 1 by auto
          show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
            using 7(3) unfolding TypeSafe_def compPointers_def using a0 a5 a10 by simp
        qed
      next
        show "balanceTypes (Accounts st')" using accFinal IH1 unfolding StateInvariant_def TypeSafe_def by auto
      next 
        have "envAddressesWellFormed e" using "7.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next 
        show "svalueTypes (Svalue e)" using "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 1(12) "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs cd" using "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 1(12) "7.prems"(1) unfolding TypeSafe_def by simp
      next 
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd" 
          unfolding typeCompat_def
        proof intros
          fix t l 
          assume tc1:"(t, l) |\<in>| fmran (Denvalue e)"
          show "case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address e)) | _ \<Rightarrow> False)"
          proof(cases l)
            case (Stackloc x1)
            then show ?thesis 
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using tc1 Stackloc using 7(3) 1(12) unfolding TypeSafe_def typeCompat_def by force
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 1(12) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KCDptr x2)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 1(12) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KMemptr x3)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 1(12) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KStoptr x4)
                then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                  using Some 1 by auto
                then obtain struct where structDef: "t = type.Storage struct" 
                  using 7(3) unfolding TypeSafe_def typeCompat_def using tc1 Some KStoptr Stackloc 
                  by (cases t, force,  fastforce, fastforce, auto)
                obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)" 
                  using 7(5) using accO tc1 unfolding fullyInitialised_def 
                  using Stackloc structDef by blast

                then have "SCon tprnt lprnt (Storage st'' (Address e))"
                proof -
                  from tprntDef obtain kpr where kprDef:"Denvalue e $$ kpr = Some (type.Storage tprnt, Storeloc lprnt)"
                    using fmlookup_ran_iff by blast
                  have "kpr = lprnt" using fiLoc kprDef by blast
                  hence denL:"Denvalue e $$ lprnt = Some (type.Storage tprnt, Storeloc lprnt)" using kprDef by simp
                  have "ctO $$ lprnt = Some (Var tprnt)" using fi2 denL by blast
                  moreover have typeEFinal:"Type (Accounts st'' (Address e)) = Some (atype.Contract (Contract e))"
                    using 7(5) atype_same "7.prems"(2,3) unfolding fullyInitialised_def 
                    by (metis accFinal)
                  ultimately show ?thesis using scNew ctoDef by blast
                qed
                then have "SCon struct x4 (Storage st'' (Address e))"
                  using tprntDef SCon_imps_sublocs by blast
                then show ?thesis using Stackloc Some KStoptr structDef storageFinal by simp
              qed
            qed
          next
            case (Storeloc x2)
            then obtain struct where structDef: "t = type.Storage struct" 
              using 7(3) tc1 unfolding TypeSafe_def typeCompat_def by (cases t,fastforce+)

            then have "SCon struct x2 (Storage st'' (Address e))"
            proof -
              have inRan:"(type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue e)"
                using tc1 Storeloc structDef by simp
              then obtain kpr where kprDef:"Denvalue e $$ kpr = Some (type.Storage struct, Storeloc x2)"
                using fmlookup_ran_iff by metis
              have "kpr = x2" using fiLoc kprDef by blast
              hence denX2:"Denvalue e $$ x2 = Some (type.Storage struct, Storeloc x2)" using kprDef by simp
              have "ctO $$ x2 = Some (Var struct)" using fi2 denX2 by blast
              moreover have typeEFinal:"Type (Accounts st'' (Address e)) = Some (atype.Contract (Contract e))"
                    using 7(5) atype_same "7.prems"(2,3) unfolding fullyInitialised_def 
                    by (metis accFinal)
              ultimately show ?thesis using scNew ctoDef by blast
            qed
            then show ?thesis using Storeloc structDef 
              by (simp add: storageFinal)
          qed
        qed
      next
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 7(3) 1(12) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 7(3) 1(12) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using 7(3) 1(12) unfolding TypeSafe_def by simp
      qed
    next 
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 7(5) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using fiC atype_same "7.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        using 1 fiFinal 7(5) unfolding fullyInitialised_def by auto
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 7(3) 1(12) by simp
    next 
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 1(12)  by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using 1(12) by simp
    next 
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using 1(12) by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 1(12) by simp
    qed
  next
    case (2 adv c g ct cn fb' v t g' v' acc st'')
    then obtain cc where ccDef: "c = Contract cc" 
      by (metis Environment.select_convs(2))

    then have a5:"assert Gas (\<lambda>st. costs (EXTERNAL ad i xe val) e cd st < state.Gas st) st =  Normal ((), st)" using 2 by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    obtain expGas where a10:" toState (local.expr ad e cd) sgas = Normal ((KValue adv, Value TAddr), expGas)" using 2(2) a6 * by simp
    then have a20:"(case (KValue adv, Value TAddr) of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err 
                    | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) expGas =
    Normal (adv, expGas)" by simp
    then obtain vd where a30:"assert Err (\<lambda>_. adv \<noteq> Address e) expGas = Normal (vd, expGas)" using 2 by simp
    then have a40:"(case Type (Accounts expGas adv) of None \<Rightarrow> throw Err expGas 
                | Some EOA \<Rightarrow> throw Err expGas 
                | Some (atype.Contract c) \<Rightarrow> return c expGas) = Normal (c, expGas)" using 2 a10 * by auto
    then have a50:"option Err (\<lambda>_. ep $$ c) expGas = Normal ((ct, cn, fb'), expGas)" using 2 by simp
    then have a60:"toState (local.expr val e cd) expGas = Normal ((KValue v, Value t), expGas\<lparr>Gas := g'\<rparr>)" using 2 a10 * by auto
    then have a70:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) 
                    | (KValue v, _) \<Rightarrow> throw Err 
                    | (_, b) \<Rightarrow> throw Err) (expGas\<lparr>Gas := g'\<rparr>) = Normal ((v,t), expGas\<lparr>Gas := g'\<rparr>)" using 2 a10 * by simp
    then have a80:"option Err (\<lambda>_. convert t (TUInt b256) v) (expGas\<lparr>Gas := g'\<rparr>) = Normal (v', expGas\<lparr>Gas := g'\<rparr>)" using 2 by simp
    then obtain loaded where a90:"loaded = ffold_init ct (emptyEnv adv c (Address e) v') (fmdom ct)" using 2(9) by blast

    then have a110:"option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) (expGas\<lparr>Gas := g'\<rparr>) = Normal (acc, expGas\<lparr>Gas := g'\<rparr>)" 
      using 2 * a10 by auto


    have tsInitAcc:"\<forall>x y. TypeSafe loaded acc emptyStore emptyTypedStore (Storage st) emptyTypedStore \<and>
       (Denvalue loaded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue loaded $$ x = Some y \<longrightarrow> (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"  
    proof - 
      have "safeContract (Accounts st) (Storage st)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 2 by simp
      moreover have "safeContract acc (state.Storage st)" 
        using "2"(9) calculation safeContract_def transfer_type_same by auto
      moreover have svv':"svalueTypes v'" unfolding svalueTypes_def
        using 2(6,7) 7(3) 7(5) 
        using exprTypeconInduct(3)[of val e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
          typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto
      moreover have "balanceTypes acc" using 2(10) unfolding balanceTypes_def
      proof - 
        have old:"balanceTypes (Accounts (st\<lparr>Gas := g'\<rparr>))" using 7(3) unfolding TypeSafe_def by simp
        have accExp:"(case subBalance (Address e) v' (Accounts (st)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance adv v' x) = Some acc" 
          using 2(9) unfolding transfer_def by blast
        have v'TC: "typeCon (TUInt b256) v'" 
          using  svv' unfolding svalueTypes_def by blast

        show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
        proof
          fix adv'
          show "typeCon (TUInt b256) (Bal (acc adv')) "
          proof(cases "adv' = (Address e)")
            case True
            then have ns:"adv' \<noteq> adv" using 2 by blast
            then have tco:"typeCon (TUInt b256) (Bal ((Accounts (st\<lparr>Gas := g'\<rparr>)) adv'))"
              using True old accExp balanceTypes_def by blast
            have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))" 
              using transfer_subRead[OF 2(9) _ v'TC ] True ns tco by auto
            then show ?thesis using True 

              by (smt (verit, ccfv_SIG) "2"(3,9) Read_ShowL_id checkUInt_def typeCon.simps(2) tco transfer_add transfer_mono transfer_sub transfer_val3)
          next
            case False
            then show ?thesis 
            proof(cases "adv' = adv")
              case True
              then have "typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))"
                using True old accExp balanceTypes_def by simp
              then have "Bal (acc adv) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))" 
                using transfer_addRead[OF 2(9)_ v'TC  ] 2(3) by auto
              then show ?thesis using True 
                using "2"(9,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))\<close> checkUInt_def transfer_val1 transfer_val2 by auto
            next
              case f2:False
              then show ?thesis using False transfer_eq[OF 2(9)] old 
                using balanceTypes_def by force
            qed
          qed
        qed
      qed
      moreover have "lessThanTopLocs emptyStore" using emptyTopLocs by simp
      moreover have "ep $$ Contract cc = Some (ct, cn, fb')" using ccDef 2(5) by simp
      moreover have "addressFormat adv" using 7(3) unfolding TypeSafe_def AddressTypes_def using 2 by (simp split:option.splits atype.splits)
      moreover have "addressFormat (Sender e)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 2 by simp
      moreover have "AddressTypes acc" using 2(9) transfer_type_same 7(3) unfolding TypeSafe_def unfolding AddressTypes_def by simp
      moreover have "addressFormat (Address e)" using "7.prems"(1) unfolding TypeSafe_def by simp
      moreover have "SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessTypeStore_def accessStore_def 
        by (simp add: emptyTypedStore_def)
      moreover have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      moreover have "Type (acc adv) = Some (atype.Contract (Contract cc))"
        using 2(9) a10 * a40 ccDef transfer_type_same by (auto split:option.splits atype.splits result.splits)

      ultimately show ?thesis
        using a90 ccDef unfolding ffold_init_def  using ffoldInitTypeSafe[of acc "Storage st" v' emptyTypedStore cc ct "(cn,fb')" adv "(Address e)" " (fmdom ct)"]  
        using typedEmptyTopLocs by blast
    qed

    have contractL:"Contract loaded = c" using a90 by simp
    have addressL:"Address loaded = adv" using a90 by simp
    have fi1:"(\<exists>c. Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)" using contractL addressL 2 a10 * a40 by simp
    have ct1:"\<exists>dud. ep $$ Contract loaded = Some (ct, dud)" using a50 contractL 2 a10 * by blast
    then have fi2:"\<forall>id v. (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)) = (ct $$ id = Some (Var v))"
      using a90 unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct adv c _ v' loaded] by auto
    then have fi3:"(\<exists>c. Type ((acc) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)"
      using fi1 contractL 2(9) transfer_type_same by simp

    have a120:" TypeSafe loaded (acc) (emptyStore) (emptyTypedStore) (Storage st) emptyTypedStore" using tsInitAcc 
      by simp
    moreover have "fullyInitialised loaded (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>))"
    proof -
      obtain c_fi where cfi0:"Type (acc (Address loaded)) = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
        using fi3 by blast
      have cfi:"Type (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) (Address loaded))
            = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
        using cfi0 by simp
      obtain dud_fi where epfi:"ep $$ Contract loaded = Some (ct, dud_fi)"
        using ct1 by blast
      have mapfi:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))"
        using fi2 by blast
      have locfi:"\<forall>id v loc. Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      proof (intro allI impI)
        fix id v loc
        assume h:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc)"
        have hloc:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
          using tsInitAcc by blast
        then show "id = loc" using h by simp
      qed
      have ptrfi:"\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue loaded) \<and>
          accessStore l (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue loaded) \<and> CompStoType t' t l' p)"
        by (simp add: accessStore_def emptyStore_def)
      show ?thesis
        unfolding fullyInitialised_def using cfi epfi mapfi locfi ptrfi by blast
    qed
    ultimately have IH1:"StateInvariant loaded (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) st'' emptyTypedStore" 
      using 7(2)[OF a5 a6 a10 a20 a30 a40 a50 _ _ a60 a70 _ a80 a90 2(8) a110, 
          of "(cn, fb')" cn fb' _ _ _ _ _ "(st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" st''] 
        2(10) 2 * a10 a90 by fastforce

    have accFinal:"Accounts st' = Accounts st''" using 2 by simp
    have storageFinal:"Storage st' = Storage st''" using 2 by simp

    have acc:"(\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep)"
      using 7(3) unfolding TypeSafe_def AddressTypes_def by blast
    obtain cOld where "Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and>Contract e = cOld" 
      using 7(5) unfolding fullyInitialised_def by simp
    then obtain ctO dudO where ctoDef: "ep $$ Contract e = Some (ctO, dudO)" using acc 
      using "7.prems"(3) typesafe_base.fullyInitialised_def typesafe_base_axioms by blast
    have SafeC:"safeContract (Accounts st'') (Storage st'')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast

    then have scNew:"\<forall>e ct dud i tp. Type (Accounts st'' (Address e)) = Some (atype.Contract (environment.Contract e)) \<and> ep $$ Contract (e::environment) = Some (ct, dud) \<and> ct $$ i = Some (Var tp) \<longrightarrow> SCon tp i (Storage st'' (Address e))"
      using SafeC unfolding safeContract_def by simp


    have fi4:"(\<forall>id v. \<exists>dud. ep $$ Contract loaded = Some (ct, dud) 
                          \<and> ct $$ id = Some (Var v) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)))" 
      using fi1 ct1 fi2 
      by presburger
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def using 2 by simp
      next 
        show "safeContract (Accounts st') (Storage st')" using IH1 storageFinal 2 unfolding StateInvariant_def TypeSafe_def by auto
      next 
        show "unique_locations (Denvalue e)" using "7.prems"(1) typeSafeUnique by blast
      next
        show "compPointers (Stack st') (Denvalue e)"  unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then have a5:"accessStore l1' (Stack st') = accessStore l1' (Stack st)" using 2 by simp
          have a10:"accessStore l2' (Stack st') = accessStore l2' (Stack st)" using 2 by auto
          show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
            using 7(3) unfolding TypeSafe_def compPointers_def using a0 a5 a10 by simp
        qed
      next
        show "balanceTypes (Accounts st')" using accFinal IH1 unfolding StateInvariant_def TypeSafe_def by auto
      next 
        have "envAddressesWellFormed e" using "7.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next 
        show "svalueTypes (Svalue e)" using "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 2 "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs cd" using "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 2 "7.prems"(1) unfolding TypeSafe_def by simp
      next 
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd" 
          unfolding typeCompat_def
        proof intros
          fix t l 
          assume tc1:"(t, l) |\<in>| fmran (Denvalue e)"
          show "case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address e)) | _ \<Rightarrow> False)"
          proof(cases l)
            case (Stackloc x1)
            then show ?thesis 
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using tc1 Stackloc using 7(3) 2 unfolding TypeSafe_def typeCompat_def by force
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 2(11) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KCDptr x2)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 2(11) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KMemptr x3)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 2(11) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KStoptr x4)
                then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                  using Some 2 by auto
                then obtain struct where structDef: "t = type.Storage struct" 
                  using 7(3) unfolding TypeSafe_def typeCompat_def using tc1 Some KStoptr Stackloc 
                  by (cases t, force,  fastforce, fastforce, auto)
                obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)" 
                  using 7(5) using accO tc1 unfolding fullyInitialised_def 
                  using Stackloc structDef by blast
                then have "SCon tprnt lprnt (Storage st'' (Address e))"
                  using ctoDef IH1 fi4 ct1  scNew 
                  by (metis (no_types, lifting) "7.prems"(2,3) \<open>\<And>thesis. (\<And>cOld. Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and> environment.Contract e = cOld \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
                      accFinal fi_denvalue_storeloc_to_contract_var atype_same)
                  
                then have "SCon struct x4 (Storage st'' (Address e))"
                  using tprntDef SCon_imps_sublocs by blast
                then show ?thesis using Stackloc Some KStoptr structDef storageFinal by simp
              qed
            qed
          next
            case (Storeloc x2)
            then obtain struct where structDef: "t = type.Storage struct" 
              using 7(3) tc1 unfolding TypeSafe_def typeCompat_def by (cases t,fastforce+)

            then have "SCon struct x2 (Storage st'' (Address e))"
              using ctoDef IH1 fi4 ct1  scNew fmlookup_ran_iff fullyInitialised_def "7.prems"(3)
              by (smt (verit, best) "7.prems"(2) Storeloc accFinal atype_same tc1)
              
            then show ?thesis using Storeloc structDef 
              by (simp add: storageFinal)
          qed
        qed
      next 
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 2(11) 7(3) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 2(11) 7(3) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using 2(11) 7(3) unfolding TypeSafe_def by simp
      qed
    next 
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 7(5) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using fiC atype_same "7.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        using 7(5) 2 unfolding fullyInitialised_def by auto
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 7(3) 2(11) by simp
    next 
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 2(11)  by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using 2(11) by simp
    next 
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using 2(11) by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" 
        using 2(11) by simp
    qed
  qed
next
  case (8 ad ex e cd st)
  show ?case 
  proof(cases rule:transfer[OF 8(3)])
    case (1 v t g adv c g' v' acc ct cn f st'')
    then obtain cc where ccDef: "Contract cc = c" 
      by (meson Environment.select_convs(2))
    then have a1:"assert Gas (\<lambda>st. costs (TRANSFER ad ex) e cd st < state.Gas st) st = Normal ((), st)" using 1 by simp
    have a10:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>) st = Normal ((), st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>)"
      by simp
    have a20:"toState (local.expr ad e cd) (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>) = Normal ((KValue adv, Value TAddr), st\<lparr>Gas := g\<rparr>)" 
      using 1 by simp
    then have a30:"(case (KValue adv, Value TAddr) of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err)
     (st\<lparr>Gas := g\<rparr>) = Normal (adv, st\<lparr>Gas := g\<rparr>)" using 1 by simp
    have a40:" toState (local.expr ex e cd) (st\<lparr>Gas := g\<rparr>) = Normal ((KValue v, Value t), st\<lparr>Gas := g'\<rparr>)" using 1 by auto
    have a50:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) | (KValue v, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) (st\<lparr>Gas := g'\<rparr>) = Normal ((v, t), (st\<lparr>Gas := g'\<rparr>))"
      using 1 by simp
    then have a60:"option Err (\<lambda>_. convert t (TUInt b256) v) (st\<lparr>Gas := g'\<rparr>) = Normal (v', st\<lparr>Gas := g'\<rparr>)" using 1 by simp
    have a70:"applyf Accounts (st\<lparr>Gas := g'\<rparr>) = Normal (Accounts (st\<lparr>Gas := g\<rparr>), (st\<lparr>Gas := g'\<rparr>))" using 1 by simp
    have a80:"Type (Accounts (st\<lparr>Gas := g\<rparr>) adv) = Some (atype.Contract c)" using 1(5) by blast
    have a90:"option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) (st\<lparr>Gas := g'\<rparr>) = Normal (acc, (st\<lparr>Gas := g'\<rparr>))"
      using 1 by simp
    have a95:"option Err (\<lambda>_. ep $$ c) (st\<lparr>Gas := g'\<rparr>) = Normal ((ct, cn, f), (st\<lparr>Gas := g'\<rparr>))" using 1 by auto
    have a100:"modify (\<lambda>st. st\<lparr>Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) (st\<lparr>Gas := g'\<rparr>)
                  = Normal ((), st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" by simp
    obtain loaded where loadedDef:"loaded = ffold_init ct (emptyEnv adv c (Address e) v') (fmdom ct)" by blast

    have tsLoaded':"\<forall>x y. TypeSafe loaded acc emptyStore emptyTypedStore (Storage st) emptyTypedStore \<and>
       (Denvalue loaded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue loaded $$ x = Some y \<longrightarrow> (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"  
    proof - 
      have "safeContract (Accounts st) (Storage st)" using 8(2) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      moreover have "safeContract acc (Storage st)" 
        using "1"(7) calculation safeContract_def transfer_type_same by force
      moreover have svv':"svalueTypes v'" unfolding svalueTypes_def
        using 1(4,3) 8(2) 8(4)  
        using exprTypeconInduct(3)[of ex e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
          typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto
      moreover have "balanceTypes acc"  unfolding balanceTypes_def
      proof - 
        have old:"balanceTypes (Accounts (st\<lparr>Gas := g'\<rparr>))" using 8(2) unfolding TypeSafe_def by simp
        have accExp:"(case subBalance (Address e) v' (Accounts (st)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance adv v' x) = Some acc" 
          using 1(7) unfolding transfer_def by blast
        have v'TC: "typeCon (TUInt b256) v'" 
          using  svv' unfolding svalueTypes_def by blast

        show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
        proof(cases "adv = (Address e)")
          case same:True
          show ?thesis using transfer_sameRead 
            by (metis "1"(7) "8"(2) balanceTypes_def same typeSafeAccounts transfer_eq v'TC)
        next
          case notSame:False
          show ?thesis 
          proof
            fix adv'
            show "typeCon (TUInt b256) (Bal (acc adv')) "
            proof(cases "adv' = (Address e)")
              case True
              then have tco:"typeCon (TUInt b256) (Bal ((Accounts (st\<lparr>Gas := g'\<rparr>)) adv'))"
                using True old accExp balanceTypes_def by blast
              have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))" 
                using transfer_subRead[OF 1(7) _ v'TC ] True notSame tco by auto
              then show ?thesis using True 
                using "1"(7,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv'))\<close> checkUInt_def transfer_val1 transfer_val2
                by (smt (verit, ccfv_SIG) notSame typeCon.simps(2) transfer_sub transfer_val3)
            next
              case False
              then show ?thesis 
              proof(cases "adv' = adv")
                case True
                then have "typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))"
                  using True old accExp balanceTypes_def by simp
                then have "Bal (acc adv) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))" 
                  using transfer_addRead[OF 1(7)_ v'TC  ] 1(3) notSame by auto
                then show ?thesis using True 
                  using "1"(7,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))\<close> checkUInt_def transfer_val1 transfer_val2 notSame by auto
              next
                case f2:False
                then show ?thesis using False transfer_eq[OF 1(7)] old 
                  using balanceTypes_def by force
              qed
            qed
          qed
        qed
      qed
      moreover have "lessThanTopLocs emptyStore" using emptyTopLocs by simp
      moreover have "ep $$ Contract cc = Some (ct, cn, f)" using ccDef 1(6) by simp
      moreover have "addressFormat adv" using 8(2) unfolding TypeSafe_def AddressTypes_def using 1 by (simp split:option.splits atype.splits)
      moreover have "addressFormat (Sender e)" using 8(2) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      moreover have "AddressTypes acc" using 1(7) transfer_type_same 8(2) unfolding TypeSafe_def unfolding AddressTypes_def by simp
      moreover have "addressFormat (Address e)" using "8.prems"(1) unfolding TypeSafe_def by simp
      moreover have "SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessTypeStore_def accessStore_def emptyTypedStore_def by auto
      moreover have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      moreover have "Type (acc adv) = Some (atype.Contract (Contract cc))"
        using a80 ccDef transfer_type_same[OF 1(7)] by simp
      ultimately show ?thesis
        using loadedDef ccDef unfolding ffold_init_def 
        using ffoldInitTypeSafe[of acc "Storage st" v' emptyTypedStore cc ct "(cn,f)" adv "(Address e)" " (fmdom ct)"]  
        using typedEmptyTopLocs 
        by blast
    qed
    then have tsLoaded:"TypeSafe loaded (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>))
     (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) (Memory (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>))
     (Storage (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) emptyTypedStore" by auto

    have contractL:"Contract loaded = c" using loadedDef by simp
    have addressL:"Address loaded = adv" using loadedDef by simp
    have fi1:"(\<exists>c. Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)" using contractL addressL 1 a10 a40 by simp
    have ctd:"\<exists>dud. ep $$ Contract loaded = Some (ct, dud)" using a50 contractL 1 a10  by blast
    then have fi2:"\<forall>id v. (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)) = (ct $$ id = Some (Var v))"
      using loadedDef unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct adv c "(Address e)" v' loaded] by auto
    then have fi3:"(\<exists>c. Type ((acc) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)"
      using  fi1  contractL 1(7) transfer_type_same by simp
    have fi4:"(\<forall>id v. \<exists>dud. ep $$ Contract loaded = Some (ct, dud) 
                          \<and> ct $$ id = Some (Var v) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)))" 
      using fi1 ctd fi2 
      by (metis (mono_tags, opaque_lifting))
    have fiLoaded:"fullyInitialised loaded (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>))"
    proof -
      obtain c_fi where cfi0:"Type (acc (Address loaded)) = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
        using fi3 by blast
      have cfi:"Type (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) (Address loaded))
            = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
        using cfi0 by simp
      obtain dud_fi where epfi:"ep $$ Contract loaded = Some (ct, dud_fi)"
        using ctd by blast
      have mapfi:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))"
        using fi2 by blast
      have locfi:"\<forall>id v loc. Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      proof (intro allI impI)
        fix id v loc
        assume h:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc)"
        have hloc:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
          using tsLoaded' by blast
        then show "id = loc" using h by simp
      qed
      have ptrfi:"\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue loaded) \<and>
          accessStore l (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue loaded) \<and> CompStoType t' t l' p)"
        by (simp add: accessStore_def emptyStore_def)
      show ?thesis
        unfolding fullyInitialised_def using cfi epfi mapfi locfi ptrfi by blast
    qed
    have stmtC:"stmt f loaded emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) = Normal ((), st'')"
      using 1(8) loadedDef unfolding ffold_init_def by simp
    have IH1:"StateInvariant loaded (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) st'' emptyTypedStore"
      using 8(1)[OF a1 a10 a20 a30 a40 a50 _ a60 a70 a80 _ a95 _ _ loadedDef _ _ a90 a100 tsLoaded stmtC fiLoaded ] by simp

    have acc:"(\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep)"
      using 8(2) unfolding TypeSafe_def AddressTypes_def by blast
    obtain cOld where "Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and> Contract e = cOld" 
      using 8(4) unfolding fullyInitialised_def by simp
    then obtain ctO dudO where ctoDef: "ep $$ Contract e = Some (ctO, dudO)" using acc 
      using "8.prems"(3) typesafe_base.fullyInitialised_def typesafe_base_axioms by blast
    have storageFinal:"Storage st' = Storage st''" using 1 by auto

    have ct1:"\<exists>dud. ep $$ Contract loaded = Some (ct, dud)" using a50 contractL 1 a10 by blast
    have SafeC:"safeContract (Accounts st'') (Storage st'')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast

    then have scNew:"\<forall>e ct dud i tp. Type (Accounts st'' (Address e)) = Some (atype.Contract (environment.Contract e)) 
                      \<and> ep $$ Contract (e::environment) = Some (ct, dud) \<and> ct $$ i = Some (Var tp) \<longrightarrow> SCon tp i (Storage st'' (Address e))"
      using SafeC unfolding safeContract_def by simp
    have accFinal:"Accounts st' = Accounts st''" using 1 by simp

    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def using 1 by simp
      next 
        show "safeContract (Accounts st') (Storage st')" using IH1 1 unfolding StateInvariant_def TypeSafe_def by auto
      next 
        show "unique_locations (Denvalue e)" using "8.prems"(1) typeSafeUnique by blast
      next
        have "compPointers (Stack st'') (Denvalue loaded)"
          using IH1 unfolding StateInvariant_def TypeSafe_def  by blast
        show "compPointers (Stack st') (Denvalue e)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then have a5:"accessStore l1' (Stack st') = accessStore l1' (Stack st)" using 1 by simp
          have a10:"accessStore l2' (Stack st') = accessStore l2' (Stack st)" using 1 by auto
          show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
            using 8(2) unfolding TypeSafe_def compPointers_def using a0 a5 a10 by simp
        qed
      next
        show "balanceTypes (Accounts st')" using 1 IH1 unfolding StateInvariant_def TypeSafe_def by auto
      next 
        have "envAddressesWellFormed e" using "8.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next 
        show "svalueTypes (Svalue e)" using "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 1 "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs cd" using "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 1 "8.prems"(1) unfolding TypeSafe_def by simp
      next 
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd" 
          unfolding typeCompat_def
        proof intros
          fix t l 
          assume tc1:"(t, l) |\<in>| fmran (Denvalue e)"
          show "case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address e)) | _ \<Rightarrow> False)"
          proof(cases l)
            case (Stackloc x1)
            then show ?thesis 
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using tc1 Stackloc using 8(2) 1 unfolding TypeSafe_def typeCompat_def by force
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 8(2) 1(9) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KCDptr x2)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 8(2) 1(9) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KMemptr x3)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 8(2) 1(9) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KStoptr x4)
                then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                  using Some 1 KStoptr by auto
                then obtain struct where structDef: "t = type.Storage struct" 
                  using 8(2) unfolding TypeSafe_def typeCompat_def using tc1 Some KStoptr Stackloc 
                  by (cases t, force,  fastforce, fastforce, auto)
                obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)" 
                  using 8(4) using accO tc1 unfolding fullyInitialised_def 
                  using Stackloc structDef by blast

                then have "SCon tprnt lprnt (Storage st'' (Address e))"
                  using ctoDef IH1 fi4 ct1  scNew
                    "8.prems"(2,3) \<open>\<And>thesis. (\<And>cOld. Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and> environment.Contract e = cOld \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
                      fi_denvalue_storeloc_to_contract_var atype_same accFinal
                  by (metis (no_types, lifting))
                  
                then have "SCon struct x4 (Storage st'' (Address e))"
                  using tprntDef SCon_imps_sublocs by blast
                then show ?thesis using Stackloc Some KStoptr structDef storageFinal by simp
              qed
            qed
          next
            case (Storeloc x2)
            then obtain struct where structDef: "t = type.Storage struct" 
              using 8(2) tc1 unfolding TypeSafe_def typeCompat_def by (cases t,fastforce+)
            
            then have "SCon struct x2 (Storage st'' (Address e))"
              using ctoDef IH1 fi4 ct1  scNew fmlookup_ran_iff fullyInitialised_def "8.prems"(3) 
              by (smt (verit, best) "8.prems"(2) Storeloc accFinal atype_same  tc1)
              
            then show ?thesis using Storeloc structDef 
              by (simp add: storageFinal)
          qed
        qed
      next 
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 1 8(2) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 1 8(2) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using 1 8(2) unfolding TypeSafe_def by simp
      qed
    next 
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 8(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using fiC atype_same "8.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        using 8(4) 1 unfolding fullyInitialised_def by auto
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 8(3) 1(9) by simp
    next 
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 1(9)  by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using 1(9) by simp
    next 
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using 1(9) by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 1(9) by simp

    qed
  next
    case (2 v t g adv g' v' acc)
    then have a1:"assert Gas (\<lambda>st. costs (TRANSFER ad ex) e cd st < state.Gas st) st = Normal ((), st)" by simp
    have a10:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>) st = Normal ((), st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>)"
      by simp
    have a20:"toState (local.expr ad e cd) (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>) = Normal ((KValue adv, Value TAddr), st\<lparr>Gas := g\<rparr>)" 
      using 2 by simp
    then have a30:"(case (KValue adv, Value TAddr) of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err)
     (st\<lparr>Gas := g\<rparr>) = Normal (adv, st\<lparr>Gas := g\<rparr>)" using 2 by simp
    have a40:" toState (local.expr ex e cd) (st\<lparr>Gas := g\<rparr>) = Normal ((KValue v, Value t), st\<lparr>Gas := g'\<rparr>)" using 2 by auto
    have a50:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) | (KValue v, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) (st\<lparr>Gas := g'\<rparr>) = Normal ((v, t), (st\<lparr>Gas := g'\<rparr>))"
      using 2 by simp
    then have a60:"option Err (\<lambda>_. convert t (TUInt b256) v) (st\<lparr>Gas := g'\<rparr>) = Normal (v', st\<lparr>Gas := g'\<rparr>)" using 2 by simp
    have a70:"applyf Accounts (st\<lparr>Gas := g'\<rparr>) = Normal (Accounts (st\<lparr>Gas := g\<rparr>), (st\<lparr>Gas := g'\<rparr>))" using 2 by simp
    have a90:"option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) (st\<lparr>Gas := g'\<rparr>) = Normal (acc, (st\<lparr>Gas := g'\<rparr>))"
      using 2 by simp

    have svv':"svalueTypes v'" unfolding svalueTypes_def
      using 2(4,3) 8(2) 8(4)   
      using exprTypeconInduct(3)[of ex e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
        typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto

    have btACC:"balanceTypes acc"  unfolding balanceTypes_def
    proof - 
      have old:"balanceTypes (Accounts (st\<lparr>Gas := g'\<rparr>))" using 8(2) unfolding TypeSafe_def by simp
      have accExp:"(case subBalance (Address e) v' (Accounts (st)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance adv v' x) = Some acc" 
        using 2(6) unfolding transfer_def by blast
      have v'TC: "typeCon (TUInt b256) v'" 
        using  svv' unfolding svalueTypes_def by blast

      show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
      proof(cases "adv = (Address e)")
        case same:True
        show ?thesis using transfer_sameRead 
          by (metis "2"(6) "8"(2) balanceTypes_def same typeSafeAccounts transfer_eq v'TC)
      next
        case notSame:False
        show ?thesis 
        proof
          fix adv'
          show "typeCon (TUInt b256) (Bal (acc adv')) "
          proof(cases "adv' = (Address e)")
            case True
            then have tco:"typeCon (TUInt b256) (Bal ((Accounts (st\<lparr>Gas := g'\<rparr>)) adv'))"
              using True old accExp balanceTypes_def by blast
            have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))" 
              using transfer_subRead[OF 2(6) _ v'TC ] True notSame tco by auto
            then show ?thesis using True 
              using "2"(6,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv'))\<close> checkUInt_def transfer_val1 transfer_val2
              by (smt (verit, ccfv_SIG) notSame typeCon.simps(2) transfer_sub transfer_val3)
          next
            case False
            then show ?thesis 
            proof(cases "adv' = adv")
              case True
              then have "typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))"
                using True old accExp balanceTypes_def by simp
              then have "Bal (acc adv) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))" 
                using transfer_addRead[OF 2(6)_ v'TC  ] 2(3) notSame by auto
              then show ?thesis using True 
                using "2"(6,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))\<close> checkUInt_def transfer_val1 transfer_val2 notSame by auto
            next
              case f2:False
              then show ?thesis using False transfer_eq[OF 2(6)] old 
                using balanceTypes_def by force
            qed
          qed
        qed
      qed
    qed

    have accfinal:"Accounts st'= acc" using 2 by simp

    have sameStores:"Storage st' = Storage st \<and> Memory st = Memory st' \<and> Stack st = Stack st'" using 2 by simp
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" unfolding AddressTypes_def
        proof intros
          fix adv
          show "case Type (Accounts st' adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep"
          proof (cases "Type (Accounts st' adv)")
            case None
            then show ?thesis by simp
          next
            case (Some a)
            then show ?thesis 
            proof(cases a)
              case EOA
              then show ?thesis using Some by simp
            next
              case (Contract x2)
              then show ?thesis using Some 8(2) unfolding TypeSafe_def using accfinal 2(6) transfer_type_same  
                by (metis transfer_type_same accfinal Some "2"(6) AddressTypes_def)
            qed
          qed
        qed
      next 
        show "safeContract (Accounts st') (Storage st')" using 8(2) 2 unfolding TypeSafe_def using sameStores 
          by (smt (verit, best) accfinal safeContract_def transfer_type_same)
      next 
        show "unique_locations (Denvalue e)" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "compPointers (Stack st') (Denvalue e)" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "balanceTypes (Accounts st')" using btACC accfinal by simp
      next 
        have "envAddressesWellFormed e" using "8.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next 
        show "svalueTypes (Svalue e)" using "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "lessThanTopLocs cd" using "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next 
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd" 
          using 8(2) unfolding TypeSafe_def using sameStores by simp
      next 
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "SomeValSomeTyp (Memory st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      qed
    next 
have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 8(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using fiC atype_same "8.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        using 8(4) 2 unfolding fullyInitialised_def by auto
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 8(3) 2(7) by simp
    next 
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 2(7)  by simp
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using 2(7) by simp
    next 
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using 2(7) by simp
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 2(7) by simp
    qed
  qed
next
  case (9 id0 tp s e\<^sub>v cd st)
  show ?case 
  proof(cases rule:blockNone[OF 9(3)])
    case (1 cd' mem' sck' e')
    have a10:"assert Gas (\<lambda>st. costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st < state.Gas st) st = Normal ((), st)" using 1 by simp
    obtain sgas where sgasDef:"sgas = state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st" by simp
    then have a20:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>) st = Normal ((), (st\<lparr>Gas := sgas\<rparr> ))" by simp
    have a30:"option Err (\<lambda>st. decl id0 tp None False cd (Memory st) (Storage st (Address e\<^sub>v)) (cd, Memory st, Stack st, e\<^sub>v)) (st\<lparr>Gas := sgas\<rparr> )
            = Normal ((cd', mem', sck', e'), (st\<lparr>Gas := sgas\<rparr> )) " using 1 by simp
    have a40:"modify (\<lambda>st. st\<lparr>Stack := sck', Memory := mem'\<rparr>) (st\<lparr>Gas := sgas\<rparr>) = Normal ((), st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)"
      by simp

    have tsDecl:"TypeSafe e' (Accounts (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) sck' mem'
     (Storage (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) cd' \<and>
    (\<forall>x l. (\<nexists>y y'. x = type.Memory y \<or> x = Value y') \<and> (x, l) |\<in>| fmran (Denvalue e') \<longrightarrow>
           (x, l) |\<in>| fmran (Denvalue e\<^sub>v)) \<and>
    (\<forall>sckl ptr.
        accessStore sckl sck' = Some ptr \<and> (\<nexists>y y'. ptr = KMemptr y \<or> ptr = KValue y') \<longrightarrow>
        accessStore sckl (Stack (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) =
        Some ptr) \<and>
    cd = cd'\<and>
    Toploc (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) \<le> Toploc mem' \<and>
    (\<forall>locs v.
        accessStore locs (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) = Some v \<longrightarrow>
        accessStore locs mem' = Some v) \<and>
    (\<forall>locs t.
        accessTypeStore locs (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) = Some t \<longrightarrow>
        accessTypeStore locs mem' = Some t) \<and>
    (\<forall>locs.
        (\<exists>tloc<Toploc (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)).
            LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<and>
            accessStore locs (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) = None) \<longrightarrow>
        accessStore locs mem' = None)"
      using typeSafeDeclNone[OF _ 1(2)] 9(2) by simp

    then have a50:"TypeSafe e' (Accounts (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) (Stack (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>))
   (Memory (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) (Storage (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) cd'" by simp
    have denLink:"\<forall>ii x. Denvalue e\<^sub>v $$ ii = Some x \<longrightarrow> Denvalue e' $$ ii = Some x" using decl_env_monotonic[OF 1(2)] by auto

    have fiDec:" fullyInitialised e' (Accounts (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) (Stack (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>))"
    proof -
      have sameStuff:"Address e' = Address e\<^sub>v \<and> Contract e' = Contract e\<^sub>v"
        using 1(2) decl_env by simp
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
          Contract e\<^sub>v = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
        using 9(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_fi) \<and>
          Contract e\<^sub>v = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
        by blast

      have cfi:"Type (Accounts (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>) (Address e')) = Some (atype.Contract c_fi) \<and>
          Contract e' = c_fi \<and> ep $$ c_fi = Some (ct_fi, dud_fi)"
        using fiC sameStuff by simp

      have mapfi:"\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id))"
      proof (intro allI)
        fix id v
        show "(ct_fi $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id))"
        proof
          assume hct:"ct_fi $$ id = Some (Var v)"
          then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id)"
            using fiC by blast
          then show "Denvalue e' $$ id = Some (type.Storage v, Storeloc id)"
            using decl_env_monotonic[OF 1(2)] by blast
        next
          assume hnew:"Denvalue e' $$ id = Some (type.Storage v, Storeloc id)"
          show "ct_fi $$ id = Some (Var v)"
          proof (cases "id = id0")
            case True
            have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
              using decl_env_storlocs_unchanged[OF 1(2)] by simp
            then have "Denvalue e\<^sub>v $$ id0 = Some (type.Storage v, Storeloc id0)"
              using hnew True by blast
            then show ?thesis using fiC True by blast
          next
            case False
            then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id)"
              using decl_env_not_i[OF 1(2)] hnew by blast
            then show ?thesis using fiC by blast
          qed
        qed
      qed

      have locfi:"\<forall>id v loc. Denvalue e' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      proof (intro allI impI)
        fix id v loc
        assume hnew:"Denvalue e' $$ id = Some (type.Storage v, Storeloc loc)"
        show "id = loc"
        proof (cases "id = id0")
          case True
          have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
            using decl_env_storlocs_unchanged[OF 1(2)] by simp
          then have "Denvalue e\<^sub>v $$ id0 = Some (type.Storage v, Storeloc loc)"
            using hnew True by blast
          then have "id0 = loc" using fiC by blast
          then show ?thesis using True by simp
        next
          case False
          then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc)"
            using decl_env_not_i[OF 1(2)] hnew by blast
          then show ?thesis using fiC by blast
        qed
      qed

      have ptrfi:"\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e') \<and>
          accessStore l (Stack (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e') \<and> CompStoType t' t l' p)"
      proof (intro allI impI)
        fix t l p
        assume in1:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e') \<and>
            accessStore l (Stack (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) = Some (KStoptr p)"
        have inOld:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v)" using tsDecl in1 by simp
        have accOld:"accessStore l (Stack st) = Some (KStoptr p)" using tsDecl in1 by simp
        from fiPtr inOld accOld obtain t' l' where oldRan:
            "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v)"
            and comp:"CompStoType t' t l' p"
          by blast
        from oldRan obtain idp where idpDef:"Denvalue e\<^sub>v $$ idp = Some (type.Storage t', Storeloc l')"
          using fmlookup_ran_iff by fast
        have "Denvalue e' $$ idp = Some (type.Storage t', Storeloc l')"
          using decl_env_monotonic[OF 1(2)] idpDef by blast
        then have newRan:"(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e')"
          by (meson fmranI)
        show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e') \<and> CompStoType t' t l' p"
          using newRan comp by blast
      qed

      show ?thesis
        unfolding fullyInitialised_def using cfi mapfi locfi ptrfi by blast
    qed

    have IH1:"StateInvariant e' (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>) st' cd'" 
      using 9(1)[OF a10 a20 a30, of cd' "(mem', sck', e')" mem' "(sck', e')" sck' e', OF _ _ _ a40 a50 _ fiDec, of st'] 1(3) sgasDef by simp
    then have fiFinal:" fullyInitialised e' (Accounts st') (Stack st')" 
      unfolding StateInvariant_def by blast
    have sameAdd:"Address e' = Address e\<^sub>v" using 1(2) decl_env by simp
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e\<^sub>v (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next 
        show "safeContract (Accounts st') (Storage st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next 
        show "unique_locations (Denvalue e\<^sub>v)" using 9(2) unfolding TypeSafe_def by simp
      next
        have cpNew:"(\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
       (type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e') \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
       (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
          using IH1 unfolding StateInvariant_def TypeSafe_def compPointers_def by auto
        show "compPointers (Stack st') (Denvalue e\<^sub>v)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then obtain i1 i2 where iDefs:" (Denvalue e\<^sub>v) $$ i1 = Some (type.Storage tp1, l1)
                                  \<and>  (Denvalue e\<^sub>v) $$ i2 = Some (type.Storage tp2, l2)" by blast
          then have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and> (type.Storage tp2, l2) |\<in>| fmran (Denvalue e')" using a0 
            by (metis denLink fmlookup_ran_iff)
          then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
            using cpNew using a0 by blast
        qed
      next
        show "balanceTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next 
        have "envAddressesWellFormed e\<^sub>v" using 9(2) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e\<^sub>v)" and "addressFormat (Sender e\<^sub>v)" by simp+
      next 
        show "svalueTypes (Svalue e\<^sub>v)" using 9(2) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "lessThanTopLocs cd" using 9(2) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next 
        have oldTC:"typeCompat (Denvalue e') (Stack st') (Memory st') (Storage st' (Address e')) cd'"
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "typeCompat (Denvalue e\<^sub>v) (Stack st') (Memory st') (Storage st' (Address e\<^sub>v)) cd" 
          unfolding typeCompat_def 
        proof intros
          fix t l
          assume inDen:"(t, l) |\<in>| fmran (Denvalue e\<^sub>v)"
          then have inDenN:"(t, l) |\<in>| fmran (Denvalue e')"
            using denLink by (meson fmlookup_ran_iff)

          show "case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e\<^sub>v)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address e\<^sub>v)) | _ \<Rightarrow> False)"
          proof(cases l)
            case (Stackloc x1)
            then have oldTC':"(
             case accessStore x1 (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd' stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e')) | _ \<Rightarrow> False))"
              using oldTC unfolding typeCompat_def using inDenN by fastforce
            then show ?thesis 
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Stackloc by fastforce
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1')
                then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Some Stackloc by force
              next
                case (KCDptr x2)
                then obtain struct where structDef:"t = Calldata struct \<and> MCon struct cd' x2"
                  using oldTC' unfolding typeCompat_def using inDenN sameAdd Some Stackloc by (cases t; auto)
                then show ?thesis using tsDecl KCDptr Some Stackloc by simp
              next
                case (KMemptr x3)
                then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Some Stackloc by fastforce
              next
                case (KStoptr x4)
                then have "case t of type.Storage struct \<Rightarrow> SCon struct x4 (Storage st' (Address e')) | _ \<Rightarrow> False"
                  using oldTC' using inDenN sameAdd Some Stackloc by (auto split:option.splits type.splits stackvalue.splits denvalue.splits)
                then obtain struct where "t = type.Storage struct \<and> SCon struct x4 (Storage st' (Address e'))" by (cases t; auto)
                then show ?thesis using Some Stackloc KStoptr 
                  by (simp add: sameAdd)
              qed
            qed
          next
            case (Storeloc x2)
            then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd 
              by (metis (no_types, lifting) denvalue.simps(6) type.exhaust type.simps(17,18,19,20))
          qed
        qed
      next 
        show "denvalueTypeCorrectness e\<^sub>v (Stack st') (Memory st')" 
          unfolding denvalueTypeCorrectness_def
        proof intros
          fix t l ptr_loc sub_loc
          assume in1:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KMemptr ptr_loc)"
          then have in2:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e')" using denLink 
            by (meson fmlookup_ran_iff)
          then show " case t of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
            using IH1 unfolding StateInvariant_def TypeSafe_def denvalueTypeCorrectness_def
            using in1 in2 by blast
        qed
      next
        show "subPrefixStructuralConsistency (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by simp
      qed
    next 
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
          Contract e\<^sub>v = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
        using 9(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_fi) \<and>
          Contract e\<^sub>v = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e\<^sub>v)) = Some (atype.Contract c_fi)"
        using fiC atype_same "9.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
      proof (intro allI impI)
        fix t l p
        assume in1:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KStoptr p)"
        have inNew:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e')"
          using denLink in1 by (meson fmlookup_ran_iff)
        from fiFinal inNew in1 obtain t' l' where newPtr:
            "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e')"
            and comp:"CompStoType t' t l' p"
          unfolding fullyInitialised_def by blast
        from newPtr obtain iid where iidDef:"Denvalue e' $$ iid = Some (type.Storage t', Storeloc l')"
          using fmlookup_ran_iff by fast
        have oldLookup:"Denvalue e\<^sub>v $$ iid = Some (type.Storage t', Storeloc l')"
        proof (cases "iid = id0")
          case True
          have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
            using decl_env_storlocs_unchanged[OF 1(2)] by simp
          then show ?thesis using iidDef True by blast
        next
          case False
          then show ?thesis using decl_env_not_i[OF 1(2) iidDef] by blast
        qed
        have oldRan:"(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v)"
          using oldLookup by (meson fmranI)
        show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p"
          using oldRan comp by blast
      qed
      show "fullyInitialised e\<^sub>v (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next 
      fix locs t
      assume in1:"accessTypeStore locs (Memory st) = Some t"
      then have same:"accessTypeStore locs (Memory st) = accessTypeStore locs mem'"
        using tsDecl in1 by simp
      then have "accessTypeStore locs (mem') = Some t"
        using in1 by simp
      then show "accessTypeStore locs (Memory st') = Some t"
        using in1 IH1 unfolding StateInvariant_def by simp
    next 
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MPointer v)"
      then have same:"accessStore locs (Memory st) = accessStore locs mem'"
        using tsDecl  by simp
      then have "accessStore locs (mem') = Some (MPointer v)"
        using in1 by simp
      then show "\<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using in1 IH1 unfolding StateInvariant_def by simp
    next 
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MValue v)"
      then have same:"accessStore locs (Memory st) = accessStore locs mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      then have "accessStore locs (mem') = Some (MValue v)"
        using in1 by simp
      then show "\<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using in1 IH1 unfolding StateInvariant_def by simp
    next 
      fix i loc
      assume in1:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        and in2:" accessStore loc (Memory st) = None"
      moreover have "Toploc (Memory st) \<le> Toploc mem'" using tsDecl unfolding ncpOMemInDMem_def by simp
      then have same:"accessStore loc (Memory st) = accessStore loc mem'"
        using tsDecl  in1 by fastforce
      moreover have "i < Toploc (mem') \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using calculation in1 
        using \<open>Toploc (Memory st) \<le> Toploc mem'\<close> order.strict_trans2 by blast
      ultimately have "accessStore loc mem' = None \<longrightarrow>
        accessStore loc (Memory st') = None" using IH1 unfolding StateInvariant_def by simp
      then show "accessStore loc (Memory st') = None"  using in2 same by simp

    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" 
        using 1 IH1 unfolding StateInvariant_def using tsDecl by simp
    qed
  qed
next
  case (10 id0 tp ex' s e\<^sub>v cd st)
  show ?case 
  proof(cases rule:blockSome[OF 10(3)])
    case (1 v t g cd' mem' sck' e')
    have a10:"assert Gas (\<lambda>st. costs (BLOCK (id0, tp, Some ex') s) e\<^sub>v cd st < state.Gas st) st = Normal ((), st)" using 1 by simp
    obtain sgas where sgasDef:"sgas = state.Gas st - costs (BLOCK (id0, tp, Some ex') s) e\<^sub>v cd st" by simp
    then have a20:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, Some ex') s) e\<^sub>v cd st\<rparr>) st = Normal ((), (st\<lparr>Gas := sgas\<rparr> ))" by simp
    have a25:"toState (local.expr ex' e\<^sub>v cd) (st\<lparr>Gas := sgas\<rparr> ) = Normal ((v, t), (st\<lparr>Gas := g\<rparr>))" using 1 sgasDef by auto
    have a30:"option Err (\<lambda>st. decl id0 tp (Some (v, t)) False cd (Memory st) (Storage st (Address e\<^sub>v)) (cd, Memory st, Stack st, e\<^sub>v)) (st\<lparr>Gas := g\<rparr> )
            = Normal ((cd', mem', sck', e'), (st\<lparr>Gas := g\<rparr> )) " using 1 by simp
    have a40:"modify (\<lambda>st. st\<lparr>Stack := sck', Memory := mem'\<rparr>) (st\<lparr>Gas := g\<rparr>) = Normal ((), st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)"
      by simp

    have "\<exists>c ct dud.
       Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
       environment.Contract e\<^sub>v = c \<and>
       ep $$ c = Some (ct, dud) \<and>
       (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
       (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
       (\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
      using sgasDef 10(4) unfolding fullyInitialised_def by simp
    moreover have "fullyInitialised e\<^sub>v (Accounts (st\<lparr>Gas := sgas\<rparr>)) (Stack (st\<lparr>Gas := sgas\<rparr>))" 
      by (simp add: "10.prems"(3))
    moreover have tsSgas:"TypeSafe e\<^sub>v (Accounts (st\<lparr>Gas := sgas\<rparr>)) (Stack (st\<lparr>Gas := sgas\<rparr>)) (Memory (st\<lparr>Gas := sgas\<rparr>)) (Storage (st\<lparr>Gas := sgas\<rparr>)) cd" using 10(2) by simp
    ultimately have tcTV:"case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx)
    | Calldata struct \<Rightarrow>
        MCon struct cd (extractValueType v) \<and>
        (\<exists>xx. v = KCDptr xx) \<and>
        (\<exists>stloc tp'' p.
            (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := sgas\<rparr>)) = Some (KCDptr p) \<and>
            (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
    | type.Memory struct \<Rightarrow>
        MCon struct (Memory (st\<lparr>Gas := sgas\<rparr>)) (extractValueType v) \<and>
        (\<exists>xx. v = KMemptr xx) \<and>
        (\<exists>stloc tp'' p.
            (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
            accessStore stloc (Stack (st\<lparr>Gas := sgas\<rparr>)) = Some (KMemptr p) \<and>
            (tp'' = struct \<and> v = KMemptr p \<or>
             (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := sgas\<rparr>)) len arr struct p (extractValueType v))))
    | type.Storage struct \<Rightarrow>
        SCon struct (extractValueType v) (Storage (st\<lparr>Gas := sgas\<rparr>) (Address e\<^sub>v)) \<and>
        (\<exists>xx. v = KStoptr xx) \<and>
        (\<exists>stloc tp''.
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
            (tp'' = struct \<and> v = KStoptr stloc \<or>
             extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))" 
      using 1(2) exprTypeconInduct(3)[of ex' "e\<^sub>v" cd "st\<lparr>Gas := sgas\<rparr>" sgas v t g] sgasDef by blast
    then have tcTV':"case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v)
    | type.Memory struct \<Rightarrow> MCon struct (Memory (st\<lparr>Gas := g\<rparr>)) (extractValueType v)
    | type.Storage struct \<Rightarrow> SCon struct (extractValueType v) (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v))" 
      by (cases t, simp+)

    have tsDecl:"TypeSafe e' (Accounts (st\<lparr>Gas := g\<rparr>)) sck' mem' (Storage (st\<lparr>Gas := g\<rparr>)) cd' \<and>
    (\<not> False \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory (st\<lparr>Gas := g\<rparr>)) locs \<longrightarrow> MCon tp mem' locs) \<and>
     ncpDenvalueLimit e' e\<^sub>v sck' (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
     ncpOMemInDMem (Memory (st\<lparr>Gas := g\<rparr>)) mem' \<and> ncpElementsNoSubPref (Memory (st\<lparr>Gas := g\<rparr>)) mem' 
\<and> ncpNewSelfPoint (Memory (st\<lparr>Gas := g\<rparr>)) mem') \<and> Toploc (Memory (st\<lparr>Gas := g\<rparr>)) \<le> Toploc mem'"
    proof -
      have tsgas:"TypeSafe e\<^sub>v (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd"
        using 10(2) by simp
      have "ncpDenvalueLimit e\<^sub>v e\<^sub>v (Stack (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))" 
        unfolding ncpDenvalueLimit_def by auto
      moreover have "ncpOMemInDMem (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))" unfolding ncpOMemInDMem_def by auto
      moreover have "ncpElementsNoSubPref (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))"
        using ncpElementsNoSubPref_def ncpElementsNoSubPref_sameMem tsgas by blast
      moreover have "ncpNewSelfPoint (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))"
        unfolding ncpNewSelfPoint_def by auto
      ultimately have acc0:"\<not> False \<longrightarrow>
    (\<forall>locs tp. MCon tp (Memory (st\<lparr>Gas := g\<rparr>)) locs \<longrightarrow> MCon tp (Memory (st\<lparr>Gas := g\<rparr>)) locs) \<and>
    Toploc (Memory (st\<lparr>Gas := g\<rparr>)) \<le> Toploc (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
    ncpDenvalueLimit e\<^sub>v e\<^sub>v (Stack (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
    ncpOMemInDMem (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
    ncpElementsNoSubPref (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and> ncpNewSelfPoint (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))" by blast
      have acc1:"\<forall>struct.
     t = type.Memory struct \<longrightarrow>
     (\<exists>stloc tp'' p.
         (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
         accessStore stloc (Stack (st\<lparr>Gas := g\<rparr>)) = Some (KMemptr p) \<and>
         (tp'' = struct \<and> v = KMemptr p \<or>
          (\<exists>len arr. p \<noteq> extractValueType v \<and> tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len arr struct p (extractValueType v))))"
        using tcTV by (cases t, blast+; fastforce) 
      have acc2:"\<forall>struct.
     t = Calldata struct \<longrightarrow>
     (\<exists>stloc tp'' p.
         (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
         accessStore stloc (Stack (st\<lparr>Gas := g\<rparr>)) = Some (KCDptr p) \<and>
         (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. p \<noteq> extractValueType v \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))"
        using tcTV by (cases t, blast+; fastforce) 
      have acc3:"\<forall>struct.
       tp = type.Storage struct \<longrightarrow>
       (\<forall>locs tp. SCon tp locs (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v)) \<longrightarrow> SCon tp locs (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v))) \<and>
       (\<exists>stloc tp''.
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
        using tcTV
      proof(cases t)
        case (Value x1)
        then have "\<forall>struct. tp \<noteq> type.Storage struct " using 1(3)  decl_KValue_tp_match 
          by blast
        then show ?thesis by simp
      next
        case (Calldata x2)
        then have "\<forall>struct. tp \<noteq> type.Storage struct " using 1(3)  decl_Calldata_tp_match 
          by blast
        then show ?thesis by simp
      next
        case (Memory x3)
        then have "\<forall>struct. tp \<noteq> type.Storage struct " using 1(3)  decl_Memory_tp_match 
          by blast
        then show ?thesis by simp
      next
        case (Storage x4)
        then have sc:"SCon x4 (extractValueType v) (Storage (st\<lparr>Gas := sgas\<rparr>) (Address e\<^sub>v)) \<and>
              (\<exists>xx. v = KStoptr xx) \<and>
              (\<exists>stloc tp''.
                  (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                  tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v))" 
          using tcTV by auto
        have tt:"(\<exists>x t' t''. x4 = STArray x t' \<and> cps2mTypeCompatible (STArray x t') (MTArray x t'')\<and> tp = type.Memory (MTArray x t''))  \<or> tp = type.Storage x4" 
          using decl_Memory_tp_options[] 1(3) Storage by simp
        then show ?thesis 
        proof(cases "tp = type.Storage x4")
          case True
          moreover have "(\<forall>locs tp. SCon tp locs (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v)) \<longrightarrow> SCon tp locs (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v)))" by auto
          moreover have "(Stack (st\<lparr>Gas := sgas\<rparr>)) = (Stack (st\<lparr>Gas := g\<rparr>))" by auto
          then have "(\<exists>stloc tp''.
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v))" 
            using sc True Storage by presburger
          ultimately show ?thesis 
            using Storage tcTV by auto
        next
          case False
          then have "(\<exists>x t' t''. x4 = STArray x t' \<and> cps2mTypeCompatible (STArray x t') (MTArray x t'')\<and> tp = type.Memory (MTArray x t''))"
            using tt by simp
          then show ?thesis by auto
        qed
      qed
      have " TypeSafe e' (Accounts (st\<lparr>Gas := g\<rparr>)) sck' mem' (Storage (st\<lparr>Gas := g\<rparr>)) cd' \<and>
    (\<not> False \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory (st\<lparr>Gas := g\<rparr>)) locs \<longrightarrow> MCon tp mem' locs) \<and>
     Toploc (Memory (st\<lparr>Gas := g\<rparr>)) \<le> Toploc mem' \<and>
     ncpDenvalueLimit e' e\<^sub>v sck' (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
     ncpOMemInDMem (Memory (st\<lparr>Gas := g\<rparr>)) mem' \<and>
     ncpElementsNoSubPref (Memory (st\<lparr>Gas := g\<rparr>)) mem' \<and>
     ncpNewSelfPoint (Memory (st\<lparr>Gas := g\<rparr>)) mem')
    "
        using typeSafeDecl[OF tsgas tcTV' tsgas 1(3) acc0 acc1 acc2 ] acc3 by fastforce
      then show ?thesis by simp
    qed



    then have a50:"TypeSafe e' (Accounts (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>))
   (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) (Storage (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) cd'" 
      using tsDecl by simp

    have fiDec:" fullyInitialised e' (Accounts (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>))"
    proof -
      have sameStuff:"Address e' = Address e\<^sub>v \<and> Contract e' = Contract e\<^sub>v" using 1(3) decl_env by simp
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
          Contract e\<^sub>v = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
        using 10(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_fi) \<and>
          Contract e\<^sub>v = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
        by blast

      have cfi:"Type (Accounts (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>) (Address e')) = Some (atype.Contract c_fi) \<and>
          Contract e' = c_fi \<and> ep $$ c_fi = Some (ct_fi, dud_fi)"
        using fiC sameStuff by simp

      have mapfi:"\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id))"
      proof (intro allI)
        fix id v
        show "(ct_fi $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id))"
        proof
          assume hct:"ct_fi $$ id = Some (Var v)"
          then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id)"
            using fiC by blast
          then show "Denvalue e' $$ id = Some (type.Storage v, Storeloc id)"
            using decl_env_monotonic[OF 1(3)] by blast
        next
          assume hnew:"Denvalue e' $$ id = Some (type.Storage v, Storeloc id)"
          show "ct_fi $$ id = Some (Var v)"
          proof (cases "id = id0")
            case True
            have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
              using decl_env_storlocs_unchanged[OF 1(3)] by simp
            then have "Denvalue e\<^sub>v $$ id0 = Some (type.Storage v, Storeloc id0)"
              using hnew True by blast
            then show ?thesis using fiC True by blast
          next
            case False
            then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id)"
              using decl_env_not_i[OF 1(3)] hnew by blast
            then show ?thesis using fiC by blast
          qed
        qed
      qed

      have locfi:"\<forall>id v loc. Denvalue e' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      proof (intro allI impI)
        fix id v loc
        assume hnew:"Denvalue e' $$ id = Some (type.Storage v, Storeloc loc)"
        show "id = loc"
        proof (cases "id = id0")
          case True
          have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
            using decl_env_storlocs_unchanged[OF 1(3)] by simp
          then have "Denvalue e\<^sub>v $$ id0 = Some (type.Storage v, Storeloc loc)"
            using hnew True by blast
          then have "id0 = loc" using fiC by blast
          then show ?thesis using True by simp
        next
          case False
          then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc)"
            using decl_env_not_i[OF 1(3)] hnew by blast
          then show ?thesis using fiC by blast
        qed
      qed

      have ptrfi:"\<forall>tt l p.
          (type.Storage tt, Stackloc l) |\<in>| fmran (Denvalue e') \<and>
          accessStore l (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e') \<and> CompStoType t' tt l' p)"
      proof (intro allI impI)
        fix tt l p
        assume in1:"(type.Storage tt, Stackloc l) |\<in>| fmran (Denvalue e')\<and>accessStore l (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some (KStoptr p)"
        then obtain idd where iddDef: "Denvalue e' $$ idd = Some (type.Storage tt, Stackloc l)" by auto
        show " \<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e') \<and> CompStoType t' tt l' p"
        proof(cases "idd = id0")
          case True
          then have ddd:"Denvalue e' $$ id0 = Some (type.Storage tt, Stackloc l)" using iddDef by simp
          then show ?thesis
          proof(cases "Denvalue e\<^sub>v $$ id0")
            case None
            have ldef:"l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Stack (st\<lparr>Gas := g\<rparr>))))" using decl_stack_top[OF 1(3) None] iddDef True by simp
            then obtain p2 where p2Def:"Some (v, t) = Some (KStoptr p2, type.Storage tt)"
              using ddd True decl_storage_tp[OF 1(3) None, of tt ] by blast
            then have dcc:"decl id0 tp (Some (KStoptr p2, type.Storage tt)) False cd (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v))
       (cd, Memory (st\<lparr>Gas := g\<rparr>), Stack (st\<lparr>Gas := g\<rparr>), e\<^sub>v) =
      Some (cd', mem', sck', e')" using 1(3) True by simp
            then have "v = KStoptr p" using decl_stack_topLoc[OF dcc None] using in1 ldef p2Def by auto
            then have "(\<exists>stloc tp''.
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
            (tp'' = tt \<and> v = KStoptr stloc \<or> p \<noteq> stloc \<and> CompStoType tp'' tt stloc p))"
              using tcTV 1(3) p2Def by auto
            then show ?thesis using decl_env_monotonic[OF 1(3)]
              by (metis CompStoType_sameLocNdTyp stackvalue.inject(4) \<open>v = KStoptr p\<close> fmlookup_ran_iff)
          next
            case (Some a)
            then have "e\<^sub>v = e' \<and> sck' = Stack st" using  decl_some_same[OF 1(3)] by auto
            then have oldIn:"(type.Storage tt, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p)"
              using in1 by simp
            then show ?thesis using fiPtr 
              using \<open>e\<^sub>v = e' \<and> sck' = Stack st\<close> by blast
          qed
        next
          case False
          then have oldD:"Denvalue e\<^sub>v $$ idd = Some (type.Storage tt, Stackloc l)"
            using iddDef in1 1 decl_env_not_i[OF 1(3)] by blast
          then show ?thesis
          proof(cases "l = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Stack st))")
            case True
            then show ?thesis
              by (metis "10.prems"(1) True oldD snd_conv stackLocs_imp_NotDen TypeSafe_def)
          next
            case False
            then have "accessStore l (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = accessStore l (Stack (st))"
              using decl_stack_change[OF 1(3)] by simp
            then have oldAcc:"accessStore l (Stack st) = Some (KStoptr p)" using in1 by simp
            from fiPtr oldD oldAcc obtain t' l' where t'Def: "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' tt l' p"
              by (meson fmranI)
            then have "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e')"
              using decl_env_monotonic[OF 1(3)] by (meson fmlookup_ran_iff)
            then show ?thesis using t'Def by auto
          qed
        qed
      qed
      show ?thesis
        unfolding fullyInitialised_def using cfi mapfi locfi ptrfi by blast
    qed
    have sameCD:"cd = cd'" using decl_env_false_same_cd[OF 1(3)] by simp
    have IH1:" StateInvariant e' (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>) st' cd'" 
      using 10(1)[OF a10 a20 a25 _ a30, of  cd' "(mem', sck', e')" mem' "(sck', e')" sck' e', OF _ _ _ _ a40 a50 _ fiDec, of st'] 1(4) sgasDef by simp

    have denLink:"\<forall>ii x. Denvalue e\<^sub>v $$ ii = Some x \<longrightarrow> Denvalue e' $$ ii = Some x" using decl_env_monotonic[OF 1(3)] by auto
    have sameAdd:"Address e' = Address e\<^sub>v"using 1(3) decl_env by simp
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e\<^sub>v (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next 
        show "safeContract (Accounts st') (Storage st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next 
        show "unique_locations (Denvalue e\<^sub>v)" using 10(2) unfolding TypeSafe_def by simp
      next
        have cpNew:"(\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
       (type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e') \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
       (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
          using IH1 unfolding StateInvariant_def TypeSafe_def compPointers_def by auto
        show "compPointers (Stack st') (Denvalue e\<^sub>v)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then obtain i1 i2 where iDefs:" (Denvalue e\<^sub>v) $$ i1 = Some (type.Storage tp1, l1)
                                  \<and>  (Denvalue e\<^sub>v) $$ i2 = Some (type.Storage tp2, l2)" by blast
          then have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and> (type.Storage tp2, l2) |\<in>| fmran (Denvalue e')" using a0 
            by (metis denLink fmlookup_ran_iff)
          then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True" 
            using cpNew using a0 by blast
        qed
      next
        show "balanceTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next 
        have "envAddressesWellFormed e\<^sub>v" using 10(2) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e\<^sub>v)" and "addressFormat (Sender e\<^sub>v)" by simp+
      next 
        show "svalueTypes (Svalue e\<^sub>v)" using 10(2) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "lessThanTopLocs cd" using 10(2) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next 
        have oldTC:"typeCompat (Denvalue e') (Stack st') (Memory st') (Storage st' (Address e')) cd'"
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "typeCompat (Denvalue e\<^sub>v) (Stack st') (Memory st') (Storage st' (Address e\<^sub>v)) cd" 
          unfolding typeCompat_def 
        proof intros
          fix t l
          assume inDen:"(t, l) |\<in>| fmran (Denvalue e\<^sub>v)"
          then have inDenN:"(t, l) |\<in>| fmran (Denvalue e')"
            using denLink by (meson fmlookup_ran_iff)

          show "case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e\<^sub>v)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address e\<^sub>v)) | _ \<Rightarrow> False)"
          proof(cases l)
            case (Stackloc x1)
            then have oldTC':"(
             case accessStore x1 (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd' stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e')) | _ \<Rightarrow> False))"
              using oldTC unfolding typeCompat_def using inDenN by fastforce
            then show ?thesis 
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Stackloc by fastforce
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1')
                then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Some Stackloc by force
              next
                case (KCDptr x2)
                then obtain struct where structDef:"t = Calldata struct \<and> MCon struct cd' x2"
                  using oldTC' unfolding typeCompat_def using inDenN sameAdd Some Stackloc by (cases t; auto)
                then show ?thesis using tsDecl KCDptr Some Stackloc sameCD by simp
              next
                case (KMemptr x3)
                then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Some Stackloc by fastforce
              next
                case (KStoptr x4)
                then have "case t of type.Storage struct \<Rightarrow> SCon struct x4 (Storage st' (Address e')) | _ \<Rightarrow> False"
                  using oldTC' using inDenN sameAdd Some Stackloc by (auto split:option.splits type.splits stackvalue.splits denvalue.splits)
                then obtain struct where "t = type.Storage struct \<and> SCon struct x4 (Storage st' (Address e'))" by (cases t; auto)
                then show ?thesis using Some Stackloc KStoptr 
                  by (simp add: sameAdd)
              qed
            qed
          next
            case (Storeloc x2)
            then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd 
              by (metis (no_types, lifting) denvalue.simps(6) type.exhaust type.simps(17,18,19,20))
          qed
        qed
      next 

        show "denvalueTypeCorrectness e\<^sub>v (Stack st') (Memory st')" 
          unfolding denvalueTypeCorrectness_def
        proof intros
          fix t l ptr_loc sub_loc
          assume in1:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KMemptr ptr_loc)"
          then have in2:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e')" using denLink 
            by (meson fmlookup_ran_iff)
          then show "(case t of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr
        | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val))"
            using IH1 unfolding StateInvariant_def TypeSafe_def denvalueTypeCorrectness_def
            using in1 in2 by blast
        qed
      next
        show "subPrefixStructuralConsistency (Memory st')"  using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "SomeValSomeTyp (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      qed

    next 
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
          Contract e\<^sub>v = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
        using 10(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_fi) \<and>
          Contract e\<^sub>v = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e\<^sub>v)) = Some (atype.Contract c_fi)"
        using fiC atype_same "10.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have fiFinal:"fullyInitialised e' (Accounts st') (Stack st')"
        using IH1 unfolding StateInvariant_def by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
      proof (intro allI impI)
        fix t l p
        assume in1:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KStoptr p)"
        have inNew:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e')"
          using denLink in1 by (meson fmlookup_ran_iff)
        from fiFinal inNew in1 obtain t' l' where newPtr:
            "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e')"
            and comp:"CompStoType t' t l' p"
          unfolding fullyInitialised_def by blast
        from newPtr obtain iid where iidDef:"Denvalue e' $$ iid = Some (type.Storage t', Storeloc l')"
          using fmlookup_ran_iff by fast
        have oldLookup:"Denvalue e\<^sub>v $$ iid = Some (type.Storage t', Storeloc l')"
        proof (cases "iid = id0")
          case True
          have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
            using decl_env_storlocs_unchanged[OF 1(3)] by simp
          then show ?thesis using iidDef True by blast
        next
          case False
          then show ?thesis using decl_env_not_i[OF 1(3) iidDef] by blast
        qed
        have oldRan:"(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v)"
          using oldLookup by (meson fmranI)
        show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p"
          using oldRan comp by blast
      qed
      show "fullyInitialised e\<^sub>v (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next 
      fix locs t
      assume in1:"accessTypeStore locs (Memory st) = Some t"
      then have "\<exists>v. accessStore locs (Memory st) = Some v"
        using 10(2) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      then obtain i where idef:"i < Toploc (Memory st) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        using 10(2) unfolding TypeSafe_def lessThanTopLocs_def by blast
      then have same:"accessTypeStore locs (Memory st) = accessTypeStore locs mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      then have "accessTypeStore locs (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some t"
        using in1 by simp
      then show "accessTypeStore locs (Memory st') = Some t"
        using in1 IH1 unfolding StateInvariant_def by simp
    next 
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MPointer v)"
      then obtain i where idef:"i < Toploc (Memory st) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        using 10(2) unfolding TypeSafe_def lessThanTopLocs_def by blast
      then have same:"accessStore locs (Memory st) = accessStore locs mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      then have "accessStore locs (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some (MPointer v)"
        using in1 by simp
      then show "\<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using in1 IH1 unfolding StateInvariant_def by simp
    next 
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MValue v)"
      then obtain i where idef:"i < Toploc (Memory st) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        using 10(2) unfolding TypeSafe_def lessThanTopLocs_def by blast
      then have same:"accessStore locs (Memory st) = accessStore locs mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      then have "accessStore locs (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some (MValue v)"
        using in1 by simp
      then show "\<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using in1 IH1 unfolding StateInvariant_def by simp
    next 
      fix i loc
      assume in1:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        and in2:" accessStore loc (Memory st) = None"
      then have same:"accessStore loc (Memory st) = accessStore loc mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      moreover have "Toploc (Memory st) \<le> Toploc mem'" using tsDecl unfolding ncpOMemInDMem_def by simp
      moreover have "i < Toploc (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using calculation in1 by auto
      ultimately have "accessStore loc (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = None \<longrightarrow>
        accessStore loc (Memory st') = None" using IH1 unfolding StateInvariant_def by simp
      then show "accessStore loc (Memory st') = None"  using in2 same by simp

    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')" 
        using 1 IH1 unfolding StateInvariant_def using tsDecl by simp
    qed
  qed
next
  case (11 i xe val e cd st)
  show ?case
  proof(cases rule:new[OF 11(3)])
    case (1 v t g ct cn fb e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' acc st'' v')
    then have a10:"assert Gas (\<lambda>st. costs (NEW i xe val) e cd st < state.Gas st) st = Normal ((), st)" by simp
    let ?sgas = "st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>" 
    have a20:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) st = Normal ((), ?sgas)" by simp
    let ?newAdd = "hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts ?sgas (Address e))))"
    have notSame:"(Address e) \<noteq> ?newAdd" 
      by (metis hash_version_inequality)
    have formatAdd:"addressFormat (hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e)))))" 
      unfolding addressFormat_def typeCon.simps
    proof - 
      have "CHR ''.'' \<notin> set (literal.explode (Address e))" 
        using 11(2) unfolding TypeSafe_def addressFormat_def typeCon.simps checkAddress_def by blast
      then have "CHR ''.'' \<notin> set (literal.explode (STR ''-'' + Address e))" 
        by (simp add: Literal.rep_eq add_Literal_assoc)
      moreover have "CHR ''.'' \<notin> set (literal.explode (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e)))))"
        using ShowLNatDot by blast

      ultimately have "CHR ''.'' \<notin> set 
                      (literal.explode ((ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e)))) 
                      + (STR ''-'' + Address e)))" 
        by (simp add: plus_literal.rep_eq)
      then show "checkAddress (hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e)))))"
        unfolding checkAddress_def hash_version_def by blast
    qed
    let ?updState = "st\<lparr>Gas := g, Accounts := (Accounts st)((?newAdd) := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>), 
                                                Storage := (Storage st)((?newAdd) := {$$})\<rparr>" 
    obtain uus where uusDef:"uus = ?updState" by blast
    have sameUpd:"Memory ?updState = Memory st \<and> Stack ?updState = Stack st" by auto
    have a30:"applyf (\<lambda>st. hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts st (Address e))))) (?sgas) 
                    = Normal (hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts ?sgas (Address e)))) , (?sgas))" using 1 by auto
    have a40:" assert Err (\<lambda>st. Type (Accounts st ?newAdd) = None) (?sgas) 
                          = Normal ((), ?sgas)" using 1  by simp
    have a50:"toState (local.expr val e cd) (?sgas) = Normal ((KValue v, Value t), st\<lparr>Gas := g\<rparr>)" using 1  by auto
    have a60:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) | (KValue v, _) \<Rightarrow> throw Err 
                  | (_, b) \<Rightarrow> throw Err) (st\<lparr>Gas := g\<rparr>) = Normal ((v,t), st\<lparr>Gas := g\<rparr>)" using 1 by simp
    have a65:"option Err (\<lambda>_. convert t (TUInt b256) v) (st\<lparr>Gas := g\<rparr>) = Normal (v', st\<lparr>Gas := g\<rparr>)" using 1 by simp
    have a70:"option Err (\<lambda>_. ep $$ i) (st\<lparr>Gas := g\<rparr>) = Normal ((ct, cn, fb), st\<lparr>Gas := g\<rparr>)" using 1 by simp
    obtain folded where a80: "folded = ffold_init ct (emptyEnv (?newAdd) i (Address e) v') (fmdom ct)"
      using 1 by blast
    have a90:"toState (local.load True (fst cn) xe folded emptyTypedStore emptyStore emptyTypedStore e cd) ?updState = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), ?updState\<lparr>Gas := g'\<rparr>)"
      using 1  a80  by simp


    have a110:" option Err (\<lambda>st. transfer (Address e) ?newAdd v' (Accounts st)) (?updState\<lparr>Gas:=g'\<rparr>) = Normal (acc, ?updState\<lparr>Gas:=g'\<rparr>)"
      using 1   by auto
    have a120:"applyf (\<lambda>st. (Stack st, Memory st)) (?updState\<lparr>Gas:=g'\<rparr>) = Normal ((Stack st, Memory st), ?updState\<lparr>Gas:=g'\<rparr>)"
      by simp
    have a130:"modify (\<lambda>st'. st'\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (?updState \<lparr>Gas:=g'\<rparr>)
              = Normal ((), ?updState\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)"
      by simp

    have BtUus:"balanceTypes (Accounts uus)"
      unfolding balanceTypes_def
    proof intros
      fix adv
      show "typeCon (TUInt b256) (Bal (Accounts uus adv)) "
      proof(cases "adv = ?newAdd")
        case True
        then have " (Bal (Accounts uus adv)) =  (ShowL\<^sub>i\<^sub>n\<^sub>t 0)" using uusDef by simp
        then show ?thesis unfolding typeCon.simps checkUInt_def 
          using Read_ShowL_id by presburger
      next
        case False
        then have "(Bal (Accounts uus adv)) = (Bal (Accounts st adv))" using uusDef by simp
        then show ?thesis using 11(2) unfolding TypeSafe_def balanceTypes_def by simp
      qed
    qed

    have svv':"svalueTypes v'" unfolding svalueTypes_def
      using 1(4,3) 11(2) 11(4)   
      using exprTypeconInduct(3)[of ]
        typeSafeConvert[of t v "(TUInt b256)"] convertSame by fastforce

    have btACC:"balanceTypes acc"  unfolding balanceTypes_def
    proof - 
      have old:"balanceTypes (Accounts (uus))" using BtUus  by simp
      have accExp:"(case subBalance (Address e) v' (Accounts (uus)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance ?newAdd v' x) = Some acc" 
        using 1(7) uusDef unfolding transfer_def by simp
      have v'TC: "typeCon (TUInt b256) v'" 
        using  svv' unfolding svalueTypes_def by blast

      show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
      proof(cases "?newAdd = (Address e)")
        case same:True
        then show ?thesis using notSame by simp
      next
        case notSame:False
        show ?thesis 
        proof
          fix adv'
          show "typeCon (TUInt b256) (Bal (acc adv')) "
          proof(cases "adv' = (Address e)")
            case True

            then have tco:"typeCon (TUInt b256) (Bal ((Accounts uus) adv'))"
              using True old accExp balanceTypes_def by blast
            have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (uus) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))" 
              using transfer_subRead[OF _ _ v'TC ] 1(7) uusDef True notSame tco by auto
            then show ?thesis using True 
              using "1"(7,3) Read_ShowL_id tco checkUInt_def transfer_val1 transfer_val2
              by (smt (verit, ccfv_SIG) notSame typeCon.simps(2) transfer_sub transfer_val3)

          next
            case False
            then show ?thesis 
            proof(cases "adv' = ?newAdd")
              case True
              then have tco:"typeCon (TUInt b256) (Bal ((Accounts uus) ?newAdd))"
                using True old accExp balanceTypes_def by simp
              then have "Bal (acc ?newAdd) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (uus) ?newAdd))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))" 
                using transfer_addRead[OF 1(7)_ v'TC  ] 1(3) notSame uusDef by auto
              moreover have "typeCon (TUInt b256) (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (uus) ?newAdd))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))" 
                using "1"(7,3) Read_ShowL_id tco checkUInt_def transfer_val1 transfer_val2 transfer_val3 
                by (smt (verit, best) b256.rep_eq calculation notSame typeCon.simps(2) transfer_add)
              ultimately show ?thesis using True by simp
            next
              case f2:False
              show ?thesis using transfer_eq[OF 1(7) False f2] old 
                using balanceTypes_def uusDef by simp
            qed
          qed
        qed
      qed
    qed

    obtain ii where iiDef: "i = Contract ii" using 1 
      by (metis Environment.select_convs(2))
    have epA:"ep $$ Contract ii = Some (ct, cn, fb)" using 1 iiDef by blast
    have atUus:"AddressTypes (Accounts uus)"
      unfolding AddressTypes_def
    proof intros
      fix adv
      show "case Type (Accounts uus adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep "
      proof(cases "Type (Accounts uus adv)")
        case None
        then show ?thesis by simp
      next
        case (Some a)
        then show ?thesis
        proof(cases a)
          case EOA
          then show ?thesis using Some by simp
        next
          case (Contract x2)
          then show ?thesis
          proof(cases "adv = ?newAdd")
            case True
            then have "Type (Accounts uus adv) = Some (atype.Contract i)" using uusDef by auto
            then have "i = x2" using Some Contract by simp
            moreover have "ep $$ i = Some (ct, cn, fb)" using epA iiDef by simp
            moreover have "addressFormat adv" using iiDef epA formatAdd True by simp
            ultimately show ?thesis using Some Contract
              by (metis Option.option.simps(5) atype.simps(5) fmlookup_dom_iff)
          next
            case False
            then have "(Accounts uus adv) = Accounts st adv" using uusDef by simp
            then show ?thesis using 11(2) unfolding TypeSafe_def AddressTypes_def using Some Contract
              by metis
          qed
        qed
      qed
    qed
    have scUus:"safeContract (Accounts uus) (Storage uus)"
      unfolding safeContract_def
    proof intros
      fix e' ct' dud' i' tp
      assume in1:"Type (Accounts uus (Address (e'::environment))) = Some (atype.Contract (Contract e')) \<and>
                 ep $$ Contract (e'::environment) = Some (ct', dud') \<and>
                 ct' $$ i' = Some (Var tp)"
      show "SCon tp i' (Storage uus (Address e'))"
      proof(cases "Address e' = ?newAdd")
        case True
        then have "(Storage uus (Address e')) = {$$}" using uusDef by simp
        then show ?thesis
        proof(induction tp arbitrary:i')
          case (STArray x1 tp)
          then show ?case by simp
        next
          case (STMap x1 tp)
          then show ?case by simp
        next
          case (STValue x)
          have "typeCon x (ival x)" by (simp add: ivalTypeCon)
          then show ?case unfolding SCon.simps accessStorage_def using STValue by simp
        qed
      next
        case False
        then have "Storage uus (Address e') = Storage st (Address e')"
          using uusDef by simp
        moreover have "Type (Accounts st (Address e')) = Some (atype.Contract (Contract e'))"
          using False in1 uusDef by simp
        moreover have "ep $$ Contract (e'::environment) = Some (ct', dud')"
          using in1 by simp
        moreover have "ct' $$ i' = Some (Var tp)"
          using in1 by simp
        moreover have "safeContract (Accounts st) (Storage st)"
          using 11(2) unfolding TypeSafe_def by simp
        ultimately show ?thesis
          unfolding safeContract_def 
          by presburger
      qed
    qed
    have cohUus:"Type (Accounts uus ?newAdd) = Some (atype.Contract (Contract ii))"
      using uusDef iiDef by simp
    have TSInit:"\<forall>x y. TypeSafe folded (Accounts uus) 
                  emptyStore emptyTypedStore (Storage uus) emptyTypedStore \<and>
       (Denvalue folded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue folded $$ x = Some y \<longrightarrow> (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
    proof - 
      have "safeContract (Accounts uus) (Storage uus)" using scUus by simp
      moreover have "balanceTypes (Accounts uus)" using BtUus by simp
      moreover have "svalueTypes v'" 
      proof - 
        have "typeCon t (extractValueType (KValue v))"
          using 1(4,3) 11(2) 11(4) 
          using exprTypeconInduct(3)[of val e cd "(st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>)" "(state.Gas (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>))" "KValue v" "Value t" g]
            typeSafeConvert[of t v "(TUInt b256)"] convertSame by simp
        then show ?thesis unfolding svalueTypes_def using 1(3) a65 
          by (metis "1"(4) convertSame extractValueType.simps(1) typeSafeConvert)
      qed
      moreover have "lessThanTopLocs emptyStore"  using emptyTopLocs by simp
      moreover have "ep $$ Contract ii = Some (ct, cn, fb)" using epA by simp
      moreover have "addressFormat (?newAdd)" using formatAdd by simp
      moreover have "addressFormat (Address e)" using 11(2) unfolding TypeSafe_def by simp
      moreover have "AddressTypes (Accounts uus)" using atUus by simp
      moreover have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      moreover have "SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessTypeStore_def accessStore_def emptyTypedStore_def by auto
      moreover have "Type (Accounts uus ?newAdd) = Some (atype.Contract (Contract ii))" using cohUus by simp

      ultimately show "\<forall>x y. TypeSafe folded (Accounts uus)
                  emptyStore emptyTypedStore (Storage uus) emptyTypedStore \<and>
       (Denvalue folded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue folded $$ x = Some y \<longrightarrow> (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))" 
        using a80 unfolding ffold_init_def 
        using ffoldInitTypeSafe[of "Accounts uus" "Storage uus" v' emptyTypedStore ii ct "(cn, fb)" ?newAdd "Address e" "fmdom ct"] 
        using iiDef typedEmptyTopLocs by blast
    qed
    have a140:"TypeSafe e\<^sub>l (Accounts (uus\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
                            (Stack (uus\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory :=m\<^sub>l\<rparr>)) 
                            (Memory (uus\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
                            (Storage (uus\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) 
                            cd\<^sub>l \<and> fullyInitialised e\<^sub>l acc k\<^sub>l" 
    proof - 

      have aa1:"load True (fst cn) xe folded emptyTypedStore emptyStore emptyTypedStore e cd ?updState g =
    Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g')" using 1(6) a80 unfolding ffold_init_def by simp
      moreover have tsE:"TypeSafe e (Accounts uus) (Stack uus) (Memory uus) (Storage uus) cd" 
        unfolding TypeSafe_def 
      proof intros
        show "AddressTypes (Accounts uus)" using atUus by simp
      next 
        show "safeContract (Accounts uus) (Storage uus)" using scUus by simp
      next 
        show "unique_locations (Denvalue e)" using 11(2) unfolding TypeSafe_def by simp
      next

        show "compPointers (Stack uus) (Denvalue e)" 
          using 11(2) unfolding TypeSafe_def 
          using sameUpd uusDef by argo
      next
        show "balanceTypes (Accounts uus)" using BtUus by simp
      next 
        have "envAddressesWellFormed e" using 11(2) sameUpd uusDef unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next 
        show "svalueTypes (Svalue e)" using 11(2) sameUpd uusDef unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack uus)" using 11(2) sameUpd uusDef unfolding TypeSafe_def by auto
      next
        show "lessThanTopLocs cd" using 11(2) sameUpd uusDef unfolding TypeSafe_def by auto
      next
        show "lessThanTopLocs (Memory uus)" using 11(2) sameUpd uusDef unfolding TypeSafe_def by auto
      next 
        have tcOld:"typeCompat (Denvalue e) (Stack st) (Memory st) (Storage st (Address e)) cd"
          using 11(2) unfolding TypeSafe_def by blast
        show "typeCompat (Denvalue e) (Stack uus) (Memory uus) (Storage uus (Address e)) cd" 
          unfolding typeCompat_def 
        proof intros
          fix t l
          assume inDen:"(t, l) |\<in>| fmran (Denvalue e)"

          show "case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack uus) of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory uus) stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage uus (Address e)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage uus (Address e)) | _ \<Rightarrow> False)"
          proof(cases l)
            case (Stackloc x1)
            have tcOld':"case accessStore x1 (Stack st) of None \<Rightarrow> False 
                         | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                         | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                         | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st) stloc | _ \<Rightarrow> False)
                         | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st (Address e)) | _ \<Rightarrow> False)"
              using sameUpd Stackloc inDen tcOld unfolding typeCompat_def by force
            then show ?thesis 
            proof(cases "accessStore x1 (Stack uus)")
              case None
              then show ?thesis using tcOld' sameUpd uusDef by simp
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1')
                then show ?thesis using tcOld' sameUpd uusDef Some Stackloc by simp
              next
                case (KCDptr x2)

                then show ?thesis using tcOld' sameUpd uusDef Some Stackloc by simp
              next
                case (KMemptr x3)
                then show ?thesis using tcOld' sameUpd uusDef Some Stackloc by (cases t; fastforce)
              next
                case (KStoptr x4)

                then show ?thesis
                proof(cases "Address e = ?newAdd")
                  case True
                  then have empt:"Storage uus (Address e) = {$$}" using uusDef by simp
                  then obtain struct where struct_def:"t = type.Storage struct"
                    using tcOld' sameUpd uusDef Some Stackloc KStoptr by (cases t; fastforce)
                  have "SCon struct x4 (Storage uus (Address e))"
                  proof(induction struct arbitrary:x4)
                    case (STArray x1 tp)
                    then show ?case by simp
                  next
                    case (STMap x1 tp)
                    then show ?case by simp
                  next
                    case (STValue x)
                    have "typeCon x (ival x)" by (simp add: ivalTypeCon)
                    then show ?case unfolding SCon.simps accessStorage_def using STValue empt by simp
                  qed
                  then show ?thesis using tcOld' sameUpd uusDef Some Stackloc KStoptr struct_def by simp
                next
                  case False
                  then have "Storage uus (Address e) = Storage st (Address e)" using uusDef by simp
                  then show ?thesis using tcOld' sameUpd uusDef Some Stackloc KStoptr by (cases t; fastforce)
                qed
              qed
            qed
          next
            case (Storeloc x2)
            then show ?thesis 
            proof(cases "Address e = ?newAdd")
              case True
              then have empt:"Storage uus (Address e) = {$$}" using uusDef by simp
              then obtain struct where struct_def:"t = type.Storage struct"
                using  sameUpd uusDef Storeloc tcOld inDen unfolding typeCompat_def by (cases t; fastforce)
              have "SCon struct x2 (Storage uus (Address e))"
              proof(induction struct arbitrary:x2)
                case (STArray x1 tp)
                then show ?case by simp
              next
                case (STMap x1 tp)
                then show ?case by simp
              next
                case (STValue x)
                have "typeCon x (ival x)" by (simp add: ivalTypeCon)
                then show ?case unfolding SCon.simps accessStorage_def using STValue empt by simp
              qed
              then show ?thesis using  tcOld inDen unfolding typeCompat_def using sameUpd uusDef Storeloc struct_def by simp
            next
              case False
              then have "Storage uus (Address e) = Storage st (Address e)" using uusDef by simp
              then show ?thesis using tcOld inDen unfolding typeCompat_def using sameUpd uusDef Storeloc by (cases t; fastforce)
            qed
          qed
        qed
      next 
        show "denvalueTypeCorrectness e (Stack uus) (Memory uus)" using uusDef using 11(2) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory uus)" using uusDef using 11(2) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory uus)" using uusDef using 11(2) unfolding TypeSafe_def by simp
      qed

      moreover have "TypeSafe folded (Accounts uus) emptyStore emptyTypedStore (Storage uus) emptyTypedStore" using TSInit 
        by blast

      moreover have a6:"fullyInitialised e (Accounts uus) (Stack uus)"
      proof -
        have fiOld:"
          \<exists>c ct dud.
            Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
            Contract e = c \<and>
            ep $$ c = Some (ct, dud) \<and>
            (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
            (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
            (\<forall>t l p.
                (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
                (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
          using 11(4) unfolding fullyInitialised_def by blast
        then obtain c_fi ct_fi dud_fi where fiC:"
            Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
            Contract e = c_fi \<and>
            ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
            (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
            (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
          and fiPtr:"\<forall>t l p.
                (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
                (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
          by blast
        have typeNew:"Type (Accounts uus (Address e)) = Some (atype.Contract c_fi)"
          using fiC uusDef notSame by simp
        have ptrNew:"\<forall>t l p.
            (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack uus) = Some (KStoptr p) \<longrightarrow>
            (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
          using fiPtr sameUpd uusDef by simp
        show ?thesis
          unfolding fullyInitialised_def using fiC typeNew ptrNew by blast
      qed

      have contractL:"Contract folded = Contract ii" using a80 iiDef by simp
     
      have ctd:"ep $$ Contract folded = Some (ct, cn, fb)" using a50 contractL 1 a10 iiDef by metis
      then have fi2:"\<forall>id v. (Denvalue folded $$ id = Some (type.Storage v, Storeloc id)) = (ct $$ id = Some (Var v))"
        using a80 unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct ?newAdd i "(Address e)" v' folded] by auto
      moreover have "fullyInitialised e (Accounts ?updState) (Stack ?updState)" using a6 uusDef by blast
      moreover have fiFolded:"fullyInitialised folded (Accounts uus) emptyStore"
      proof -
        obtain c_fi where cfi:
          "Type (Accounts uus (Address folded)) = Some (atype.Contract c_fi) \<and> Contract folded = c_fi"
          using a80 11(4) uusDef unfolding fullyInitialised_def by simp
        obtain dud_fi where epfi:"ep $$ Contract folded = Some (ct, dud_fi)"
          using ctd by blast
        have mapfi:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue folded $$ id = Some (type.Storage v, Storeloc id))"
          using fi2 by blast
        have locfi:"\<forall>id v loc. Denvalue folded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
        proof (intro allI impI)
          fix id v loc
          assume h:"Denvalue folded $$ id = Some (type.Storage v, Storeloc loc)"
          have hloc:"Denvalue folded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
            using TSInit by blast
          then show "id = loc" using h by simp
        qed
        have ptrfi:"\<forall>t l p.
            (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue folded) \<and> accessStore l emptyStore = Some (KStoptr p) \<longrightarrow>
            (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue folded) \<and> CompStoType t' t l' p)"
          by (simp add: accessStore_def emptyStore_def)
        show ?thesis
          unfolding fullyInitialised_def using cfi epfi mapfi locfi ptrfi by blast
      qed

      ultimately have exprTS:" TypeSafe e\<^sub>l (Accounts ?updState) k\<^sub>l m\<^sub>l (Storage ?updState) cd\<^sub>l \<and>
    fullyInitialised e\<^sub>l (Accounts ?updState) k\<^sub>l \<and> fullyInitialised e\<^sub>l
     (Accounts ?updState) k\<^sub>l" 
        using  exprTypeconInduct(4)[of True "fst cn" xe folded emptyTypedStore emptyStore
            emptyTypedStore e cd ?updState g e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'] uusDef by blast

      have cc1:"TypeSafe e\<^sub>l (acc) (k\<^sub>l) (m\<^sub>l) (Storage (uus)) cd\<^sub>l" 
        unfolding TypeSafe_def 
      proof intros
        show "AddressTypes acc" unfolding AddressTypes_def using tsE unfolding TypeSafe_def AddressTypes_def using 1(7) transfer_type_same uusDef by simp
      next 
        have trUus:"transfer (Address e) ?newAdd v' (Accounts uus) = Some acc"
          using 1(7) uusDef by simp
        have scUus':"safeContract (Accounts uus) (Storage uus)"
          using tsE unfolding TypeSafe_def by simp
        show "safeContract acc (state.Storage uus)"
        proof (unfold safeContract_def, intro allI impI)
          fix env ct' dud' i' tp
          assume in1:"Type (acc (Address (env::environment))) = Some (atype.Contract (Contract env)) \<and>
                     ep $$ Contract env = Some (ct', dud') \<and>
                     ct' $$ i' = Some (Var tp)"
          have typeOld:"Type (Accounts uus (Address env)) = Some (atype.Contract (Contract env))"
            using in1 transfer_type_same[OF trUus, of "Address env"] by simp
          show "SCon tp i' (state.Storage uus (Address env))"
            using scUus' in1 typeOld unfolding safeContract_def by blast
        qed
      next 
        show "unique_locations (Denvalue e\<^sub>l)" using exprTS unfolding TypeSafe_def by blast
      next 
        show "compPointers k\<^sub>l (Denvalue e\<^sub>l)" using exprTS unfolding TypeSafe_def by blast
      next 
        show "balanceTypes acc" using btACC by auto
      next
        have "envAddressesWellFormed e\<^sub>l" using exprTS unfolding TypeSafe_def by blast
        then show "addressFormat (Address e\<^sub>l)" and "addressFormat (Sender e\<^sub>l)" by simp+
      next
        show "svalueTypes (Svalue e\<^sub>l)" using exprTS unfolding TypeSafe_def by blast
      next
        show " lessThanTopLocs k\<^sub>l" using exprTS unfolding TypeSafe_def by blast
      next
        show " lessThanTopLocs cd\<^sub>l" using exprTS unfolding TypeSafe_def by blast
      next
        show "lessThanTopLocs m\<^sub>l" using exprTS unfolding TypeSafe_def by blast
      next 
        show "typeCompat (Denvalue e\<^sub>l) k\<^sub>l m\<^sub>l (Storage uus (Address e\<^sub>l)) cd\<^sub>l" using uusDef exprTS unfolding TypeSafe_def by blast
      next 
        show "denvalueTypeCorrectness e\<^sub>l k\<^sub>l m\<^sub>l" using TypeSafe_def exprTS by blast
      next
        show "subPrefixStructuralConsistency m\<^sub>l" using TypeSafe_def exprTS by blast
      next
        show "SomeValSomeTyp m\<^sub>l" using TypeSafe_def exprTS by blast
      qed

      have elFolded:"Address e\<^sub>l = Address folded \<and> Contract e\<^sub>l = Contract folded" using 1 a80 
        using  msel_ssel_expr_load_rexp_gas(4) aa1 by blast
      have cc2:"fullyInitialised e\<^sub>l acc k\<^sub>l"
      proof -
        have fiOld:"
          \<exists>c ct dud.
            Type (Accounts ?updState (Address e\<^sub>l)) = Some (atype.Contract c) \<and>
            Contract e\<^sub>l = c \<and>
            ep $$ c = Some (ct, dud) \<and>
            (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc id))) \<and>
            (\<forall>id v loc. Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
            (\<forall>t l p.
                (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore l k\<^sub>l = Some (KStoptr p) \<longrightarrow>
                (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p))"
          using exprTS unfolding fullyInitialised_def by blast
        then obtain c_fi ct_fi dud_fi where fiC:"
            Type (Accounts ?updState (Address e\<^sub>l)) = Some (atype.Contract c_fi) \<and>
            Contract e\<^sub>l = c_fi \<and>
            ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
            (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc id))) \<and>
            (\<forall>id v loc. Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
          and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore l k\<^sub>l = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p)"
          by blast
        have typeNew:"Type (acc (Address e\<^sub>l)) = Some (atype.Contract c_fi)"
          using fiC 1(7) transfer_type_same uusDef by simp
        show ?thesis
          unfolding fullyInitialised_def using fiC fiPtr typeNew by blast
      qed

      then show "TypeSafe e\<^sub>l (Accounts (uus\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (uus\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
     (Memory (uus\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Storage (uus\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) cd\<^sub>l
\<and> fullyInitialised e\<^sub>l acc k\<^sub>l"
        using cc1 by auto
    qed
    have a140':"TypeSafe e\<^sub>l (Accounts (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
   (Memory (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Storage (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) cd\<^sub>l" 
      using a140 uusDef by auto
    have "st\<lparr>Gas := g', Accounts := (Accounts st)((?newAdd) := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>), 
                                                Storage := (Storage st)((?newAdd) := {$$})\<rparr>
= (?updState\<lparr>Gas := g'\<rparr>)" by simp
    then have a18Exp:"local.stmt (snd cn) e\<^sub>l cd\<^sub>l
     (?updState\<lparr>Gas := g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) = Normal ((), st'')" using 1(8) by argo
    have a150:"fullyInitialised e\<^sub>l acc k\<^sub>l" using a140 by simp


    have IH1:" StateInvariant e\<^sub>l (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) st'' cd\<^sub>l"
      using 11(1)[OF a10 a20 a30  a40 a50 a60 _ a65  a70 _ _ _ a80 a90 _  _ _ a110 a120 _ a130 a140' a18Exp] a30 1(8) a150  by simp

    have st'Final:"st' = incrementAccountContracts (Address e) (st''\<lparr>Stack := Stack st, Memory := Memory st\<rparr>)" using 1 by blast

    then have sameStores:"Memory st = Memory st' \<and> Stack st = Stack st'" using 1 by simp
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        have old:"AddressTypes (Accounts st'')" using IH1 unfolding StateInvariant_def TypeSafe_def by auto
        show "AddressTypes (Accounts st')" using old unfolding AddressTypes_def using  st'Final by fastforce
        
      next 
        have scOld:"safeContract (Accounts st'') (Storage st'')"
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "safeContract (Accounts st') (Storage st')"
        proof (unfold safeContract_def, intro allI impI)
          fix env ct' dud' i' tp
          assume in1:"Type (Accounts st' (Address (env::environment))) = Some (atype.Contract (Contract env)) \<and>
                     ep $$ Contract env = Some (ct', dud') \<and> ct' $$ i' = Some (Var tp)"
          have typeOld:"Type (Accounts st'' (Address env)) = Some (atype.Contract (Contract env))"
            using in1 st'Final by simp
          have stoEq:"Storage st' (Address env) = Storage st'' (Address env)"
            using st'Final by simp
          have "SCon tp i' (Storage st'' (Address env))"
            using scOld in1 typeOld unfolding safeContract_def by blast
          then show "SCon tp i' (Storage st' (Address env))"
            using stoEq by simp
        qed
      next 
        show "unique_locations (Denvalue e)" using 11(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "compPointers (Stack st') (Denvalue e)" using 11(2) st'Final unfolding StateInvariant_def TypeSafe_def by simp
      next
        show "balanceTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def balanceTypes_def using  st'Final sameStores  by fastforce
      next 
        have "envAddressesWellFormed e" using "11.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next 
        show "svalueTypes (Svalue e)" using "11.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 11(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "lessThanTopLocs cd" using "11.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 11(2) unfolding TypeSafe_def using sameStores by simp
      next 
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd" 
          unfolding typeCompat_def 
        proof intros
          fix t l
          assume inDen:"(t, l) |\<in>| fmran (Denvalue e)" 

          have acc:"(\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep)"
            using 11(2) unfolding TypeSafe_def AddressTypes_def by blast
          obtain cOld where cOldDef:"Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and> Contract e = cOld" 
            using 11(4) unfolding fullyInitialised_def by simp
          then obtain ctO dudO where ctoDef: "ep $$ Contract e = Some (ctO, dudO)" using acc  
            using "11.prems"(3) typesafe_base.fullyInitialised_def typesafe_base_axioms by blast
          have storageFinal:"Storage st' = Storage st''" using 1 by auto
          have scSt'':"safeContract (Accounts st'') (Storage st'')"
            using IH1 unfolding StateInvariant_def TypeSafe_def by blast
          have trUus:"transfer (Address e) ?newAdd v' (Accounts uus) = Some acc"
            using 1(7) uusDef by simp
          have typeStE:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using cOldDef by simp
          have typeUusE:"Type (Accounts uus (Address e)) = Some (atype.Contract (Contract e))"
            using typeStE notSame uusDef by simp
          have typeAccE:"Type (acc (Address e)) = Some (atype.Contract (Contract e))"
            using transfer_type_same[OF trUus, of "Address e"] typeUusE by simp
          let ?stInit = "?updState\<lparr>Gas := g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>"
          have typeInitE:"Type (Accounts ?stInit (Address e))
                        = Some (atype.Contract (Contract e))"
            using typeAccE by simp
          have typeSt''E:"Type (Accounts st'' (Address e)) = Some (atype.Contract (Contract e))"
          proof (rule atype_same)
            show "local.stmt (snd cn) e\<^sub>l cd\<^sub>l ?stInit = Normal ((), st'')"
              using 1(8) 
              using a18Exp by argo
            show "Type (Accounts ?stInit (Address e)) = Some (atype.Contract (Contract e))"
              using typeInitE .
          qed

          show "case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc (Stack st') of None \<Rightarrow> False 
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False))
           | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc (Storage st' (Address e)) | _ \<Rightarrow> False)"
          proof(cases l)
            case (Stackloc x1)

            then show ?thesis 
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using 11(2) unfolding TypeSafe_def typeCompat_def using inDen sameStores Stackloc by fastforce
            next
              case (Some a)
              then show ?thesis 
              proof(cases a)
                case (KValue x1')
                then show ?thesis using 11(2) unfolding TypeSafe_def typeCompat_def using inDen sameStores Stackloc Some by fastforce
              next
                case (KCDptr x2)
                then show ?thesis using 11(2) unfolding TypeSafe_def typeCompat_def using inDen sameStores Stackloc Some by fastforce
              next
                case (KMemptr x3)
                then show ?thesis using 11(2) unfolding TypeSafe_def typeCompat_def using inDen sameStores Stackloc Some by (cases t; fastforce)
              next
                case (KStoptr x4)
                then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                  using Some 1 by auto
                then obtain struct where structDef: "t = type.Storage struct" 
                  using 11(2) unfolding TypeSafe_def typeCompat_def using inDen Some KStoptr Stackloc 
                  by (cases t, force,  fastforce, fastforce, auto)
                obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)" 
                  using 11(4) using accO inDen unfolding fullyInitialised_def 
                  using Stackloc structDef by blast
                then have "SCon tprnt lprnt (Storage st'' (Address e))"
                proof -
                  from tprntDef have inRan: "(type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e)" by simp
                  then obtain k where kDef: "Denvalue e $$ k = Some (type.Storage tprnt, Storeloc lprnt)"
                    using fmlookup_ran_iff by auto
                  from 11(4) obtain ct_x dud_x where
                    epX: "ep $$ (Contract e) = Some (ct_x, dud_x)" and
                    bijX: "\<forall>id v. ct_x $$ id = Some (Var v) \<longleftrightarrow> Denvalue e $$ id = Some (type.Storage v, Storeloc id)" and
                    uniqX: "\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
                    unfolding fullyInitialised_def by blast
                  from kDef uniqX have "k = lprnt" by auto
                  then have "Denvalue e $$ lprnt = Some (type.Storage tprnt, Storeloc lprnt)" using kDef by simp
                  then have "ct_x $$ lprnt = Some (Var tprnt)" using bijX by auto
                  moreover from epX ctoDef have "ct_x = ctO" by auto
                  ultimately have "ctO $$ lprnt = Some (Var tprnt)" by simp
                  then show ?thesis
                    using ctoDef scSt'' typeSt''E unfolding safeContract_def by blast
                qed
                  
                then have "SCon struct x4 (Storage st'' (Address e))"
                  using tprntDef SCon_imps_sublocs by blast
                then show ?thesis using Stackloc Some KStoptr structDef storageFinal by simp
              qed
            qed
          next
            case (Storeloc x2)
            then obtain struct where structDef: "t = type.Storage struct" 
              using 11(2) inDen unfolding TypeSafe_def typeCompat_def by (cases t,fastforce+)

            then have "SCon struct x2 (Storage st'' (Address e))"
            proof -
              from inDen Storeloc structDef have inRan: "(type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue e)" by simp
              then obtain k where kDef: "Denvalue e $$ k = Some (type.Storage struct, Storeloc x2)"
                using fmlookup_ran_iff by auto
              from 11(4) obtain ct_x dud_x where
                epX: "ep $$ (Contract e) = Some (ct_x, dud_x)" and
                bijX: "\<forall>id v. ct_x $$ id = Some (Var v) \<longleftrightarrow> Denvalue e $$ id = Some (type.Storage v, Storeloc id)" and
                uniqX: "\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
                unfolding fullyInitialised_def by blast
              from kDef uniqX have "k = x2" by auto
              then have "Denvalue e $$ x2 = Some (type.Storage struct, Storeloc x2)" using kDef by simp
              then have "ct_x $$ x2 = Some (Var struct)" using bijX by auto
              moreover from epX ctoDef have "ct_x = ctO" by auto
              ultimately have "ctO $$ x2 = Some (Var struct)" by simp
              then show ?thesis
                using ctoDef scSt'' typeSt''E unfolding safeContract_def by blast
            qed
            then show ?thesis using Storeloc structDef 
              by (simp add: storageFinal)
          qed
        qed
      next 
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 1(9) 11(2) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 1(9) 11(2) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using 1(9) 11(2) unfolding TypeSafe_def by simp
      qed
    next 
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 11(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using IH1 fiC atype_same[OF 1(8)] st'Final unfolding StateInvariant_def 
        using "11.prems"(2) atype_same by presburger
      have ptrNew:"\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
      proof (intro allI impI)
        fix t l p
        assume in1:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p)"
        have "accessStore l (Stack st) = Some (KStoptr p)" using in1 sameStores by simp
        then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p"
          using fiPtr in1 by blast
      qed
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC typeNew ptrNew by blast

    next 
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using sameStores by auto
    next 
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using sameStores by auto
    next 
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using sameStores by auto
    next 
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None" 
        using sameStores by auto
    next 
      show "Toploc (Memory st) \<le> Toploc (Memory st')"
        using sameStores by auto
    qed
  qed  
qed

end


end
