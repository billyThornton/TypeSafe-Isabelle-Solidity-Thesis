theory TypeSafe_Memory_Copies
  imports TypeSafe_Support TypeSafe_Hashing_Subs  TypeSafe_Mem_Sto_Comp

begin


subsubsection \<open>Consistency Preservation Under Disjoint Locations\<close>
text \<open>
If two locations @{text destl} and @{text destl'} are disjoint — neither is a sub-prefix of
the other under @{text LSubPrefL2} — then an update to @{text destl} cannot affect
@{text MCon} at @{text destl'}.  This lemma is the foundation for all sub-prefix preservation
arguments: it shows that the @{text MCon} invariant is inherited at unrelated locations.
\<close>

lemma MCon_preserved_under_disjoint_location:
  assumes "(\<not>LSubPrefL2 destl'  destl) \<and> \<not>LSubPrefL2 destl  destl' "
  shows  "(\<forall>l l'. TypedStoSubpref l destl' t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)
          \<and> cps2mTypeCompatible t t'
          \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')
          \<and> MCon t' v' destl' \<longrightarrow> MCon t' v'' destl'" using assms 
proof (induction t' arbitrary:destl' t)
  case (MTArray x1 t')
  show ?case 
  proof intros
    assume " (\<forall>l l'. TypedStoSubpref l destl' t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and>
    cps2mTypeCompatible t (MTArray x1 t') \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and> MCon (MTArray x1 t') v' destl'"
    then have a10:"(\<forall>l l'. TypedStoSubpref l destl' t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
      and a20:"cps2mTypeCompatible t (MTArray x1 t')"
      and a30:"(\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')"
      and a40:"MCon (MTArray x1 t') v' destl'" by blast+
    show "MCon (MTArray x1 t') v'' destl'"
    proof(cases "x1>0")
      case True
      have "\<forall>i<x1.
             case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case t' of MTValue typ \<Rightarrow> MCon t' v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
              | Some (MPointer loc2) \<Rightarrow> (case t' of MTArray len' arr' \<Rightarrow> MCon t' v'' loc2 | MTValue Types \<Rightarrow> False)" 
      proof (intros)
        fix i assume iLess:"i<x1"
        then show " case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case t' of MTValue typ \<Rightarrow> MCon t' v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
              | Some (MPointer loc2) \<Rightarrow> (case t' of MTArray len' arr' \<Rightarrow> MCon t' v'' loc2 | MTValue Types \<Rightarrow> False)"
        proof(cases t')
          case mtr:(MTArray x11 x12)
          then obtain t''' where tdef:"t = STArray x1 (STArray x11 t''')" using a20 mtr cps2mTypeCompatible.simps True 
            by (metis stypes.exhaust)
          then have a45:"cps2mTypeCompatible (STArray x11 t''') (MTArray x11 x12)" using a20 by (simp add: mtr)

          have b100:"\<not> LSubPrefL2 (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl" using Mutual_NonSub_SpecificNonSub MTArray by auto
          then have "\<not> LSubPrefL2 destl (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using Not_Sub_More_Specific MTArray by auto
          then have a50:"(\<forall>l l'. TypedStoSubpref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STArray x11 t''') \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and>
                      cps2mTypeCompatible (STArray x11 t''') (MTArray x11 x12) \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') 
                      \<and> MCon (MTArray x11 x12) v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow>
                      MCon (MTArray x11 x12) v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
            using MTArray(1)[of "(hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(STArray x11 t''')"] b100 mtr by blast
          have a55:"\<forall>l l'. TypedStoSubpref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STArray x11 t''') \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l" 
            using a10 stoMoreSpecificTypedSubpref[of destl' x1 "(STArray x11 t''')" v'] iLess using tdef by blast 
          then have a60:"accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using b100 a30 by blast
          then show ?thesis 
          proof(cases "accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
            case None
            then show ?thesis using a10 iLess a40 by auto
          next
            case (Some a)
            then show ?thesis 
            proof(cases a)
              case (MValue x1)
              then show ?thesis using a40 iLess mtr Some by auto
            next
              case (MPointer x2')
              then have x2'def:"x2' = (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a55 Some 
                using iLess TypedStoSubpref.simps(2) a10 tdef by blast
              have "\<forall>i<x1.
             case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case t' of MTArray n MTypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t' v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case t' of MTArray len' arr' \<Rightarrow> MCon t' v' loc2 | MTValue Types \<Rightarrow> False)" 
                using  MCon.simps(2)[of x1 t' v' destl']
                using a40 by auto
              then have "MCon t' v' (x2')" using a40 iLess Some mtr MPointer tdef MCon.simps(2)[of x1 t' v' destl'] True by fastforce
              then have "MCon t' v'' x2'" using a50 b100 a55 a30 a45 tdef  x2'def mtr by blast
              then show ?thesis  using Some MPointer mtr a60 by auto
            qed
          qed
        next
          case (MTValue x2)
          then have  tdef:"t = STArray x1 (STValue x2)" using a20 cps2mTypeCompatible.simps True 
            by (metis stypes.exhaust)
          then have a45:"cps2mTypeCompatible (STValue x2) (MTValue x2)" using a20 by (simp add: MTValue)
          have b100:"\<not> LSubPrefL2 (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl" using Mutual_NonSub_SpecificNonSub MTArray by auto
          then have "\<not> LSubPrefL2 destl (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using Not_Sub_More_Specific MTArray by auto
          then have a50:"(\<forall>l l'. TypedStoSubpref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STValue x2) 
                    \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) 
                    \<and> cps2mTypeCompatible (STValue x2) (MTValue x2) 
                    \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') 
                      \<and> MCon (MTValue x2) v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow>
                      MCon (MTValue x2) v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))
            " using MTArray(1)[of "(hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b100  using MTValue by force
          then have a60:"accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using b100 a30 by simp
          then show ?thesis
          proof(cases "accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
            case None
            then show ?thesis using iLess a40 by auto
          next
            case (Some a)
            then show ?thesis 
            proof(cases a)
              case (MValue x1)
              then have "MCon t' v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a40 iLess Some MTValue by auto
              then have "MCon t' v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a50 b100 a60 a30 Some MValue MTValue by auto
              then show ?thesis using Some MValue MTValue a60 by auto
            next
              case (MPointer x2')
              then show ?thesis using a40 iLess MTValue Some by auto
            qed

          qed
        qed
      qed
      moreover have "(\<exists>p. accessStore destl' v'' = Some (MPointer p)) \<or> accessStore destl' v'' = None" 
        using MTArray.prems True a10 a20 a30 a40 by force
      ultimately show ?thesis using MCon.simps(2)[of x1 t' v'' destl']
        by (simp add: True)
    next
      case False
      then show ?thesis using a40 by simp
    qed
  qed
next
  case (MTValue x)
  show ?case 
  proof intros
    assume *:"(\<forall>l l'. TypedStoSubpref l destl' t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and>
    cps2mTypeCompatible t (MTValue x) \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and> MCon (MTValue x) v' destl'"
    then have "accessStore destl' v' = accessStore destl' v''" using MTValue by simp
    then show "MCon (MTValue x) v'' destl'"  using * by simp
  qed
qed

subsubsection \<open>Destination Root Preservation\<close>
text \<open>
The top-level entry at the destination root location @{text destl} is unchanged after any
recursive copy step.  Concretely, @{text "accessStore destl"} and @{text "accessTypeStore destl"}
return the same value before and after the call.

@{text cpm2m} works by iterating @{text iter'} over each array index: at each step it calls
@{text cpm2mrec} on one index, and @{text cpm2mrec} may recursively call @{text iter'} for
nested arrays.  To support the mutual induction the following root-preservation lemmas are
established first, covering all three copy directions: @{text cpm2mrec} (memory to memory),
@{text cps2mrec} (storage to memory), and @{text cpm2srec} (memory to storage).
\<close>

text \<open>@{text updateTypedStore} only writes to the single location @{text destl}, so any
@{text destl'} with @{text "destl' \<noteq> destl"} is unchanged in both value and type stores.\<close>

lemma updateTypedStore_neq_loc:
  "destl' \<noteq> destl
   \<Longrightarrow> accessStore destl' (updateTypedStore destl v t m) = accessStore destl' m
     \<and> accessTypeStore destl' (updateTypedStore destl v t m) = accessTypeStore destl' m"
  unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
  by auto

lemma cpm2mrec_preserves_dest_root_both:
  shows "(cpm2mrec (hash ls suffixa) (hash ld suffix') t ms m = Some v'')
    \<longrightarrow> accessStore ld v'' = accessStore ld m
      \<and> accessTypeStore ld v'' = accessTypeStore ld m"
proof (induction t arbitrary: m v'' suffixa suffix' ls)
  case (MTArray x1 t)
  show ?case
  proof
    assume run:"cpm2mrec (hash ls suffixa) (hash ld suffix') (MTArray x1 t) ms m = Some v''"
    then obtain l where src_ptr:"accessStore (hash ls suffixa) ms = Some (MPointer l)"
      using cpm2mrec.simps(1) by (auto split: if_splits option.splits memoryvalue.splits)
    have expanded:"Some v'' =
        (let m0 = updateTypedStore (hash ld suffix') (MPointer (hash ld suffix')) (MTArray x1 t) m
         in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m0 x1)"
      using run src_ptr
      by (simp add: cpm2mrec.simps(1) split: if_splits option.splits memoryvalue.splits)
    then obtain m0 where m0_def:
      "m0 = updateTypedStore (hash ld suffix') (MPointer (hash ld suffix')) (MTArray x1 t) m" by simp
    have init:
      "accessStore ld m0 = accessStore ld m \<and> accessTypeStore ld m0 = accessTypeStore ld m"
      using m0_def hash_inequality updateTypedStore_neq_loc 
      by metis
    have iter_run:
      "iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m0 x1 = Some v''"
      using expanded m0_def 
      by presburger
    have step:
      "\<And>i m1 m2.
        accessStore ld m1 = accessStore ld m \<and> accessTypeStore ld m1 = accessTypeStore ld m
        \<Longrightarrow> cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m1 = Some m2
        \<Longrightarrow> accessStore ld m2 = accessStore ld m \<and> accessTypeStore ld m2 = accessTypeStore ld m"
    proof -
      fix i m1 m2
      assume inv:
        "accessStore ld m1 = accessStore ld m \<and> accessTypeStore ld m1 = accessTypeStore ld m"
      assume rec:
        "cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m1 = Some m2"
      have rec':
        "cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (hash suffix' (ShowL\<^sub>n\<^sub>a\<^sub>t i))) t ms m1 = Some m2"
        using hash_suffixes_associative rec by simp
      then have
        "accessStore ld m2 = accessStore ld m1 \<and> accessTypeStore ld m2 = accessTypeStore ld m1"
        using MTArray.IH by blast
      with inv show
        "accessStore ld m2 = accessStore ld m \<and> accessTypeStore ld m2 = accessTypeStore ld m"
        by auto
    qed
    show "accessStore ld v'' = accessStore ld m \<and> accessTypeStore ld v'' = accessTypeStore ld m"
      using iter'_invariant[
        where I = "\<lambda>m1. accessStore ld m1 = accessStore ld m \<and> accessTypeStore ld m1 = accessTypeStore ld m",
        OF iter_run init step] 
      by simp
  qed
next
  case (MTValue x)
  show ?case
  proof
    assume run:"cpm2mrec (hash ls suffixa) (hash ld suffix') (MTValue x) ms m = Some v''"
    then obtain v where src_val:"accessStore (hash ls suffixa) ms = Some (MValue v)"
      using cpm2mrec.simps(2) by (auto split: option.splits memoryvalue.splits)
    have "v'' = updateTypedStore (hash ld suffix') (MValue v) (MTValue x) m"
      using run src_val cpm2mrec.simps(2)[of "hash ls suffixa" "hash ld suffix'" x ms m] by simp
    then show "accessStore ld v'' = accessStore ld m \<and> accessTypeStore ld v'' = accessTypeStore ld m"
      using hash_inequality updateTypedStore_neq_loc by metis
  qed
qed

lemma cpm2mrec_preserves_dest_root:
  shows "(cpm2mrec (hash ls suffixa) (hash ld suffix') t ms m = Some v'')\<longrightarrow> accessStore ld v'' = accessStore ld m"
  using cpm2mrec_preserves_dest_root_both by blast

lemma cpm2mrec_preserves_dest_root_typed:
  shows "(cpm2mrec (hash ls suffixa) (hash ld suffix') t ms m = Some v'')\<longrightarrow> accessTypeStore ld v'' = accessTypeStore ld m"
  using cpm2mrec_preserves_dest_root_both by blast

lemma cps2mrec_preserves_dest_root_both:
  shows "(cps2mrec (hash ls suffixa) (hash ld suffix') t ms m' = Some v'')
    \<longrightarrow> accessStore ld v'' = accessStore ld m'
      \<and> accessTypeStore ld v'' = accessTypeStore ld m'"
proof (induction t arbitrary: m' v'' suffixa suffix' ls)
  case (STArray x1 t)
  show ?case
  proof
    assume run: "cps2mrec (hash ls suffixa) (hash ld suffix') (STArray x1 t) ms m' = Some v''"
    have expanded: "Some v'' =
      (let m0 = updateTypedStore (hash ld suffix') (MPointer (hash ld suffix'))
         (MTArray x1 (case cps2mTypeConvert t of Some t' \<Rightarrow> t' | None \<Rightarrow> MTValue TBool)) m'
       in iter' (\<lambda>i. cps2mrec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m0 x1)"
      using run by (simp add: cps2mrec.simps(1) split: option.splits memoryvalue.splits)
    then obtain m0 where m0_def:
      "m0 = updateTypedStore (hash ld suffix') (MPointer (hash ld suffix'))
        (MTArray x1 (case cps2mTypeConvert t of Some t' \<Rightarrow> t' | None \<Rightarrow> MTValue TBool)) m'" by simp
    have init:
      "accessStore ld m0 = accessStore ld m' \<and> accessTypeStore ld m0 = accessTypeStore ld m'"
      using m0_def hash_inequality updateTypedStore_neq_loc by metis
    have iter_run:
      "iter' (\<lambda>i. cps2mrec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m0 x1 = Some v''"
      using expanded m0_def 
      by presburger
    have step:
      "\<And>i m1 m2.
        accessStore ld m1 = accessStore ld m' \<and> accessTypeStore ld m1 = accessTypeStore ld m'
        \<Longrightarrow> cps2mrec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m1 = Some m2
        \<Longrightarrow> accessStore ld m2 = accessStore ld m' \<and> accessTypeStore ld m2 = accessTypeStore ld m'"
    proof -
      fix i m1 m2
      assume inv:
        "accessStore ld m1 = accessStore ld m' \<and> accessTypeStore ld m1 = accessTypeStore ld m'"
      assume rec:
        "cps2mrec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m1 = Some m2"
      have rec':
        "cps2mrec (hash ls (hash suffixa (ShowL\<^sub>n\<^sub>a\<^sub>t i))) (hash ld (hash suffix' (ShowL\<^sub>n\<^sub>a\<^sub>t i))) t ms m1 = Some m2"
        using hash_suffixes_associative rec by simp
      then have
        "accessStore ld m2 = accessStore ld m1 \<and> accessTypeStore ld m2 = accessTypeStore ld m1"
        using STArray.IH by blast
      with inv show
        "accessStore ld m2 = accessStore ld m' \<and> accessTypeStore ld m2 = accessTypeStore ld m'"
        by auto
    qed
    show "accessStore ld v'' = accessStore ld m' \<and> accessTypeStore ld v'' = accessTypeStore ld m'"
      using iter'_invariant[
        where I = "\<lambda>m1. accessStore ld m1 = accessStore ld m' \<and> accessTypeStore ld m1 = accessTypeStore ld m'",
        OF iter_run init step]
      by simp
  qed
next
  case (STValue x)
  show ?case
  proof
    assume run: "cps2mrec (hash ls suffixa) (hash ld suffix') (STValue x) ms m' = Some v''"
    then obtain v where src_val: "accessStorage x (hash ls suffixa) ms = v"
      using cps2mrec.simps(2)[of "hash ls suffixa" "hash ld suffix'" x ms m']
      by (auto split: option.splits memoryvalue.splits)
    have "v'' = updateTypedStore (hash ld suffix') (MValue v) (MTValue x) m'"
      using run src_val cps2mrec.simps(2)[of "hash ls suffixa" "hash ld suffix'" x ms m'] by simp
    then show "accessStore ld v'' = accessStore ld m' \<and> accessTypeStore ld v'' = accessTypeStore ld m'"
      using hash_inequality updateTypedStore_neq_loc by metis
  qed
next
  case (STMap k v)
  then show ?case using cps2mrec.simps(3) by auto
qed

lemma cps2mrec_preserves_dest_root:
  shows "(cps2mrec (hash ls suffixa) (hash ld suffix') t ms m' = Some v'')\<longrightarrow> accessStore ld v'' = accessStore ld m'"
  using cps2mrec_preserves_dest_root_both by blast

lemma cps2mrec_preserves_dest_root_typed:
  shows "(cps2mrec (hash ls suffixa) (hash ld suffix') t ms m' = Some v'')\<longrightarrow> accessTypeStore ld v'' = accessTypeStore ld m'"
  using cps2mrec_preserves_dest_root_both by blast

lemma cpm2srec_preserves_dest_root:
  shows "\<forall>t'. (cpm2srec (hash ls suffixa) (hash ld suffix') t ms m' = Some v'')\<longrightarrow> accessStorage t' ld v'' = accessStorage t' ld m'"
proof intros
  fix t'
  assume **:"cpm2srec (hash ls suffixa) (hash ld suffix') t ms m' = Some v''" 
  then show "accessStorage t' ld v'' = accessStorage t' ld m'" 
  proof (induction t arbitrary: m' v'' suffixa suffix' ls)
    case (MTArray x1 t)
    then obtain l where ldef:"accessStore (hash ls suffixa) ms = Some (MPointer l)" unfolding  cpm2srec.simps by (simp split:option.splits memoryvalue.splits)
    then have a60:"Some v'' =  iter' (\<lambda>i. cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m' x1" 
      using MTArray unfolding cpm2srec.simps(1) by (simp split:option.splits memoryvalue.splits)
    show ?case
    proof(induction rule: iter'_induct[OF _ _ a60[symmetric]])
      case (1 v')
      then have "v' = m'" using iter'.simps by simp
      then show ?case  by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m' x = Some v'"
          and a20:"accessStorage t' ld v' = accessStorage t' ld m'"
          and a30:"cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
      then show ?case  
        using MTArray.IH hash_suffixes_associative by auto
    qed
  next
    case (MTValue x)
    then have "hash ld suffix' \<noteq> ld" 
      by (simp add: hash_inequality)
    then show ?case using MTValue unfolding cpm2srec.simps accessStorage_def by (auto split:option.splits memoryvalue.splits)
  qed
qed

subsubsection \<open>Single-Step Change for Recursive Copy Functions\<close>
text \<open>
Each call to @{text cpm2mrec} or @{text cps2mrec} (a single recursive copy step) only modifies
locations that are sub-prefixes of the destination index being written.  Any location whose
suffix differs from the destination suffix is left unchanged.

These lemmas underpin the iterated single-change results: by showing the invariant holds at
every recursive step, it can be propagated across the full @{text iter'} loop.  The
@{text iterIndexMinOne} helper establishes that a successful iteration of length @{text x}
implies the existence of an intermediate result after @{text x} steps.
\<close>

lemma cpm2mrecSingleChange:
  assumes " Some v'' = cpm2mrec (hash ls suffixa) (hash ld suffixb) t ms a  "
  shows "((\<forall>x'. suffix' \<noteq> hash suffixb x')
          \<and> suffix' \<noteq> suffixb
          \<longrightarrow> accessStore (hash ld suffix') a = accessStore (hash ld suffix') v'')"
proof intros
  fix suffix'
  assume **:" (\<forall>x'. suffix' \<noteq> hash suffixb x') \<and> suffix' \<noteq> suffixb" 
  show "accessStore (hash ld suffix') a = accessStore (hash ld suffix') v''" using ** assms
  proof(induction t arbitrary:a v'' suffixb ls suffixa suffix')
    case (MTArray x1 t)
    then obtain l where  a40:"accessStore (hash ls suffixa) ms = Some (MPointer l)" using cpm2mrec.simps(1) by (auto split:if_splits option.splits memoryvalue.splits) 
    have a60:"Some v'' =
            (let m = updateTypedStore (hash ld suffixb) (MPointer (hash ld suffixb))
                  (MTArray x1 t) a
                 in iter' (\<lambda>i'. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (hash (hash ld suffixb) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) t ms) m x1)" 
      using a40 MTArray cpm2mrec.simps(1)[of "hash ls suffixa" "hash ld suffixb" x1 t ms a] by (simp split:option.splits memoryvalue.splits)
    then obtain m' where a50:" m'= updateTypedStore (hash ld suffixb) (MPointer (hash ld suffixb))
                  (MTArray x1 t) a" by simp
    then have a55:"accessStore ld a = accessStore ld m'" unfolding updateTypedStore_def updateTypeStore_def accessStore_def updateStore_def using hash_inequality by simp
    then have a70:"Some v'' =iter' (\<lambda>i'. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (hash (hash ld suffixb) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) t ms) m' x1" using a60 a50 by presburger
    show ?case
    proof(induction rule: iter'_induct[OF _ _ a70[symmetric]])
      case (1 v')      
      then have "v' = m'" using iter'.simps by simp
      then show ?case using hash_never_equal_sufix MTArray(2) a50  unfolding updateTypedStore_def updateTypeStore_def accessStore_def updateStore_def by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i'. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (hash (hash ld suffixb)(ShowL\<^sub>n\<^sub>a\<^sub>t i')) t ms) m' x = Some v'"
          and a20:"accessStore (hash ld suffix') a = accessStore (hash ld suffix') v'"
          and a30:"cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash ld suffixb) (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
      have a40:"cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (hash suffixb (ShowL\<^sub>n\<^sub>a\<^sub>t x))) t ms v' = Some v''" using hash_suffixes_associative a30  by simp
      have a50:"suffix' \<noteq> suffixb" using MTArray(2) by simp
      then have a60:" suffix' \<noteq> hash suffixb (ShowL\<^sub>n\<^sub>a\<^sub>t x)" by (simp add: MTArray.prems(1))
      then have a70:"(\<forall>xa. suffix' \<noteq> hash (hash suffixb (ShowL\<^sub>n\<^sub>a\<^sub>t x)) xa)" by (simp add: MTArray.prems(1) hash_suffixes_associative)
      then have "(\<forall>x. suffix' \<noteq> hash suffixb x)" using MTArray by simp
      then have "accessStore (hash ld suffix') v' = accessStore (hash ld suffix') v''" using MTArray(1)[of suffix' "hash suffixb (ShowL\<^sub>n\<^sub>a\<^sub>t x)" v'' l "(ShowL\<^sub>n\<^sub>a\<^sub>t x)" v']
          hash_never_equal_prefix MTArray(2) a40 a50 by (simp add: hash_suffixes_associative) 
      then show ?case using a20 by simp
    qed
  next
    case (MTValue x)
    then have a10:"Some v'' =  (case accessStore (hash ls suffixa) ms of None \<Rightarrow> None | Some (MValue v) \<Rightarrow> Some (updateTypedStore (hash ld suffixb) (MValue v) (MTValue x) a) | Some (MPointer literal) \<Rightarrow> None)" 
      using cpm2mrec.simps(2)[of "hash ls suffixa" "hash ld suffixb" x ms a ] by simp
    then obtain v where  " accessStore (hash ls suffixa) ms = Some (MValue v)" by (simp split:option.splits memoryvalue.splits)
    then have "Some v'' =  Some (updateTypedStore (hash ld suffixb) (MValue v) (MTValue x) a)" using a10 by simp
    then show ?case using hash_never_equal_sufix MTValue unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
  qed 
qed

lemma iterIndexMinOne:
  assumes "iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md (Suc x) = Some v''"
  shows "\<exists>v'. iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md x = Some v'"
proof -
  have "Some v'' =(if Suc x \<le> 0 then Some md
     else case iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md (Suc x - 1) of None \<Rightarrow> None
          | Some xa \<Rightarrow> cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t (Suc x - 1))) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t (Suc x - 1))) t ms xa)" 
    using assms iter'.simps[of " (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms)" md "(Suc x)"] by simp
  then have **:"Some v'' = (case iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md (Suc x - 1) of None \<Rightarrow> None
          | Some xa \<Rightarrow> cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t (Suc x - 1))) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t (Suc x - 1))) t ms xa)" by simp
  then show ?thesis
  proof(cases "iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md (Suc x - 1)")
    case None
    then show ?thesis using ** by simp
  next
    case (Some a)
    then have "Some v'' = cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t (Suc x - 1))) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t (Suc x - 1))) t ms a" using ** by simp
    then have "iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md x = 
               iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md (Suc x - 1)" by simp
    then show ?thesis using Some by simp
  qed
qed

lemma cps2mrecSingleChange:
  assumes " Some v'' = cps2mrec (hash ls suffixa) (hash ld suffixb) t ms a  "
  shows "
          ( (\<forall>x'. suffix' \<noteq> hash suffixb x')
          \<and> suffix' \<noteq> suffixb
          \<longrightarrow> accessStore (hash ld suffix') a = accessStore (hash ld suffix') v'')"
proof intros
  fix suffix'
  assume **:" (\<forall>x'. suffix' \<noteq> hash suffixb x') \<and> suffix' \<noteq> suffixb" 
  show "accessStore (hash ld suffix') a = accessStore (hash ld suffix') v''" using ** assms
  proof(induction t arbitrary:a v'' suffixb ls suffixa suffix')
    case (STArray x1 t)
    have a60:"Some v'' =
            (let m = updateTypedStore (hash ld suffixb) (MPointer (hash ld suffixb))
              (MTArray x1 (case cps2mTypeConvert t of Some t' \<Rightarrow> t' | None \<Rightarrow> MTValue TBool)) a
                 in iter' (\<lambda>i'. cps2mrec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (hash (hash ld suffixb) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) t ms) m x1)" 
      using  STArray cps2mrec.simps(1)[of "(hash ls suffixa)" "(hash ld suffixb)" x1 t ms a] by (simp split:option.splits memoryvalue.splits)
    then obtain m' where a50:" m'= updateTypedStore (hash ld suffixb) (MPointer (hash ld suffixb))
              (MTArray x1 (case cps2mTypeConvert t of Some t' \<Rightarrow> t' | None \<Rightarrow> MTValue TBool)) a" by simp
    then have a55:"accessStore ld a = accessStore ld m'" unfolding updateTypedStore_def updateTypeStore_def accessStore_def updateStore_def using hash_inequality by simp
    then have a70:"Some v'' =iter' (\<lambda>i'. cps2mrec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (hash (hash ld suffixb) (ShowL\<^sub>n\<^sub>a\<^sub>t i')) t ms) m' x1" using a60 a50 by presburger
    show ?case
    proof(induction rule: iter'_induct[OF _ _ a70[symmetric]])
      case (1 v')      
      then have "v' = m'" using iter'.simps by simp
      then show ?case using hash_never_equal_sufix STArray(2) a50  unfolding accessStore_def updateStore_def updateTypedStore_def updateTypeStore_def by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i'. cps2mrec (hash (hash ls suffixa)  (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (hash (hash ld suffixb)(ShowL\<^sub>n\<^sub>a\<^sub>t i')) t ms) m' x = Some v'"
          and a20:"accessStore (hash ld suffix') a = accessStore (hash ld suffix') v'"
          and a30:"cps2mrec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash ld suffixb) (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
      have a40:"cps2mrec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (hash suffixb (ShowL\<^sub>n\<^sub>a\<^sub>t x))) t ms v' = Some v''" using hash_suffixes_associative a30  by simp
      have a50:"suffix' \<noteq> suffixb" using STArray(2) by simp
      then have a60:" suffix' \<noteq> hash suffixb (ShowL\<^sub>n\<^sub>a\<^sub>t x)" by (simp add: STArray.prems(1))
      then have a70:"(\<forall>xa. suffix' \<noteq> hash (hash suffixb (ShowL\<^sub>n\<^sub>a\<^sub>t x)) xa)" by (simp add: STArray.prems(1) hash_suffixes_associative)
      then have "(\<forall>x. suffix' \<noteq> hash suffixb x)" using STArray by simp
      then have "accessStore (hash ld suffix') v' = accessStore (hash ld suffix') v''" using STArray(1)[of _ _ v'' "(hash ls suffixa)" "(ShowL\<^sub>n\<^sub>a\<^sub>t x)" ]
          hash_never_equal_prefix STArray(2) a40 a50 by (metis a70) 
      then show ?case using a20 by simp
    qed

  next
    case (STValue x)
    then have a10:"Some v'' = (let v = accessStorage x (hash ls suffixa) ms in Some (updateTypedStore (hash ld suffixb) (MValue v) (MTValue x) a))" 
      using cps2mrec.simps(2)[of "hash ls suffixa" "hash ld suffixb" x ms a ] by simp
    then obtain v where  "accessStorage x (hash ls suffixa) ms = v" by (simp split:option.splits memoryvalue.splits)
    then have "Some v'' = Some (updateTypedStore (hash ld suffixb) (MValue v) (MTValue x) a)" using a10 by simp
    then show ?case using hash_never_equal_sufix STValue unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
  next 
    case (STMap k v)
    then show ?case using cps2mrec.simps by simp
  qed 
qed

lemma accessPrePost1:
  shows " Some v'' = iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x1
          \<and> (\<forall>suffix. hash destl suffix \<noteq> destl)  \<longrightarrow> accessStore destl m = accessStore destl v'' "
proof intros
  assume " Some v'' = iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x1 \<and>   (\<forall>suffix. hash destl suffix \<noteq> destl)"
  then have *:"Some v'' = iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x1"
    and **: "(\<forall>suffix. hash destl suffix \<noteq> destl)" by simp+
  then show "accessStore destl m = accessStore destl v''"
  proof(induction rule: iter'_induct[OF _ _ *[symmetric]])
    case (1 v')
    then show ?case by simp
  next
    case (2 x v'')
    then obtain v'
      where a10:"iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x = Some v'"
        and a20:"(Some v' = iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x \<and> (\<forall>suffix. hash destl suffix \<noteq> destl) \<longrightarrow> accessStore destl m = accessStore destl v')"
        and a30:"cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' srcMem v' = Some v''" by blast
    then show ?case using cpm2mrec_preserves_dest_root[of srcl "(ShowL\<^sub>n\<^sub>a\<^sub>t x)" destl "(ShowL\<^sub>n\<^sub>a\<^sub>t x)" t' srcMem v' v''] 
      using "**" by auto
  qed
qed

lemma cps2mAccessPrePost:
  shows " Some v'' = iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x1
          \<and> (\<forall>suffix. hash destl suffix \<noteq> destl)  \<longrightarrow> accessStore destl m = accessStore destl v'' "
proof intros
  assume " Some v'' = iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x1 \<and>   (\<forall>suffix. hash destl suffix \<noteq> destl)"
  then have *:"Some v'' = iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x1"
    and **: "(\<forall>suffix. hash destl suffix \<noteq> destl)" by simp+
  then show "accessStore destl m = accessStore destl v''"
  proof(induction rule: iter'_induct[OF _ _ *[symmetric]])
    case (1 v')
    then show ?case by simp
  next
    case (2 x v'')
    then obtain v'
      where a10:"iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x = Some v'"
        and a20:"(Some v' = iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) m x \<and> (\<forall>suffix. hash destl suffix \<noteq> destl) \<longrightarrow> accessStore destl m = accessStore destl v')"
        and a30:"cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' srcMem v' = Some v''" by blast
    then show ?case using cps2mrec_preserves_dest_root 
      using "**" by simp
  qed
qed

subsubsection \<open>Sub-Prefix Preservation: Location-Prefix Condition\<close>
text \<open>
A copy operation only modifies locations that are sub-prefixes of the destination root.
Any location @{text destl'} that is not a sub-prefix of @{text destl} (under @{text LSubPrefL2})
is left unchanged in both the value and type stores.

This section covers the @{text both}-access (value and type together), value-only, and typed-only
variants for all three recursive copy functions: @{text cpm2mrec}, @{text cps2mrec}, and
@{text cpm2srec}.  The @{text cpm2srec_SubPrefixes2} lemma additionally handles the case where
the type compatibility predicate (@{text cps2mTypeCompatible}) is involved.
\<close>

text \<open>The following meta-lemma lifts a pointwise step-preservation property
to a full @{text iter'} run.  It abstracts the repeated pattern in every
@{text SubPrefixes_both} proof: the @{text Not_Sub_More_Specific} chain and
invariant bookkeeping are done once here.\<close>

lemma iter'_SubPref_both:
  fixes destl :: String.literal
  assumes run:       "iter' f init_m x = Some v'"
  assumes init:      "\<forall>loc. \<not>LSubPrefL2 loc destl
    \<longrightarrow> accessStore loc a = accessStore loc init_m
      \<and> accessTypeStore loc a = accessTypeStore loc init_m"
  assumes step_pres: "\<And>i m m'. f i m = Some m'
    \<Longrightarrow> \<forall>loc. \<not>LSubPrefL2 loc (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))
        \<longrightarrow> accessStore loc m = accessStore loc m'
          \<and> accessTypeStore loc m = accessTypeStore loc m'"
  shows "\<forall>loc. \<not>LSubPrefL2 loc destl
    \<longrightarrow> accessStore loc a = accessStore loc v'
      \<and> accessTypeStore loc a = accessTypeStore loc v'"
proof (rule iter'_invariant[OF run,
    where I = "\<lambda>m1. \<forall>loc. \<not>LSubPrefL2 loc destl
      \<longrightarrow> accessStore loc a = accessStore loc m1
        \<and> accessTypeStore loc a = accessTypeStore loc m1"])
  show "\<forall>loc. \<not>LSubPrefL2 loc destl
    \<longrightarrow> accessStore loc a = accessStore loc init_m
      \<and> accessTypeStore loc a = accessTypeStore loc init_m"
    using init .
next
  fix i m1 m2
  assume IH_iter: "\<forall>loc. \<not>LSubPrefL2 loc destl
    \<longrightarrow> accessStore loc a = accessStore loc m1
      \<and> accessTypeStore loc a = accessTypeStore loc m1"
  assume rec: "f i m1 = Some m2"
  show "\<forall>loc. \<not>LSubPrefL2 loc destl
    \<longrightarrow> accessStore loc a = accessStore loc m2
      \<and> accessTypeStore loc a = accessTypeStore loc m2"
  proof (intro allI impI)
    fix loc assume not_sub: "\<not>LSubPrefL2 loc destl"
    then have inv1: "accessStore loc a = accessStore loc m1 \<and> accessTypeStore loc a = accessTypeStore loc m1"
      using IH_iter by blast
    have not_sub_child: "\<not>LSubPrefL2 loc (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
      using not_sub Not_Sub_More_Specific by simp
    then have inv2: "accessStore loc m1 = accessStore loc m2 \<and> accessTypeStore loc m1 = accessTypeStore loc m2"
      using step_pres[OF rec] by blast
    show "accessStore loc a = accessStore loc m2 \<and> accessTypeStore loc a = accessTypeStore loc m2"
      using inv1 inv2 by simp
  qed
qed

lemma cpm2mrec_SubPrefixes_both:
  "cpm2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'. (\<not>LSubPrefL2 destl' destl) \<longrightarrow>
      accessStore destl' a = accessStore destl' v'''
    \<and> accessTypeStore destl' a = accessTypeStore destl' v''')"
proof (induction tp arbitrary: srcl destl srcMem a v''')
  case (MTArray x1 t)
  show ?case
  proof
    assume run: "cpm2mrec srcl destl (MTArray x1 t) srcMem a = Some v'''"
    then obtain l where src_ptr: "accessStore srcl srcMem = Some (MPointer l)"
      using cpm2mrec.simps(1)[of srcl destl x1 t srcMem a]
      by (auto split: if_splits option.splits memoryvalue.splits)
    have expanded:
      "Some v''' =
        (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a
         in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1)"
      using run src_ptr cpm2mrec.simps(1)[of srcl destl x1 t srcMem a]
      by simp
    then obtain m where mdef: "m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a" by auto
    have init: "\<forall>destl'. \<not>LSubPrefL2 destl' destl
        \<longrightarrow> accessStore destl' a = accessStore destl' m
          \<and> accessTypeStore destl' a = accessTypeStore destl' m"
      using mdef updateTypedStore_neq_loc 
      by (metis LSubPrefL2_def)
    have iter_run:
      "iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1 = Some v'''"
      using expanded mdef by presburger
    have step_pres: "\<And>i m1 m2.
        cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m1 = Some m2
        \<Longrightarrow> \<forall>loc. \<not>LSubPrefL2 loc (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))
            \<longrightarrow> accessStore loc m1 = accessStore loc m2
              \<and> accessTypeStore loc m1 = accessTypeStore loc m2"
      using MTArray.IH by blast
    show "\<forall>destl'. \<not>LSubPrefL2 destl' destl
      \<longrightarrow> accessStore destl' a = accessStore destl' v''' \<and> accessTypeStore destl' a = accessTypeStore destl' v'''"
      using iter'_SubPref_both[OF iter_run init step_pres] .
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix destl'
    assume run: "cpm2mrec srcl destl (MTValue x) srcMem a = Some v'''"
    assume not_sub: "\<not>LSubPrefL2 destl' destl"
    then have not_eq: "destl' \<noteq> destl" by (simp add: LSubPrefL2_def)
    then obtain v where src_val: "accessStore srcl srcMem = Some (MValue v)"
      using run cpm2mrec.simps(2)[of srcl destl x srcMem a]
      by (auto split: option.splits memoryvalue.splits)
    have as2:"v''' = updateTypedStore destl (MValue v) (MTValue x) a"
      using run src_val cpm2mrec.simps(2)[of srcl destl x srcMem a] by simp
    then show "accessStore destl' a = accessStore destl' v'''"
      using not_eq updateTypedStore_neq_loc by metis
    show "accessTypeStore destl' a = accessTypeStore destl' v'''"
      using as2 not_eq updateTypedStore_neq_loc by metis
  qed
qed

lemma cpm2mrec_SubPrefixes:
  "cpm2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'. (\<not>LSubPrefL2 destl' destl) \<longrightarrow> accessStore destl' a = accessStore destl' v''')"
  using cpm2mrec_SubPrefixes_both by blast

lemma cps2mrec_SubPrefixes_both:
  "cps2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'. (\<not>LSubPrefL2 destl' destl) \<longrightarrow>
      accessStore destl' a = accessStore destl' v'''
    \<and> accessTypeStore destl' a = accessTypeStore destl' v''')"
proof (induction tp arbitrary: srcl destl srcMem a v''')
  case (STArray x1 t)
  show ?case
  proof
    assume run: "cps2mrec srcl destl (STArray x1 t) srcMem a = Some v'''"
    have expanded:
      "Some v''' =
        (case cps2mTypeConvert t of
          None \<Rightarrow> None
        | Some t' \<Rightarrow>
            let m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a
            in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1)"
      using run cps2mrec.simps(1)[of srcl destl x1 t srcMem a]
      by (auto split: option.splits memoryvalue.splits)
    then obtain t' where t'Def: "cps2mTypeConvert t = Some t'" by fastforce
    then obtain m where mdef: "m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a" by auto
    have init: "\<forall>destl'. \<not>LSubPrefL2 destl' destl
        \<longrightarrow> accessStore destl' a = accessStore destl' m
          \<and> accessTypeStore destl' a = accessTypeStore destl' m"
      using mdef updateTypedStore_neq_loc by (metis LSubPrefL2_def)
    have iter_run0:
      "iter' (\<lambda>i m'. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m')
        (updateTypedStore destl (MPointer destl) (MTArray x1 t') a) x1 = Some v'''"
      using run t'Def unfolding cps2mrec.simps(1) Let_def by (auto split:option.splits)
    have iter_run:
      "iter' (\<lambda>i m'. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m') m x1 = Some v'''"
      using iter_run0 mdef by simp
    have step_pres: "\<And>i m1 m2.
        cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m1 = Some m2
        \<Longrightarrow> \<forall>loc. \<not>LSubPrefL2 loc (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))
            \<longrightarrow> accessStore loc m1 = accessStore loc m2
              \<and> accessTypeStore loc m1 = accessTypeStore loc m2"
      using STArray.IH by blast
    show "\<forall>destl'. \<not>LSubPrefL2 destl' destl
      \<longrightarrow> accessStore destl' a = accessStore destl' v''' \<and> accessTypeStore destl' a = accessTypeStore destl' v'''"
      using iter'_SubPref_both[OF iter_run init step_pres] .
  qed
next
  case (STValue x)
  show ?case
  proof intros
    fix destl'
    assume run: "cps2mrec srcl destl (STValue x) srcMem a = Some v'''"
    assume not_sub: "\<not>LSubPrefL2 destl' destl"
    then have not_eq: "destl' \<noteq> destl" by (simp add: LSubPrefL2_def)
    have result:
      "v''' = updateTypedStore destl (MValue (accessStorage x srcl srcMem)) (MTValue x) a"
      using run cps2mrec.simps(2)[of srcl destl x srcMem a] by simp
    then show "accessStore destl' a = accessStore destl' v'''"
      using not_eq updateTypedStore_neq_loc by metis
    show "accessTypeStore destl' a = accessTypeStore destl' v'''"
      using result not_eq updateTypedStore_neq_loc by metis
  qed
next
  case (STMap x1 tp)
  then show ?case using cps2mrec.simps(3) by auto
qed

lemma cps2mrec_SubPrefixes:
  "cps2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'. (\<not>LSubPrefL2 destl' destl) \<longrightarrow> accessStore destl' a = accessStore destl' v''')"
  using cps2mrec_SubPrefixes_both by blast

lemma cpm2srec_SubPrefixes:
  "cpm2srec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl' t. (\<not>LSubPrefL2 destl' destl) \<longrightarrow> accessStorage t destl' a = accessStorage t destl' v''')" 
proof(induction tp arbitrary:srcl destl srcMem a v''' )
  case (MTArray x1 tp)
  show ?case 
  proof intros
    fix destl' t
    assume "cpm2srec srcl destl (MTArray x1 tp) srcMem a = Some v'''"
    then have 
      **: "cpm2srec srcl destl (MTArray x1 tp) srcMem a = Some v'''" by auto+
    then obtain l where ldef:"accessStore srcl srcMem = Some (MPointer l)"
      using ** cpm2srec.simps(1)[of srcl destl x1 tp srcMem a ] by (auto split:if_splits option.splits memoryvalue.splits)
    then have a5:"Some v''' =   iter' (\<lambda>i. cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) a x1" 
      using ** cpm2srec.simps(1)[of srcl destl x1 tp srcMem a ] by (auto split:if_splits option.splits memoryvalue.splits)

    show "\<not> LSubPrefL2 destl' destl \<Longrightarrow>  accessStorage t destl' a = accessStorage t destl' v'''" 
    proof(induction rule: iter'_induct[OF _ _ a5[symmetric]]) 
      case (1 v')
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) a x = Some v'"
          and a20:"(\<not> LSubPrefL2 destl' destl \<longrightarrow> accessStorage t destl' a = accessStorage t destl' v')"
          and a30:"cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) tp srcMem v' = Some v''" by blast
      then show ?case
      proof(cases tp)
        case (MTArray x11 x12)
        then show ?thesis 
          using "2.prems" MTArray.IH a20 a30 Not_Sub_More_Specific by fastforce
      next
        case (MTValue x2)
        then have a50:"cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTValue x2) srcMem v' = Some v''" using a30 by simp
        then obtain v where vdef: "accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem  = Some (MValue v)" 
          using a30 unfolding cpm2srec.simps by (auto split:if_splits option.splits memoryvalue.splits)
        then have "Some v'' = Some (v'(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) $$:= v))" using a50 unfolding cpm2srec.simps by (auto split:if_splits option.splits memoryvalue.splits)
        then show ?thesis by (metis "2.prems" MTArray a20 a30 Not_Sub_More_Specific)
      qed
    qed
  qed
next
  case (MTValue x)
  then show ?case 
  proof intros
    fix destl' t 
    assume *:"cpm2srec srcl destl (MTValue x) srcMem a = Some v'''" 
      and **:" \<not> LSubPrefL2 destl' destl"
    then obtain v where vdef: "accessStore srcl srcMem  = Some (MValue v)" 
      unfolding cpm2srec.simps by (auto split:if_splits option.splits memoryvalue.splits)
    then have "Some v''' = Some (a(destl $$:= v))" using * unfolding cpm2srec.simps by (auto split:if_splits option.splits memoryvalue.splits)
    moreover have "destl' \<noteq> destl" using ** LSubPrefL2_def by simp
    ultimately show "accessStorage t destl' a = accessStorage t destl' v''' " using ** accessStorage_def by simp
  qed
qed

subsubsection \<open>Value Type Preservation Under Iterated Copying\<close>
text \<open>
When the copied type is a value type (@{text MTValue}/@{text STValue}), every destination
index written by the iteration holds a value entry (not a pointer) in the resulting memory.
These lemmas are used in the @{text MCon}/@{text SCon} correctness proofs to discharge the
value-branch obligations.
\<close>

lemma Cpm2mrec_val_types:
  assumes "iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (MTValue x2) srcMem) m x1 = Some v'"
  shows "\<forall>i<x1. (\<exists>val. accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MValue val))"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by simp
next
  case (2 x v'')
  then obtain v' 
    where a10: "iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (MTValue x2) srcMem) m x = Some v'"
      and a20: "(\<forall>i<x. \<exists>val. accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MValue val))" 
      and a30:"cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTValue x2) srcMem v' = Some v''" by blast
  obtain t where a40: "accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MValue t)" using a30 using cpm2mrec.simps(2) by (auto split:option.splits memoryvalue.splits)
  show ?case 
  proof intros
    fix i assume *:"i<Suc x"
    show "\<exists>val. accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some (MValue val) "
    proof(cases "(i<x)")
      case True
      then have "\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
        by (simp add: Read_Show_nat'_id hash_int_prefix hash_never_equal_sufix readLintNotEqual ShowLNatDot)
      then have "accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using cpm2mrec_SubPrefixes a30 a40 by force
      then show ?thesis using a20 True by metis
    next
      case False
      then have "i = x" using * by simp
      moreover have "Some v'' =  (case accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem of None \<Rightarrow> None 
                | Some (MValue v) \<Rightarrow>  Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v') 
                | Some (MPointer literal) \<Rightarrow> None)" 
        using cpm2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 srcMem v'] a30 by simp
      ultimately show ?thesis using a40 
        unfolding updateTypedStore_def updateTypeStore_def accessStore_def updateStore_def by simp
    qed
  qed
qed

lemma Cps2mrec_val_types:
  assumes "iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STValue x2) srcMem) m x1 = Some v'"
  shows "\<forall>i<x1. (\<exists>val. accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MValue val))"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by simp
next
  case (2 x v'')
  then obtain v' 
    where a10: "iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STValue x2) srcMem) m x = Some v'"
      and a20: "(\<forall>i<x. \<exists>val. accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MValue val))" 
      and a30:"cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (STValue x2) srcMem v' = Some v''" by blast
  obtain t where a40: " accessStorage x2 srcl srcMem = t" using a30 using cps2mrec.simps(2) by (auto split:option.splits memoryvalue.splits)
  show ?case 
  proof intros
    fix i assume *:"i<Suc x"
    show "\<exists>val. accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some (MValue val) "
    proof(cases "(i<x)")
      case True
      then have "\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
        by (simp add: Read_Show_nat'_id hash_int_prefix hash_never_equal_sufix readLintNotEqual ShowLNatDot)
      then have "accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using cps2mrec_SubPrefixes a30 a40 by force
      then show ?thesis using a20 True by metis
    next
      case False
      then have "i = x" using * by simp
      moreover have "Some v'' =  (let v = accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem
     in Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v'))" 
        using cps2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 srcMem v'] a30 by simp
      ultimately show ?thesis using a40 unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
        by auto        
    qed
  qed
qed


subsubsection \<open>Pointer Self-Reference Preservation\<close>
text \<open>
After a copy, every pointer stored within the destination region points to itself (i.e.\ the
pointer value equals the location at which it is stored).  This self-referential invariant
reflects the structural layout of arrays: sub-location pointers introduced by
@{text cpm2mrec}/@{text cps2mrec} always satisfy @{text "accessStore l v' = Some (MPointer l)"},
matching the requirement imposed by @{text MCon}/@{text SCon}.

Results are given for the recursive step (@{text cpm2mrecPtrsPointToSelf},
@{text cps2mrecPtrsPointToSelf}) and lifted to the iterated wrappers
(@{text cpm2mSelfPointers}, @{text cps2mSelfPointers}).
\<close>

lemma cpm2mrecPtrsPointToSelf:
  shows "cpm2mrec srcl destl t srcMem destm = Some v'
          \<longrightarrow>  (\<forall>l l'. (TypedMemSubPref l destl t \<or> l = destl) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
proof(induction t arbitrary: srcl destl  srcMem destm v')
  case (MTArray x1 t)
  show ?case
  proof intros
    fix l l'
    assume *:"cpm2mrec srcl destl (MTArray x1 t) srcMem destm = Some v' "
      and **:"(TypedMemSubPref l destl (MTArray x1 t) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l')"
    have a10:"Some v' = (case accessStore srcl srcMem of None \<Rightarrow> None | Some (MValue literal) \<Rightarrow> None
     | Some (MPointer l) \<Rightarrow>
         let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) destm
         in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1)"
      using * cpm2mrec.simps(1)[of srcl destl x1 t srcMem destm] by simp
    then obtain l''' where a20:"accessStore srcl srcMem = Some (MPointer l''')" 
      by (auto split:option.splits memoryvalue.splits mtypes.splits)
    then have a30:"Some v' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) destm
         in iter' (\<lambda>i. cpm2mrec (hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1)" 
      using a10 by simp
    then obtain m where a40:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t) destm" by auto
    then have a45:"accessStore destl m = Some(MPointer destl)" 
      unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then have a50:"Some v' = iter' (\<lambda>i. cpm2mrec (hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl  (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1" 
      using a30 a40 by presburger
    show "l' = l" using a45 **
    proof(induction rule: iter'_induct[OF _ _ a50[symmetric]])
      case (1 v')
      then show ?case by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. cpm2mrec (hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x = Some v'"
          and a20:" (accessStore destl m = Some (MPointer destl) \<longrightarrow> (TypedMemSubPref l destl (MTArray x t) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) "
          and a30:"cpm2mrec (hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t srcMem v' = Some v''" by blast
      then have "accessStore destl m = Some (MPointer destl)" using 2 by auto
      then show ?case
      proof(cases "l = destl")
        case True
        then show ?thesis using 2(1,3,4) cpm2mrec_preserves_dest_root by auto
      next
        case f1:False
        then show ?thesis 
        proof(cases "TypedMemSubPref l destl (MTArray x t)")
          case True
          then obtain i where  b10:"i<x \<and> (TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)))" by auto
          then have b15:"LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using typedPrefix_imp_SubPref[of l "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t] unfolding LSubPrefL2_def by auto
          then have b20:"(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using b10
            by (metis Read_Show_nat'_id hash_never_equal_sufix less_not_refl)
          have "\<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using LSubPrefL2_def[of l "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"] b15 b20 Mutual_NonSub_SpecificNonSub hash_int_prefix ShowLNatDot by auto
          then have b50:"accessStore l v' = accessStore l v''" 
            using * cpm2mrec_SubPrefixes a30 by simp
          then show ?thesis using a20 2 using True by auto
        next
          case False
          then have b5:"TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using 2(4) TypedMemSubPref.simps(2)[of l destl "(Suc x)" t] f1 
            using less_Suc_eq by auto
          have b10:"accessStore l v'' = Some (MPointer l')" using 2(4) by auto

          have "(\<forall>l l'. (TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<and> accessStore l v'' = Some (MPointer l') \<longrightarrow> l' = l)" 
            using  MTArray[of "(hash l''' (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem v' v''] a30 by simp
          then show ?thesis using b5 b10 by blast
        qed
      qed
    qed
  qed
next
  case (MTValue x)
  then show ?case 
  proof intros
    fix l l'
    assume *:"cpm2mrec srcl destl (MTValue x) srcMem destm = Some v'" 
      and **:"(TypedMemSubPref l destl (MTValue x) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l')"
    have "Some v' = (case accessStore srcl srcMem of None \<Rightarrow> None 
                | Some (MValue v) \<Rightarrow> Some (updateTypedStore destl (MValue v) (MTValue x) destm)
                | Some (MPointer literal) \<Rightarrow> None)" 
      using cpm2mrec.simps(2)[of srcl destl x srcMem destm] * by simp
    then obtain v where b10: "accessStore destl v' = Some (MValue v)" 
      unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
      by (auto split:option.splits memoryvalue.splits)
    show "l' = l" using b10 ** by auto
  qed
qed

lemma cps2mrecPtrsPointToSelf:
  shows "cps2mrec srcl destl t srcMem destm = Some v'
          \<longrightarrow>  (\<forall>l l'. (TypedStoSubpref l destl t \<or> l = destl) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)" 
proof(induction t arbitrary: srcl destl  srcMem destm v')
  case (STArray x1 t)
  show ?case 
  proof intros
    fix l l'
    assume *:"cps2mrec srcl destl (STArray x1 t) srcMem destm = Some v' " 
      and **:"(TypedStoSubpref l destl (STArray x1 t) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l')"
    have a10:"Some v' =  (case cps2mTypeConvert t of None \<Rightarrow> None
     | Some t' \<Rightarrow>
         let m = updateTypedStore destl (MPointer destl) (MTArray x1 t') destm
         in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1)" 
      using * cps2mrec.simps(1)[of srcl destl x1 t srcMem destm] by simp
    then obtain t' where t'def:"cps2mTypeConvert t = Some t'" by fastforce
    then obtain m where a40:"m =  updateTypedStore destl (MPointer destl) (MTArray x1 t') destm" by auto
    then have a45:"accessStore destl m = Some(MPointer destl)" 
      unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
      by simp
    then have a50:"Some v' = iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl  (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1" 
      using a40 a10 t'def 
      by (metis (no_types, lifting) Option.option.simps(5))
    show "l' = l" using a45 **
    proof(induction rule: iter'_induct[OF _ _ a50[symmetric]])
      case (1 v')
      then show ?case by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x = Some v'"
          and a20:" (accessStore destl m = Some (MPointer destl) \<longrightarrow> (TypedStoSubpref l destl (STArray x t) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) "
          and a30:"cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t srcMem v' = Some v''" by blast
      then have "accessStore destl m = Some (MPointer destl)" using 2 by auto
      then show ?case 
      proof(cases "l = destl")
        case True
        then show ?thesis using 2 cpm2mrec_preserves_dest_root 
          by (metis (no_types, opaque_lifting) LSubPrefL2_def cps2mrec_SubPrefixes hash_inequality hash_suffixes_associative)
      next
        case f1:False
        then show ?thesis 
        proof(cases "TypedStoSubpref l destl (STArray x t)")
          case True
          then obtain i where  b10:"i<x \<and> (TypedStoSubpref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)))" 
            using f1 by auto
          then have b15:"LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using TypedStoSubpref_imp_LSubPrefL2[of l "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t] unfolding LSubPrefL2_def by auto
          then have b20:"(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using b10
            by (metis Read_Show_nat'_id hash_never_equal_sufix less_not_refl)
          have "\<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using LSubPrefL2_def[of l "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"] b15 b20 Mutual_NonSub_SpecificNonSub hash_int_prefix ShowLNatDot by auto
          then have b50:"accessStore l v' = accessStore l v''" 
            using * cps2mrec_SubPrefixes a30 by simp
          then show ?thesis using a20 2 using True by auto
        next
          case False
          then have b5:"TypedStoSubpref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using 2(4) TypedStoSubpref.simps(2)[of l destl "(Suc x)" t] f1 
            using less_Suc_eq by auto
          have b10:"accessStore l v'' = Some (MPointer l')" using 2(4) by auto

          have "(\<forall>l l'. (TypedStoSubpref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<and> accessStore l v'' = Some (MPointer l') \<longrightarrow> l' = l)" 
            using  STArray[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem v' v''] a30 by simp
          then show ?thesis using b5 b10 by blast
        qed
      qed
    qed
  qed
next
  case (STValue x)
  then show ?case 
  proof intros
    fix l l'
    assume *:"cps2mrec srcl destl (STValue x) srcMem destm = Some v'" 
      and **:"(TypedStoSubpref l destl (STValue x) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l')"
    have "Some v' = (let v = accessStorage x srcl srcMem in Some (updateTypedStore destl (MValue v) (MTValue x) destm))" 
      using cps2mrec.simps(2)[of srcl destl x srcMem destm] * by simp
    then obtain v where b10: "accessStore destl v' = Some (MValue v)" 
      unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def 
      by (auto split:option.splits memoryvalue.splits)
    show "l' = l" using b10 ** by auto
  qed
next
  case (STMap k v)
  then show ?case using cps2mrec.simps(3) by force
qed

lemma cpm2mSelfPointers:
  assumes "iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1 = Some v'"
  shows "(\<forall>l l'. TypedMemSubPref l destl (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"  using assms(1)
proof(induction  rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x = Some v'"
      and a20: "(\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') 
                  \<longrightarrow> l' = l)"
      and a30: "cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t srcMem v' = Some v''" by blast
  show ?case 
  proof intros
    fix l l'
    assume *:"TypedMemSubPref l destl (MTArray (Suc x) t) \<and> accessStore l v'' = Some (MPointer l')"
    show "l' = l"
    proof(cases t)
      case (MTArray x11 x12)

      then show ?thesis 
      proof(cases "TypedMemSubPref l destl (MTArray x t)")
        case True
        then obtain i where  b10:"i<x \<and> (TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)))" by auto
        then have b15:"LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using typedPrefix_imp_SubPref[of l "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t] unfolding LSubPrefL2_def by auto
        then have b20:"(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using b10
          by (metis Read_Show_nat'_id hash_never_equal_sufix less_not_refl)
        have "\<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using LSubPrefL2_def[of l "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"] b15 b20 Mutual_NonSub_SpecificNonSub hash_int_prefix ShowLNatDot by auto
        then have b50:"accessStore l v' = accessStore l v''" 
          using * cpm2mrec_SubPrefixes a30 by simp
        then show ?thesis using a20 True *  b50 by metis
      next
        case False
        then have "TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using TypedMemSubPref.simps(2)[of l destl "(Suc x)" t] *
          using less_Suc_eq by auto
        then show ?thesis using a30 cpm2mrecPtrsPointToSelf[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t srcMem v' v''] * by blast
      qed
    next
      case (MTValue x2)
      then have "Some v'' = (case accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem of None \<Rightarrow> None 
                | Some (MValue v) \<Rightarrow> Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v') 
                | Some (MPointer literal) \<Rightarrow> None)" 
        using a30 cpm2mrec.simps(2)[of  "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 srcMem v'] by simp
      have "(\<exists>i<Suc x. TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t  \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using TypedMemSubPref.simps(2)[of l destl "Suc x" t] * by auto
      then obtain i where b400:"i< Suc x \<and> TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (MTValue x2)" using MTValue by auto
      then have "l =  (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" by simp
      then obtain val where "accessStore l v'' = Some (MValue val)" using Cpm2mrec_val_types[of srcl destl x2 srcMem m "Suc x" v''] 2(2) MTValue b400 by auto
      then show ?thesis using  * by simp 
    qed
  qed
qed

lemma cps2mSelfPointers:
  assumes "iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1 = Some v'"
  shows "(\<forall>l l'. l \<noteq> destl \<and> TypedStoSubpref l destl (STArray x1 t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"  using assms(1)
proof(induction  rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x = Some v'"
      and a20: "(\<forall>l l'. l \<noteq> destl \<and> TypedStoSubpref l destl (STArray x t) \<and> accessStore l v' = Some (MPointer l') 
                  \<longrightarrow> l' = l)"
      and a30: "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t srcMem v' = Some v''" by blast
  show ?case 
  proof intros
    fix l l'
    assume *:"l \<noteq> destl \<and> TypedStoSubpref l destl (STArray (Suc x) t) \<and> accessStore l v'' = Some (MPointer l')"
    show "l' = l"
    proof(cases t)
      case (STArray x11 x12)

      then show ?thesis 
      proof(cases "TypedStoSubpref l destl (STArray x t)")
        case True
        then obtain i where  b10:"i<x \<and> (TypedStoSubpref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"
          using * by auto
        then have b15:"LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using TypedStoSubpref_imp_LSubPrefL2[of l "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t] unfolding LSubPrefL2_def by auto
        then have b20:"(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using b10
          by (metis Read_Show_nat'_id hash_never_equal_sufix less_not_refl)
        have "\<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using LSubPrefL2_def[of l "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"] b15 b20 Mutual_NonSub_SpecificNonSub hash_int_prefix ShowLNatDot by auto
        then have b50:"accessStore l v' = accessStore l v''" 
          using * cps2mrec_SubPrefixes a30 by simp
        then show ?thesis using a20 True *  b50 by metis
      next
        case False
        then have "TypedStoSubpref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using TypedStoSubpref.simps(2)[of l destl "(Suc x)" t] *
          using less_Suc_eq by auto
        then show ?thesis using a30 cps2mrecPtrsPointToSelf[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t srcMem v' v''] * by blast
      qed
    next
      case (STValue x2)
      then have "Some v'' = (let v = accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem in Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v'))" 
        using a30 cps2mrec.simps(2)[of  "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 srcMem v'] by simp
      have "(\<exists>i<Suc x. TypedStoSubpref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t  \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using TypedStoSubpref.simps(2)[of l destl "Suc x" t] * by auto
      then obtain i where b400:"i< Suc x \<and> TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (MTValue x2)" using STValue by auto
      then have "l =  (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" by simp
      then obtain val where "accessStore l v'' = Some (MValue val)" using Cps2mrec_val_types[of srcl destl x2 srcMem m "Suc x" v''] 2(2) STValue b400 by auto
      then show ?thesis using  * by simp 
    next 
      case (STMap k v)
      then show ?thesis 
        using a30 cps2mrec.simps(3) by auto
    qed
  qed
qed

lemma cpm2mrec_preserves_prior_child_case:
  assumes iter: "iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x = Some v'"
    and step: "cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''"
    and mcon: "MCon (MTArray x t) v' ld"
    and iless: "i < x"
  shows "case accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
          | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)"
proof -
  let ?child = "hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
  let ?changed = "hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  have self_root:
    "\<forall>l l'. TypedMemSubPref l ld (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
    using cpm2mSelfPointers[OF iter] by blast
  then have self_child:
    "\<forall>l l'. TypedMemSubPref l ?child t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
    using moreSpecificTypedSubPref[of ld x t v'] iless by blast
  have outside:
    "\<forall>destl'. \<not> LSubPrefL2 destl' ?changed \<longrightarrow> accessStore destl' v' = accessStore destl' v''"
    using cpm2mrec_SubPrefixes[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ?changed t ms v' v''] step by simp
  have neq_hash: "?child \<noteq> ?changed"
    using iless by (metis Read_Show_nat'_id hash_never_equal_sufix less_irrefl_nat)
  then have not_sub_child: "\<not> LSubPrefL2 ?child ?changed"
    using ShowLNatDot hash_int_prefix by simp
  from neq_hash have not_sub_changed: "\<not> LSubPrefL2 ?changed ?child"
    using ShowLNatDot hash_int_prefix by simp
  have keep_child:
    "accessStore ?child v' = accessStore ?child v''"
    using outside not_sub_child by simp
  show ?thesis
  proof (cases t)
    case (MTArray len' arr')
    then obtain loc2 where ptr:
      "accessStore ?child v' = Some (MPointer loc2)"
      using MConArrayPointers[of x len' arr' v' ld i] mcon iless by auto
    have loc_eq: "loc2 = ?child"
      using self_root iless ptr by auto
    have child_mcon_v':
      "MCon t v' ?child"
      using mcon ptr loc_eq MTArray iless by auto
    have child_mcon_v'':
      "MCon t v'' ?child"
      using MCon_mem_preserved_disjoint_update[of ?child ?changed t v' v'']
        self_child outside child_mcon_v' not_sub_child not_sub_changed
      by blast
    then show ?thesis
      using keep_child ptr loc_eq MTArray by force
  next
    case (MTValue x2)
    then obtain val where val:
      "accessStore ?child v' = Some (MValue val)"
      using mcon iless 
      using MCon_sub_MTVal_imps_val by presburger
    have child_mcon_v':
      "MCon t v' ?child"
      using mcon MTValue iless val by auto
    have child_mcon_v'':
      "MCon t v'' ?child"
      using MCon_mem_preserved_disjoint_update[of ?child ?changed t v' v'']
        self_child outside child_mcon_v' not_sub_child not_sub_changed
      by blast
    then show ?thesis
      using keep_child val MTValue 
      by (metis MTValue child_mcon_v'' keep_child val Option.option.simps(5) memoryvalue.simps(5) mtypes.simps(6))
  qed
qed

lemma cps2mrec_preserves_prior_child_case:
  assumes iter: "iter' (\<lambda>i. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) m x = Some v'"
    and step: "cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' ms v' = Some v''"
    and mcon: "MCon (MTArray x t) v' ld"
    and compat: "cps2mTypeCompatible t' t"
    and iless: "i < x"
  shows "case accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
          | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)"
proof -
  let ?child = "hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
  let ?changed = "hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  have self_child:
    "\<forall>l l'. TypedStoSubpref l ?child t' \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
    using cps2mSelfPointers[OF iter] iless 
    by (metis \<open>\<forall>l l'.
   l \<noteq> ld \<and>
   TypedStoSubpref l ld (STArray x t') \<and>
   accessStore l v' = Some (MPointer l') \<longrightarrow>
   l' = l\<close> iless TypedStoSubpref.simps(2) TypedStoSubpref_hashes)
  have outside:
    "\<forall>destl'. \<not> LSubPrefL2 destl' ?changed \<longrightarrow> accessStore destl' v' = accessStore destl' v''"
    using cps2mrec_SubPrefixes[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ?changed t' ms v' v''] step by simp
  have neq_hash: "?child \<noteq> ?changed"
    using iless by (metis Read_Show_nat'_id hash_never_equal_sufix less_irrefl_nat)
  then have not_sub_child: "\<not> LSubPrefL2 ?child ?changed"
    using ShowLNatDot hash_int_prefix by simp
  from neq_hash have not_sub_changed: "\<not> LSubPrefL2 ?changed ?child"
    using ShowLNatDot hash_int_prefix by simp
  have keep_child:
    "accessStore ?child v' = accessStore ?child v''"
    using outside not_sub_child by simp
  show ?thesis
  proof (cases t)
    case (MTArray len' arr')
    then obtain loc2 where ptr:
      "accessStore ?child v' = Some (MPointer loc2)"
      using MConArrayPointers[of x len' arr' v' ld i] mcon iless by auto
    have loc_eq: "loc2 = ?child"
      using self_child ptr TypedStoSubpref_sameLoc by blast
    have child_mcon_v':
      "MCon t v' ?child"
      using mcon ptr loc_eq MTArray iless by auto
    have child_mcon_v'':
      "MCon t v'' ?child"
      using MCon_preserved_under_disjoint_location[of ?child ?changed t' v' t v'']
        self_child compat outside child_mcon_v' not_sub_child not_sub_changed
      by blast
    then show ?thesis
      using keep_child ptr loc_eq MTArray by force
  next
    case (MTValue x2)
    then obtain val where val:
      "accessStore ?child v' = Some (MValue val)"
      using mcon iless 
      by (metis mcon iless MTValue MCon_sub_MTVal_imps_val)
    have child_mcon_v':
      "MCon t v' ?child"
      using mcon MTValue iless val by auto
    have child_mcon_v'':
      "MCon t v'' ?child"
      using MCon_preserved_under_disjoint_location[of ?child ?changed t' v' t v'']
        self_child compat outside child_mcon_v' not_sub_child not_sub_changed
      by blast
    then show ?thesis
      using keep_child val MTValue 
      by (metis MTValue val keep_child child_mcon_v'' Option.option.simps(5) memoryvalue.simps(5) mtypes.simps(6))
  qed
qed

lemma cpm2srec_preserves_prior_child_scon:
  assumes step: "cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''"
    and scon: "SCon tp (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'"
    and iless: "i < x"
  shows "SCon tp (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''"
proof -
  have not_sub1: "\<not> LSubPrefL2 (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
    using iless by (metis ShowLNatDot hash_int_prefix hashesIntSame nat_neq_iff)
  then have not_sub2: "\<not> LSubPrefL2 (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
    using iless scon
    by (metis ShowLNatDot hash_int_prefix)
  have same_root:
    "\<forall>t. accessStorage t (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStorage t (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''"
    using cpm2srec_SubPrefixes step not_sub1 by auto
  have same_deeper:
    "\<forall>i' t. accessStorage t (hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) i') v' = accessStorage t (hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) i') v''"
    using not_sub1 not_sub2 Mutual_NonSub_SpecificNonSub step cpm2srec_SubPrefixes by blast
  show ?thesis
    using SCon_noDots[OF scon same_deeper same_root ShowLNatDot] .
qed


subsubsection \<open>Consistency Implication Lemmas for Recursive Copy Functions\<close>
text \<open>
These are the key correctness lemmas for the single-step recursive copy functions.  They state
that, given a well-formed source, a successful copy produces a well-formed destination.

\<^item> @{text cpm2mrec_imps_MCon_dest}: copying from a @{text MCon}-consistent memory region
  to @{text destl} makes @{text destl} @{text MCon}-consistent in the result.
\<^item> @{text cps2mrec_SCon_imps_MCon_dest}: copying from a @{text SCon}-consistent storage
  region into memory makes the destination @{text MCon}-consistent.
\<^item> @{text cpm2srec_imps_SCon_dest}: copying from a @{text MCon} memory region into storage
  makes the destination @{text SCon}-consistent.

The proofs proceed by induction on the type structure, with the pointer and value cases handled
separately.
\<close>



lemma cps2mrec_SCon_imps_MCon_dest :(*Remove type from Memsubpref*)
  "SCon tp srcl srcMem \<and> cps2mTypeCompatible (STArray l tp) (MTArray l t') \<and>
   cps2mrec srcl destl tp srcMem a = Some v'''                    
          \<longrightarrow> MCon t' v''' destl
"
  (*Can get the precondition of assms(1) using the conclusion of assms(1) and MCon.def*)
proof (induction tp arbitrary:srcl destl srcMem a v''' l t')
  case (STArray x1 tp)
  show ?case 
  proof intros
    assume " SCon (STArray x1 tp) srcl srcMem \<and> cps2mTypeCompatible (STArray l (STArray x1 tp)) (MTArray l t') \<and> cps2mrec srcl destl (STArray x1 tp) srcMem a = Some v'''"
    then have *:" SCon (STArray x1 tp) srcl srcMem"
      and **:"cps2mTypeCompatible (STArray l (STArray x1 tp)) (MTArray l t')"
      and ***:"cps2mrec srcl destl (STArray x1 tp) srcMem a = Some v''' "
      by auto+
    obtain t''' where t'''def:"t' = MTArray x1 t'''" using ** 
      by (metis mtypes.exhaust cps2mTypeCompatible.simps(2) cps2mTypeCompatible.simps(3))

    then have a5:"Some v''' = (case cps2mTypeConvert tp of None \<Rightarrow> None
     | Some t' \<Rightarrow>
         let m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a
         in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x1)" 
      using ***  cps2mrec.simps(1)[of srcl destl x1 tp srcMem a] by simp
    then obtain t3 where t'Def:"cps2mTypeConvert tp = Some t3" by fastforce
    then obtain m where mdef:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t3) a" by auto
    then have "MCon (MTArray x1 t''') v''' destl"
    proof(cases "x1>0")
      case True
      then have srcMcon:"(\<forall>i\<in>{0..x1 - 1}. SCon tp (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) srcMem)" 
        using * SCon.simps(2)[of x1 tp srcl srcMem] by auto
      then have **:"cps2mTypeCompatible  (STArray x1 tp)  (MTArray x1 t''')" using ** t'''def by auto
      then have v''def:"Some v''' =  iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x1" 
        using a5  mdef t'Def 
        by (metis (lifting) Option.option.simps(5)) 
      have "\<forall>i<x1. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' of None \<Rightarrow> False 
             | Some (MValue val) \<Rightarrow> (case t''' of MTValue typ \<Rightarrow> MCon t''' v''' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t''' of MTArray len' arr' \<Rightarrow> MCon t''' v''' loc2 | MTValue Types \<Rightarrow> False)" 
        using * **
      proof(induction rule: iter'_induct[OF _ _ v''def[symmetric]])
        case (1 v')
        then show ?case by simp
      next
        case (2 x v'')
        then obtain v'
          where a10:"iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x = Some v'"
            and a20:"SCon (STArray x tp) srcl srcMem \<longrightarrow>   cps2mTypeCompatible (STArray x tp) (MTArray x t''') \<longrightarrow>
                          (\<forall>i<x. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False 
                            | Some (MValue val) \<Rightarrow> (case t''' of  MTValue typ \<Rightarrow> MCon t''' v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
                            | Some (MPointer loc2) \<Rightarrow> (case t''' of MTArray len' arr' \<Rightarrow> MCon t''' v' loc2 | MTValue Types \<Rightarrow> False))"
            and a30:"cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) tp srcMem v' = Some v''" by blast
        have "SCon (STArray x tp) srcl srcMem " using 2(3) using SCon.simps by auto
        then have a40:"(\<forall>i<x. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False 
                            | Some (MValue val) \<Rightarrow> (case t''' of  MTValue typ \<Rightarrow> MCon t''' v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
                            | Some (MPointer loc2) \<Rightarrow> (case t''' of MTArray len' arr' \<Rightarrow> MCon t''' v' loc2 | MTValue Types \<Rightarrow> False))" 
          using a20 2 by auto
        have a50:"(\<exists>p. accessStore destl v' = Some (MPointer p)) \<or> accessStore destl v' = None" using 2 
        proof -
          have "accessStore destl v'' = accessStore destl v'"
            using  a30 cps2mrec_preserves_dest_root by (metis)
          moreover have "accessStore destl m = accessStore destl v''" 
            using "2.hyps" cps2mAccessPrePost[of v'' srcl destl tp srcMem m "Suc x"] hash_inequality by auto
          moreover have "accessStore destl m = Some (MPointer destl)" using mdef 
            unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
          ultimately show ?thesis by metis
        qed
        show ?case 
        proof intros
          fix i 
          assume iless:"i<Suc x"
          show "case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
                | Some (MValue val) \<Rightarrow> (case t''' of MTValue x \<Rightarrow> MCon t''' v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t''' of MTArray x xa \<Rightarrow> MCon t''' v'' loc2 | MTValue Types \<Rightarrow> False)" 
          proof(cases "i < x")
            case True
            then have MCondestl:"MCon (MTArray x t''') v' destl" using a40 MCon.simps(2)[of x t''' v' destl] a50 by simp
            then show ?thesis
            proof(cases t''')
              case mtr:(MTArray x11 x12)
              then obtain stotp where stotp:"tp = STArray x11 stotp" using 2(4) iless True cps2mTypeCompatible.simps 
                by (metis stypes.exhaust)
              have tpt''comp:"cps2mTypeCompatible tp t'''" using 2(4)by simp

              have "Some v'' = 
                    (case cps2mTypeConvert stotp of None \<Rightarrow> None
                  | Some t' \<Rightarrow>
                    let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 t') v'
                    in iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) stotp srcMem) m x11)"
                using cps2mrec.simps(1)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" " (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 stotp srcMem v' ] a30 stotp by auto
              then have b10:"  (\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
                using STArray(1)[of " (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem  ] a30 cps2mrec_SubPrefixes[of " (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" " (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" tp srcMem v' v''] by simp
              then have b15:"(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) 
                              \<and> \<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) 
                              \<longrightarrow> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'')" by simp
              have " (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq>  (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using True 
                by (metis Read_Show_nat'_id less_irrefl_nat)
              then have b16:"hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
                by (simp add: hash_never_equal_sufix)
              have b17:"\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using hash_int_prefix ShowLNatDot b16 by simp
              have b18:"\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using ShowLNatDot hash_int_prefix b16 by simp
              have b19:"\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v''" using b10 by auto
              have accessSt:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))  v'  = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))  v''" 
                by (simp add: b15 b16 b17)
              then obtain val where valdef:" accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer val)" 
                using MConArrayPointers[of x x11 x12 v' destl i] a40 MCondestl True mtr by auto
              have "Suc x - 1 = x" by simp
              then have subPref:"TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl (STArray x tp)" 
                using 2(3) True
                by (metis True TypedStoSubpref.simps(2) stotp)
              have child_self:"\<forall>l l'. TypedStoSubpref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
              proof (intro allI impI)
                fix l l'
                assume asm:"TypedStoSubpref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp \<and> accessStore l v' = Some (MPointer l')"
                have l_neq:"l \<noteq> destl"
                  using asm TypedStoSubpref_hashes by blast
                have "TypedStoSubpref l destl (STArray x tp)"
                  using asm True TypedStoSubpref.simps(2) by blast
                then show "l' = l"
                  using cps2mSelfPointers[of srcl destl tp srcMem m x v'] a10 asm l_neq by blast
              qed
              have valeq:"val = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
                using child_self valdef TypedStoSubpref_sameLoc by blast
              then have b20:"MCon t''' v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))"  using a40  mtr True valdef by fastforce 
              then have "MCon t''' v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MCon_preserved_under_disjoint_location[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" tp v' t''' v''] a10 b17 b18 b20 b19 child_self tpt''comp by blast
              then show ?thesis using accessSt valdef mtr valeq by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5))
            next
              case (MTValue x2)
              then have stotp:"tp = (STValue x2)" using 2(4) iless True cps2mTypeCompatible.simps 
                by (metis stypes.exhaust)
              have tpt''comp:"cps2mTypeCompatible tp t'''" using 2(4) by simp
              then have "(let v = accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem
                           in Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v')) = Some v''" 
                using cps2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"  x2 srcMem v'] a30 stotp by simp
              then have b10:"(\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
                using STArray(1)[of " (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem ] a30 cps2mrec_SubPrefixes[of " (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" " (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" tp srcMem v' v''] by simp
              then have b15:"(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) 
                              \<and> \<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) 
                              \<longrightarrow> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'')" by simp
              have " (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq>  (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using True 
                by (metis Read_Show_nat'_id less_irrefl_nat)
              then have b16:"hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
                by (simp add: hash_never_equal_sufix)

              have b17:"\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using ShowLNatDot hash_int_prefix b16 by simp
              have b18:"\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using ShowLNatDot hash_int_prefix b16 by simp
              have b20:"MCon t''' v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a40  MTValue True by (auto split:option.splits memoryvalue.splits mtypes.splits)
              then have "MCon t''' v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MCon_mem_preserved_disjoint_update[of "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" ] using MTValue b10 b17 b18 by simp
              moreover have "accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" 
                by (simp add: b15 b16 b17)
              moreover obtain val where "accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MValue val)" 
                using a40 MTValue True b20 by (auto split:option.splits memoryvalue.splits mtypes.splits)
              ultimately show ?thesis 
                by (simp add: MTValue b15 b16 b17)
            qed


          next
            case False
            then have iIsx:"i = x" using iless by simp
            then show ?thesis 
            proof(cases t''')
              case mtr:(MTArray x11 x12)
              then obtain stotp where stotp:"tp = STArray x11 stotp" using 2(4) iless True cps2mTypeCompatible.simps 
                by (metis stypes.exhaust)
              have tpt''comp:"cps2mTypeCompatible tp t'''" using 2(4) by simp

              have b20:"Some v'' = 
                    (case cps2mTypeConvert stotp of None \<Rightarrow> None
                  | Some t' \<Rightarrow>
                    let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 t') v'
                    in iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) stotp srcMem) m x11)"
                using cps2mrec.simps(1)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" " (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 stotp srcMem v' ] a30 stotp by auto
              then obtain t2 where t2Def:" cps2mTypeConvert stotp = Some t2" by fastforce
              then obtain m where b30:"m =  updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 t2) v'" by auto
              then have b40:"Some v'' = iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) stotp srcMem) m x11" 
                using b20 b30 t2Def by (metis (no_types, lifting) Option.option.simps(5))
              then have b50:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))" 
                using b30 iIsx unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
              have "\<forall>suffs. hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) suffs \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using hash_inequality by simp
              then have b60:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' =  accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m " 
                using cps2mAccessPrePost[of v'' "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" stotp srcMem m x11] b40 iIsx by presburger
              have "MCon t''' v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using STArray[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem "(Suc x)" t''' " (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] 2(4) a30 b20 t'''def 2 by simp
              then show ?thesis using b50 b60 mtr by simp (*need to show that loc2 is hash destl x*)
            next
              case (MTValue x2)
              then have stotp:"tp = (STValue x2)" using 2(4) iless True cps2mTypeCompatible.simps 
                by (metis stypes.exhaust)
              have tpt''comp:"cps2mTypeCompatible tp t'''" using 2(4) by simp
              then have b10:"(let v = accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem
     in Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v')) = Some v''" 
                using cps2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"  x2 srcMem v'] a30 stotp by simp
              then obtain v where b20:"v = accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem" by (simp split:option.splits memoryvalue.splits)
              then have b30:"v'' = (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v')" using b10 by (simp split:option.splits memoryvalue.splits)
              then have b40:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some (MValue v)" 
                using iIsx unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
              have "(\<forall>i\<in>{0..Suc x - 1}. SCon tp (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) srcMem)" using 2(3) SCon.simps(2)[of "Suc x" tp srcl srcMem ] by auto
              then have b50:"typeCon x2 (accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) srcMem)" using SCon.simps(1)[of x2 "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" srcMem] stotp iIsx by simp
              have b60:"(case srcMem $$ hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x) of None \<Rightarrow> ival x2 | Some v \<Rightarrow> v) = v" using b20 unfolding accessStorage_def by blast
              then show ?thesis  using iIsx MTValue b20 iless MCon.simps(1) b40 b50 by (metis (full_types, lifting) mtypes.simps(6) memoryvalue.simps(5) Option.option.simps(5))
            qed
          qed
        qed
      qed
      moreover have "(\<exists>p. accessStore destl v''' = Some (MPointer p)) \<or> accessStore destl v''' = None" 
      proof - 
        have "accessStore destl m = accessStore destl v'''"
          using cps2mAccessPrePost[of v''' srcl destl tp srcMem m x1] 
            accessStore_updateStore hash_inequality mdef v''def by blast
        moreover have "accessStore destl m = Some (MPointer destl)"
          using mdef unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis using MCon.simps(2)[of x1 t''' v''' destl]
        by (simp add: True)
    next
      case False
      then show ?thesis 
        using "**" t'''def by auto
    qed

    then show " MCon t' v''' destl" using t'''def by auto
  qed
next
  case (STMap x1 tp)
  then show ?case by simp
next
  case (STValue x)
  then show ?case
  proof intros
    assume a1:" SCon (STValue x) srcl srcMem \<and> cps2mTypeCompatible (STArray l (STValue x)) (MTArray l t') \<and> cps2mrec srcl destl (STValue x) srcMem a = Some v'''"
    then have *:"SCon (STValue x) srcl srcMem"
      and **:"cps2mTypeCompatible (STArray l (STValue x)) (MTArray l t')"
      and ***:"cps2mrec srcl destl (STValue x) srcMem a = Some v'''" by simp+

    then have a10:"Some v''' = (let v = accessStorage x srcl srcMem in Some (updateTypedStore destl (MValue v) (MTValue x) a))" 
      using cps2mrec.simps(2)[of srcl destl x srcMem a ] by simp

    then obtain v where b20:"v = accessStorage x srcl srcMem" by (simp split:option.splits memoryvalue.splits)
    then have b30:"v''' =  (updateTypedStore destl (MValue v) (MTValue x) a)" using a10 by (simp split:option.splits memoryvalue.splits)
    then have b40:"accessStore destl v''' = Some (MValue v)" unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
    then have b50:"typeCon x (accessStorage x srcl srcMem)" using SCon.simps(1)[of x "srcl" srcMem] * by simp
    have b60:"(case srcMem $$ srcl of None \<Rightarrow> ival x | Some v \<Rightarrow> v) = v" using b20 unfolding accessStorage_def by blast
    then have "typeCon x v" using b50 b20 by simp
    then show "MCon t' v''' destl"  using  STValue b20  MCon.simps(1) b40 
      by (metis memoryvalue.simps(5) Option.option.simps(5) a1 cps2mTypeCompatible.simps(1) cps2mTypeCompatible.simps(2) cps2mTypeCompatible.simps(6) extractType.cases)
  qed
qed


lemma cpm2srec_imps_SCon_dest :
  "(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon t' srcMem l) 
  \<and>(\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon t' srcMem srcl)
 \<and> cps2mTypeCompatible (STArray l tp) (MTArray l t') \<and>
   cpm2srec srcl destl t' srcMem a = Some v'''                    
          \<longrightarrow> SCon tp destl v'''"
proof (induction t' arbitrary:srcl destl srcMem a v''' l tp)
  case (MTArray x1 t')
  show ?case 
  proof intros
    assume "(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTArray x1 t') srcMem l) \<and>
    (\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon (MTArray x1 t') srcMem srcl) \<and> cps2mTypeCompatible (STArray l tp) (MTArray l (MTArray x1 t')) \<and> cpm2srec srcl destl (MTArray x1 t') srcMem a = Some v'''"
    then have *:"(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTArray x1 t') srcMem l)"
      and ****:"(\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon (MTArray x1 t') srcMem srcl)"
      and **:"cps2mTypeCompatible (STArray l tp) (MTArray l (MTArray x1 t'))"
      and ***:"cpm2srec srcl destl (MTArray x1 t') srcMem a = Some v'''"
      by blast+
    obtain t''' where t'''def:"tp = STArray x1 t'''" using ** 
      by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
    obtain ptr where ptrDef:"accessStore srcl srcMem = Some (MPointer ptr)"
      using ***  unfolding cpm2srec.simps by (auto split:option.splits memoryvalue.splits)
    then have a5:"(iter' (\<lambda>i. cpm2srec (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) a x1) = Some v'''" 
      using ***  unfolding cpm2srec.simps by simp

    then have "SCon (STArray x1 t''') destl v'''" 
    proof -

      have **:"cps2mTypeCompatible  (STArray x1 t''')  (MTArray x1 t')" using ** t'''def by auto
      have "\<forall>i<x1. SCon t''' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'''" using * ** ptrDef 
      proof(induction rule: iter'_induct[OF _ _ a5])
        case (1 v')
        then show ?case by simp
      next
        case (2 x v'')
        then obtain v'
          where a10:" iter' (\<lambda>i. cpm2srec (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' srcMem) a x = Some v'"
            and a20:"((\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTArray x t') srcMem l) \<longrightarrow>
          cps2mTypeCompatible (STArray x t''') (MTArray x t') \<longrightarrow> accessStore srcl srcMem = Some (MPointer ptr) 
          \<longrightarrow> (\<forall>i<x. SCon t''' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'))"
            and a30:"cpm2srec (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' srcMem v' = Some v''" by blast
        show ?case 
        proof intros
          fix i 
          assume iless:"i<Suc x"
          show "SCon t''' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" 
          proof(cases "i < x")
            case True
            then have scOA:"(\<forall>i<x. SCon t''' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v')" using a20 True 2 by auto 
            then have scO:"SCon t''' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" using True by simp
            then show ?thesis
              using cpm2srec_preserves_prior_child_scon[OF a30 scO True] by simp
          next 
            case False
            then have "i = x" using iless by auto
            moreover have "(\<forall>l. accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MPointer l) \<longrightarrow> MCon t' srcMem l)" 
              using "2.prems"(1) MCon_imps_sub_Mcon ptrDef by blast
            moreover have "(\<forall>val. accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MValue val) 
                            \<longrightarrow> MCon t' srcMem (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t x)))" 
              using "2.prems"(1) MCon_imps_sub_Mcon ptrDef by blast
            ultimately show ?thesis using a30 MTArray[of  "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem _ t''' "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] 
              using "2.prems"(2) by blast
          qed
        qed
      qed
      then show "SCon (STArray x1 t''') destl v'''" using t'''def by auto
    qed
    then show "SCon tp destl v'''" 
      by (simp add: t'''def)
  qed

next
  case (MTValue x)
  show ?case 
  proof intros
    assume **:"(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTValue x) srcMem l) \<and>
      (\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon (MTValue x) srcMem srcl) \<and>
      cps2mTypeCompatible (STArray l tp) (MTArray l (MTValue x)) \<and> cpm2srec srcl destl (MTValue x) srcMem a = Some v'''"
    then have *:"cpm2srec srcl destl (MTValue x) srcMem a = Some v'''" by simp
    then obtain v where ptrDef:"accessStore srcl srcMem = Some (MValue v)"
      unfolding cpm2srec.simps by (auto split:option.splits memoryvalue.splits)
    then have v'''Def:"(a(destl $$:= v)) =  v'''" using * unfolding cpm2srec.simps by (auto split:option.splits memoryvalue.splits)
    have mcMem:"MCon (MTValue x) srcMem srcl" using ptrDef ** by blast
    have "cps2mTypeCompatible tp (MTValue x)" using ** unfolding cps2mTypeCompatible.simps by simp
    then have "STValue x = tp" using cps2mTypeCompatible.simps 
      using cps2mTypeCompatible.elims(2) by auto
    moreover have "SCon (STValue x) destl v'''" using v'''Def mcMem ptrDef accessStorage_def unfolding SCon.simps MCon.simps by auto
    ultimately show "SCon tp destl v'''" using ** by simp
  qed
qed

subsubsection \<open>Top-Level Location Preservation\<close>
text \<open>
Any copy operation — recursive or iterated — preserves the top-level location tag (@{text Toploc})
of the memory.  This is a structural invariant: copies only update sub-locations within the
destination region and never relocate the overall memory object.

Results are given for both the single-step recursive functions (@{text cpm2mrec},
@{text cps2mrec}) and the iterated wrappers (@{text cpm2m}, @{text cps2m}).
\<close>

lemma cpm2mrecTopLocSame:
  shows " cpm2mrec srcl destl tp' srcMem a = Some v''' \<longrightarrow> Toploc a = Toploc v'''" 
proof( induction tp' arbitrary: srcl destl  a v''')
  case (MTArray x1 tp)
  show ?case  
  proof intros
    assume *:" cpm2mrec srcl destl (MTArray x1 tp) srcMem a = Some v'''"
    then have a10:"Some v''' = (case accessStore srcl srcMem of None \<Rightarrow> None | Some (MValue literal) \<Rightarrow> None
              | Some (MPointer l) \<Rightarrow> 
              let m = updateTypedStore destl (MPointer destl) (MTArray x1 tp) a in iter' (\<lambda>i m'. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem m') m x1)" using cpm2mrec.simps(1)[of srcl destl x1 tp srcMem a] by simp
    then obtain p where a20:"Some (MPointer p) =  accessStore srcl srcMem" by (auto split:option.splits memoryvalue.splits)
    then have a30:"Some v''' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 tp) a in iter' (\<lambda>i m'. cpm2mrec (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem m') m x1)"
      using a10 by (auto split:option.splits memoryvalue.splits)
    then obtain m where a40:"m =  updateTypedStore destl (MPointer destl) (MTArray x1 tp) a" by auto
    then have a50:"Toploc a = Toploc m"unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then have a60:"Some v''' =  iter' (\<lambda>i. cpm2mrec (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x1" using a10 a20 a30 a40 by metis
    then show "Toploc a =Toploc v'''" using a50
    proof(induction rule: iter'_induct[OF _ _ a60[symmetric]])
      case (1 v')
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v' 
        where b10:" iter' (\<lambda>i. cpm2mrec (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x = Some v'"
          and b20:"(Some v' = iter' (\<lambda>i. cpm2mrec (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x \<longrightarrow> Toploc a = Toploc m \<longrightarrow> Toploc a = Toploc v')"
          and b30: "cpm2mrec (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) tp srcMem v' = Some v''" by blast
      then have "Toploc a= Toploc v'" using 2 by simp
      then show ?case using MTArray[of " (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"  v' v''' ] b30  using MTArray by auto
    qed
  qed
next
  case (MTValue x)
  then show ?case using cpm2mrec.simps(2)[of srcl destl x srcMem a] unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
    by (auto split:option.splits memoryvalue.splits)
qed

lemma cps2mrecTopLocSame:
  shows " cps2mrec srcl destl tp' srcMem a = Some v''' \<longrightarrow> Toploc a = Toploc v'''" 
proof( induction tp' arbitrary: srcl destl  a v''')
  case (STArray x1 tp)
  show ?case  
  proof intros
    assume *:" cps2mrec srcl destl (STArray x1 tp) srcMem a = Some v'''"
    then have a10:"Some v''' = (case cps2mTypeConvert tp of None \<Rightarrow> None
     | Some t' \<Rightarrow>
         let m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a
         in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x1)" 
      using cps2mrec.simps(1)[of srcl destl x1 tp srcMem a] by simp
    then obtain t' where t'Def:"cps2mTypeConvert tp = Some t'" by fastforce
    then obtain m where a40:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a" by auto
    then have a50:"Toploc a = Toploc m" unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then have a60:"Some v''' =  iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x1" 
      using a10 a40 t'Def by (metis (no_types, lifting) Option.option.simps(5))
    then show "Toploc a =Toploc v'''" using a50
    proof(induction rule: iter'_induct[OF _ _ a60[symmetric]])
      case (1 v')
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v' 
        where b10:" iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x = Some v'"
          and b20:"(Some v' = iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) m x \<longrightarrow> Toploc a = Toploc m \<longrightarrow> Toploc a = Toploc v')"
          and b30: "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) tp srcMem v' = Some v''" by blast
      then have "Toploc a= Toploc v'" using 2 by simp
      then show ?case using STArray[of " (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"  v' v''' ] b30  using STArray by auto
    qed
  qed
next
  case (STValue x)
  then show ?case using cps2mrec.simps(2)[of srcl destl x srcMem a] 
    unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def 
    by (auto split:option.splits memoryvalue.splits)
next 
  case (STMap k v)
  then show ?case using cps2mrec.simps(3) by simp
qed

lemma cpm2mTopLocSame:
  assumes "iter' (\<lambda>i m. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
    and "x>0"
  shows "Toploc md = Toploc updM"
proof (rule iter'_invariant[OF assms(1)])
  show "Toploc md = Toploc md" by simp
next
  fix i m m'
  assume "Toploc md = Toploc m"
    and "cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  then show "Toploc md = Toploc m'" using cpm2mrecTopLocSame by auto
qed

lemma cps2mTopLocSame:
  assumes "iter' (\<lambda>i m. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "Toploc md = Toploc updM"
proof (rule iter'_invariant[OF assms(1)])
  show "Toploc md = Toploc md" by simp
next
  fix i m m'
  assume "Toploc md = Toploc m"
    and "cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  then show "Toploc md = Toploc m'" using cps2mrecTopLocSame by auto
qed

subsubsection \<open>Iterated Single-Change Lemmas: Location-Prefix Restriction\<close>
text \<open>
These lemmas lift the recursive single-change results to the iterated copies @{text cpm2m},
@{text cpm2s}.  A location that is not a sub-prefix of the destination root (or is the root
itself) is unchanged in both the value and type stores after the full iteration.

The proof uses @{text iter'_invariant}: the property is maintained as an invariant across every
step of the iteration, relying on the recursive single-change lemmas from the previous section.
Variants cover memory-to-memory (@{text cpm2m}), memory-to-storage (@{text cpm2s}), and
separate value/type store projections.
\<close>

lemma cpm2mSingleChange:
  assumes "iter' (\<lambda>i m. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStore locs md = accessStore locs updM"
proof (rule iter'_invariant[OF assms(1)])
  show "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStore locs md = accessStore locs md" by simp
next
  fix i m m'
  assume IH:"\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStore locs md = accessStore locs m"
    and step:"cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  show "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStore locs md = accessStore locs m'"
  proof intros
    fix locs
    assume *:"\<not>LSubPrefL2 locs ld \<or> locs = ld"
    then have "accessStore locs md = accessStore locs m" using IH by simp
    moreover have "accessStore locs m = accessStore locs m'"
      using cpm2mrec_SubPrefixes[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t ms m m']
      using step * Not_Sub_More_Specific by (metis cpm2mrec_preserves_dest_root)
    ultimately show "accessStore locs md = accessStore locs m'" by simp
  qed
qed

lemma cpm2mSingleChange_Typed:
  assumes "iter' (\<lambda>i m. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs updM"
proof (rule iter'_invariant[OF assms(1)])
  show "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs md" by simp
next
  fix i m m'
  assume IH:"\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs m"
    and step:"cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  show "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs m'"
  proof intros
    fix locs
    assume *:"\<not>LSubPrefL2 locs ld \<or> locs = ld"
    then have "accessTypeStore locs md = accessTypeStore locs m" using IH by simp
    moreover have "accessTypeStore locs m = accessTypeStore locs m'"
      using cpm2mrec_SubPrefixes_both[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t ms m m']
      using step * Not_Sub_More_Specific by (metis cpm2mrec_preserves_dest_root_typed)
    ultimately show "accessTypeStore locs md = accessTypeStore locs m'" by simp
  qed
qed

lemma cpm2sSingleChange:
  assumes "iter' (\<lambda>i m. cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStorage t' locs md = accessStorage t' locs updM"
proof (rule iter'_invariant[OF assms(1)])
  show "\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStorage t' locs md = accessStorage t' locs md" by simp
next
  fix i m m'
  assume IH:"\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStorage t' locs md = accessStorage t' locs m"
    and step:"cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  show "\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStorage t' locs md = accessStorage t' locs m'"
  proof intros
    fix t' locs
    assume *:"\<not>LSubPrefL2 locs ld \<or> locs = ld"
    then have "accessStorage t' locs md = accessStorage t' locs m" using IH by simp
    moreover have "accessStorage t' locs m = accessStorage t' locs m'"
      using cpm2srec_SubPrefixes[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t ms m m']
      using step * Not_Sub_More_Specific by (metis cpm2srec_preserves_dest_root)
    ultimately show "accessStorage t' locs md = accessStorage t' locs m'" by simp
  qed
qed

lemma cps2mSingleChange_both:
  assumes "iter' (\<lambda>i m. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow>
      accessStore locs md = accessStore locs updM
    \<and> accessTypeStore locs md = accessTypeStore locs updM"
proof (rule iter'_invariant[OF assms(1)])
  show "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow>
      accessStore locs md = accessStore locs md
    \<and> accessTypeStore locs md = accessTypeStore locs md"
    by simp
next
  fix i m m'
  assume IH:
    "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow>
      accessStore locs md = accessStore locs m
    \<and> accessTypeStore locs md = accessTypeStore locs m"
    and step: "cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  show "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow>
      accessStore locs md = accessStore locs m'
    \<and> accessTypeStore locs md = accessTypeStore locs m'"
  proof intros
    fix locs
    assume asm: "\<not>LSubPrefL2 locs ld \<or> locs = ld"
    then have inv1:
      "accessStore locs md = accessStore locs m
        \<and> accessTypeStore locs md = accessTypeStore locs m"
      using IH by blast
    have inv2:
      "accessStore locs m = accessStore locs m'
        \<and> accessTypeStore locs m = accessTypeStore locs m'"
    proof (cases "locs = ld")
      case True
      then show ?thesis
        using step cps2mrec_preserves_dest_root_both by simp
    next
      case False
      with asm have not_sub: "\<not>LSubPrefL2 locs ld" by simp
      have not_sub_child: "\<not>LSubPrefL2 locs (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
        using not_sub Not_Sub_More_Specific by simp
      show ?thesis
        using cps2mrec_SubPrefixes_both[
          of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t ms m m'] step not_sub_child
        by blast
    qed
    show "accessStore locs md = accessStore locs m'"
      using inv1 inv2 by simp
    show "accessTypeStore locs md = accessTypeStore locs m'"
      using inv1 inv2 by simp
  qed
qed

lemma cps2mSingleChange:
  assumes "iter' (\<lambda>i m. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStore locs md = accessStore locs updM"
  using cps2mSingleChange_both[OF assms] by blast

lemma cps2mSingleChange_Typed:
  assumes "iter' (\<lambda>i m. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs updM"
  using cps2mSingleChange_both[OF assms] by blast

subsubsection \<open>Sub-Prefix Preservation: Typed Membership Condition\<close>
text \<open>
A second family of sub-prefix preservation lemmas, using @{text TypedMemSubPref} and
@{text TypedStoSubpref} instead of the plain @{text LSubPrefL2} relation.  These predicates
combine location prefix membership with the array-length information encoded in the type,
giving a tighter characterisation of which locations are modified.

A location that is not the destination root and is not a typed sub-prefix of the destination
is unchanged in both the value and type stores.  Results are given for @{text cpm2mrec},
@{text cps2mrec} (recursive), and their @{text both}-access counterparts.
\<close>


lemma cpm2mrec_dest_case:
  assumes step: "cpm2mrec srcl destl t ms md = Some v''"
    and mcon: "MCon t v'' destl"
  shows "case accessStore destl v'' of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v'' destl | _ \<Rightarrow> False)
          | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)"
proof (cases t)
  case (MTArray x1 t')
  obtain l where ldef: "accessStore srcl ms = Some (MPointer l)"
    using step cpm2mrec.simps(1)[of srcl destl x1 t' ms md] MTArray unfolding Let_def
    by (auto split: if_splits option.splits memoryvalue.splits)
  let ?m = "updateTypedStore destl (MPointer destl) (MTArray x1 t') md"
  have expanded:
    "Some v'' =
      (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t') md
       in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) m x1)"
    using step ldef MTArray cpm2mrec.simps(1)[of srcl destl x1 t' ms md]  unfolding Let_def 
    by (auto split: if_splits option.splits memoryvalue.splits)
  have run:
    "iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) ?m x1 = Some v''"
    using expanded unfolding Let_def by simp
  have keep_store:
    "accessStore destl ?m = accessStore destl v''"
    using cpm2mSingleChange run 
    by blast
  have root_ptr:
    "accessStore destl v'' = Some (MPointer destl)"
    using keep_store
    unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
    by simp
  show ?thesis
    using root_ptr mcon MTArray by simp
next
  case (MTValue x)
  then obtain v where vdef: "accessStore srcl ms = Some (MValue v)"
    using step cpm2mrec.simps(2)[of srcl destl x ms md]
    by (auto split: option.splits memoryvalue.splits)
  then have v''def: "v'' = updateTypedStore destl (MValue v) (MTValue x) md"
    using step MTValue cpm2mrec.simps(2)[of srcl destl x ms md] by simp
  then show ?thesis
    using mcon MTValue
    unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
    by simp
qed


lemma cps2mrec_dest_case:
  assumes step: "cps2mrec srcl destl tp ms md = Some v''"
    and mcon: "MCon t v'' destl"
  shows "case accessStore destl v'' of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v'' destl | _ \<Rightarrow> False)
          | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)"
proof (cases tp)
  case (STArray x1 tp')
  obtain tt where conv: "cps2mTypeConvert tp' = Some tt"
    using step STArray cps2mrec.simps(1)[of srcl destl x1 tp' ms md]
    by (auto split: option.splits memoryvalue.splits)
  let ?m = "updateTypedStore destl (MPointer destl) (MTArray x1 tt) md"
  have expanded:
    "Some v'' =
      (let m = updateTypedStore destl (MPointer destl) (MTArray x1 tt) md
       in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp' ms) m x1)"
    using step STArray conv by (simp add: cps2mrec.simps(1))
  have run:
    "iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp' ms) ?m x1 = Some v''"
    using expanded unfolding Let_def by simp
  have keep_store:
    "accessStore destl ?m = accessStore destl v''"
    using cps2mSingleChange[OF run] by simp
  have root_ptr:
    "accessStore destl v'' = Some (MPointer destl)"
    using keep_store
    unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
    by simp
  then show ?thesis
    using keep_store mcon STArray
    by (metis mcon root_ptr  memoryvalue.simps(6)  mtypes.exhaust  Option.option.simps(5)  mtypes.simps(5)  MCon.simps(1))
next
  case (STMap x1 tp')
  then show ?thesis
    using step cps2mrec.simps(3) by simp
next
  case (STValue x)
  have v''def: "v'' = updateTypedStore destl (MValue (accessStorage x srcl ms)) (MTValue x) md"
    using step STValue cps2mrec.simps(2)[of srcl destl x ms md] by simp
  have root_val:
    "accessStore destl v'' = Some (MValue (accessStorage x srcl ms))"
    using v''def
    unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
    by simp
  then show ?thesis
    using mcon STValue root_val
    by (cases t, auto split: option.splits memoryvalue.splits)
qed


lemma cpm2mrec_SubPrefixes2_both:
  "cpm2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'. destl' \<noteq> destl \<and> (\<not> TypedMemSubPref destl' destl tp)
    \<longrightarrow> accessStore destl' a = accessStore destl' v'''
      \<and> accessTypeStore destl' a = accessTypeStore destl' v''')"
proof (induction tp arbitrary: srcl destl srcMem a v''')
  case (MTArray x1 t)
  show ?case
  proof
    assume run: "cpm2mrec srcl destl (MTArray x1 t) srcMem a = Some v'''"
    then obtain l where src_ptr: "accessStore srcl srcMem = Some (MPointer l)"
      using cpm2mrec.simps(1)[of srcl destl x1 t srcMem a]
      by (auto split: if_splits option.splits memoryvalue.splits)
    have expanded:
      "Some v''' =
        (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a
         in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1)"
      using run src_ptr cpm2mrec.simps(1)[of srcl destl x1 t srcMem a] by simp
    then obtain m where mdef: "m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a" by auto
    have iter_run:
      "iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1 = Some v'''"
      using expanded mdef by presburger
    have init:
      "\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray 0 t)
        \<longrightarrow> accessStore destl' a = accessStore destl' m
          \<and> accessTypeStore destl' a = accessTypeStore destl' m"
      using mdef updateTypedStore_neq_loc by metis
    have step:
      "\<And>i m1 m2.
        (\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray i t)
          \<longrightarrow> accessStore destl' a = accessStore destl' m1
            \<and> accessTypeStore destl' a = accessTypeStore destl' m1)
        \<Longrightarrow> cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m1 = Some m2
        \<Longrightarrow> (\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray (Suc i) t)
          \<longrightarrow> accessStore destl' a = accessStore destl' m2
            \<and> accessTypeStore destl' a = accessTypeStore destl' m2)"
    proof intros
      fix i m1 m2 destl'
      assume IH_iter:
        "\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray i t)
          \<longrightarrow> accessStore destl' a = accessStore destl' m1
            \<and> accessTypeStore destl' a = accessTypeStore destl' m1"
      assume rec: "cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m1 = Some m2"
      assume asm: "destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray (Suc i) t)"
      have asm_prev: "destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray i t)"
        using asm TypedMemSubPref.simps(2) lessI 
        by auto
      then have inv1:
        "accessStore destl' a = accessStore destl' m1
          \<and> accessTypeStore destl' a = accessTypeStore destl' m1"
        using IH_iter by blast
      have asm_child:
        "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> \<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t"
        using asm by (metis TypedMemSubPref.simps(2) lessI)
      have inv2:
        "accessStore destl' m1 = accessStore destl' m2
          \<and> accessTypeStore destl' m1 = accessTypeStore destl' m2"
        using MTArray.IH[of "hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)" "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" srcMem m1 m2] rec asm_child
        by blast
      show
        "accessStore destl' a = accessStore destl' m2" using inv1 inv2 by simp
      show "accessTypeStore destl' a = accessTypeStore destl' m2" using inv1 inv2
        by auto
    qed
    have final_inv:
      "\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x1 t)
        \<longrightarrow> accessStore destl' a = accessStore destl' v'''
          \<and> accessTypeStore destl' a = accessTypeStore destl' v'''"
      using iter'_indexed_invariant[
        where P = "\<lambda>i m1. \<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray i t)
          \<longrightarrow> accessStore destl' a = accessStore destl' m1
            \<and> accessTypeStore destl' a = accessTypeStore destl' m1",
        OF iter_run init step] .
    show "\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x1 t)
      \<longrightarrow> accessStore destl' a = accessStore destl' v'''
        \<and> accessTypeStore destl' a = accessTypeStore destl' v'''"
      using final_inv .
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix destl'
    assume run: "cpm2mrec srcl destl (MTValue x) srcMem a = Some v'''"
    assume asm: "destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTValue x)"
    then obtain v where src_val: "accessStore srcl srcMem = Some (MValue v)"
      using run cpm2mrec.simps(2)[of srcl destl x srcMem a]
      by (auto split: option.splits memoryvalue.splits)
    have asm2:"v''' = updateTypedStore destl (MValue v) (MTValue x) a"
      using run src_val cpm2mrec.simps(2)[of srcl destl x srcMem a] by simp
    then show "accessStore destl' a = accessStore destl' v'''"
      using asm updateTypedStore_neq_loc by metis
    show "accessTypeStore destl' a = accessTypeStore destl' v'''"
      using asm asm2 updateTypedStore_neq_loc by metis
  qed
qed

lemma cpm2mrec_SubPrefixes2:
  "cpm2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'. destl' \<noteq> destl \<and> (\<not> TypedMemSubPref destl' destl tp) \<longrightarrow> accessStore destl' a = accessStore destl' v''')" 
  using cpm2mrec_SubPrefixes2_both by blast

lemma cpm2mrec_SubPrefixes2_typed:
  "cpm2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'. destl' \<noteq> destl \<and> (\<not> TypedMemSubPref destl' destl tp) \<longrightarrow> accessTypeStore destl' a = accessTypeStore destl' v''')" 
  using cpm2mrec_SubPrefixes2_both by blast

lemma cps2mrec_SubPrefixes2_both:
  "cps2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'.  destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl tp \<longrightarrow>
      accessStore destl' a = accessStore destl' v'''
    \<and> accessTypeStore destl' a = accessTypeStore destl' v''')"
proof (induction tp arbitrary: srcl destl srcMem a v''')
  case (STArray x1 t)
  show ?case
  proof
    assume run: "cps2mrec srcl destl (STArray x1 t) srcMem a = Some v'''"
    have expanded:
      "Some v''' = (case cps2mTypeConvert t of None \<Rightarrow> None
       | Some t' \<Rightarrow>
           let m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a
           in iter' (\<lambda>i m'. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m') m x1)"
      using run cps2mrec.simps(1)[of srcl destl x1 t srcMem a]
      by (auto split: option.splits memoryvalue.splits)
    then obtain t' where t'def:"cps2mTypeConvert t = Some t'" by fastforce
    then obtain m where mdef:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a" by auto
    have iter_run0:
      "iter' (\<lambda>i m'. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m')
        (updateTypedStore destl (MPointer destl) (MTArray x1 t') a) x1 = Some v'''"
      using run t'def unfolding cps2mrec.simps(1) Let_def by (simp)
    have iter_run:
      "iter' (\<lambda>i m'. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m') m x1 = Some v'''"
      using iter_run0 mdef by simp
    have init:
      "\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray 0 t)
        \<longrightarrow> accessStore destl' a = accessStore destl' m
          \<and> accessTypeStore destl' a = accessTypeStore destl' m"
      using mdef updateTypedStore_neq_loc by metis
    have step:
      "\<And>i m1 m2.
        (\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray i t)
          \<longrightarrow> accessStore destl' a = accessStore destl' m1
            \<and> accessTypeStore destl' a = accessTypeStore destl' m1)
        \<Longrightarrow> cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m1 = Some m2
        \<Longrightarrow> (\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray (Suc i) t)
          \<longrightarrow> accessStore destl' a = accessStore destl' m2
            \<and> accessTypeStore destl' a = accessTypeStore destl' m2)"
    proof intros
      fix i m1 m2 destl'
      assume IH_iter:
        "\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray i t)
          \<longrightarrow> accessStore destl' a = accessStore destl' m1
            \<and> accessTypeStore destl' a = accessTypeStore destl' m1"
      assume rec: "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m1 = Some m2"
      assume asm: "destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray (Suc i) t)"
      have asm_prev: "destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray i t)"
        using asm TypedStoSubpref.simps(2) lessI by auto
      then have inv1:
        "accessStore destl' a = accessStore destl' m1
          \<and> accessTypeStore destl' a = accessTypeStore destl' m1"
        using IH_iter by blast
      have asm_child:
        "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> \<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t"
        using asm 
        using TypedStoSubpref_sameLoc by auto 
      have inv2:
        "accessStore destl' m1 = accessStore destl' m2
          \<and> accessTypeStore destl' m1 = accessTypeStore destl' m2"
        using STArray.IH[of "hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" srcMem m1 m2] rec asm_child
        by blast
      show "accessStore destl' a = accessStore destl' m2"
        using inv1 inv2 by simp
      show "accessTypeStore destl' a = accessTypeStore destl' m2"
        using inv1 inv2 by auto
    qed
    have final_inv:
      "\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray x1 t)
        \<longrightarrow> accessStore destl' a = accessStore destl' v'''
          \<and> accessTypeStore destl' a = accessTypeStore destl' v'''"
      using iter'_indexed_invariant[
        where P = "\<lambda>i m1. \<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray i t)
          \<longrightarrow> accessStore destl' a = accessStore destl' m1
            \<and> accessTypeStore destl' a = accessTypeStore destl' m1",
        OF iter_run init step] .
    show "\<forall>destl'. destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STArray x1 t)
      \<longrightarrow> accessStore destl' a = accessStore destl' v'''
        \<and> accessTypeStore destl' a = accessTypeStore destl' v'''"
      using final_inv .
  qed
next
  case (STValue x)
  show ?case
  proof intros
    fix destl'
    assume run: "cps2mrec srcl destl (STValue x) srcMem a = Some v'''"
    assume asm: "destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl (STValue x)"
    have result:
      "v''' = updateTypedStore destl (MValue (accessStorage x srcl srcMem)) (MTValue x) a"
      using run cps2mrec.simps(2)[of srcl destl x srcMem a] by simp
    then show "accessStore destl' a = accessStore destl' v'''"
      using asm updateTypedStore_neq_loc by metis
    show "accessTypeStore destl' a = accessTypeStore destl' v'''"
      using asm result updateTypedStore_neq_loc by metis
  qed
next
  case (STMap x1 tp)
  then show ?case using cps2mrec.simps(3) by auto
qed

lemma cps2mrec_SubPrefixes2:
  "cps2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'.  destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl tp \<longrightarrow> accessStore destl' a = accessStore destl' v''')"
  using cps2mrec_SubPrefixes2_both by blast

lemma cps2mrec_SubPrefixes2_Typed:
  "cps2mrec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl'.  destl' \<noteq> destl \<and> \<not> TypedStoSubpref destl' destl tp \<longrightarrow> accessTypeStore destl' a = accessTypeStore destl' v''')"
  using cps2mrec_SubPrefixes2_both by blast

lemma cpm2srec_SubPrefixes2:
  "cpm2srec srcl destl tp srcMem a = Some v''' \<longrightarrow>
  (\<forall>destl' tp' t.  destl' \<noteq> destl \<and> cps2mTypeCompatible tp' tp \<and> \<not> TypedStoSubpref destl' destl tp' \<longrightarrow> accessStorage t destl' a = accessStorage t destl' v''')"
proof(induction tp arbitrary:srcl destl srcMem a v''' )
  case (MTArray x1 tp)
  show ?case 
  proof intros
    fix destl' tp' t 
    assume **:"cpm2srec srcl destl (MTArray x1 tp) srcMem a = Some v'''"
      and ***:"destl' \<noteq> destl \<and> cps2mTypeCompatible tp' (MTArray x1 tp) \<and> \<not> TypedStoSubpref destl' destl tp'"
    then obtain l where ldef:"accessStore srcl srcMem = Some (MPointer l)"
      using ** cpm2srec.simps(1)[of srcl destl x1 tp srcMem a ] by (auto split:if_splits option.splits memoryvalue.splits)
    then have a5:"Some v''' =   iter' (\<lambda>i. cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) a x1" 
      using ** cpm2srec.simps(1)[of srcl destl x1 tp srcMem a ] by (auto split:if_splits option.splits memoryvalue.splits)
    obtain st where stDef:"tp' = STArray x1 st" using *** 
      by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
    then have comp:" cps2mTypeCompatible (STArray x1 st) (MTArray x1 tp)" 
      using "***" by auto
    then have sub:"\<not> TypedStoSubpref destl' destl (STArray x1 st)" using *** stDef by blast
    show "accessStorage t destl' a = accessStorage t destl' v'''" using comp sub
    proof(induction rule: iter'_induct[OF _ _ a5[symmetric]]) 
      case (1 v')
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp srcMem) a x = Some v'"
          and a20:"(cps2mTypeCompatible (STArray x st) (MTArray x tp)  \<longrightarrow> \<not> TypedStoSubpref destl' destl (STArray x st) \<longrightarrow> accessStorage t destl' a = accessStorage t destl' v')"
          and a30:"cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) tp srcMem v' = Some v''" by blast

      then show ?case
      proof(cases tp)
        case (MTArray x11 x12)
        then show ?thesis 
        proof(cases "x = 0")
          case True
          then have "a = v'" using a10 by simp
          then show ?thesis 
            by (metis "2.prems"(1,2) MTArray.IH True TypedStoSubpref_sameLoc a30 cps2mTypeCompatible.simps(2) TypedStoSubpref.simps(2))
        next
          case False
          then have "accessStorage t destl' a = accessStorage t destl' v'" using a20 2 by simp
          moreover have "accessStorage t destl' v' = accessStorage t destl' v''" 
            using MTArray.IH[of "(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem v' v''] a30 
            by (metis "2.prems"(1,2) TypedStoSubpref_sameLoc cps2mTypeCompatible.simps(2) lessI TypedStoSubpref.simps(2))
          ultimately show ?thesis using MTArray.IH[of "(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem v' v''] a30 by auto
        qed
      next
        case (MTValue x2)
        then have a50:"cpm2srec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTValue x2) srcMem v' = Some v''" using a30 by simp
        then obtain v where vdef: "accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem  = Some (MValue v)" 
          using a30 unfolding cpm2srec.simps by (auto split:if_splits option.splits memoryvalue.splits)
        then have a70:"Some v'' = Some (v'(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) $$:= v))" using a50 unfolding cpm2srec.simps by (auto split:if_splits option.splits memoryvalue.splits)
        then show ?thesis 
        proof(cases "x = 0")
          case True
          then have "a = v'" using a10 by simp
          then show ?thesis 
            using "2.prems"(1,2) MTArray True a30 
            by (metis TypedStoSubpref_sameLoc cps2mTypeCompatible.simps(2) TypedStoSubpref.simps(2))
        next
          case False
          then have "x>0" by blast
          then have "cps2mTypeCompatible (STArray x st) (MTArray x tp)" 
            using "2.prems"(1) by auto
          have "accessStorage t destl' a = accessStorage t destl' v'" using a20 False 2 by simp
          moreover have "accessStorage t destl' v' = accessStorage t destl' v''" using a30 
            by (metis "2.prems"(2) MTArray TypedStoSubpref_sameLoc \<open>cps2mTypeCompatible (STArray x st) (MTArray x tp)\<close> cps2mTypeCompatible.simps(2) lessI
                TypedStoSubpref.simps(2))
          ultimately show ?thesis using a70 a50 a20 by auto
        qed
      qed
    qed
  qed
next
  case (MTValue x)
  then show ?case 
  proof intros
    fix destl' tp' t 
    assume *:"cpm2srec srcl destl (MTValue x) srcMem a = Some v'''" 
      and **:"destl' \<noteq> destl \<and> cps2mTypeCompatible tp' (MTValue x) \<and> \<not> TypedStoSubpref destl' destl tp'"
    then obtain v where vdef: "accessStore srcl srcMem  = Some (MValue v)" 
      unfolding cpm2srec.simps by (auto split:if_splits option.splits memoryvalue.splits)
    then have "Some v''' = Some (a(destl $$:= v))" using * unfolding cpm2srec.simps by (auto split:if_splits option.splits memoryvalue.splits)
    moreover have "destl' \<noteq> destl" using ** LSubPrefL2_def by simp
    ultimately show "accessStorage t destl' a = accessStorage t destl' v''' " using ** accessStorage_def 
      by auto
  qed
qed

subsubsection \<open>Iterated Single-Change Lemmas: Typed Sub-Prefix Restriction\<close>
text \<open>
These lemmas strengthen the earlier single-change results by using the typed sub-prefix
predicates (@{text TypedMemSubPref} and @{text TypedStoSubpref}) rather than the plain
location-prefix relation.  A location that is not a typed sub-prefix of the destination
(taking into account the array length encoded in the type) is guaranteed to be unmodified.

Variants are provided for value store, type store, and combined (@{text both}) access, and for
all three iterated copy directions: memory-to-memory (@{text cpm2m}), memory-to-storage
(@{text cpm2s}), and storage-to-memory (@{text cps2m}).
\<close>

lemma cpm2mSingleChange2:
  assumes "iter' (\<lambda>i m. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs.  \<not>TypedMemSubPref locs ld (MTArray x t) \<longrightarrow> accessStore locs md = accessStore locs updM"
proof (rule iter'_indexed_invariant[OF assms(1)])
  show "\<forall>locs. \<not>TypedMemSubPref locs ld (MTArray 0 t) \<longrightarrow> accessStore locs md = accessStore locs md" by simp
next
  fix i m m'
  assume IH:"\<forall>locs. \<not>TypedMemSubPref locs ld (MTArray i t) \<longrightarrow> accessStore locs md = accessStore locs m"
    and step:"cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  show "\<forall>locs. \<not>TypedMemSubPref locs ld (MTArray (Suc i) t) \<longrightarrow> accessStore locs md = accessStore locs m'"
  proof intros
    fix locs
    assume *:"\<not>TypedMemSubPref locs ld (MTArray (Suc i) t)"
    then have "accessStore locs md = accessStore locs m" using IH by auto
    moreover have "accessStore locs m = accessStore locs m'"
      using cpm2mrec_SubPrefixes2[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t ms m m']
      using * step by auto
    ultimately show "accessStore locs md = accessStore locs m'" by simp
  qed
qed

lemma cpm2mSingleChange2_typed:
  assumes "iter' (\<lambda>i m. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs.  \<not>TypedMemSubPref locs ld (MTArray x t) \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs updM"
proof (rule iter'_indexed_invariant[OF assms(1)])
  show "\<forall>locs. \<not>TypedMemSubPref locs ld (MTArray 0 t) \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs md" by simp
next
  fix i m m'
  assume IH:"\<forall>locs. \<not>TypedMemSubPref locs ld (MTArray i t) \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs m"
    and step:"cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  show "\<forall>locs. \<not>TypedMemSubPref locs ld (MTArray (Suc i) t) \<or> locs = ld \<longrightarrow> accessTypeStore locs md = accessTypeStore locs m'"
  proof intros
    fix locs
    assume *:"\<not>TypedMemSubPref locs ld (MTArray (Suc i) t) \<or> locs = ld"
    then have "accessTypeStore locs md = accessTypeStore locs m" using IH by auto
    moreover have "accessTypeStore locs m = accessTypeStore locs m'"
      using cpm2mrec_SubPrefixes2_typed[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t ms m m']
      using * step by (metis TypedMemSubPref.simps(2) lessI cpm2mrec_preserves_dest_root_typed)
    ultimately show "accessTypeStore locs md = accessTypeStore locs m'" by simp
  qed
qed


lemma cpm2sSingleChange2:
  assumes "iter' (\<lambda>i m. cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs t' t''.  cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> ld 
        \<and> \<not>TypedStoSubpref locs ld (STArray x t') \<longrightarrow> accessStorage t'' locs md = accessStorage t'' locs updM"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md x = Some v'"
      and a20:"(\<forall>locs t' t''. cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> ld \<and> \<not> TypedStoSubpref locs ld (STArray x t') \<longrightarrow> accessStorage t'' locs md = accessStorage t'' locs v')"
      and a30:"cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
  show ?case 
  proof intros
    fix locs t' t''
    assume *:"cps2mTypeCompatible (STArray (Suc x) t') (MTArray (Suc x) t) \<and> locs \<noteq> ld \<and> \<not> TypedStoSubpref locs ld (STArray (Suc x) t')"
    then show "accessStorage t'' locs md = accessStorage t'' locs v''" 
    proof(cases "x = 0")
      case True
      then have "accessStorage t'' locs md = accessStorage t'' locs v'"  using a10 by simp
      then show ?thesis using cpm2srec_SubPrefixes2 a30 
        using "*" 
        by (metis True TypedStoSubpref_sameLoc cps2mTypeCompatible.simps(2) TypedStoSubpref.simps(2))
    next
      case False
      then have "cps2mTypeCompatible (STArray x t') (MTArray x t)"  
        by (meson "*" bot_nat_0.not_eq_extremum cps2mTypeCompatible.simps(2))
      have "\<not> TypedStoSubpref locs ld (STArray x t')" using False * by simp
      have "\<not> TypedStoSubpref locs ld (STArray x t') \<longrightarrow> accessStorage t'' locs md = accessStorage t'' locs v'" using a20 
        using "*" \<open>cps2mTypeCompatible (STArray x t') (MTArray x t)\<close> by blast
      then show ?thesis using a30 cpm2srec_SubPrefixes2 * 
        by (metis TypedStoSubpref_sameLoc \<open>\<not> TypedStoSubpref locs ld (STArray x t')\<close> cps2mTypeCompatible.simps(2) lessI TypedStoSubpref.simps(2))
    qed

  qed
qed

lemma cps2mSingleChange2_both:
  assumes "iter' (\<lambda>i m. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs. locs \<noteq> ld \<and> \<not>TypedStoSubpref locs ld (STArray x t) \<longrightarrow>
      accessStore locs md = accessStore locs updM
    \<and> accessTypeStore locs md = accessTypeStore locs updM"
proof (rule iter'_indexed_invariant[OF assms(1)])
  show "\<forall>locs. locs \<noteq> ld \<and> \<not>TypedStoSubpref locs ld (STArray 0 t) \<longrightarrow>
      accessStore locs md = accessStore locs md
    \<and> accessTypeStore locs md = accessTypeStore locs md"
    by simp
next
  fix i m m'
  assume IH:
    "\<forall>locs. locs \<noteq> ld \<and> \<not>TypedStoSubpref locs ld (STArray i t) \<longrightarrow>
      accessStore locs md = accessStore locs m
    \<and> accessTypeStore locs md = accessTypeStore locs m"
    and step: "cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m = Some m'"
  show "\<forall>locs. locs \<noteq> ld \<and> \<not>TypedStoSubpref locs ld (STArray (Suc i) t) \<longrightarrow>
      accessStore locs md = accessStore locs m'
    \<and> accessTypeStore locs md = accessTypeStore locs m'"
  proof intros
    fix locs
    assume asm: "locs \<noteq> ld \<and> \<not>TypedStoSubpref locs ld (STArray (Suc i) t)"
    have asm_prev: "locs \<noteq> ld \<and> \<not>TypedStoSubpref locs ld (STArray i t)"
      using asm TypedStoSubpref.simps(2) lessI by auto
    then have inv1:
      "accessStore locs md = accessStore locs m
        \<and> accessTypeStore locs md = accessTypeStore locs m"
      using IH by blast
    have asm_child:
      "locs \<noteq> hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> \<not>TypedStoSubpref locs (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t"
      using asm 
      by (metis asm TypedStoSubpref.simps(2) TypedStoSubpref_sameLoc lessI)
    have inv2:
      "accessStore locs m = accessStore locs m'
        \<and> accessTypeStore locs m = accessTypeStore locs m'"
      using cps2mrec_SubPrefixes2_both[
        of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t ms m m'] step asm_child
      by blast
    show "accessStore locs md = accessStore locs m'"
      using inv1 inv2 by simp
    show "accessTypeStore locs md = accessTypeStore locs m'"
      using inv1 inv2 by simp
  qed
qed

lemma cps2mSingleChange2:
  assumes "iter' (\<lambda>i m. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs. locs \<noteq> ld \<and> \<not>TypedStoSubpref locs ld (STArray x t) \<longrightarrow> accessStore locs md = accessStore locs updM"
  using cps2mSingleChange2_both[OF assms] by blast

lemma cps2mSingleChange2_Typed:
  assumes "iter' (\<lambda>i m. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
  shows "\<forall>locs. locs \<noteq> ld \<and> \<not>TypedStoSubpref locs ld (STArray x t) \<longrightarrow> accessTypeStore locs md = accessTypeStore locs updM"
  using cps2mSingleChange2_both[OF assms] by blast

subsubsection \<open>Memory and Storage Consistency Propagation Under Iterated Copies\<close>
text \<open>
These are the main correctness lemmas for the iterated copy operations.  They establish that
copying a well-formed (@{text MCon} or @{text SCon}) source array into a destination produces
a well-formed destination array.

The inductive argument follows the @{text iter'} structure: at each step the destination has been
initialised up to index @{text len}, the next call to @{text cpm2mrec} (or @{text cps2mrec})
writes index @{text len}, and we must show @{text MCon} up to @{text len}.  The source is
assumed to be @{text MCon} for the full length throughout.

Also included are helper lemmas about locations that are not typed sub-prefixes of the changed
region (@{text cpm2mNotSubPrefsOfOriginal}, @{text cpm2mLocationRelatedToTopNotInOrig},
@{text cps2mNotSubPrefsOfChanged}), which support the inductive step.
\<close>

lemma cpm2mrec_imps_MCon_dest :
  "(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon tp srcMem l) 
  \<and>(\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon tp srcMem srcl) \<and> 
   cpm2mrec srcl destl tp srcMem a = Some v'''                    
          \<longrightarrow> MCon tp v''' destl"
proof (induction tp arbitrary:srcl destl srcMem a v''')
  case (MTArray x1 t)
  show ?case
  proof intros
    assume "(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTArray x1 t) srcMem l) 
        \<and> (\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon (MTArray x1 t) srcMem srcl) 
        \<and> cpm2mrec srcl destl (MTArray x1 t) srcMem a = Some v'''"
    then have *:"(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTArray x1 t) srcMem l)"
      and **:"cpm2mrec srcl destl (MTArray x1 t) srcMem a = Some v'''"
      and ***:"(\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon (MTArray x1 t) srcMem srcl) "
      by auto+

(*Expand the cpm2mrec defintion*)
    obtain l where ldef:"accessStore srcl srcMem = Some (MPointer l)"
      using ** cpm2mrec.simps(1)[of srcl destl x1 t srcMem a ] 
      by (auto split:if_splits option.splits memoryvalue.splits)
    then have a5:"Some v''' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a 
                  in iter' (\<lambda>i m'. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem m') m x1)"
      using ** by (simp add: cpm2mrec.simps(1))
    then obtain m where mdef:"m =  updateTypedStore destl (MPointer destl) (MTArray x1 t) a" by auto

(*We know this specific subset of srcMem is Mcon*)
    then show " MCon (MTArray x1 t) v''' destl"
    proof(cases "x1>0")
      case True
      then have "MCon (MTArray x1 t) srcMem l" using ldef * by auto
      then have srcMcon:"\<forall>i<x1.
               case accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) srcMem of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case t of MTValue x \<Rightarrow> MCon t srcMem (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
               | Some (MPointer loc2) \<Rightarrow> (case t of MTArray x xa \<Rightarrow> MCon t srcMem loc2 | MTValue Types \<Rightarrow> False)" 
        using MCon.simps(2)[of x1 t srcMem l] by auto

(*Concludes with the following from **  *)
      have v''def:"Some v''' =  iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x1" 
        using a5 ldef mdef by metis 

      have "\<forall>i<x1. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' of None \<Rightarrow> False 
             | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v''' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v''' loc2 | MTValue Types \<Rightarrow> False)" 
        using * ldef
      proof(induction rule: iter'_induct[OF _ _ v''def[symmetric]])
        case (1 v')
        then show ?case by simp
      next
        case (2 x v'')
        then obtain v'
          where a10:"iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t srcMem) m x = Some v'"
            and a20:"(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTArray x t) srcMem l) \<longrightarrow> 
                          (\<forall>i<x. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False 
                            | Some (MValue val) \<Rightarrow> (case t of  MTValue typ \<Rightarrow> MCon t v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
                            | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v' loc2 | MTValue Types \<Rightarrow> False))"
            and a30:"cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t srcMem v' = Some v''" by blast
        then have a40:"(\<forall>i<x. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False 
                            | Some (MValue val) \<Rightarrow> (case t of  MTValue typ \<Rightarrow> MCon t v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
                            | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v' loc2 | MTValue Types \<Rightarrow> False))" using 2 by fastforce
        have a50:"MCon (MTArray (Suc x) t) srcMem l" using 2 by auto
        have a55:"(\<exists>p. accessStore destl v' = Some (MPointer p)) \<or> accessStore destl v' = None" using 2 
        proof -
          have "accessStore destl v'' = accessStore destl v'"
            using a30 cpm2mrec_preserves_dest_root[of l _ destl _ t srcMem v' v''] by blast
          moreover have "accessStore destl m = accessStore destl v''"
            using "2.hyps" accessPrePost1[of v'' l destl t srcMem m "Suc x"] 
              accessStore_updateStore hash_inequality mdef by auto
          moreover have "accessStore destl m = Some (MPointer destl)" 
            using mdef unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
          ultimately show ?thesis by auto
        qed

        show ?case 
        proof intros
          fix i 
          assume iless:"i<Suc x"

          show "case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
                | Some (MValue val) \<Rightarrow> (case t of MTValue x \<Rightarrow> MCon t v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray x xa \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)" 
          proof(cases "i < x")
            case True

            then have MCondestl:"MCon (MTArray x t) v' destl" using a40 MCon.simps(2)[of x t v' destl] a55 by simp

            then show ?thesis
              using cpm2mrec_preserves_prior_child_case[OF a10 a30 MCondestl True] by simp


          next
            case False
            then have iIsx:"i = x" using iless by simp
            have child_ptr:
              "\<And>loc2. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MPointer loc2) \<Longrightarrow> MCon t srcMem loc2"
              using a50 using MCon_imps_sub_Mcon by blast
            have child_val:
              "\<And>val. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MValue val) \<Longrightarrow> MCon t srcMem (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
              using a50 using MCon_imps_sub_Mcon by blast
            have MCON: "MCon t v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
              using MTArray[of "(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))" srcMem "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v'']
                a30 child_ptr child_val
              by blast
            then show ?thesis
              using cpm2mrec_dest_case[OF a30 MCON] iIsx by blast
          qed
        qed
      qed

      moreover have "(\<exists>p. accessStore destl v''' = Some (MPointer p)) \<or> accessStore destl v''' = None" 
      proof - 
        have "accessStore destl m = accessStore destl v'''"
          using accessPrePost1[of v''' l destl t srcMem m x1] 
            accessStore_updateStore hash_inequality mdef v''def by blast
        moreover have "accessStore destl m = Some (MPointer destl)"
          using mdef unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
        ultimately show ?thesis by auto
      qed

      ultimately show ?thesis using MCon.simps(2)[of x1 t v''' destl]  by (simp add: True)
    next
      case False
      then show ?thesis 
        using "*" ldef by auto
    qed
  qed
next
  case (MTValue x)
  then show ?case
  proof intros
    assume "(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTValue x) srcMem l) \<and> 
            (\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon (MTValue x) srcMem srcl)
            \<and> cpm2mrec srcl destl (MTValue x) srcMem a = Some v'''"
    then have *:"(\<forall>l. accessStore srcl srcMem = Some (MPointer l) \<longrightarrow> MCon (MTValue x) srcMem l)"
      and **:"(\<forall>val. accessStore srcl srcMem = Some (MValue val) \<longrightarrow> MCon (MTValue x) srcMem srcl)"
      and ***:"cpm2mrec srcl destl (MTValue x) srcMem a = Some v'''" by simp+

    then have a10:"Some v''' =  (case accessStore srcl srcMem of None \<Rightarrow> None
              | Some (MValue v) \<Rightarrow> Some (updateTypedStore destl (MValue v) (MTValue x) a) 
              | Some (MPointer literal) \<Rightarrow> None)" 
      using cpm2mrec.simps(2)[of srcl destl x srcMem a ] by simp
    then obtain v where  vdef:"Some (MValue v) = accessStore srcl srcMem" 
      by (simp split:option.splits memoryvalue.splits)
    then have "accessStore destl v''' = accessStore srcl srcMem" 
      using a10 unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def 
      by (auto split:option.splits memoryvalue.splits)
    moreover have "typeCon x v" using vdef ** by simp
    ultimately show "MCon (MTValue x) v''' destl" using ** MCon.simps(1)[of x v''' destl] vdef a10 
      by (auto split:option.splits memoryvalue.splits)
  qed
qed

lemma MCon_cpm2m: 
  assumes "iter' (\<lambda>i m. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
    and "MCon (MTArray x t) ms ls"
    and "(\<exists>p. accessStore (ld) md = Some (MPointer p)) \<or> accessStore (ld) md = None"
  shows " MCon (MTArray x t) updM ld" using assms(2) 
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case using MCon.simps by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md x = Some v'"
      and a20:"(MCon (MTArray x t) ms ls \<and> 0 < x \<longrightarrow> MCon (MTArray x t) v' ld)"
      and a30:"cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
  then have a40:"MCon (MTArray (Suc x) t) ms ls" using "2.prems" by auto


  have " (\<forall>destl'. \<not> LSubPrefL2 destl' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
    using cpm2mrec_SubPrefixes[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t ms v' v''] using a30 by simp
  then have "accessStore ld v' = accessStore ld v''" 
    using a30 cpm2mrec_preserves_dest_root by auto


  then have ld:"(\<exists>p. accessStore (ld) v'' = Some (MPointer p)) \<or> accessStore (ld) v'' = None" 
  proof(cases "x =0")
    case True
    then have v'MD:"v' = md" using a10 by auto
    then have "cpm2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms md = Some v''" using a30 by blast
    then have "(\<forall>destl'. \<not> LSubPrefL2 destl' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' md = accessStore destl' v'')" 
      using cpm2mrec_SubPrefixes[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t ms md v''] by simp
    then have "accessStore ld md = accessStore ld v''" 
      using cpm2mrec_preserves_dest_root v'MD using \<open>accessStore ld v' = accessStore ld v''\<close> by blast
    then show ?thesis using assms(3) by simp
  next
    case False
    then have "MCon (MTArray x t) ms ls" using a40 by auto
    then have "MCon (MTArray x t) v' ld" using a20 False by auto
    then show ?thesis 
      by (metis \<open>accessStore ld v' = accessStore ld v''\<close> MCon.simps(2))
  qed


  have "\<forall>i<Suc x.
             case accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case t of  MTValue x \<Rightarrow> MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
              | Some (MPointer loc2) \<Rightarrow> (case t of MTArray x xa \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)" 
  proof intros
    fix i assume *:"i<Suc x"
    show "case accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
           | Some (MValue val) \<Rightarrow> (case t of  MTValue x \<Rightarrow> MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
           | Some (MPointer loc2) \<Rightarrow> (case t of MTArray x xa \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases t)
      case (MTArray x11 x12)
      then show ?thesis 
      proof(cases "i<x")
        case True
        have b10: "MCon (MTArray x t) v' ld" using a20 a40 True by fastforce
        then show ?thesis
          using cpm2mrec_preserves_prior_child_case[OF a10 a30 b10 True] by simp
      next
        case False
        then have iIsx:"i = x" using * by auto
        have child_ptr:
          "\<And>loc2. accessStore (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MPointer loc2) \<Longrightarrow> MCon t ms loc2"
          using a40 
          using MCon_imps_sub_Mcon by blast
        have child_val:
          "\<And>val. accessStore (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MValue val) \<Longrightarrow> MCon t ms (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
          using a40  using MCon_imps_sub_Mcon by blast
        have MCON:"MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
          using cpm2mrec_imps_MCon_dest[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ms t "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v'']
            a30 child_ptr child_val
          by blast
        then show ?thesis
          using cpm2mrec_dest_case[OF a30 MCON] iIsx 
          by blast
      qed
    next
      case (MTValue x2)
      then show ?thesis 
      proof(cases "i<x")
        case True

        have b10: "MCon (MTArray x t) v' ld" using a20 2 True by auto
        then show ?thesis
          using cpm2mrec_preserves_prior_child_case[OF a10 a30 b10 True] by simp
      next
        case False

        then have iIsx: "i = x" using * by simp
        have child_ptr:
          "\<And>loc2. accessStore (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MPointer loc2) \<Longrightarrow> MCon t ms loc2"
          using a40  using MCon_imps_sub_Mcon by blast
        have child_val:
          "\<And>val. accessStore (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MValue val) \<Longrightarrow> MCon t ms (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
          using a40 using MCon_imps_sub_Mcon by blast
        have MCON:"MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
          using cpm2mrec_imps_MCon_dest[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ms t "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v'']
            a30 child_ptr child_val
          by blast
        then show ?thesis
          using cpm2mrec_dest_case[OF a30 MCON] iIsx 
          by blast
      qed
    qed
  qed
  then show ?case using cpm2mrec_imps_MCon_dest MCon.simps(2)[of "Suc x" t v'' "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))"] ld by simp
qed

lemma cps2m:
  assumes "iter' (\<lambda>i m. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms m) md x = Some updM"
    and "SCon (STArray x t') ls ms"
    and "cps2mTypeCompatible (STArray x t') (MTArray x t)"
    and "(\<exists>p. accessStore (ld) md = Some (MPointer p)) \<or> accessStore (ld) md = None"
  shows "MCon (MTArray x t) updM ld" using assms(2) assms(3) assms(4)
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case  using MCon.simps by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) md x = Some v'"
      and a20:"(SCon (STArray x t') ls ms \<longrightarrow> 0 < x \<longrightarrow> cps2mTypeCompatible (STArray x t') (MTArray x t) \<longrightarrow> MCon (MTArray x t) v' ld)"
      and a30:"cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' ms v' = Some v''" by blast
  then have a40:"SCon (STArray (Suc x) t') ls ms" using "2.prems" by auto

  have " (\<forall>destl'. \<not> LSubPrefL2 destl' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
    using cps2mrec_SubPrefixes a30 by simp
  then have "accessStore ld v' = accessStore ld v''" 
    using a30 cps2mrec_preserves_dest_root by auto
  then have ld:"(\<exists>p. accessStore (ld) v'' = Some (MPointer p)) \<or> accessStore (ld) v'' = None" 
  proof(cases "x =0")
    case True
    then have v'MD:"v' = md" using a10 by auto
    then have "cps2mrec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' ms md = Some v''" using a30 by blast
    then have "(\<forall>destl'. \<not> LSubPrefL2 destl' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' md = accessStore destl' v'')" 
      using cps2mrec_SubPrefixes[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' ms md v''] by simp
    then have "accessStore ld md = accessStore ld v''" 
      using cpm2mrec_preserves_dest_root v'MD using \<open>accessStore ld v' = accessStore ld v''\<close> by blast
    then show ?thesis using assms(4) by simp
  next
    case False
    then have "SCon (STArray x t') ls ms" using a40 by auto
    then have "MCon (MTArray x t) v' ld" using a20 False 
      by (metis assms(3) cps2mTypeCompatible.simps(2) less_nat_zero_code linorder_neqE_nat)
    then show ?thesis 
      by (metis \<open>accessStore ld v' = accessStore ld v''\<close> MCon.simps(2))
  qed

  have "\<forall>i<Suc x.
             case accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
             | Some (MValue val) \<Rightarrow> (case t of  MTValue x \<Rightarrow> MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray x xa \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)" 
  proof intros
    fix i assume *:"i<Suc x"
    show "case accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False 
           | Some (MValue val) \<Rightarrow> (case t of  MTValue x \<Rightarrow> MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
           | Some (MPointer loc2) \<Rightarrow> (case t of MTArray x xa \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases t)
      case (MTArray x11 x12)
      then show ?thesis 
      proof(cases "i<x")
        case True
        have b10: "MCon (MTArray x t) v' ld" using a20 a40 2(4) 2(5) True by fastforce
        have b20: "cps2mTypeCompatible t' t" using 2(4) cps2mTypeCompatible.simps True by simp
        then show ?thesis
          using cps2mrec_preserves_prior_child_case[OF a10 a30 b10 b20 True] by simp
      next
        case False
        then have iIsx:"i = x" using * by auto
        have b10:"(\<forall>i\<in>{0..Suc x - 1}. SCon t' (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) ms)" 
          using a40 using SCon.simps(2)[of "Suc x" t' "ls" "ms"] by auto
        have MCON:"MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
          using cps2mrec_SCon_imps_MCon_dest[of t' "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ms  "Suc x" t "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v'']
            2(4) a30  iIsx b10
          by simp
        then show ?thesis
          using cps2mrec_dest_case[OF a30 MCON] iIsx 
          by blast
      qed
    next
      case (MTValue x2)
      then show ?thesis 
      proof(cases "i<x")
        case True
        have b10: "MCon (MTArray x t) v' ld" using a20 2 True by auto
        have b20: "cps2mTypeCompatible t' t" using 2(4) cps2mTypeCompatible.simps True by simp
        then show ?thesis
          using cps2mrec_preserves_prior_child_case[OF a10 a30 b10 b20 True] by simp
      next
        case False
        then have iIsx: "i = x" using * by simp
        then have b10:"(\<forall>i\<in>{0..Suc x - 1}. SCon t' (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) ms)" 
          using a40 using SCon.simps(2)[of "Suc x" t' "ls" "ms"] by auto
        then have MCON:"MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
          using cps2mrec_SCon_imps_MCon_dest[of t' "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ms  "Suc x" t "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] 2(4) a30  iIsx b10 by simp
        then show ?thesis
          using cps2mrec_dest_case[OF a30 MCON] iIsx 
          by blast
      qed
    qed
  qed
  then show ?case using cpm2mrec_imps_MCon_dest MCon.simps(2)[of "Suc x" t v'' "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))"] ld by simp
qed


lemma MCon_cpm2s:
  assumes "iter' (\<lambda>i m. cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m) md x = Some updM"
    and "MCon (MTArray x t) ms ls"
    and "cps2mTypeCompatible (STArray x t') (MTArray x t)"
  shows "SCon (STArray x t') ld updM" using assms(2) assms(3)
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case  using MCon.simps by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md x = Some v'"
      and a20:"(MCon (MTArray x t) ms ls \<longrightarrow> cps2mTypeCompatible (STArray x t') (MTArray x t) \<longrightarrow> SCon (STArray x t') ld v')"
      and a30:"cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
  then have a40:"MCon (MTArray (Suc x) t) ms ls" using "2.prems" by auto

  have " (\<forall>destl' t. \<not> LSubPrefL2 destl' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow>  accessStorage t destl' v' =  accessStorage t destl' v'')" 
    using cpm2srec_SubPrefixes a30 by simp
  then have "\<forall>t.  accessStorage t ld v' = accessStorage t ld v''"
    using a30 cpm2srec_preserves_dest_root by auto
  have "(\<forall>i<Suc x. SCon t' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'')" 
  proof intros
    fix i assume *:"i<Suc x"
    show "SCon t' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''"
    proof(cases t')
      case (STArray x11 x12)
      then show ?thesis 
      proof(cases "i<x")
        case True
        have b10: "SCon (STArray x t') ld v' " using a20 a40 2(4)  
          using True by fastforce
        then show ?thesis
          using cpm2srec_preserves_prior_child_scon a30 b10 True by simp

      next
        case False
        then have iIsx:"i = x" using * by auto
        then have MCON:"SCon t' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v''" 
          using cpm2srec_imps_SCon_dest[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ms t _ t' "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] 2(4) a30  iIsx 
          using MCon_imps_sub_Mcon a40 by blast
        then show ?thesis using MCON  iIsx by simp
      qed
    next
      case (STMap x21 x22)
      then show ?thesis using 2 by simp
    next
      case (STValue x3)
      then show ?thesis 
      proof(cases "i<x")
        case True
        then have "SCon (STArray x t') ld v'" using a20 a40 2(4) by auto
        then have "SCon t' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" using True by simp
        then show ?thesis
          using cpm2srec_preserves_prior_child_scon[OF a30 _ True] STValue 
          by blast
      next
        case False
        then have "i = x" 
          using "*" by auto
        then show ?thesis 
          by (meson MCon_imps_sub_Mcon
              \<open>\<And>thesis. (\<And>v'. iter' (\<lambda>i. cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md x = Some v'
 \<Longrightarrow> MCon (MTArray x t) ms ls \<longrightarrow> cps2mTypeCompatible (STArray x t') (MTArray x t) 
\<longrightarrow> SCon (STArray x t') ld v' \<Longrightarrow> cpm2srec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v'' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
              a40 assms(3) cpm2srec_imps_SCon_dest lessI)
      qed                          
    qed
  qed
  then show ?case using cpm2mrec_imps_MCon_dest SCon.simps(2)[of "Suc x" t' ld v''] by simp
qed


lemma cpm2mNotSubPrefsOfOriginal:
  assumes "MCon (MTArray x11 x12) m' stl2"
    and "\<forall>l'. l' \<noteq> stl1 \<longrightarrow> \<not> LSubPrefL2 stl1 l'"
    and "\<forall>loc. LSubPrefL2 loc stl1 \<longrightarrow> accessStore loc mem' = None"
    and "\<not> LSubPrefL2 stl2 stl1"
    and "MCon (MTArray x11 x12) mem' stl2"
    and "\<forall>locs. \<not> LSubPrefL2 locs stl1 \<longrightarrow> accessStore locs mem' = accessStore locs m'"
    and "\<forall>l' \<noteq> stl1. \<not>(LSubPrefL2 stl1 l')"
  shows "\<not>TypedMemSubPrefPtrs m' x11 x12 stl2 stl1" using assms
proof(induction x12 arbitrary:stl2 x11)
  case (MTArray x1 x12)
  have "(\<forall>i<x11. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l \<noteq> stl1 \<and> \<not>TypedMemSubPrefPtrs m' x1 x12 l stl1))" 
  proof intros
    fix i 
    assume idef':"i<x11" 
    have d5:"\<forall>i<x11. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' =  accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem'" using MTArray.prems LSubPrefL2_def 
      by (metis Mutual_NonSub_SpecificNonSub)
    then have d10:"\<forall>i<x11. \<exists>l'. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m'  = Some (MPointer l')"  using MTArray.prems
      by (metis MConArrayPointers less_nat_zero_code neq0_conv)

    then obtain l' where idef:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m'  = Some (MPointer l')"  using MTArray.prems(1) idef' by fastforce
    then have idef2:" accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l')" using d5 idef' by auto

    have "(case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False 
          | Some (MValue val) \<Rightarrow> (case MTArray x1 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 x12) m' (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
          | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 x12) m' loc2 | MTValue Types \<Rightarrow> False))" 
      using MCon.simps(2)[of x11 "MTArray x1 x12" m' stl2] MTArray idef idef' by metis
    then have mdcond:"MCon (MTArray x1 x12) m' l'" using idef by simp
    then have "\<forall>i<x1. \<exists>x. accessStore (hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some x" 
      by (metis bot_nat_0.not_eq_extremum less_nat_zero_code mcon_accessStore)
    have "(case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' of None \<Rightarrow> False 
          | Some (MValue val) \<Rightarrow> (case MTArray x1 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 x12) mem' (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
          | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 x12) mem' loc2 | MTValue Types \<Rightarrow> False))" 
      using MTArray.prems(5) MCon.simps(2)[of x11 "MTArray x1 x12" mem' stl2] idef idef2 idef' by metis
    then have memCond:"MCon (MTArray x1 x12) mem' l'" using idef idef2 by simp
    then have d40:"\<forall>i<x1. \<exists>x. accessStore (hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some x" using idef2 idef 
      by (metis bot_nat_0.not_eq_extremum less_nat_zero_code mcon_accessStore)
    have d90:"hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" using MTArray.prems using LSubPrefL2_def by auto
    have "l' \<noteq> stl1" 
    proof
      assume e1:"l' = stl1"
      then have "LSubPrefL2 l' stl1" using LSubPrefL2_def by auto
      then have "\<forall>i. LSubPrefL2 (hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) stl1" using e1 LSubPrefL2_def by auto
      then have "\<forall>i. accessStore (hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = None" using MTArray.prems(3) by auto
      then show False using d40 
        using \<open>MCon (MTArray x1 x12) mem' l'\<close> by fastforce
    qed
    moreover have "\<not>TypedMemSubPrefPtrs m' x1 x12 l' stl1" using MTArray.IH[of x1 l'] using mdcond MTArray.prems(2,3,6) memCond idef idef2 
      by (metis MCon_imps_Some MTArray.IH LSubPrefL2_def hash_suffixes_associative option.discI)
    ultimately show "\<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> l \<noteq> stl1 \<and> \<not> TypedMemSubPrefPtrs m' x1 x12 l stl1 " 
      by (simp add: idef)
  qed

  then show ?case using TypedMemSubPrefPtrs.simps(2)[of m' x11 x1 x12 stl2 stl1]   
    by (metis memoryvalue.inject(2)  option.inject)
next
  case (MTValue x)
  then show ?case 
    by (metis LSubPrefL2_def TypedMemSubPrefPtrs.simps(1) hash_inequality)
qed

lemma cpm2mLocationRelatedToTopNotInOrig:
  assumes  " LSubPrefL2 intimLoc l"
    and "\<not> LSubPrefL2 stl2 l"
    and "MCon (MTArray x11 x12) m' stl2"
    and "\<forall>loc. LSubPrefL2 loc stl1 \<longrightarrow> accessStore loc mem' = None"
    and "MCon (MTArray x11 x12) mem' stl2"
    and "\<forall>locs. \<not> LSubPrefL2 locs stl1 \<longrightarrow> accessStore locs mem' = accessStore locs m'"
    and "\<forall>l' \<noteq> l. \<not>(LSubPrefL2 l l')"
    and "stl1 = l"
  shows "\<not>TypedMemSubPrefPtrs m' x11 x12 stl2 intimLoc" using assms
proof(induction x12 arbitrary:x11 stl2)
  case (MTArray x1 x12)
  have "(\<forall>i<x11. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l \<noteq> intimLoc \<and> \<not>TypedMemSubPrefPtrs m' x1 x12 l intimLoc))" 
  proof intros
    fix i assume d10:"i<x11"
    then obtain l' where idef:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l')" using MTArray.prems
      by (metis MConArrayPointers MCon.simps(2))
    then have "l \<noteq> l'" using idef MTArray LSubPrefL2_def  d10
      by (smt (verit, best)  cpm2mNotSubPrefsOfOriginal TypedMemSubPrefPtrs.simps(2))
    moreover have "MCon (MTArray x1 x12) mem' l'" using MTArray.prems idef d10
      by (metis CompTypeRemainsMCon   Mutual_NonSub_SpecificNonSub CompMemType.simps(2))
    moreover have " MCon (MTArray x1 x12) m' l'" using MTArray.prems idef d10
      by (metis CompTypeRemainsMCon CompMemType.simps(2))
    moreover have "\<not> LSubPrefL2 l' l" using calculation MTArray.prems idef LSubPrefL2_def 
      by (metis MCon_imps_Some  hash_suffixes_associative option.distinct(1))
    ultimately have "\<not>TypedMemSubPrefPtrs m' x1 x12 l' intimLoc" using MTArray.IH[of l' x1] MTArray.prems idef by blast
    then show "\<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> l \<noteq> intimLoc \<and> \<not> TypedMemSubPrefPtrs m' x1 x12 l intimLoc" using d10 idef 
      using MTArray.prems(1) \<open>\<not> LSubPrefL2 l' l\<close> by auto
  qed
  then show ?case using TypedMemSubPrefPtrs.simps(2)[of m' x11 x1 x12 stl2 intimLoc] by auto

next
  case (MTValue x)
  then have "(\<forall>i<x11. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> intimLoc)" using LSubPrefL2_def  
    using Mutual_NonSub_SpecificNonSub by blast
  then show ?case using TypedMemSubPrefPtrs.simps(1)[of m' x11 x stl2 intimLoc] by blast
qed



lemma cps2mNotSubPrefsOfChanged:
  assumes "MCon (MTArray x t) m' stl1"
    and "\<not> LSubPrefL2 stl2 stl1"
    and "\<forall>la l'. TypedStoSubpref la stl1 (STArray x' t') \<and> accessStore la m' = Some (MPointer l') \<longrightarrow> l' = la"
    and "0 < x"
    and "cps2mTypeCompatible (STArray x' t') (MTArray x t)"
  shows "\<not>TypedMemSubPrefPtrs m' x t stl1 stl2" using assms
proof(induction t' arbitrary:stl1 x x' t)
  case (STArray x1 t')
  then have a1:"(0 < x \<and> x' = x \<and> cps2mTypeCompatible (STArray x1 t') t)" 
    using cps2mTypeCompatible.simps(2)[of x' "STArray x1 t'" x t] by blast
  then obtain t'' where tdef:"t = MTArray x1 t''" using cps2mTypeCompatible.simps by (cases t; auto)
  have d10:"\<forall>i<x. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"
  proof intros
    fix i
    assume idef:"i < x"
    then obtain l where ptr:"accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l)"
      using MConArrayPointers[of x x1 t'' m' stl1 i] STArray.prems(1) tdef by blast
    have sub:"TypedStoSubpref (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) stl1 (STArray x' t')"
      using idef a1 
      using TypedStoSubpref_sameLoc by auto
    then have "l = hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
      using STArray.prems(3) ptr 
      by (metis STArray.prems(3) ptr TypedStoSubpref.simps(2) idef a1)
    then show "accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"
      using ptr by blast
  qed

  have "(\<forall>i<x. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> \<not>(l = stl2 \<or> hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl2 \<or> TypedMemSubPrefPtrs m' x1 t'' l stl2))" 
  proof intros
    fix i
    assume idef:"i<x"
    then have ac:"accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))" using d10 by simp
    have "(hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> stl2" using STArray LSubPrefL2_def by blast
    have mcond:"\<forall>i<x. (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case MTArray x1 t'' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t'') m' (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t'' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t'') m' loc2 | MTValue Types \<Rightarrow> False)) \<and>
                ((\<exists>p. accessStore stl1 m' = Some (MPointer p)) \<or> accessStore stl1 m' = None)" 
      using MCon.simps(2)[of x "(MTArray x1 t'')" m' stl1] STArray.prems(1) idef tdef a1 by auto
    have " \<forall>la l'. TypedStoSubpref la (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (STArray x1 t') \<and> accessStore la m' = Some (MPointer l') \<longrightarrow> l' = la" 
      using STArray.prems(3) idef stoMoreSpecificTypedSubpref a1 by blast
    moreover have "MCon (MTArray x1 t'') m' (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using STArray.prems(1) ac mcond a1 tdef  
      using CompTypeRemainsMCon idef CompMemType.simps(2) by blast
    moreover have "\<not> LSubPrefL2 stl2 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using STArray.prems(2) LSubPrefL2_def Not_Sub_More_Specific by auto
    ultimately have "\<not>TypedMemSubPrefPtrs m' x1 t'' (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) stl2" using STArray.IH[of x1 t'' "(hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"x1] idef ac a1 tdef by fastforce
    then show "\<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) 
              \<and> \<not> (l = stl2 \<or> hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl2 \<or> TypedMemSubPrefPtrs m' x1 t'' l stl2) " 
      using ac \<open>hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl2\<close> tdef by simp
  qed
  then show ?case using TypedMemSubPrefPtrs.simps(2)[of m' x x1 t'' stl1 stl2] using tdef by auto
next
  case (STMap x1 t')
  then show ?case 
    by (metis cps2mTypeCompatible.simps(2,4))
next
  case (STValue x)
  then show ?case
    using LSubPrefL2_def TypedMemSubPrefPtrs.simps(1) 
    by (metis cps2mTypeCompatible.simps(2) cps2mTypeCompatible.simps(6) mcon_accessStore)
qed



subsubsection \<open>Type Compatibility Under Copying\<close>
text \<open>
These lemmas establish how type annotations at sub-locations are updated when copying between
memory and storage regions with compatible but structurally distinct types.  The key predicates
are @{text TypedMemSubPref} and @{text TypedStoSubpref}, which identify which locations fall
within the typed footprint of a copy destination.

Covered operations: @{text cpm2mrec}, @{text cpm2m} (memory-to-memory), @{text cps2mrec},
@{text cps2m} (storage-to-memory).  The @{text somesome} variants additionally establish that
every typed sub-location of the destination holds a value after the copy.
\<close>

lemma cpm2mrec_array_root_both:
  assumes step: "cpm2mrec srcl destl (MTArray x t) ms md = Some v'''"
  shows "accessTypeStore destl v''' = Some (MTArray x t)
    \<and> accessStore destl v''' = Some (MPointer destl)"
proof -
  obtain l where ldef: "accessStore srcl ms = Some (MPointer l)"
    using step cpm2mrec.simps(1)[of srcl destl x t ms md]
    by (auto split: if_splits option.splits memoryvalue.splits)
  let ?m = "updateTypedStore destl (MPointer destl) (MTArray x t) md"
  have expanded:
    "Some v''' =
      (let m = updateTypedStore destl (MPointer destl) (MTArray x t) md
       in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x)"
    using step ldef by (simp add: cpm2mrec.simps(1))
  have run:
    "iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) ?m x = Some v'''"
    using expanded unfolding Let_def by simp
  have keep_type:
    "accessTypeStore destl ?m = accessTypeStore destl v'''"
    using cpm2mSingleChange_Typed[OF run] by blast
  have keep_store:
    "accessStore destl ?m = accessStore destl v'''"
    using cpm2mSingleChange[OF run] by simp
  show ?thesis
    using keep_type keep_store 
    unfolding accessTypeStore_def updateTypedStore_def accessStore_def updateTypeStore_def updateStore_def 
    by simp
qed

lemma cpm2mrec_child_root_type:
  assumes step: "cpm2mrec srcl destl t ms md = Some v'''"
  shows "accessTypeStore destl v''' = Some t"
proof (cases t)
  case (MTArray x1 t')
  have step_arr: "cpm2mrec srcl destl (MTArray x1 t') ms md = Some v'''"
    using step MTArray by simp
  from cpm2mrec_array_root_both[OF step_arr]
  show ?thesis 
    using MTArray by fastforce
next
  case (MTValue x)
  then obtain v where "accessStore srcl ms = Some (MValue v)"
    using step cpm2mrec.simps(2)[of srcl destl x ms md]
    by (auto split: option.splits memoryvalue.splits)
  then have "v''' = updateTypedStore destl (MValue v) (MTValue x) md"
    using step MTValue cpm2mrec.simps(2)[of srcl destl x ms md] by simp
  then show ?thesis
    using MTValue by fastforce
qed

lemma cpm2m_TypeCompChangeIndexs:
  assumes "iter' (\<lambda>i m''. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m'') md x1 = Some v'"
  shows "\<forall>i<x1. accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some t"
proof (rule iter'_indexed_type_writes[
    where loc = "\<lambda>i. hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" and tp = t, OF assms])
  fix i j m1 m2
  assume j_less: "j < i"
    and step: "cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m1 = Some m2"
  show "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t j)) m2 =
      accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t j)) m1"
    using j_less step
    by (metis ShowLNatDot cpm2mrec_SubPrefixes_both hash_int_prefix hashesIntSame nat_neq_iff)
next
  fix i m1 m2
  assume step: "cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m1 = Some m2"
  show "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some t"
    using cpm2mrec_child_root_type[OF step] .
qed



lemma cpm2mrec_TypeCompChange:
  "cpm2mrec srcl destl tp ms md = Some v''' \<longrightarrow>
  (\<forall>destl'. TypedMemSubPref destl' destl tp \<longrightarrow>
  (case tp of MTValue val \<Rightarrow> accessTypeStore destl v''' = Some tp
      | MTArray x' t' \<Rightarrow> (\<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
                          (case t'' of MTArray parent_len parent_arr \<Rightarrow> 
                              \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                           | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
                        )))"
proof(induction tp arbitrary:srcl destl ms md v''')
  case (MTArray x1 t)
  show ?case
  proof intros
    fix destl'
    assume **:"cpm2mrec srcl destl (MTArray x1 t) ms md = Some v'''"
      and ***:"TypedMemSubPref destl' destl (MTArray x1 t)"
    obtain l where ldef:"accessStore srcl ms = Some (MPointer l)"
      using ** cpm2mrec.simps(1)[of srcl destl x1 t ms] 
      by (auto split:if_splits option.splits memoryvalue.splits)
    then have a5:"Some v''' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) md
                  in iter' (\<lambda>i m'. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m') m x1)"
      using ** by (simp add: cpm2mrec.simps(1))
    then obtain m where mdef:"m =  updateTypedStore destl (MPointer destl) (MTArray x1 t) md" by auto


    then have v''Def:"Some v''' = iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x1"
      using a5 ldef unfolding cpm2mrec.simps by presburger
    have "case MTArray x1 t of
       MTArray x' t' \<Rightarrow>
         \<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
               (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
       | MTValue val \<Rightarrow> accessTypeStore destl v''' = Some (MTArray x1 t)" using ***
    proof(induction rule: iter'_induct[OF _ _ v''Def[symmetric]])
      case (1 v')
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i m'. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m') m x = Some v'"
          and a20:"(TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
          (case MTArray x t of
           MTArray x' t' \<Rightarrow>
             \<exists>t''. CompMemType v' x' t' t'' destl destl' \<and>
                   (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
                    | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval))
           | MTValue val \<Rightarrow> accessTypeStore destl v' = Some (MTArray x t)))"
          and a30:"cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
      then show ?case
      proof(cases "destl' = destl")
        case True
        then show ?thesis using 2 
          by (metis LSubPrefL2_def TypedMemSubPref.simps(2) hash_flatten_right hash_inequality
              typedPrefix_imp_SubPref)
      next
        case f1:False
        then show ?thesis
        proof(cases "TypedMemSubPref destl' destl (MTArray x t)")
          case True
          then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
            by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
          moreover have "\<forall>i<x. \<not> TypedMemSubPref (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using True 
            by (smt (verit, ccfv_threshold) LSubPrefL2_def TypedMemSubPref.simps(2) hash_flatten_right hashesInts nat_neq_iff
                neg_MemLSubPrefL2_imps_TypedMemSubPref)
          ultimately have i1:"\<forall>i<x. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" 
            using cpm2mrec_SubPrefixes2_typed[of "(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t ms v' v''] a30 
            by (meson ShowLNatDot f1 hash_injective)
          obtain t'' where i2:"(CompMemType v' x t t'' destl destl' \<and>
             (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval)))" 
            using True a20 a10 by auto


          have i5:"\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
            using a30 cpm2mrec_SubPrefixes by blast
          moreover have i6:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
            by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
                nat_neq_iff typedPrefix_imp_SubPref)
          moreover have i7:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" 
            using calculation by auto
          moreover have i8:"\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
            using cpm2mSelfPointers[OF a10] by blast
          show ?thesis
          proof(cases t'')
            case (MTArray x11 x12)
            then have cc0:"CompMemType v' x t (MTArray x11 x12) destl destl' \<and> (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some x12)" 
              using i2 by simp
            then have "CompMemType v'' x t (MTArray x11 x12) destl destl' \<and> (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12)"
              using CompMemType_preservation_induction[OF i5 i6 i7 cc0 i8] i1 
              by (smt (verit, ccfv_threshold) LSubPrefL2_def True TypedMemSubPref.simps(2) a30 
                  hash_flatten_right hashesInts i6 cpm2mrec_SubPrefixes_both
                  typedPrefix_imp_SubPref)
            then show ?thesis  using CompMemType_extend2 by force
          next
            case (MTValue x2)
            then have cc0:"accessTypeStore destl' v' = Some (MTValue x2) \<and> CompMemType v' x t (MTValue x2) destl destl'" using i2 by simp
            then have "CompMemType v'' x t (MTValue x2) destl destl' \<and> accessTypeStore destl' v'' = Some (MTValue x2)"
              using CompMemTypeValue_preservation_induction[OF i5 i6 i7 cc0 i8] 
              using True a30 i6 cpm2mrec_SubPrefixes_both by blast
            then show ?thesis using CompMemType_extend by fastforce
          qed 
        next
          case False
          then have subs:"(\<forall>i<x. \<not>TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" by simp
          moreover obtain i where idef:"i<Suc x \<and> (TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t  \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
            using 2(3) f1 unfolding TypedMemSubPref.simps by auto
          have iIsx:"i = x" 
          proof(rule ccontr)
            assume a0:"i \<noteq> x"
            then have "i < x \<and> (TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t  \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
              using idef by simp
            then show False using subs by auto
          qed

          then have "cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" using a30 by simp

          then have IH1:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        (case t of
          MTArray x' t' \<Rightarrow>
           \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
                  | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
         | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t)" 
            using MTArray.IH[of "(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ms v' v''] idef a30 iIsx by simp

	          then show ?thesis
	          proof(cases t)
	            case (MTArray x11 x12)
	            have step_arr:
	              "cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12) ms v' = Some v''"
	              using a30 MTArray by simp
	            obtain ll where llDef:
	              "accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MPointer ll)"
	              using step_arr cpm2mrec.simps(1)[of "(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12 ms v']
	              by (auto split: if_splits option.splits memoryvalue.splits)
	            have v''Def:
	              "Some v'' = iter' (\<lambda>i. cpm2mrec (hash ll (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms)
	                (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v') x11"
	              using step_arr llDef unfolding cpm2mrec.simps(1) Let_def by (simp)
	            have root_bundle:
	              "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 x12)
	                \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	              using cpm2mrec_array_root_both[OF step_arr] by simp
	            then show ?thesis
	            proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	              case True
	              then have "accessTypeStore destl' v'' = Some (MTArray x11 x12)"
	                using root_bundle by simp
	              moreover have "CompMemType v'' (Suc x) (MTArray x11 x12) (MTArray x11 x12) destl destl'"
	                using MTArray True root_bundle unfolding CompMemType.simps by blast
	              moreover have "\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12" 
	                using cpm2m_TypeCompChangeIndexs[OF v''Def[symmetric]] True by simp
	              ultimately show ?thesis using MTArray True root_bundle by force
	            next
	              case False
	              then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t"  using subs iIsx 
                using idef by blast
              then have "(case t of
     MTArray x' t' \<Rightarrow>
       \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
	             (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
	              | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
	     | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t)" 
	                using IH1 by simp
	              then have "\<exists>t''. CompMemType v'' x11 x12 t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
	             (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
	              | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))"
	                using MTArray by simp
	              then show ?thesis using MTArray root_bundle by auto
	            qed
	          next
	            case (MTValue x2)
            then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using idef iIsx by simp
            then have v''Def:"(case accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms of None \<Rightarrow> None
                       | Some (MValue v) \<Rightarrow> Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v') 
                       | Some (MPointer literal) \<Rightarrow> None) = Some v''"
              using a30 cpm2mrec.simps(2)[of "(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"  x2 ms v'] MTValue by simp
            then obtain v where "accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MValue v)" by (auto split:option.splits memoryvalue.splits)
            then have "v'' = (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v') " using v''Def by simp
            then show ?thesis unfolding updateTypeStore_def updateTypedStore_def accessTypeStore_def updateStore_def using MTValue  
              using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> accessTypeStore_def by auto
          qed
        qed

      qed
    qed
    then show "case MTArray x1 t of
  MTArray x' t' \<Rightarrow>
    \<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
          (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
           | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
  | MTValue val \<Rightarrow> accessTypeStore destl v''' = Some (MTArray x1 t)" by simp
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix destl'
    assume **:"cpm2mrec srcl destl (MTValue x) ms md = Some v'''"
      and ***:" TypedMemSubPref destl' destl (MTValue x)"
    then have "destl' = destl" by simp
    obtain v where "accessStore srcl ms = Some (MValue v) \<and> v''' = updateTypedStore destl (MValue v) (MTValue x) md"
      using ** unfolding cpm2mrec.simps by (auto split:option.splits memoryvalue.splits)
    then show "(case MTValue x of
         MTArray x' t' \<Rightarrow>
           \<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                  | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
         | MTValue val \<Rightarrow> accessTypeStore destl v''' = Some (MTValue x))"
      using \<open>destl' = destl\<close> unfolding updateTypedStore_def updateTypeStore_def accessTypeStore_def by simp
  qed
qed

lemma cpm2m_TypeCompChange:
  assumes "iter' (\<lambda>i m''. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m'') md x1 = Some v'"
  shows "(\<forall>destl'. TypedMemSubPref destl' destl (MTArray x1 t) \<longrightarrow> 
          (\<exists>st. CompMemType v' x1 t st destl destl' \<and>
            (case st of MTArray parent_len parent_arr \<Rightarrow> 
              \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval))))"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter' (\<lambda>i m''. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m'') md x = Some v'"
      and a20: "(\<forall>destl'.
             TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
             (\<exists>st. CompMemType v' x t st destl destl' \<and>
                   (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
                    | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval))))"
      and a30: "cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
  then have "(\<forall>destl'.
        TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        (case t of
         MTArray x' t' \<Rightarrow>
           \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
                  | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
         | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t))"
    using cpm2mrec_TypeCompChange[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t ms v' v''] by blast
  show ?case
  proof intros
    fix destl'
    assume a1:"TypedMemSubPref destl' destl (MTArray (Suc x) t)"
    show "(\<exists>st. CompMemType v'' (Suc x) t st destl destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval)))"
    proof(cases "TypedMemSubPref destl' destl (MTArray x t)")
      case True
      then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using True
        by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
      moreover have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using True
        by (smt (verit, ccfv_threshold) LSubPrefL2_def ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesInts nat_neq_iff
            neg_MemLSubPrefL2_imps_TypedMemSubPref)
      ultimately have i1:"(\<forall>destl'.
        destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> \<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        accessTypeStore destl' v' = accessTypeStore destl' v'')"
        using cpm2mrec_SubPrefixes2_typed[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t ms v' v''] a30 by simp
      obtain st where i2:" (CompMemType v' x t st destl destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval)))" using True a20 by blast

      have store_preserved: "\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
        using a30 cpm2mrec_SubPrefixes by blast
      moreover have no_prefix_conflict: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
        by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
            nat_neq_iff typedPrefix_imp_SubPref)
      moreover have store_consistency: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" 
        using calculation by auto


      moreover have self_pointers:"\<forall>l l'. TypedMemSubPref l destl (MTArray x t) 
                                  \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
        using cpm2mSelfPointers[OF a10] by blast

      show ?thesis
      proof(cases st)
        case (MTArray x11 x12)
        have i1':"\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" 
          using i1 
          by (smt (verit) LSubPrefL2_def True TypedMemSubPref.simps(2) hash_flatten_right hashesInts no_prefix_conflict
              typedPrefix_imp_SubPref)
        then have "CompMemType v' x t (MTArray x11 x12) destl destl' \<and> 
                    (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some x12)" 
          using i2 MTArray by simp
        then have "CompMemType v'' x t (MTArray x11 x12) destl destl' 
                  \<and> (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12)" 
          using CompMemType_preservation_induction[OF store_preserved no_prefix_conflict 
              store_consistency _self_pointers i1'] 
          by blast
        then show ?thesis using CompMemType_extend2 MTArray by force
      next
        case (MTValue x2)
        then have "CompMemType v' x t (MTValue x2) destl destl' \<and> accessTypeStore destl' v' = Some (MTValue x2)" 
          using i2 by auto
        then have "CompMemType v'' x t (MTValue x2) destl destl' \<and> accessTypeStore destl' v'' = Some (MTValue x2)"
          using CompMemTypeValue_preservation_induction[OF store_preserved no_prefix_conflict 
              store_consistency _self_pointers] using i1 
          using \<open>\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t\<close> \<open>destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> by blast 
        then show ?thesis using CompMemType_extend by fastforce
      qed
    next
      case False
      then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<or> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" 
        using a1 unfolding TypedMemSubPref.simps  
        using less_SucE by blast
	      then show ?thesis 
	      proof(cases t)
	        case (MTArray x11 x12)
	        have step_arr:
	          "cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12) ms v' = Some v''"
	          using a30 MTArray by simp
	        obtain l where ldef:
	          "accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MPointer l)"
	          using step_arr cpm2mrec.simps(1)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12 ms v']
	          by (auto split: if_splits option.splits memoryvalue.splits)
	        have v''Def:
	          "Some v'' = iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms)
	            (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v') x11"
	          using step_arr ldef unfolding Let_def cpm2mrec.simps(1) by (simp)
	        have root_bundle:
	          "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 x12)
	            \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	          using cpm2mrec_array_root_both[OF step_arr] by simp
	        then show ?thesis
	        proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	          case True
	          then have "accessTypeStore destl' v'' = Some (MTArray x11 x12)"
	            using root_bundle by simp
	          then have "\<forall>i<x11. accessTypeStore (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12"
	            using cpm2m_TypeCompChangeIndexs[OF v''Def[symmetric]] by blast
	          moreover have "CompMemType v'' (Suc x) (MTArray x11 x12) (MTArray x11 x12) destl destl'"
	            using MTArray True root_bundle unfolding CompMemType.simps by blast
	          ultimately show ?thesis using MTArray True root_bundle mtypes.simps(5) by blast
	        next
	          case False
	          then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" 
            using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<or> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t\<close> by blast
          then have "(case t of
                     MTArray x' t' \<Rightarrow>
           \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
	                  | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
	         | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t)" 
	            using cpm2mrec_TypeCompChange[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t ms v' v''] a30 by simp

	          then show ?thesis using MTArray root_bundle by auto
	        qed
	      next
        case (MTValue x2)
        then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
          using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<or> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t\<close> by auto
        then obtain v where "accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MValue v) \<and> 
                            (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v') = v''"
          using a30 cpm2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 ms v'] MTValue 
          by (simp split:option.splits memoryvalue.splits)
        then show ?thesis unfolding updateTypeStore_def updateTypedStore_def accessTypeStore_def updateStore_def using MTValue  
          using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> accessTypeStore_def by auto
      qed
    qed
  qed
qed



lemma cps2mrec_array_root_both:
  assumes step: "cps2mrec srcl destl (STArray x t) ms md = Some v'''"
    and conv: "cps2mTypeConvert t = Some tt"
  shows "accessTypeStore destl v''' = Some (MTArray x tt)
    \<and> accessStore destl v''' = Some (MPointer destl)"
proof -
  let ?m = "updateTypedStore destl (MPointer destl) (MTArray x tt) md"
  have expanded:
    "Some v''' =
      (let m = updateTypedStore destl (MPointer destl) (MTArray x tt) md
       in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x)"
    using step conv by (simp add: cps2mrec.simps(1))
  have run:
    "iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) ?m x = Some v'''"
    using expanded unfolding Let_def by simp
  have keep_root:
    "accessStore destl ?m = accessStore destl v'''
      \<and> accessTypeStore destl ?m = accessTypeStore destl v'''"
    using cps2mSingleChange_both[OF run] 
    accessStore_updateStore unfolding updateTypedStore_def
    by simp
  show ?thesis
    using keep_root
    unfolding updateTypedStore_def accessTypeStore_def updateTypeStore_def updateStore_def accessStore_def 
    by simp
qed

lemma cps2mrec_child_root_type:
  assumes step: "cps2mrec srcl destl t ms md = Some v'''"
    and comp: "cps2mTypeCompatible (STArray l t) (MTArray l tp)"
  shows "accessTypeStore destl v''' = Some tp"
proof (cases t)
  case (STArray x1 t')
  have step_arr: "cps2mrec srcl destl (STArray x1 t') ms md = Some v'''"
    using step STArray by simp
  obtain tt where conv: "cps2mTypeConvert t' = Some tt"
    using step_arr cps2mrec.simps(1)[of srcl destl x1 t' ms md]
    by (auto split: option.splits memoryvalue.splits)
  have tp_def: "tp = MTArray x1 tt"
  proof -
    have "cps2mTypeConvert (STArray l (STArray x1 t')) = Some (MTArray l tp)"
      using comp convertComp 
      using STArray by blast
    then show ?thesis
      using STArray conv by simp
  qed
  from cps2mrec_array_root_both[OF step_arr conv]
  show ?thesis using tp_def by simp
next
  case (STMap x21 x22)
  then show ?thesis
    using step cps2mrec.simps(3) by simp
next
  case (STValue x3)
  have tp_def: "tp = MTValue x3"
  proof -
    have "cps2mTypeConvert (STArray l (STValue x3)) = Some (MTArray l tp)"
      using comp STValue convertComp 
      by blast
    then show ?thesis
      using STValue by simp
  qed
  obtain v where vdef: "accessStorage x3 srcl ms = v"
    by blast
  then have "v''' = updateTypedStore destl (MValue v) (MTValue x3) md"
    using step STValue cps2mrec.simps(2)[of srcl destl x3 ms md] by simp
  then show ?thesis
    using tp_def by simp
qed

lemma cps2m_TypeCompChangeIndexs:
  assumes "iter' (\<lambda>i m''. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m'') md x1 = Some v'"
    and "cps2mTypeCompatible (STArray x1 t) (MTArray x1 t')"
  shows "\<forall>i<x1. accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some t'"
proof (rule iter'_indexed_type_writes[
    where loc = "\<lambda>i. hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" and tp = t', OF assms(1)])
  fix i j m1 m2
  assume j_less: "j < i"
    and step: "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m1 = Some m2"
  show "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t j)) m2 =
      accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t j)) m1"
    using j_less step
    by (metis ShowLNatDot cps2mrec_SubPrefixes_both hash_int_prefix hashesIntSame nat_neq_iff)
next
  fix i m1 m2
  assume step: "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m1 = Some m2"
  show "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m2 = Some t'"
    using cps2mrec_child_root_type[OF step assms(2)] .
qed

lemma cps2mrec_TypeCompChange:
  "cps2mrec srcl destl t' ms md = Some v''' \<longrightarrow> cps2mTypeCompatible (STArray l t') (MTArray l tp)\<longrightarrow>
  (\<forall>destl'. TypedMemSubPref destl' destl tp \<longrightarrow>
  (case tp of MTValue val \<Rightarrow> accessTypeStore destl v''' = Some tp
      | MTArray x' t' \<Rightarrow> (\<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
                          (case t'' of MTArray parent_len parent_arr \<Rightarrow> 
                              \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                           | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
                        )))"
proof(induction t' arbitrary:srcl destl ms md v''' l tp)
  case (STArray x1 t')
  show ?case 
  proof intros
    fix destl' 
    assume **:"cps2mrec srcl destl (STArray x1 t') ms md = Some v'''"
      and ****:"cps2mTypeCompatible (STArray l (STArray x1 t')) (MTArray l tp)"
      and ***:"TypedMemSubPref destl' destl tp"
    obtain t'' where ldef:"cps2mTypeConvert t' = Some t''"
      using ** cps2mrec.simps(1)[of srcl destl x1 t' ms] by (auto split:if_splits option.splits memoryvalue.splits)
    then have a5:"Some v''' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t'') md 
                              in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) m x1)"
      using ** by (simp add: cps2mrec.simps(1))
    then obtain m where mdef:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t'') md " by auto
    then have v''Def:"Some v''' =  iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) m x1"
      using a5 ldef unfolding cpm2mrec.simps by presburger
    obtain t''' where t'''def:"tp = MTArray x1 t'''" using ****   
      by (metis mtypes.exhaust cps2mTypeCompatible.simps(2) cps2mTypeCompatible.simps(3))
    then have ****:"cps2mTypeCompatible (STArray x1 t') (MTArray x1 t''')" using **** by simp
    have ***:"TypedMemSubPref destl' destl (MTArray x1 t''')" using t'''def *** by blast
    have "\<exists>t''. CompMemType v''' x1 t''' t'' destl destl' \<and>
               (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))" using *** ****
    proof(induction rule: iter'_induct[OF _ _ v''Def[symmetric]])
      case (1 v')
      then show ?case 
        by (simp add: t'''def)
    next
      case (2 x v'')
      then obtain v'
        where a10:" iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) m x = Some v'"
          and a20:"(TypedMemSubPref destl' destl (MTArray x t''') \<longrightarrow>
          cps2mTypeCompatible (STArray x t') (MTArray x t''') \<longrightarrow>
          (\<exists>t''. CompMemType v' x t''' t'' destl destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
                  | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval))))"
          and a30:"cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' ms v' = Some v''" by blast
      then show ?case
      proof(cases "destl' = destl")
        case True
        then show ?thesis using 2 
          by (metis LSubPrefL2_def TypedMemSubPref.simps(2)  hash_flatten_right hash_inequality
              typedPrefix_imp_SubPref)
      next
        case f1:False
        then show ?thesis
        proof(cases "TypedMemSubPref destl' destl (MTArray x t''')")
          case True
          then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
            by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
          moreover have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'''" using True
            by (smt (verit, ccfv_threshold) LSubPrefL2_def ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesInts nat_neq_iff
                neg_MemLSubPrefL2_imps_TypedMemSubPref)
          then have "\<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'" 
            using "2.prems"(2) compatible_TypedStoSubpref_imps_TypedMemSubPref 
            by (simp add: calculation)
          ultimately have i1:"accessTypeStore destl' v' = accessTypeStore destl' v''"
            using cps2mrec_SubPrefixes2_both[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' ms v' v''] a30 by blast

          obtain t'' where i2:"(CompMemType v' x t''' t'' destl destl' \<and>
             (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval)))" 
            using True a20 a10 2 by auto


          have i5:"\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
            using a30 cps2mrec_SubPrefixes_both by blast
          moreover have i6:"\<forall>l. TypedMemSubPref l destl (MTArray x t''') \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
            by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
                nat_neq_iff typedPrefix_imp_SubPref)
          moreover have i7:"\<forall>l. TypedMemSubPref l destl (MTArray x t''') \<longrightarrow> accessStore l v' = accessStore l v''" 
            using calculation by auto
          moreover have i8:"\<forall>l l'. TypedMemSubPref l destl (MTArray x t''') \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
          proof (intro allI impI)
            fix l l'
            assume asm:"TypedMemSubPref l destl (MTArray x t''') \<and> accessStore l v' = Some (MPointer l')"
            have l_neq:"l \<noteq> destl"
            proof
              assume "l = destl"
              then have "TypedMemSubPref destl destl (MTArray x t''')" using asm by blast
              then obtain i where "i < x \<and> (TypedMemSubPref destl (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t''' \<or> destl = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
                unfolding TypedMemSubPref.simps by blast
              then show False using hash_inequality 
                by (metis hash_inequality LSubPrefL2_def hash_flatten_right neg_MemLSubPrefL2_imps_TypedMemSubPref)
            qed
            have sto_sub_root:"TypedStoSubpref l destl (STArray x t')"
              using "2.prems"(2) asm compatible_TypedStoSubpref_imps_TypedMemSubPref l_neq 
              by auto
            then show "l' = l"
              using cps2mSelfPointers[OF a10] asm l_neq by blast
          qed
          show ?thesis
          proof(cases t'')
            case (MTArray x11 x12)
            then have cc0:"CompMemType v' x t''' (MTArray x11 x12) destl destl' \<and>
                                (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some x12)" 
              using i2 by simp
            then have "CompMemType v'' x t''' (MTArray x11 x12) destl destl' \<and>
                          (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12)"
              using CompMemType_preservation_induction[OF i5 i6 i7 cc0 i8] i1 
              by (smt (verit, ccfv_threshold) LSubPrefL2_def True TypedMemSubPref.simps(2) a30 
                  hash_flatten_right hashesInts i6 cps2mrec_SubPrefixes_both
                  typedPrefix_imp_SubPref)
            then show ?thesis  using CompMemType_extend2 by force
          next
            case (MTValue x2)
            then have cc0:"accessTypeStore destl' v' = Some (MTValue x2) \<and> CompMemType v' x t''' (MTValue x2) destl destl'" using i2 by simp
            then have "CompMemType v'' x t''' (MTValue x2) destl destl' \<and> accessTypeStore destl' v'' = Some (MTValue x2)"
              using CompMemTypeValue_preservation_induction[OF i5 i6 i7 cc0 i8] 
              using True a30 i6 cps2mrec_SubPrefixes_both by blast
            then show ?thesis using CompMemType_extend by fastforce
          qed 

        next
          case False
          then have subs:"(\<forall>i<x. \<not>TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t''' \<and> destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" by simp
          moreover obtain i where idef:"i<Suc x \<and> (TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t'''  \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
            using 2(3) f1 unfolding TypedMemSubPref.simps by auto
          have iIsx:"i = x" 
          proof(rule ccontr)
            assume a0:"i \<noteq> x"
            then have "i < x \<and> (TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t''' \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
              using idef by simp
            then show False using subs by auto
          qed

          then have "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' ms v' = Some v''" using a30 by simp

          then have IH1:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t''' \<longrightarrow>
        (case t''' of
         MTArray x' t' \<Rightarrow>
           \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
                  | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
         | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t''')" 
            using STArray.IH[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ms v' v''] idef a30 iIsx 
            using "2.prems"(2) by presburger

          then show ?thesis
          proof(cases t')
            case (STArray x11 x12)
            then obtain tF where tfDef: "t''' = MTArray x11 tF" 
              by (metis "2.prems"(2) mtypes.exhaust cps2mTypeCompatible.simps(2,3))
            then have a:"Some v'' = (case cps2mTypeConvert x12 of None \<Rightarrow> None
                              | Some t' \<Rightarrow>
                              let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 t') v'
                              in iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11)"
              using a30 cps2mrec.simps(1)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12 ms v'] STArray by auto
            then obtain ll where llDef:"cps2mTypeConvert x12 =  Some ll" by (auto split:option.splits memoryvalue.splits)

	            then have a':"let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 ll) v'
	                              in iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11 = Some v''" using a by simp
	            have step_arr:
	              "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (STArray x11 x12) ms v' = Some v''"
	              using a30 STArray by simp
	            have v''Def:
	              "Some v'' = iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms)
	                (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 ll) v') x11"
	              using a' llDef unfolding Let_def by simp
	            have root_bundle:
	              "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 ll)
	                \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	              using cps2mrec_array_root_both[OF step_arr llDef] by simp
	            then show ?thesis
	            proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	              case True
	              then have "accessTypeStore destl' v'' = Some (MTArray x11 ll)"
	                using root_bundle by simp
	              moreover have "CompMemType v'' (Suc x) (MTArray x11 ll) (MTArray x11 ll) destl destl'"
	                using True root_bundle unfolding CompMemType.simps by blast
	              moreover have "\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some ll" 
	                using cps2m_TypeCompChangeIndexs[OF v''Def[symmetric]] True 2(4) llDef 
	                using STArray convertComp tfDef by auto
	              ultimately show ?thesis using root_bundle 
	                by (smt (verit, best) "2.prems"(2) mtypes.simps(5) STArray convertComp cps2mTypeCompatible.simps(2) llDef option.inject tfDef)
	            next
              case False
              then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'''"  using subs iIsx 
                using idef by blast
              then have "(case t''' of
     MTArray x' t' \<Rightarrow>
       \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
             (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
     | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t''')" 
                using IH1 by simp
              then show ?thesis using STArray root_bundle t'''def 2(4) 
                using tfDef by auto
            qed
          next
            case (STMap x21 x22)
            then show ?thesis using 2 by simp
          next
            case (STValue x3)
            then have destl'Def:"destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using idef iIsx 2(4) 
              using convertComp by force
            then have v''Def:"Some v'' = (let v = accessStorage x3 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms in Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x3) v'))"
              using a30 cps2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x3 ms v'] STValue by simp
            then obtain v where "accessStorage x3 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = v" by (auto split:option.splits memoryvalue.splits)
            then have "v'' = (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x3) v') " using v''Def by simp
            then have "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTValue x3)"
              unfolding updateTypeStore_def updateTypedStore_def accessTypeStore_def updateStore_def by simp
            then show ?thesis using STValue destl'Def convertComp 2(4) by fastforce
          qed
        qed
      qed
    qed
    then show "case tp of
       MTArray x' t' \<Rightarrow>
         \<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
               (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
       | MTValue val \<Rightarrow> accessTypeStore destl v''' = Some tp" 
      by (simp add: t'''def)
  qed
next
  case (STMap x1 t')
  then show ?case by simp
next
  case (STValue x)
  show ?case 
  proof intros
    fix destl'
    assume **:"cps2mrec srcl destl (STValue x) ms md = Some v'''"
      and ****:"cps2mTypeCompatible (STArray l (STValue x)) (MTArray l tp)"
      and ***:"TypedMemSubPref destl' destl tp"
    then have "destl' = destl" 
      by (meson TypedStoSubpref.simps(1) compatible_TypedStoSubpref_imps_TypedMemSubPref cps2mTypeCompatible.simps(2))
    obtain v where "accessStorage x srcl ms = v \<and> Some (updateTypedStore destl (MValue v) (MTValue x) md) = Some v'''"
      using ** unfolding cps2mrec.simps by (auto split:option.splits memoryvalue.splits)
    then show "case tp of
       MTArray x' t' \<Rightarrow>
         \<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
               (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
       | MTValue val \<Rightarrow> accessTypeStore destl v''' = Some tp"
      using \<open>destl' = destl\<close> **** convertComp unfolding updateTypedStore_def updateTypeStore_def accessTypeStore_def 
      by fastforce
  qed
qed


lemma cps2m_TypeCompChange:
  assumes "iter' (\<lambda>i m''. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms m'') md x1 = Some v'"
    and "cps2mTypeCompatible (STArray x1 t') (MTArray x1 t)"
  shows "(\<forall>destl'. TypedMemSubPref destl' destl (MTArray x1 t) \<longrightarrow>
  (\<exists>st. CompMemType v' x1 t st destl destl' \<and>
            (case st of MTArray parent_len parent_arr \<Rightarrow> 
              \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval))))" using assms(2)
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: " iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) md x = Some v'"
      and a20: "(cps2mTypeCompatible (STArray x t') (MTArray x t) \<longrightarrow>
          (\<forall>destl'.
              TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
              (\<exists>st. CompMemType v' x t st destl destl' \<and>
                    (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
                     | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval)))))"
      and a30: "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' ms v' = Some v''" by blast
  then have "(\<forall>destl'.
        TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        (case t of
         MTArray x' t' \<Rightarrow>
           \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
                  | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
         | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t))"
    using "2.prems"  cps2mrec_TypeCompChange by presburger
  show ?case
  proof intros
    fix destl'
    assume a1:"TypedMemSubPref destl' destl (MTArray (Suc x) t)"
    show "\<exists>st. CompMemType v'' (Suc x) t st destl destl' \<and>
            (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))"
    proof(cases "TypedMemSubPref destl' destl (MTArray x t)")
      case True
      then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using True
        by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
      moreover have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using True
        by (smt (verit, ccfv_threshold) LSubPrefL2_def ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesInts nat_neq_iff
            neg_MemLSubPrefL2_imps_TypedMemSubPref)
      then have "\<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'" 
        using "2.prems" compatible_TypedStoSubpref_imps_TypedMemSubPref 
        by (simp add: calculation)
      ultimately have i1:"accessTypeStore destl' v' = accessTypeStore destl' v''"
        using cps2mrec_SubPrefixes2_both[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' ms v' v''] a30 by blast

      obtain t'' where i2:"(CompMemType v' x t t'' destl destl' \<and>
       (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
        | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval)))" 
        using True a20 a10 2 by auto


      have i5:"\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
        using a30 cps2mrec_SubPrefixes_both by blast
      moreover have i6:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
        by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
            nat_neq_iff typedPrefix_imp_SubPref)
      moreover have i7:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" 
        using calculation by auto
      moreover have i8:"\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
      proof (intro allI impI)
        fix l l'
        assume asm:"TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l')"
        have l_neq:"l \<noteq> destl"
        proof
          assume "l = destl"
          then have "TypedMemSubPref destl destl (MTArray x t)" using asm by blast
          then obtain i where "i < x \<and> (TypedMemSubPref destl (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> destl = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
            unfolding TypedMemSubPref.simps by blast
          then show False using hash_inequality 
            by (metis hash_inequality LSubPrefL2_def hash_flatten_right neg_MemLSubPrefL2_imps_TypedMemSubPref)
        qed
        have sto_sub_root:"TypedStoSubpref l destl (STArray x t')"
          using "2.prems" asm compatible_TypedStoSubpref_imps_TypedMemSubPref l_neq by auto
        then show "l' = l"
          using cps2mSelfPointers[OF a10] asm l_neq by blast
      qed
      show ?thesis
      proof(cases t'')
        case (MTArray x11 x12)
        then have cc0:"CompMemType v' x t (MTArray x11 x12) destl destl' \<and>
                          (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some x12)" 
          using i2 by simp
        then have "CompMemType v'' x t (MTArray x11 x12) destl destl' \<and>
                    (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12)"
          using CompMemType_preservation_induction[OF i5 i6 i7 cc0 i8] i1 
          by (smt (verit, ccfv_threshold) LSubPrefL2_def True TypedMemSubPref.simps(2) a30 
              hash_flatten_right hashesInts i6 cps2mrec_SubPrefixes_both
              typedPrefix_imp_SubPref)
        then show ?thesis  using CompMemType_extend2 by force
      next
        case (MTValue x2)
        then have cc0:"accessTypeStore destl' v' = Some (MTValue x2) \<and> CompMemType v' x t (MTValue x2) destl destl'" using i2 by simp
        then have "CompMemType v'' x t (MTValue x2) destl destl' \<and> accessTypeStore destl' v'' = Some (MTValue x2)"
          using CompMemTypeValue_preservation_induction[OF i5 i6 i7 cc0 i8] 
          using True a30 i6 cps2mrec_SubPrefixes_both by blast
        then show ?thesis using CompMemType_extend by fastforce
      qed 
    next
      case False
      then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<or> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" 
        using a1 unfolding TypedMemSubPref.simps  
        using less_SucE by blast
	      then show ?thesis 
	      proof(cases t)
	        case (MTArray x11 x12)
	          then obtain x12' where t'Def:"t' = STArray x11 x12'" using 2(3) 
	            by (metis cps2mTypeCompatible.elims(2) cps2mTypeCompatible.simps(2,6))
        then have a:"Some v'' =  (case cps2mTypeConvert x12' of None \<Rightarrow> None
     | Some t' \<Rightarrow>
         let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 t') v'
         in iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12' ms) m x11)"
          using a30 cps2mrec.simps(1)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12' ms v'] by auto
        then have x12'Def:"cps2mTypeConvert x12' = Some x12" using convertComp MTArray t'Def
          using "2.prems" by force
	        have step_arr:
	          "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (STArray x11 x12') ms v' = Some v''"
	          using a30 MTArray t'Def by simp
	        have v''Def:
	          "Some v'' = iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12' ms)
	            (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v') x11"
	          using a x12'Def unfolding Let_def by simp
	        have root_bundle:
	          "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 x12)
	            \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	          using cps2mrec_array_root_both[OF step_arr x12'Def] by simp
	        then show ?thesis
	        proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	          case True
	          then have "accessTypeStore destl' v'' = Some (MTArray x11 x12)"
	            using root_bundle by simp
	          moreover have "CompMemType v'' (Suc x) (MTArray x11 x12) (MTArray x11 x12) destl destl'"
	            using MTArray True root_bundle unfolding CompMemType.simps by blast
	          moreover have "\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12" 
	            using cps2m_TypeCompChangeIndexs[OF v''Def[symmetric]] True 
	            using MTArray assms(2) cps2mTypeCompatible.simps(2) t'Def by blast
	          ultimately show ?thesis using MTArray True root_bundle by force
	        next
	          case False
          then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" 
            using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<or> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t\<close> by blast
          then have "(case t of
                     MTArray x' t' \<Rightarrow>
                      \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
                  | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
                     | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t)" 
            using cps2mrec_TypeCompChange[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' ms v' v''] 2(3) a30 
            by auto
	          then have "\<exists>t''. CompMemType v'' x11 x12 t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
	                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
	                              | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))"
	            using MTArray by auto
	          then show ?thesis using MTArray root_bundle by auto
	        qed
	      next
        case (MTValue x2)
        then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
          using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<or> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t\<close> by auto
        then have "Some v'' = (let v = accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms in Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v'))"
          using a30 cps2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 ms v'] MTValue 
          by (metis "2.prems" stypes.exhaust cps2mTypeCompatible.simps(1,2,3,4))
        then show ?thesis unfolding updateTypeStore_def updateTypedStore_def accessTypeStore_def updateStore_def using MTValue  
          using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> accessTypeStore_def by auto
      qed
    qed
  qed
qed

lemma cps2mrec_somesome:
  "cps2mrec srcl destl tp ms a = Some v''' \<longrightarrow> cps2mTypeCompatible tp tp' \<longrightarrow>
  (\<forall>destl'. TypedMemSubPref destl' destl tp' \<longrightarrow> ((\<exists>t. accessStore destl' v''' = Some t) 
      \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v''' = Some tt)))"
proof(induction tp arbitrary:destl a v''' srcl tp')
  case (STArray x1 t)
  show ?case
  proof intros 
    fix destl'
    assume **:"cps2mrec srcl destl (STArray x1 t) ms a = Some v'''"
      and ****:"cps2mTypeCompatible (STArray x1 t) tp'"
      and ***:"TypedMemSubPref destl' destl tp'"
    have a5:"Some v'''
            = (case cps2mTypeConvert t of None \<Rightarrow> None
     | Some t' \<Rightarrow> let m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x1)" 
      using **  cps2mrec.simps(1)[of srcl destl x1 t ms a] by simp
    then obtain t' where ldef:"cps2mTypeConvert t = Some t'" by (auto split:option.splits memoryvalue.splits)
    then have a6:"Some v''' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t') a in iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x1)"
      using a5 by auto
    then obtain m where mdef:"updateTypedStore destl (MPointer destl) (MTArray x1 t') a = m" by auto
    then have v''def:"Some v''' = iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x1" using a6 by simp
    have tp'Def:"tp' = MTArray x1 t'" using **** ldef 
      using convertComp by fastforce
    then have ****:"cps2mTypeCompatible (STArray x1 t) (MTArray x1 t')" using **** by blast
    have ***:"TypedMemSubPref destl' destl (MTArray x1 t')" using *** tp'Def by blast
    have "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)" 
      using *** ****
    proof(induction rule: iter'_induct[OF _ _ v''def[symmetric]]) 
      case (1)
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x = Some v'"
          and a20:"(TypedMemSubPref destl' destl (MTArray x t') \<longrightarrow>
          cps2mTypeCompatible (STArray x t) (MTArray x t') \<longrightarrow> (\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt))"
          and a30:"cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
      then show ?case 
      proof(cases "destl' = destl")
        case True
        then show ?thesis using a10 a30 
          by (metis "***" LSubPrefL2_def TypedMemSubPref.simps(2) hash_flatten_right hash_inequality typedPrefix_imp_SubPref)
      next
        case f1:False
        then show ?thesis 
        proof(cases "TypedMemSubPref destl' destl (MTArray x t')")
          case True
          then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
            by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
          moreover have "\<forall>i<x. \<not> TypedMemSubPref (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'" using True 
            by (smt (verit, ccfv_threshold) LSubPrefL2_def TypedMemSubPref.simps(2) hash_flatten_right hashesInts nat_neq_iff
                neg_MemLSubPrefL2_imps_TypedMemSubPref)
          moreover have "(\<forall>destl'. destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> \<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' v'')"
            using cps2mrec_SubPrefixes2_both[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t ms v' v'' ] a30 by blast
          moreover have "(\<forall>destl'. destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> \<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' 
                            \<longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' v'')"
            using  2(4) compatible_TypedStoSubpref_imps_TypedMemSubPref calculation by simp
          ultimately have i1:"\<forall>i<x. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" 
            by (meson ShowLNatDot f1 hash_injective)
          have i2:"(\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt)"
            using True a20 
            using "***" "2.prems"(2) by force

          have i5:"\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
            using a30 cps2mrec_SubPrefixes_both by blast
          moreover have i6:"\<forall>l. TypedMemSubPref l destl (MTArray x t') \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
            by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
                nat_neq_iff typedPrefix_imp_SubPref)
          ultimately have i7:"\<forall>l. TypedMemSubPref l destl (MTArray x t') \<longrightarrow> accessStore l v' = accessStore l v''" by auto
          have i8:"\<forall>l l'. TypedMemSubPref l destl (MTArray x t') \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
          proof (intro allI impI)
            fix l l'
            assume asm:"TypedMemSubPref l destl (MTArray x t') \<and> accessStore l v' = Some (MPointer l')"
            have l_neq:"l \<noteq> destl"
            proof
              assume "l = destl"
              then have "TypedMemSubPref destl destl (MTArray x t')" using asm by blast
              then obtain i where "i < x \<and> (TypedMemSubPref destl (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' \<or> destl = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
                unfolding TypedMemSubPref.simps by blast
              then show False using hash_inequality             
                by (metis hash_inequality LSubPrefL2_def hash_flatten_right neg_MemLSubPrefL2_imps_TypedMemSubPref)

            qed
            have sto_sub_root:"TypedStoSubpref l destl (STArray x t)"
              using 2(4) asm compatible_TypedStoSubpref_imps_TypedMemSubPref l_neq by auto
            then show "l' = l"
              using cps2mSelfPointers[OF a10] asm l_neq by blast
          qed

          show ?thesis using i2 
            using True a30 i6 i7 cps2mrec_SubPrefixes_both by auto
        next
          case False
          then have b5:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
            using 2 TypedMemSubPref.simps(2)[of destl' destl "(Suc x)" t'] f1 
            using less_Suc_eq 
            by (metis TypedMemSubPref.simps(2))
          have "\<not> TypedStoSubpref destl' destl (STArray x t)" 
            using 2(4) compatible_TypedStoSubpref_imps_TypedMemSubPref 
            using False 
            by (simp add: f1)
          then have "accessTypeStore destl' m = accessTypeStore destl' v'" 
            using cps2mSingleChange2_both[of srcl destl t ms m x v'] a10 f1 False by blast
          then have "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" using a30 by simp
          then have IH1:"(\<forall>destl'. TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> 
                            (\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt))" 
            using 2(4) STArray.IH[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v'' t'] by simp

          have "(\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt)" 
          proof(cases "t")
            case (STArray x11 x12)
            then have a:"Some v'' = (case cps2mTypeConvert x12 of None \<Rightarrow> None
                              | Some t' \<Rightarrow>
                         let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 t') v'
                         in iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11)"
              using a30 cps2mrec.simps(1)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12 ms v'] 
              by simp
            then obtain tpp where lldef:"cps2mTypeConvert x12 = Some tpp" by (auto split:option.splits memoryvalue.splits)
	            have step_arr:
	              "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (STArray x11 x12) ms v' = Some v''"
	              using a30 STArray by simp
	            have v''Def:
	              "Some v'' = iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms)
	                (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 tpp) v') x11"
	              using  lldef unfolding Let_def 
	              by (metis (lifting) Option.option.simps(5) a)
	            have root_bundle:
	              "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 tpp)
	                \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	              using cps2mrec_array_root_both[OF step_arr lldef] by simp
	            then show ?thesis 
	              using IH1 root_bundle b5 by auto
	          next
            case (STMap x21 x22)
            then show ?thesis using 2 by simp
          next
            case (STValue x2)
            then show ?thesis using IH1 b5 
              using ldef by auto
          qed
          then show ?thesis by blast         
        qed
      qed
    qed
    then show "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)" by auto
  qed
next
  case (STMap x1 tp)
  then show ?case by simp
next
  case (STValue x)
  show ?case 
  proof intros
    fix destl'
    assume **:"cps2mrec srcl destl (STValue x) ms a = Some v'''"
      and ****:"cps2mTypeCompatible (STValue x) tp'"
    assume ***:"TypedMemSubPref destl' destl tp'"

    have tp'Def:"tp' = (MTValue x)" using **** cps2mTypeCompatible.simps 
      using convertComp by force
    then have mdef:"Some v''' = (let v = accessStorage x srcl ms in Some (updateTypedStore destl (MValue v) (MTValue x) a))"
      using ** cps2mrec.simps(2)[of srcl destl x ms a] by simp
    then obtain v where vdef: "accessStorage x srcl ms = v" by (auto split:option.splits memoryvalue.splits)
    then have v'''def:"Some v''' = Some (updateTypedStore destl (MValue v) (MTValue x) a)" using mdef by simp
    then have "accessTypeStore destl v''' = Some (MTValue x)" using mdef
      unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    moreover have "accessStore destl' v''' = Some (MValue v)"
      using v'''def unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def 
      using "***" tp'Def by simp
    ultimately show "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)" 
      using "***" tp'Def by fastforce
  qed
qed

lemma cps2m_TypeCompChange_somesome:
  assumes "iter' (\<lambda>i m''. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms m'') md x1 = Some v'"
    and "cps2mTypeCompatible (STArray x1 t') (MTArray x1 t)"
  shows "(\<forall>destl'. TypedMemSubPref destl' destl (MTArray x1 t) \<longrightarrow> 
          ((\<exists>t. accessStore destl' v' = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v' = Some tt)))" using assms(2)
proof(induction  rule: iter'_induct[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter' (\<lambda>i. cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t' ms) md x = Some v'"
      and a20: "(cps2mTypeCompatible (STArray x t') (MTArray x t) \<longrightarrow>
          (\<forall>destl'. TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow> (\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt)))"
      and a30: " cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' ms v' = Some v''" by blast

  show ?case 
  proof intros
    fix destl' 
    assume a1:"TypedMemSubPref destl' destl (MTArray (Suc x) t)" 
    show "((\<exists>t. accessStore destl' v'' = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v'' = Some tt))"
    proof(cases "TypedMemSubPref destl' destl (MTArray x t)")
      case True
      then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"  using True
        by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
      moreover have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using True 
        by (smt (verit, ccfv_threshold) LSubPrefL2_def ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesInts nat_neq_iff
            neg_MemLSubPrefL2_imps_TypedMemSubPref)
      ultimately have i1:"\<forall>destl'. destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> \<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow>
        accessTypeStore destl' v' = accessTypeStore destl' v''" 
        using cps2mrec_SubPrefixes2_both[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' ms v' v''] a30 by blast
      then have i1':"\<forall>destl'. destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> \<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        accessTypeStore destl' v' = accessTypeStore destl' v''" using 2(3) 
        by (simp add: compatible_TypedStoSubpref_imps_TypedMemSubPref)
      then have i2:"(\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt)" 
        using i1 True a20 2(3) by auto

      have store_preserved: "\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
        using a30 cps2mrec_SubPrefixes_both by blast
      moreover have no_prefix_conflict: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
        by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
            nat_neq_iff typedPrefix_imp_SubPref)
      ultimately have store_consistency: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" 
        by auto

      show ?thesis using i2 
        using True \<open>\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t\<close> \<open>destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> i1 store_consistency 
        by (simp add: i1')

    next
      case False
      then have a2:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
        using a1 unfolding TypedMemSubPref.simps 
        using less_SucE by blast
      then show ?thesis  
      proof(cases t')
        case (STArray x11 x12)
        then have a:"Some v'' = (case cps2mTypeConvert x12 of None \<Rightarrow> None
     | Some t' \<Rightarrow>
         let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 t') v'
         in iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11)"
          using a30 cps2mrec.simps(1)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12 ms v'] by auto
        then obtain l where ldef:"cps2mTypeConvert x12 = Some l" by (auto split:option.splits memoryvalue.splits)
	        have step_arr:
	          "cps2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (STArray x11 x12) ms v' = Some v''"
	          using a30 STArray by simp
	        have v''Def:
	          "Some v'' = iter' (\<lambda>i. cps2mrec (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms)
	            (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 l) v') x11"
	          by (metis (lifting) Option.option.simps(5) a ldef)
	        have root_bundle:
	          "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 l)
	            \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	          using cps2mrec_array_root_both[OF step_arr ldef] by simp
	        then show ?thesis
	        proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	          case True
          then have "\<forall>i<x11. TypedMemSubPref (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 l)" by auto
	          then have "\<forall>i<x11. accessTypeStore (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some l"
	            using cps2m_TypeCompChangeIndexs[OF v''Def[symmetric]] 2(3) ldef 
	            by (metis mtypes.exhaust STArray convertComp cps2mTypeCompatible.simps(2,3))
	          moreover have "CompMemType v'' (Suc x) (MTArray x11 l) (MTArray x11 l) destl destl'"
	            using True root_bundle unfolding CompMemType.simps by blast
	          ultimately show ?thesis using root_bundle mtypes.simps(5) True by simp
	        next
	          case False
          then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using a2 by blast
          then have "(\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt)" 
            using cps2mrec_somesome[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' ms v' v''] 2 a30 by simp
	          then show ?thesis using root_bundle by auto
	        qed
      next
        case (STMap x21 x22)
        then show ?thesis using 2 by simp
      next
        case (STValue x2) 
        then have tdef:"t = MTValue x2" using 2(3) cps2mTypeCompatible.simps  
          using convertComp by force
        then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using a2 2(3) cps2mTypeCompatible.simps 
          by (metis TypedMemSubPref.simps(1))
        then have v'':"Some v'' = (let v = accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms in Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v'))"
          using a30 cps2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 ms v' ] STValue by simp
        then obtain v where "accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = (v)" by (auto split:option.splits memoryvalue.splits)
        then have "Some v'' = Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v')" using v'' by simp
        then show ?thesis unfolding updateTypeStore_def updateTypedStore_def accessTypeStore_def updateStore_def using tdef STValue   
          using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> accessTypeStore_def a30 cps2mrec_somesome 
          by (metis TypedMemSubPref.simps(1) cps2mTypeCompatible.simps(1))
      qed
    qed
  qed
qed


end
