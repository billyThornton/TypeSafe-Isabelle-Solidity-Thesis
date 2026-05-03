theory TypeSafe_Expressions
  imports TypeSafe_Copies TypeSafe_Environment

begin

context typesafe_base
begin

section \<open>The following demonstrate that the supported Solidity expressions of isabelle-solidity
        do not violate the Typesafety of a given environment.\<close>


subsection \<open>Olift and Plift\<close>
lemma oliftTypeInput:
  assumes "olift op t1 t2 v1 v2 = Some(v',t')"
  shows "(\<exists>b. t1 = (TSInt b) \<or> t1 = (TUInt b)) \<and> (\<exists>b2. t2 = (TSInt b2) \<or> t2 = (TUInt b2))"
proof
  show "\<exists>b. t1 = TSInt b \<or> t1 = TUInt b" using assms olift.simps by (cases t1; cases t2; simp split:if_split_asm)
next
  show "\<exists>b2. t2 = TSInt b2 \<or> t2 = TUInt b2" using assms olift.simps by (cases t1; cases t2; simp split:if_split_asm)
qed

lemma pliftTypeInput:
  assumes "plift op t1 t2 v1 v2 = Some(v',t')"
  shows "(\<exists>b. t1 = (TSInt b) \<or> t1 = (TUInt b)) \<and> (\<exists>b2. t2 = (TSInt b2) \<or> t2 = (TUInt b2))"
proof
  show "\<exists>b. t1 = TSInt b \<or> t1 = TUInt b" using assms plift.simps by (cases t1; cases t2; simp split:if_split_asm)
next
  show "\<exists>b2. t2 = TSInt b2 \<or> t2 = TUInt b2" using assms plift.simps by (cases t1; cases t2; simp split:if_split_asm)
qed

lemma vtandTypeOut:
  assumes "vtand t1 t2 v1 v2 = Some(v', t')"
  shows "(v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<or> v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) \<and> t' = TBool"
proof -
  have a10:"t1 = TBool \<and> t2 = TBool" using assms vtand.elims by blast
  have "vtand TBool TBool v1 v2 = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool) \<or> vtand TBool TBool v1 v2 = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False, TBool)" using vtand.simps assms by simp
  then show "(v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<or> v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) \<and> t' = TBool" using assms a10 by auto
qed

lemma vtorTypeOut:
  assumes "vtor t1 t2 v1 v2 = Some(v', t')"
  shows "(v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<or> v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) \<and> t' = TBool"
proof -
  have a10:"t1 = TBool \<and> t2 = TBool" using assms vtor.elims by blast
  have "vtor TBool TBool v1 v2 = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool) \<or> vtor TBool TBool v1 v2 = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False, TBool)" using vtor.simps assms by simp
  then show "(v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<or> v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) \<and> t' = TBool" using assms a10 by auto
qed

lemma vtandTypeCon:
  assumes "vtand t1 t2 v1 v2 = Some(v', t')"
    and "(v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<or> v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) \<and> t' = TBool"
  shows "typeCon t' v'" using checkBool_def createBool_def  ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def assms by (simp split:if_splits)

subsubsection \<open>Results of successful olift must be typecon\<close>
lemma oliftTypeCon:
  assumes "olift op t1 t2 v1 v2 = Some(v',t')"
    and "t1 = TSInt b1 \<or> t1 = TUInt b1"
    and "t2 = TSInt b2 \<or> t2 = TUInt b2"
  shows "typeCon t' v'"
proof -
  consider (s1) "t1 = TSInt b1" | (u1) "t1 = TUInt b1" using assms(2) by auto
  then show ?thesis
  proof(cases)
    case s1
    consider (s2) "t2 = TSInt b2" | (u2) "t2 = TUInt b2" using assms(3) by auto
    then show ?thesis 
    proof(cases)
      case s2
      then have a10:"v' = createSInt (max b1 b2) (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))" using s1 olift.simps(1) assms by simp
      then have a20:"t' =  TSInt (max b1 b2)" using s1 s2 olift.simps(1) assms by simp
      then have "checkSInt (max b1 b2) (createSInt (max b1 b2) (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2)))" 
        using checkSIntCreate[of "(max b1 b2)" "(op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))"]  assms(3) by simp
      then show ?thesis using a10 a20 by simp
    next
      case u2
      then have a10:"v' = createSInt b1 (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))" using s1 olift.simps(3) assms by (simp split:if_split_asm)
      then have a20:"t' =  TSInt b1" using s1 u2 olift.simps(3) assms by (simp split:if_split_asm)
      then have "checkSInt b1 (createSInt b1 (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2)))" 
        using checkSIntCreate[of "b1" "(op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))"] assms(3) by simp
      then show ?thesis using a10 a20 by simp
    qed
  next
    case u1
    consider (s2) "t2 = TSInt b2" | (u2) "t2 = TUInt b2" using assms(3) by auto
    then show ?thesis 
    proof(cases)
      case s2
      then have a10:"v' = createSInt b2 (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))" using u1 olift.simps(4) assms by (simp split:if_split_asm)
      then have a20:"t' =  TSInt b2" using u1 s2 olift.simps(4) assms by (simp split:if_split_asm)
      then have "checkSInt b2 (createSInt b2 (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2)))" 
        using checkSIntCreate[of "b2" "(op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))"] assms(3) by simp
      then show ?thesis using a10 a20 by simp 
    next
      case u2
      then have a10:"v' = createUInt (max b1 b2) (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))" using u1 olift.simps(2) assms by simp
      then have a20:"t' =  TUInt (max b1 b2)" using u1 u2 olift.simps(2) assms by simp
      then have "checkUInt (max b1 b2) (createUInt (max b1 b2) (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2)))" 
        using checkUIntCreate[of "(max b1 b2)" "(op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))"] assms(3) by simp
      then show ?thesis using a10 a20 by simp
    qed
  qed
qed

subsubsection \<open>Results of successful plift must be typecon\<close>
lemma pliftTypeCon:
  assumes "plift op t1 t2 v1 v2 = Some(v',t')"
    and "t1 = TSInt b1 \<or> t1 = TUInt b1"
    and "t2 = TSInt b2 \<or> t2 = TUInt b2"
  shows "typeCon t' v'"
proof -
  consider (s1) "t1 = TSInt b1" | (u1) "t1 = TUInt b1" using assms(2) by auto
  then show ?thesis
  proof(cases)
    case s1
    consider (s2) "t2 = TSInt b2" | (u2) "t2 = TUInt b2" using assms(3) by auto
    then show ?thesis 
    proof(cases)
      case s2
      then have a10:"v' = createBool (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))" using s1 plift.simps(1) assms by simp
      then have a20:"t' =  TBool" using s1 s2 plift.simps(1) assms by simp
      then have "checkBool (createBool (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2)))" unfolding checkBool_def createBool_def using ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by simp
      then show ?thesis using a10 a20 by simp
    next
      case u2
      then have a10:"v' = createBool (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))" using s1 plift.simps(3) assms by (simp split:if_split_asm)
      then have a20:"t' = TBool" using s1 u2 plift.simps(3) assms by (simp split:if_split_asm)
      then have "checkBool (createBool (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2)))"  unfolding checkBool_def createBool_def using ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by simp
      then show ?thesis using a10 a20 by simp
    qed
  next
    case u1
    consider (s2) "t2 = TSInt b2" | (u2) "t2 = TUInt b2" using assms(3) by auto
    then show ?thesis 
    proof(cases)
      case s2
      then have a10:"v' = createBool (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))" using u1 plift.simps(4) assms by (simp split:if_split_asm)
      then have a20:"t' = TBool" using u1 s2 plift.simps(4) assms by (simp split:if_split_asm)
      then have "checkBool (createBool (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2)))"  unfolding checkBool_def createBool_def using ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by simp
      then show ?thesis using a10 a20 by simp
    next
      case u2
      then have a10:"v' = createBool (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2))" using u1 plift.simps(2) assms by simp
      then have a20:"t' =  TBool" using u1 u2 plift.simps(2) assms by simp
      then have "checkBool (createBool (op (ReadL\<^sub>i\<^sub>n\<^sub>t v1) (ReadL\<^sub>i\<^sub>n\<^sub>t v2)))" unfolding checkBool_def createBool_def using ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by simp
      then show ?thesis using a10 a20 by simp
    qed
  qed
qed

subsubsection \<open>Lift Of an expression with olift must be typecon\<close>
lemma oliftSuccess:
  assumes "lift expr (olift op) e1 e2 ev cd st g = Normal ((KValue v, Value t), g')"
  shows "typeCon t v"
proof -
  obtain v1 t1 g'' where a10:"expr e1 ev cd st g = Normal((KValue v1, Value t1), g'')" 
    using lift_def assms by (auto split:result.split_asm stackvalue.split_asm type.split_asm)
  then obtain v2 t2 g''' where a20:"expr e2 ev cd st g'' = Normal((KValue v2, Value t2), g''')" using lift_def assms by (auto split:result.split_asm stackvalue.split_asm type.split_asm)
  then have a30:"(olift op) t1 t2 v1 v2 = Some(v, t)" using a10 a20 assms lift_def by (auto split:result.split_asm stackvalue.split_asm type.split_asm option.split_asm)
  then obtain b1 where a40:"t1 = TSInt b1 \<or> t1 = TUInt b1" using oliftTypeInput[of op t1 t2 v1 v2 v t] a10 by auto
  then obtain b2 where a50:"t2 = TSInt b2 \<or> t2 = TUInt b2" using oliftTypeInput[of op t1 t2 v1 v2 v t] a20 a30 by auto
  then show ?thesis using oliftTypeCon[of op t1 t2 v1 v2 v t b1 b2] a30 a40 a50 by simp
qed

subsubsection \<open>Lift Of an expression with plift must be typecon\<close>
lemma pliftSuccess:
  assumes "lift expr (plift op) e1 e2 ev cd st g = Normal ((KValue v, Value t), g')"
  shows "typeCon t v"
proof -
  obtain v1 t1 g'' where a10:"expr e1 ev cd st g = Normal((KValue v1, Value t1), g'')" using lift_def assms by (auto split:result.split_asm stackvalue.split_asm type.split_asm)
  then obtain v2 t2 g''' where a20:"expr e2 ev cd st g'' = Normal((KValue v2, Value t2), g''')" using lift_def assms by (auto split:result.split_asm stackvalue.split_asm type.split_asm)
  then have a30:"(plift op) t1 t2 v1 v2 = Some(v, t)" using a10 a20 assms lift_def by (auto split:result.split_asm stackvalue.split_asm type.split_asm option.split_asm)
  then obtain b1 where a40:"t1 = TSInt b1 \<or> t1 = TUInt b1" using pliftTypeInput[of op t1 t2 v1 v2 v t] a10 by auto
  then obtain b2 where a50:"t2 = TSInt b2 \<or> t2 = TUInt b2" using pliftTypeInput[of op t1 t2 v1 v2 v t] a20 a30 by auto
  then show ?thesis using pliftTypeCon[of op t1 t2 v1 v2 v t b1 b2] a30 a40 a50 by simp
qed

subsection \<open>Proof that expressions do not violate type consistency\<close>
text \<open>The following lemma proves that given a typesafe environment 
    all expressions, Memory selections, Storage selections and rexpressions return type consistent
    values. I.e. the string values returned are conform to the types that are expected. 
    This demonstrates that the semantics of expressions do not alter the values in any way which may
    violate type consistency
    Further this lemma also ensures that the env, mem, cd, store that are created by load typesafe
    with respect to one another.\<close>


(*Includes assumptions that the environment being used is fully intialised. using ffold_init
  I.e. it exist in Accounts and also all the Contract variables have be initialised using ffold init
  This is true from the context of statements. 
*)
lemma exprTypeconInduct[rule_format]:
  "\<forall>l1'  t1' g1' arr. msel c1 t1 l1 xe1 ev1 cd1 st1 g1 = Normal ((l1', t1'), g1') \<and> 
                            MCon t1 (if c1 then Memory st1 else cd1) l1 \<and> 
                            TypeSafe ev1 (Accounts st1) (Stack st1) (Memory st1) (Storage st1) cd1 \<and>
                            fullyInitialised ev1 (Accounts st1) (Stack st1) \<longrightarrow> 
                            (xe1 \<noteq> Nil \<longrightarrow> (\<exists>len arr. (t1 = MTArray len arr) \<and> 
                                            (case t1' of MTValue val \<Rightarrow>  CompMemType (if c1 then Memory st1 else cd1) len arr t1' l1 l1'
                                                        |(MTArray l' ar') \<Rightarrow> (\<exists>p. accessStore l1' (if c1 then Memory st1 else cd1) = Some (MPointer p) \<and>
                                                                               CompMemType (if c1 then Memory st1 else cd1) len arr t1' l1 p))))"
  "\<forall>l2' v2' t2' g2'. ssel t2 l2 xe2 ev2 cd2 st2 g2 = Normal ((l2', t2'), g2') \<and>  
                            SCon t2 l2  (Storage st2 (Address ev2))  \<and> 
                            TypeSafe ev2 (Accounts st2) (Stack st2) (Memory st2) (Storage st2) cd2 \<and>
                            fullyInitialised ev2 (Accounts st2) (Stack st2) \<longrightarrow> 
                            (xe2 \<noteq> Nil \<longrightarrow> CompStoType t2 t2' l2 l2')"
  "\<forall>v t g4'. expr e4 ev4 cd4 st4 g4 = Normal ((v, t), g4') \<and> 
                TypeSafe ev4 (Accounts st4) (Stack st4) (Memory st4) (Storage st4 ) cd4 \<and>
                  fullyInitialised ev4 (Accounts st4) (Stack st4) \<longrightarrow> 
                    (case t of Value typ \<Rightarrow> (typeCon typ (extractValueType(v)) \<and> (\<exists>xx. v = KValue xx))
                     | Calldata struct \<Rightarrow> (MCon struct cd4 (extractValueType(v)) \<and> (\<exists>xx. v = KCDptr xx)
                                              \<and> (\<exists>stloc tp'' p. (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev4)\<and> accessStore stloc (Stack st4) =Some (KCDptr p)
                                              \<and> ((tp'' = struct \<and>  v = KCDptr p) \<or> 
                                              (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd4 len arr struct p (extractValueType v)))))
                     | type.Memory struct \<Rightarrow> (MCon struct (Memory st4) (extractValueType(v)) \<and> (\<exists>xx. v = KMemptr xx) \<and> 
                                          (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev4)\<and> accessStore stloc (Stack st4) =Some (KMemptr p)
                                              \<and> ((tp'' = struct \<and> v = (KMemptr p)) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and>tp'' = MTArray len arr \<and> CompMemType (Memory st4) len arr struct p (extractValueType v)))))
                     | type.Storage struct \<Rightarrow> (SCon struct (extractValueType(v)) (Storage st4 (Address ev4))) \<and> (\<exists>xx. v = KStoptr xx)
                                                \<and> (\<exists>stloc tp''. (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev4)
                                                \<and>((((tp'' = struct \<and>  v = KStoptr stloc) \<or> 
                                                                  ((extractValueType v) \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))
                                                              )))" 

"\<forall>ev cd k m g'. load lcp lis lxs lev0 lcd0 lk lm lev lcd lst lg = Normal ((ev, cd, k, m), g') \<and>
                      (\<not>lcp \<longrightarrow> (\<forall>locs tp. MCon tp (Memory lst) locs \<longrightarrow> MCon tp lm locs) 
                                        \<and> Toploc (Memory lst) \<le> Toploc lm
                                        \<and> ncpDenvalueLimit lev0 lev lk (Stack lst) (Memory lst) 
                                        \<and> ncpOMemInDMem (Memory lst) lm
                                        \<and> ncpElementsNoSubPref (Memory lst) lm
                                        \<and> ncpNewSelfPoint (Memory lst) lm
\<and> Address lev = Address lev0
) \<and>
                    (TypeSafe lev (Accounts lst) (Stack lst) (Memory lst) (Storage lst ) lcd) \<and> 
                    (TypeSafe lev0 (Accounts lst) lk lm (Storage lst ) lcd0) \<and>
                     fullyInitialised lev (Accounts lst) (Stack lst) \<and>  fullyInitialised lev0 (Accounts lst) lk
\<longrightarrow>
                    (TypeSafe ev (Accounts lst) k m (Storage lst ) cd) \<and>
 fullyInitialised ev (Accounts lst) k
\<and> (\<not>lcp \<longrightarrow> (\<forall>locs tp. MCon tp (Memory lst) locs \<longrightarrow> MCon tp m locs) 
                                        \<and> Toploc (Memory lst) \<le> Toploc m
                                        \<and> ncpDenvalueLimit ev lev k (Stack lst) (Memory lst)  
                                        \<and> ncpOMemInDMem (Memory lst) m
                                        \<and> ncpElementsNoSubPref (Memory lst) m
                                        \<and> ncpNewSelfPoint (Memory lst) m)"
"\<forall>v3' t3'  g3'. rexp l3 ev3 cd3 st3 g3 = Normal ((v3', t3'), g3') \<and> TypeSafe ev3 (Accounts st3) (Stack st3) (Memory st3) (Storage st3 ) cd3 
                                          \<and> fullyInitialised ev3 (Accounts st3) (Stack st3)\<longrightarrow> 
                     (case t3' of Value typ \<Rightarrow> (typeCon typ (extractValueType(v3')) \<and> (\<exists>xx. v3' = KValue xx))
                                         | Calldata struct \<Rightarrow> (MCon struct cd3 (extractValueType(v3')) \<and> (\<exists>xx. v3' = KCDptr xx)
                                              \<and> (\<exists>stloc tp'' p. (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev3)\<and> accessStore stloc (Stack st3) =Some (KCDptr p)
                                              \<and> ((tp'' = struct \<and>  v3' = KCDptr p) \<or> 
                                              (\<exists>len arr. (extractValueType v3') \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd3 len arr struct p (extractValueType v3')))))
                                         | type.Memory struct \<Rightarrow> (MCon struct (Memory st3) (extractValueType(v3'))\<and> (\<exists>xx. v3' = KMemptr xx)
                                          \<and> (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev3)\<and> accessStore stloc (Stack st3) =Some (KMemptr p)
                                              \<and> ((tp'' = struct \<and>  v3' = KMemptr p) \<or> 
                                              (\<exists>len arr. (extractValueType v3') \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st3) len arr struct p (extractValueType v3')))))
                                         | type.Storage struct \<Rightarrow>  (SCon struct (extractValueType(v3')) (Storage st3 (Address ev3))) \<and> (\<exists>xx. v3' = KStoptr xx)
                                                \<and> (\<exists>stloc tp''. (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev3)
                                                \<and>(
                                                                  (((tp'' = struct \<and>  v3' = KStoptr stloc) \<or> 
                                                                  ((extractValueType v3') \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v3'))))
                                                              )))"
proof (induct rule: msel_ssel_expr_load_rexp.induct
    [where ?P1.0="\<lambda>c1 t1 l1 xe1 ev1 cd1 st1 g1. (\<forall>l1'  t1' g1' arr. msel c1 t1 l1 xe1 ev1 cd1 st1 g1 = Normal ((l1',  t1'), g1') 
                                        
                                        \<and> MCon t1 (if c1 then Memory st1 else cd1) l1 
                                        \<and> TypeSafe ev1 (Accounts st1) (Stack st1) (Memory st1) (Storage st1) cd1 \<and>
                                            fullyInitialised ev1 (Accounts st1) (Stack st1)
                                          \<longrightarrow> (xe1 \<noteq> Nil \<longrightarrow>  
                                                  (\<exists>len arr. (t1 = MTArray len arr) \<and> 
                                                      (case t1' of MTValue val \<Rightarrow>  CompMemType (if c1 then Memory st1 else cd1) len arr t1' l1 l1'
                                                                  |(MTArray l' ar') \<Rightarrow> (\<exists>p. accessStore l1' (if c1 then Memory st1 else cd1) = Some (MPointer p) \<and> 
                                                                                       CompMemType (if c1 then Memory st1 else cd1) len arr t1' l1 p )))))
"
      and ?P2.0="\<lambda>t2 l2 xe2 ev2 cd2 st2 g2. (\<forall>l2' v2' t2' g2'. ssel t2 l2 xe2 ev2 cd2 st2 g2 = Normal ((l2',  t2'), g2')\<and> SCon t2 l2  (Storage st2 (Address ev2)) 
                                            \<and> TypeSafe ev2 (Accounts st2) (Stack st2) (Memory st2) (Storage st2 ) cd2 
                                            \<and> fullyInitialised ev2 (Accounts st2) (Stack st2) \<longrightarrow> 
                                              (xe2 \<noteq> Nil \<longrightarrow> CompStoType t2 t2' l2 l2'))"
      and ?P3.0="\<lambda>e4 ev4 cd4 st4 g4. (\<forall>v t g4'. expr e4 ev4 cd4 st4 g4 = Normal ((v, t), g4') \<and> 
                    TypeSafe ev4 (Accounts st4) (Stack st4) (Memory st4) (Storage st4 ) cd4 \<and>
                 fullyInitialised ev4 (Accounts st4) (Stack st4) \<longrightarrow> 
                    (case t of Value typ \<Rightarrow> (typeCon typ (extractValueType(v)) \<and> (\<exists>xx. v = KValue xx))
                     | Calldata struct \<Rightarrow> (MCon struct cd4 (extractValueType(v)) \<and> (\<exists>xx. v = KCDptr xx)
\<and> (\<exists>stloc tp'' p. (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev4)\<and> accessStore stloc (Stack st4) =Some (KCDptr p)
                                              \<and> ((tp'' = struct \<and>  v = KCDptr p) \<or> 
                                              (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd4 len arr struct p (extractValueType v)))))
                     | type.Memory struct \<Rightarrow> (MCon struct (Memory st4) (extractValueType(v)) \<and> (\<exists>xx. v = KMemptr xx) \<and> 
                                          (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev4)\<and> accessStore stloc (Stack st4) =Some (KMemptr p)
                                              \<and> ((tp'' = struct \<and> v = (KMemptr p)) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and>  tp'' = MTArray len arr \<and> CompMemType (Memory st4) len arr struct p (extractValueType v)))))
                     | type.Storage struct \<Rightarrow> (SCon struct (extractValueType(v)) (Storage st4 (Address ev4))) \<and> (\<exists>xx. v = KStoptr xx)
                                                \<and> (\<exists>stloc tp''. (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev4)
                                                \<and>(
                                                                  (((tp'' = struct \<and>  v = KStoptr stloc) \<or> 
                                                                  ((extractValueType v) \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))
                                                              ))))"
      and ?P4.0="\<lambda>lcp lis lxs lev0 lcd0 lk lm lev lcd lst lg. (\<forall>ev cd k m g'. load lcp lis lxs lev0 lcd0 lk lm lev lcd lst lg = Normal ((ev, cd, k, m), g') \<and>
                                            (\<not>lcp \<longrightarrow> (\<forall>locs tp. MCon tp (Memory lst) locs \<longrightarrow> MCon tp lm locs) 
                                        \<and> Toploc (Memory lst) \<le> Toploc lm
                                        \<and> ncpDenvalueLimit lev0 lev lk (Stack lst) (Memory lst)  
                                        \<and> ncpOMemInDMem (Memory lst) lm
                                        \<and> ncpElementsNoSubPref (Memory lst) lm
                                        \<and> ncpNewSelfPoint (Memory lst) lm
                                        \<and> Address lev = Address lev0
                                    ) \<and>
                    (TypeSafe lev (Accounts lst) (Stack lst) (Memory lst) (Storage lst ) lcd) \<and> 
                    (TypeSafe lev0 (Accounts lst) lk lm (Storage lst ) lcd0) \<and>
                    fullyInitialised lev (Accounts lst) (Stack lst) \<and>  fullyInitialised lev0 (Accounts lst) (lk) \<longrightarrow> 
                                                              (TypeSafe ev (Accounts lst) k m (Storage lst ) cd) \<and>
                       
 fullyInitialised ev (Accounts lst) (k) \<and>
                       (\<not>lcp \<longrightarrow> (\<forall>locs tp. MCon tp (Memory lst) locs \<longrightarrow> MCon tp m locs) 
                                        \<and> Toploc (Memory lst) \<le> Toploc m
                                        \<and> ncpDenvalueLimit ev lev k (Stack lst) (Memory lst)  
                                        \<and> ncpOMemInDMem (Memory lst) m
                                        \<and> ncpElementsNoSubPref (Memory lst) m
                                        \<and> ncpNewSelfPoint (Memory lst) m)
)"
      and ?P5.0="\<lambda>l3 ev3 cd3 st3 g3. (\<forall>v3' t3' g3'. rexp l3 ev3 cd3 st3 g3 = Normal (( v3',  t3'), g3') 
\<and> TypeSafe ev3 (Accounts st3) (Stack st3) (Memory st3) (Storage st3 ) cd3 \<and>
                  fullyInitialised ev3 (Accounts st3) (Stack st3)\<longrightarrow> 
                     (case t3' of Value typ \<Rightarrow> (typeCon typ (extractValueType(v3')) \<and> (\<exists>xx. v3' = KValue xx))
                                         | Calldata struct \<Rightarrow> (MCon struct cd3 (extractValueType(v3')) \<and> (\<exists>xx. v3' = KCDptr xx)
                                              \<and> (\<exists>stloc tp'' p. (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev3)\<and> accessStore stloc (Stack st3) =Some (KCDptr p)
                                              \<and> ((tp'' = struct \<and>  v3' = KCDptr p) \<or> 
                                              (\<exists>len arr. (extractValueType v3') \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd3 len arr struct p (extractValueType v3'))))
                                            )
                                         | type.Memory struct \<Rightarrow> (MCon struct (Memory st3) (extractValueType(v3'))\<and> (\<exists>xx. v3' = KMemptr xx)
                                          \<and> (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev3)\<and> accessStore stloc (Stack st3) =Some (KMemptr p)
                                              \<and> ((tp'' = struct \<and> v3' = KMemptr p) \<or> 
                                              (\<exists>len arr. (extractValueType v3') \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st3) len arr struct p (extractValueType v3')))))
                                         | type.Storage struct \<Rightarrow> (SCon struct (extractValueType(v3')) (Storage st3 (Address ev3))) \<and> (\<exists>xx. v3' = KStoptr xx)
                                                \<and> (\<exists>stloc tp''. (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev3)
                                                \<and>(
                                                                  (((tp'' = struct \<and>  v3' = KStoptr stloc) \<or> 
                                                                  ((extractValueType v3') \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v3'))))
                                                              ))))"
      ])
  case (1 uu uv uw ux uy uz g)
  then show ?case using msel.simps(1) by simp 
next
  case (2 va vb vc vd ve vf vg g)
  then show ?case using msel.simps(2) by simp 
next
  case (3 mm al t loc x env cd st g)
  show ?case
  proof(intros)
    fix l1' t1' g1' arr 
    assume a1:
      "local.msel mm (MTArray al t) loc [x] env cd st g = Normal ((l1', t1'), g1') \<and>
      
       MCon (MTArray al t) (if mm then Memory st else cd) loc \<and> TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd 
      \<and> fullyInitialised env (Accounts st) (Stack st)"

    then obtain kv b g4'  where a20: "local.expr x env cd st g = Normal ((KValue kv, Value (TUInt b)), g4')"
      and a30: "less (TUInt b) (TUInt b256) kv (ShowL\<^sub>i\<^sub>n\<^sub>t (int al)) = Some ((ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), TBool)"
      using a1 msel.simps(3) 
      by (simp split: result.split_asm prod.split_asm types.split_asm type.split_asm if_split_asm stackvalue.split_asm option.split_asm memoryvalue.split_asm) 
    have a50: "checkUInt b kv" using 3(1) a1 a20 typeCon.simps(2)[of b "extractValueType (KValue kv)"] extractValueType.simps(1)[of kv] by auto
    then have a60:"ReadL\<^sub>i\<^sub>n\<^sub>t(kv) < int al " using a20 a30 less_def plift.simps(2)[of "(<)" b b256 kv "(ShowL\<^sub>i\<^sub>n\<^sub>t (int al))"] Read_ShowL_id[of "(int al)"] unfolding createBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    then have a62:"0\<le>ReadL\<^sub>i\<^sub>n\<^sub>t(kv)" and a65:"(ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) = kv" using a50 checkUInt_def[of b kv] by simp+
    have a64:"(ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))) = kv" using ShowLnat_ReadLint_inverse a62 a50 unfolding checkUInt_def by simp
    then have a70:"(nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) \<in> {0..al-1}" using a60 a62 by simp
    have a90: "l1' = (hash loc kv)" using a20  msel.simps(3)[of mm al t loc x env cd st g] a30 a1 by simp
    then have a100: "t =  t1'" using a1 msel.simps by (simp split:if_split_asm result.split_asm prod.split_asm  stackvalue.split_asm type.split_asm)
    have **:"MCon (MTArray al t) (if mm then Memory st else cd) loc" using a1 by blast
    then have defexp:"(if al = 0 then False else 
                        \<forall>i::nat <al. 
                                                (case (accessStore (hash loc  (ShowL\<^sub>n\<^sub>a\<^sub>t i))((if mm then Memory st else cd))) of
                                                 (Some (MPointer loc2)) \<Rightarrow> 
                                                        (case t of MTArray len' arr' \<Rightarrow> (MCon t (if mm then Memory st else cd) (loc2))
                                                            | _ \<Rightarrow> False)
                                                  | Some(MValue val) \<Rightarrow>  
                                                        (case t of MTValue typ \<Rightarrow> (MCon t (if mm then Memory st else cd) (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                                                            | _ \<Rightarrow> False)
                                                  | _ \<Rightarrow> False
                                                 )
          \<and>  ((\<exists>p. accessStore loc (if mm then Memory st else cd) = Some (MPointer p)) \<or> accessStore loc (if mm then Memory st else cd) = None))" using MCon.simps(2)[of al t "(if mm then Memory st else cd)" loc ] by simp
    have alNonZero:"al \<noteq> 0" using a60 a62 by simp
    then have b0:"(case (accessStore (hash loc  (ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))))((if mm then Memory st else cd))) of
                                             (Some (MPointer loc2)) \<Rightarrow> 
                                                    (case t of MTArray len' arr' \<Rightarrow> (MCon t (if mm then Memory st else cd) (loc2))
                                                        | _ \<Rightarrow> False)
                                              | Some(MValue val) \<Rightarrow>  
                                                    (case t of MTValue typ \<Rightarrow> (MCon t (if mm then Memory st else cd) (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)))))
                                                        | _ \<Rightarrow> False)
                                              | _ \<Rightarrow> False
                                             )" using defexp a60 a65 alNonZero by simp
    then obtain v1' where b1:"(accessStore (hash loc  (ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))))((if mm then Memory st else cd))) = Some v1'" using a64 
      by fastforce    
    then have a80:"(accessStore (hash loc kv) (if (\<not>mm) then cd else (Memory st))) =  Some(v1')" using a1 a70 a64 by auto



    assume b99:" [x] \<noteq> []" 
    have "\<exists>len arr.
          MTArray al t = MTArray len arr \<and>
          (case t1' of
           MTArray l' ar' \<Rightarrow>
             \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) \<and>
                 CompMemType (if mm then Memory st else cd) len arr t1' loc p
           | MTValue val \<Rightarrow>
               CompMemType (if mm then Memory st else cd) len arr t1' loc l1')" 
    proof(cases t)
      case (MTArray x11 x12)
      then obtain p where  "accessStore (hash loc kv) (if mm then Memory st else cd) = Some (MPointer p)"  using  b0 b1   a1 a70 a65 a80 a64  defexp 
        by (metis (no_types, lifting) mtypes.simps(5) memoryvalue.exhaust memoryvalue.simps(5) Option.option.simps(5))
      moreover have "CompMemType (if mm then Memory st else cd) al t t loc p" using calculation
        by (smt (z3) "**" MConPtrsMustBeSubLocs MTArray a60 a62 a80 b1 nat_less_iff CompMemType.simps(2))
      ultimately have "\<exists>p. accessStore (hash loc kv) (if mm then Memory st else cd) = Some (MPointer p) \<and> (CompMemType (if mm then Memory st else cd) al t t loc p)" by simp
      then show ?thesis using MTArray 
        using "**" CompTypeRemainsMCon mtypes.simps(5) a100 a90 by blast
    next
      case (MTValue x2)

      then show ?thesis 
        using MTValue CompMemType.simps(1) 
        using a100 a60 a62 a64 a90 nat_less_iff 
        by (metis (lifting) mtypes.simps(6))

    qed
    then show "\<exists>len arr.
          MTArray al t = MTArray len arr \<and>
          (case t1' of
           MTArray l' ar' \<Rightarrow>
             \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) \<and>
                 CompMemType (if mm then Memory st else cd) len arr t1' loc p
           | MTValue val \<Rightarrow>
               CompMemType (if mm then Memory st else cd) len arr t1' loc l1')"
      using a90 a100 by blast
  qed
next
  case (4 mm al t loc x y ys env cd st g)
  show ?case 
  proof (intros)
    fix l1' t1' g1' arr
    assume a1: "local.msel mm (MTArray al t) loc (x # y # ys) env cd st g = Normal ((l1', t1'), g1') \<and>
       MCon (MTArray al t) (if mm then Memory st else cd) loc \<and> TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd 
        \<and> fullyInitialised env (Accounts st) (Stack st)"

    then obtain kv b g4' l where a20: "local.expr x env cd st g = Normal ((KValue kv, Value (TUInt b)), g4')"
      and a30: "less (TUInt b) (TUInt b256) kv (ShowL\<^sub>i\<^sub>n\<^sub>t (int al)) = Some ((ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), TBool)"
      and a40: "accessStore (hash loc kv) (if mm then Memory st else cd) = Some (MPointer l)"
      and a45:"local.msel mm (MTArray al t) loc (x # y # ys) env cd st g = local.msel mm t l (y # ys) env cd st g4'"
      using a1 msel.simps(4) by (simp split: result.split_asm prod.split_asm types.split_asm type.split_asm if_split_asm stackvalue.split_asm option.split_asm memoryvalue.split_asm)  

    have a50: "checkUInt b kv" using 4(1) a1 a20 by simp
    then have a60:"ReadL\<^sub>i\<^sub>n\<^sub>t(kv) < int al " using a20 a30 less_def plift.simps(2)[of "(<)" b b256 kv "(ShowL\<^sub>i\<^sub>n\<^sub>t (int al))"] Read_ShowL_id[of "int al"] unfolding createBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    then have a62:"0\<le>ReadL\<^sub>i\<^sub>n\<^sub>t(kv)" and a65:"(ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) = kv" using a50 checkUInt_def[of b kv] by simp+
    then have a64:"(ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))) = kv" using ShowLnat_ReadLint_inverse a50 unfolding checkUInt_def by simp
    then have a70:"(nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) \<in> {0..al-1}" using a60 by simp
    then have a80:"(accessStore (hash loc kv) (if (\<not>mm) then cd else (Memory st))) =  Some(MPointer l)" using a1(1) a40 by presburger
    have a90:"al > 0" using a60 a62 by simp 
    have a91:" MCon (MTArray al t) (if mm then Memory st else cd) loc" using a1 by blast
    then have defexp:"(case (accessStore (hash loc  (ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))))((if mm then Memory st else cd))) of
                                           (Some (MPointer loc2)) \<Rightarrow> 
                                                  (case t of MTArray len' arr' \<Rightarrow> (MCon t (if mm then Memory st else cd) (loc2))
                                                      | _ \<Rightarrow> False)
                                            | Some(MValue val) \<Rightarrow>  
                                                  (case t of MTValue typ \<Rightarrow> (MCon t (if mm then Memory st else cd) (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)))))
                                                      | _ \<Rightarrow> False)
                                            | _ \<Rightarrow> False
                                           )" using MCon.simps(2)[of al t _ loc] a90 a60  by simp
    then have a95:"case t of MTArray len' arr' \<Rightarrow> MCon t (if mm then Memory st else cd) l | MTValue Types \<Rightarrow> False" using a80 a64 by (auto split:if_splits )
    then obtain len' arr' where  tdef:"t = MTArray len' arr'" using a1 a70 a65 a64 a80 a90 a60 defexp by (cases t; simp)
    then have a100:"MCon t (if mm then Memory st else cd) l" using a1 a70 a65 a64 a80 a90 a60 defexp a95 by simp


    assume b99:"x # y # ys \<noteq> []"
    have b10: "\<exists>len arr.
          MTArray al t = MTArray len arr \<and>
          (case t1' of
           MTArray l' ar' \<Rightarrow>
             \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) \<and>
                 CompMemType (if mm then Memory st else cd) len arr t1' loc p
           | MTValue val \<Rightarrow>
               CompMemType (if mm then Memory st else cd) len arr t1' loc l1')"
    proof(cases ys)
      case Nil
      then have b15:"\<forall>l1' v1' t1' g1' arr.
       local.msel mm t l (y # ys) env cd st g4' = Normal ((l1', t1'), g1') \<and>
       MCon t (if mm then Memory st else cd) l \<and> TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd \<longrightarrow>
        
        (y # ys \<noteq> [] \<longrightarrow>
         (\<exists>len arr.
            t = MTArray len arr \<and>
            (case t1' of MTArray l' ar' \<Rightarrow> \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) 
                                            \<and> CompMemType (if mm then Memory st else cd) len arr t1' l p
                                            
             | MTValue val \<Rightarrow> CompMemType (if mm then Memory st else cd) len arr t1' l l1')))" 
        using 4(2)[of "((KValue kv, Value (TUInt b)))" g4' "(kv, b)" g4' kv b ] a20 a30 a40  a45 a100 a1 by (auto split:if_splits option.splits )

      have b20: "local.msel mm t l [y] env cd st g4'  = Normal ((l1', t1'), g1')" using a45 Nil a1 by simp
      then obtain kv' b' where b30:"expr y env cd st g4' = Normal (((KValue kv', Value (TUInt b')), g1'))" 
        using msel.simps(3)[of mm len' arr' l y env cd st g4'] tdef  by (auto split:result.splits stackvalue.splits type.splits types.splits if_splits)
      then have b40:"Valuetypes.less (TUInt b') (TUInt b256) kv' (ShowL\<^sub>i\<^sub>n\<^sub>t (int len')) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"        
        using msel.simps(3)[of mm len' arr' l y env cd st g4'] tdef b20 by (auto split:result.splits stackvalue.splits type.splits types.splits if_splits)

      then have b50:"l1' = hash l kv'"
        using msel.simps(3)[of mm len' arr' l y env cd st g4'] tdef b20 b30
        by (auto split:result.splits stackvalue.splits type.splits types.splits if_splits)
      then have b60:"ReadL\<^sub>i\<^sub>n\<^sub>t(kv') < int len'"
        using tdef b20 b40 less_def plift.simps(2)[of "(<)" b' b256 kv' ] Read_ShowL_id[of "int len'"] createBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def 
        by (auto split:result.splits stackvalue.splits type.splits types.splits if_splits)
      then have "(y # ys \<noteq> [] \<longrightarrow>
        (\<exists>len arr.
           t = MTArray len arr \<and>
           (case t1' of
            MTArray l' ar' \<Rightarrow>
              \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) \<and>
                  CompMemType (if mm then Memory st else cd) len arr t1' l p
            | MTValue val \<Rightarrow>
                CompMemType (if mm then Memory st else cd) len arr t1' l l1')))" 
        using b15 b20 a1 a100 Nil by simp
      then have b70:"(
            (case t1' of MTArray l' ar' \<Rightarrow> \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) 
                                                \<and> CompMemType (if mm then Memory st else cd) len' arr' t1' l p
                                                
             | MTValue val \<Rightarrow> CompMemType (if mm then Memory st else cd) len' arr' t1' l l1' 
                              ))" 
        using b99 tdef by simp
      then show ?thesis 
      proof(cases t1')
        case (MTArray x11 x12)
        then have "\<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) 
                    \<and> CompMemType (if mm then Memory st else cd) len' arr' t1' l p
                    " 
          using b70 by simp
        then obtain p where pdef:" accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) \<and> CompMemType (if mm then Memory st else cd) len' arr' t1' l p"  by auto
        have "CompMemType (if mm then Memory st else cd) al ( MTArray len' arr') t1' loc p"
          using CompMemType.simps(2)[of "(if mm then Memory st else cd)" al len' arr' t1' loc p] 
          by (metis a40 a60 a62 a64 nat_less_iff pdef)
        then show ?thesis using MTArray b70 pdef tdef 
          using CompTypeRemainsMCon mtypes.simps(5) a91 by blast
      next
        case (MTValue x2)
        then have c10:"CompMemType (if mm then Memory st else cd) len' arr' t1' l l1'" using b70 by simp
        then have noteq:"l \<noteq> l1'" 
          by (metis b50 hash_inequality)
        have "l \<noteq> loc" using b50 MConPtrsMustBeSubLocs2[of al t "(if mm then Memory st else cd)" loc] a91  
          using MConSubTypes a100 CompMemJustType.simps(2) tdef by blast
        then show ?thesis using MTValue b70 tdef using a1 a70 a65 a64 a80 a90 a60 defexp a95 noteq a40 c10
          by (metis (no_types, lifting) mtypes.simps(6) a62 nat_less_iff
              CompMemType.simps(2))
      qed
    next
      case (Cons a list)
      then have b15:"\<forall>l1' v1' t1' g1' arr.
       local.msel mm t l (y # ys) env cd st g4' = Normal ((l1', t1'), g1') \<and>
       MCon t (if mm then Memory st else cd) l \<and> TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd \<longrightarrow>
       (y # ys \<noteq> [] \<longrightarrow>(\<exists>len arr.
            t = MTArray len arr \<and>
            (case t1' of MTArray l' ar' \<Rightarrow> \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) 
                                            \<and> CompMemType (if mm then Memory st else cd) len arr t1' l p
                                            
             | MTValue val \<Rightarrow> CompMemType (if mm then Memory st else cd) len arr t1' l l1' )))" 
        using 4(2)[of "((KValue kv, Value (TUInt b)))" g4' "(kv, b)" g4' kv b ] a20 a30 a40  a45 a1 by (auto split:if_splits option.splits )
      have b20: "local.msel mm t l (y#ys) env cd st g4'  = Normal ((l1', t1'), g1')" using a45 Cons a1 by simp
      then have b30:"\<exists>len arr.
            t = MTArray len arr \<and>
            (case t1' of MTArray l' ar' \<Rightarrow> \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) 
                                            \<and> CompMemType (if mm then Memory st else cd) len arr t1' l p
                                            
             | MTValue val \<Rightarrow> CompMemType (if mm then Memory st else cd) len arr t1' l l1' )" 
        using b15 b20 a1 a100  by simp
      then show ?thesis
      proof(cases t1')
        case (MTArray x11 x12)
        then have " \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) \<and> CompMemType (if mm then Memory st else cd) al t t1' loc p" 
          using b30 a40 a62 a64 nat_less_iff 
          using a60 by fastforce
        then show ?thesis using MTArray 
          using CompTypeRemainsMCon mtypes.simps(5) a91 by blast
      next
        case (MTValue x2)
        then have "CompMemType (if mm then Memory st else cd) al t t1' loc l1'" using b30 
          using a40 a60 a62 a64 nat_less_iff by fastforce
        then show ?thesis using MTValue b30 by force
      qed
    qed
    then show "\<exists>len arr.
          MTArray al t = MTArray len arr \<and>
          (case t1' of
           MTArray l' ar' \<Rightarrow>
             \<exists>p. accessStore l1' (if mm then Memory st else cd) = Some (MPointer p) \<and>
                 CompMemType (if mm then Memory st else cd) len arr t1' loc p 
           | MTValue val \<Rightarrow>
               CompMemType (if mm then Memory st else cd) len arr t1' loc l1')" by simp
  qed
next
  case (5 tp loc vi vj vk g)
  then show ?case
  proof (intros)
    fix l2' v2' t2' g2' 
    assume a1: "local.ssel tp loc [] vi vj vk g = Normal ((l2', t2'), g2') \<and>
       SCon tp loc (Storage vk (Address vi)) \<and> TypeSafe vi (Accounts vk) (Stack vk) (Memory vk) (Storage vk) vj 
\<and> fullyInitialised vi (Accounts vk) (Stack vk)"
    assume *:"[] \<noteq> []"
    then have a10:"loc = l2'" and a20:"t2' = tp" using ssel.simps(1) by simp+
    show " CompStoType tp t2' loc l2' " using * by simp
  qed
next
  case (6 vl vm vn vo vp vq vr g)
  then show ?case using ssel.simps(2) by simp
next
  case (7 al t loc x xs env cd st g)
  show ?case
  proof(intros)
    fix l2' v2' t2' g2' 
    assume a1:"local.ssel (STArray al t) loc (x # xs) env cd st g = Normal ((l2', t2'), g2') \<and>
       SCon (STArray al t) loc (Storage st (Address env)) \<and> TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd  
      \<and>  fullyInitialised env (Accounts st) (Stack st)"
    assume b99:"x # xs \<noteq> []"   
    then obtain kv b g4' where a20: "local.expr x env cd st g = Normal ((KValue kv, Value (TUInt b)), g4')"
      and a30: "less (TUInt b) (TUInt b256) kv (ShowL\<^sub>i\<^sub>n\<^sub>t (int al)) = Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)"
      and a40:"ssel (STArray al t) loc (x # xs) env cd st g = ssel t (hash loc kv) xs env cd st g4'"
      using a1 ssel.simps(3) by (simp split: result.split_asm prod.split_asm types.split_asm type.split_asm if_split_asm stackvalue.split_asm)  

    have a50: "checkUInt b kv" using 7(1) a1 a20 by simp
    then have a60:"ReadL\<^sub>i\<^sub>n\<^sub>t(kv) < int al " using a20 a30 less_def plift.simps(2)[of "(<)" b b256 kv "(ShowL\<^sub>i\<^sub>n\<^sub>t (int al))"] Read_ShowL_id[of "(int al)"] unfolding createBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    then have a62:"0\<le>ReadL\<^sub>i\<^sub>n\<^sub>t(kv)" and a65:"(ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) = kv" using a50 checkUInt_def[of b kv] by simp+
    then have a67:"(ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))) = kv" using ShowLnat_ReadLint_inverse a50 unfolding checkUInt_def by simp
    then have a68:"nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv) < al" by (simp add: a60 a62 nat_less_iff)
    then have b10:"SCon t (hash loc kv) (Storage st (Address env)) \<and> (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) \<in> {0..al-1}"
      using a1  a65 a67 by force

    have b10:"CompStoType (STArray al t) t2' loc l2' \<and> loc \<noteq> l2'"
    proof(cases xs)
      case Nil
      then have "ssel t (hash loc kv) xs env cd st g4' = Normal(((hash loc kv), t),g2')" using ssel.simps(1) a1 a40 by simp
      then have b30:"l2' = (hash loc kv) \<and> t2' = t" using a40 a1 by simp
      then have "(\<exists>i<al. TypedStoSubpref l2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t)" using a67 a68 TypedStoSubpref_sameLoc by auto
      moreover have "(\<exists>i<al. CompStoType t t2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l2')" using a67 a68 b30 CompStoType_sameLocNdTyp by auto
      moreover have "l2' \<noteq> loc" using b30 by (simp add: hash_inequality)
      ultimately show ?thesis using TypedStoSubpref.simps(2)[of l2' loc al t ] b30 CompStoType.simps(2)[of al t t2' loc l2'] by simp

    next
      case (Cons a list) 
      have b20:"xs \<noteq> [] \<longrightarrow> CompStoType t t2'  (hash loc kv) l2'" 
        using 7(2) a1 a20 a30 a40 b10 by simp
      then have b30:"CompStoType t t2'  (hash loc kv) l2'" using Cons by simp
      have "al > 0" using a60  by (metis a62 bot_nat_0.not_eq_extremum less_nat_zero_code nat_less_iff) 
      then have "\<forall>i::nat. i\<in>{0..al - 1} \<longrightarrow> i<al" using a60 by auto
      then have b40:"(\<exists>i<al. TypedStoSubpref l2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> l2' = hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
        using a60 a65 a67 b20 b30 by (metis CompStoType_imps_TypedStoSubpref a68)

      then show ?thesis
      proof(cases t)
        case (STArray x11 x12)
        then have c1:"loc \<noteq> l2'" using b30 TypedStoSubpref.simps(2)[of l2' "(hash loc kv)" x11 x12] TypedStoSubpref_hashes 
          by (metis b40 hash_inequality)
        have "((\<exists>i<al. CompStoType t t2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l2'))" using b30 a67 a68 by auto
        moreover have "((\<exists>i<al. TypedStoSubpref l2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t))" 
          using b30 a67 a68 TypedStoSubpref_sameLoc b40 by blast
        ultimately show ?thesis using  CompStoType.simps(2)[of al t t2' loc l2'] b30 TypedStoSubpref.simps(2)[of l2' loc al t] c1 by simp 
      next
        case (STMap x21 x22)
        then have c1:"loc \<noteq> l2'" 
          using b30 TypedStoSubpref.simps(2) TypedStoSubpref_hashes by (metis b40)
        have "((\<exists>i<al. CompStoType t t2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l2'))" using b30 a67 a68 by auto
        moreover have "((\<exists>i<al. TypedStoSubpref l2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t))" 
          using b30 a67 a68 TypedStoSubpref_sameLoc b40 by blast
        ultimately show ?thesis using  CompStoType.simps(2)[of al t t2' loc l2'] b30 TypedStoSubpref.simps(2)[of l2' loc al t] c1 by simp 
      next
        case (STValue x3) 
        then have "l2' = (hash loc kv)" using b30 TypedStoSubpref.simps(1)[of l2' " (hash loc kv)" x3] by auto
        then have c1:"loc \<noteq> l2'" by (metis hash_inequality)
        have "(\<exists>i<al. CompStoType t t2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l2')" using b30 a67 a68 by auto
        moreover have "(\<exists>i<al. TypedStoSubpref l2' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t)" using b30 a67 a68 
          using TypedStoSubpref_sameLoc b40 by blast
        ultimately show ?thesis using  CompStoType.simps(2)[of al t t2' loc l2'] b30 TypedStoSubpref.simps(2)[of l2' loc al t] c1 by simp 
      qed
    qed
    show "CompStoType (STArray al t) t2' loc l2'" using b10 by auto
  qed
next
  case (8 vs t loc x xs env cd st g)
  show ?case
  proof(intros)
    fix l2' v2' t2' g2' 
    assume a1:"local.ssel (STMap vs t) loc (x # xs) env cd st g = Normal ((l2', t2'), g2') \<and>
       SCon (STMap vs t) loc (Storage st (Address env)) \<and> TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd
      \<and>  fullyInitialised env (Accounts st) (Stack st) "

    then obtain kv g4' t'' where a20: "local.expr x env cd st g = Normal ((KValue kv, Value t''), g4')"
      and a30: "comp t'' vs"
      and a40:"ssel (STMap vs t) loc (x # xs) env cd st g = ssel t (hash loc kv) xs env cd st g4'"
      using a1 ssel.simps(4) by (simp split: result.split_asm prod.split_asm types.split_asm type.split_asm if_split_asm stackvalue.split_asm)  

    then have "typeCon t'' kv" using 8(1) a1 by simp
    then have b20:"typeCon vs kv" using SameCompTypeCon[of t'' vs kv] a30  by simp 
    then have b10:"SCon t (hash loc kv) (Storage st (Address env))" using SCon.simps(3)[of vs t loc "(Storage st (Address env))"] a1 by simp

    assume "x # xs \<noteq> []"
    then have b10:"CompStoType (STMap vs t) t2' loc l2'"
    proof(cases xs)
      case Nil
      then have "ssel t (hash loc kv) xs env cd st g4' = Normal(((hash loc kv), t),g2')" using ssel.simps(1) a1 a40 by simp
      then have b30:"l2' = (hash loc kv) \<and> t2' = t" using a40 a1 by simp

      then have " (\<exists>i. typeCon vs i \<and> (TypedStoSubpref l2' (hash loc i) t \<or> l2' = hash loc i))" using b20 by auto
      then show ?thesis using TypedStoSubpref.simps(3)[of l2' loc vs t ] b30 b20 
        using CompStoType_sameLocNdTyp TypedStoSubpref_sameLoc by auto
    next
      case (Cons a list) 
      have "(xs \<noteq> [] \<longrightarrow> CompStoType t t2' (hash loc kv) l2')"  using 8(2) a1 a20 a30 a40 b10 by simp
      then have b30:"CompStoType t t2' (hash loc kv) l2'" using Cons by blast
      then show ?thesis 
      proof(cases "t2' = t")
        case True
        then show ?thesis using b20 b30 a40 a1 Cons by auto
      next
        case False
        then have " (\<exists>i. typeCon vs i \<and>  CompStoType t t2' (hash loc i) l2')"  using b20 b30 by auto
        then show ?thesis using b30 b20 using CompStoType.simps(3)[of vs t t2' loc l2'] False by auto
      qed
    qed
    show "CompStoType (STMap vs t) t2' loc l2'" using b10 by simp
  qed
next
  case (9 b x ev cd st g')
  then show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (e.INT b x) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st ) cd
                \<and>  fullyInitialised ev (Accounts st) (Stack st) "
    show " case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp'' .
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))) "
    proof -
      have a10:"t = Value (TSInt b)" using expr.simps(1) a1 by (simp split:if_split_asm)
      then have a20:"v = KValue (createSInt b x)" using expr.simps(1) a1 by (simp split:if_split_asm)
      moreover have "typeCon (TSInt b) (createSInt b x) = checkSInt (b) (createSInt b x)" by simp
      moreover have "checkSInt (b) (createSInt b x)" using checkSIntCreate by simp
      ultimately have "typeCon (TSInt b) (extractValueType v)" by (simp split:if_split_asm)
      then show ?thesis using a10 a20 by (simp split:if_split_asm)
    qed
  qed
next
  case (10 b x ev cd st g')
  then show ?case
  proof (intros)
    fix v t g
    assume a1: "local.expr (UINT b x) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st ) cd
                \<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have "v = KValue (createUInt b x)" using expr.simps(2) by (simp split:if_split_asm)
    moreover have "t = Value (TUInt b)" using a1 expr.simps(2) by (simp split:if_split_asm)
    moreover have "typeCon (TUInt b) (createUInt b x) = checkUInt (b) (createUInt b x)"  using a1 expr.simps(2) by (simp split:if_split_asm)
    moreover have "checkUInt b (createUInt b x)" using checkUIntCreate by simp
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))) " by simp
  qed
next
  case (11 ad ev cd st g')
  then show ?case
  proof (intros)
    fix v t g
    assume a1: "local.expr (ADDRESS ad) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st ) cd
                \<and> fullyInitialised ev (Accounts st) (Stack st)"
    have a10:"v = KValue (createAddress ad)" using a1 expr.simps(3) by (simp split:if_split_asm)
    then have a20:"t = Value TAddr" using a1 expr.simps(3) by (simp split:if_split_asm)
    then have "typeCon TAddr ad = checkAddress ad" by simp
    then show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      using a10 a20 unfolding checkAddress_def 
      using createAddressNoDots 
        typeCon.simps(4)[of "(createAddress ad)"] 
        extractValueType.simps(1)[of "createAddress ad"] by (simp add: checkAddress_def)
  qed
next
  case (12 ad ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (BALANCE ad) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st ) cd
                \<and> fullyInitialised ev (Accounts st) (Stack st)"
    then obtain adv where 3:"expr ad ev cd st (g' - costs\<^sub>e (BALANCE ad) ev cd st) = Normal ((KValue adv, Value TAddr), g)" using expr.simps(4) by (simp split:if_split_asm prod.split_asm result.split_asm stackvalue.split_asm type.split_asm types.split_asm)
    moreover have a5:"expr (BALANCE ad) ev cd st g' = Normal ((KValue (Bal ((Accounts st) adv)), Value (TUInt b256)), g)" using a1 expr.simps(4) 3 by (simp split:if_split_asm prod.split_asm result.split_asm stackvalue.split_asm type.split_asm types.split_asm)
    moreover have "v = KValue (Bal ((Accounts st) adv))" using a1 a5 by simp
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp'' .
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))" 
      using a1 typeSafeAccounts[of "ev" "(Accounts st)" "(Stack st)" "(Memory st)" "(Storage st)" cd] balanceTypes_def by simp
  qed
next
  case (13 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr THIS ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st ) cd
                \<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have "v = KValue (Address ev)" using expr.simps(5) by (simp split:if_split_asm)
    moreover have "t = Value TAddr" using a1 expr.simps(5) by (simp split:if_split_asm)
    moreover have "typeCon TAddr (Address ev) = checkAddress (Address ev)" using expr.simps(5) by (simp split:if_split_asm)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      unfolding checkAddress_def using a1 unfolding TypeSafe_def addressFormat_def by simp
  qed
next
  case (14 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr SENDER ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
                \<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have "v = KValue (Sender ev)" using expr.simps(6) by (simp split:if_split_asm)
    moreover have "t = Value TAddr" using a1 expr.simps(6) by (simp split:if_split_asm)
    moreover have "typeCon TAddr (Sender ev) = checkAddress (Sender ev)" using expr.simps(6) by (simp split:if_split_asm)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      unfolding checkAddress_def using a1 unfolding TypeSafe_def addressFormat_def by simp
  qed
next
  case (15 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr VALUE ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
                \<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have "t = Value (TUInt b256)" using expr.simps(7) by (simp split:if_split_asm)
    moreover have "v = KValue(Svalue ev)" using a1 expr.simps(7) by (simp split:if_split_asm)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      using a1 typeSafeSvalue[of "ev" "(Accounts st)" "(Stack st)" "(Memory st)" "(Storage st)" cd] svalueTypes_def by simp
  qed
next
  case (16 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr TRUE ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
                \<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have "t = Value TBool" using expr.simps(8) by (simp split:if_split_asm)
    moreover have "v = KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True)" using a1 expr.simps(8) by (simp split:if_split_asm)
    moreover have "typeCon TBool (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True) = checkBool (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True)" using expr.simps(8) by (simp split:if_split_asm)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      unfolding checkBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
  qed
next
  case (17 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr FALSE ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
                \<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have "t = Value TBool" using expr.simps(9) by (simp split:if_split_asm)
    moreover have "v = KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False)" using a1 expr.simps(9) by (simp split:if_split_asm)
    moreover have "typeCon TBool (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) = checkBool (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False)" using expr.simps(9) by (simp split:if_split_asm)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      unfolding checkBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
  qed
next
  case (18 x ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (NOT x) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
\<and> fullyInitialised ev (Accounts st) (Stack st)"
    moreover have 1: "assert Gas (\<lambda>g. g > costs\<^sub>e (NOT x) ev cd st) g' = Normal ((), g')" using expr.simps(10) a1 by (simp split:if_split_asm)
    moreover have 2: "modify (\<lambda>g. g - costs\<^sub>e (NOT x) ev cd st) g' = Normal ((), g' - costs\<^sub>e (NOT x) ev cd st)" using a1 by simp
    moreover obtain v'' g'' where 3:"expr x ev cd st (g' - costs\<^sub>e (NOT x) ev cd st) = Normal ((KValue v'', Value TBool), g'')" using a1 expr.simps(10) by (simp split:if_split_asm prod.split_asm result.split_asm stackvalue.split_asm type.split_asm types.split_asm)
    ultimately have a5:"v'' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<or> v'' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False" using a1 expr.simps(10) by (simp split:if_split_asm prod.split_asm result.split_asm stackvalue.split_asm type.split_asm types.split_asm)
    then consider (T) "v'' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True" |(F)  "v'' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False" by auto
    then show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
    proof(cases)
      case T
      then have a10:"expr FALSE ev cd st g'' = Normal ((v, t), g)" using 1 2 3 expr.simps(10)[of x ev cd st g'] a1 by simp
      then have "t = Value TBool" using expr.simps(9) by (simp split:if_split_asm)
      moreover have "v = KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False)" using a1 expr.simps(9) a10 by (simp split:if_split_asm)
      moreover have "typeCon TBool (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) = checkBool (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False)" using expr.simps(9) by (simp split:if_split_asm)
      ultimately show ?thesis unfolding checkBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    next
      case F
      then have a20:"expr TRUE ev cd st g'' = Normal ((v, t), g)" using 1 2 3 expr.simps(10)[of x ev cd st g'] a1 ReadShow.true_neq_false by simp
      then have "t = Value TBool" using expr.simps(8) by (simp split:if_split_asm)
      moreover have "v = KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True)" using a1 expr.simps(8) a20 by (simp split:if_split_asm)
      moreover have "typeCon TBool (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True) = checkBool (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True)" using expr.simps(8) by (simp split:if_split_asm)
      ultimately show ?thesis unfolding checkBool_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    qed
  qed
next
  case (19 e1 e2 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (PLUS e1 e2) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
\<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have a2:"lift expr add e1 e2 ev cd st (g' - costs\<^sub>e (PLUS e1 e2) ev cd st) = Normal ((v, t), g)"  using expr.simps(11) a1 by (simp split:if_split_asm)
    moreover obtain t' where  "t = Value t'" using a2 by (auto split:result.splits)
    moreover obtain v' where "v = KValue v'" using a2 by (auto split:result.splits)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      using oliftSuccess[of "(+)" e1 e2 ev cd st "(g' - costs\<^sub>e (PLUS e1 e2) ev cd st)" v' t' g] add_def a1 a2 by simp
  qed
next
  case (20 e1 e2 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (MINUS e1 e2) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
\<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have a2:"lift expr sub e1 e2 ev cd st (g' - costs\<^sub>e (MINUS e1 e2) ev cd st) = Normal ((v, t), g)"  using expr.simps(12) a1 by (simp split:if_split_asm)
    moreover obtain t' where  "t = Value t'" using a2 by (auto split:result.splits)
    moreover obtain v' where "v = KValue v'" using a2 by (auto split:result.splits)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      using oliftSuccess[of "(-)" e1 e2 ev cd st "(g' - costs\<^sub>e (MINUS e1 e2) ev cd st)" v' t' g] sub_def a2 a1 by simp
  qed
next
  case (21 e1 e2 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (LESS e1 e2) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
\<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have a2:"lift expr less e1 e2 ev cd st (g' - costs\<^sub>e (LESS e1 e2) ev cd st) = Normal ((v, t), g)"  using expr.simps(13) a1 by (simp split:if_split_asm)
    moreover obtain t' where  "t = Value t'" using a2 by (auto split:result.splits)
    moreover obtain v' where "v = KValue v'" using a2 by (auto split:result.splits)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      using pliftSuccess[of "(<)" e1 e2 ev cd st "(g' - costs\<^sub>e (LESS e1 e2) ev cd st)" v' t' g] less_def by simp
  qed
next
  case (22 e1 e2 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (EQUAL e1 e2) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
\<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have a2:"lift expr equal e1 e2 ev cd st (g' - costs\<^sub>e (EQUAL e1 e2) ev cd st) = Normal ((v, t), g)"  using expr.simps(14) a1 by (simp split:if_split_asm)
    moreover obtain t' where  "t = Value t'" using a2 by (auto split:result.splits)
    moreover obtain v' where "v = KValue v'" using a2 by (auto split:result.splits)
    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      using pliftSuccess[of "(=)" e1 e2 ev cd st "(g' - costs\<^sub>e (EQUAL e1 e2) ev cd st)" v' t' g] equal_def by simp
  qed
next
  case (23 e1 e2 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (AND e1 e2) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
\<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have a10:"lift expr vtand e1 e2 ev cd st (g' - costs\<^sub>e (AND e1 e2) ev cd st) = Normal ((v, t), g)"  using expr.simps(15) a1 by (simp split:if_split_asm)
    then obtain v1 t1 g'' where a20:"expr e1 ev cd st (g' - costs\<^sub>e (AND e1 e2) ev cd st) = Normal((KValue v1, Value t1), g'')" using lift_def by (auto split:result.split_asm stackvalue.split_asm type.split_asm)
    then obtain v2 t2 g''' where a25:"expr e2 ev cd st g'' = Normal((KValue v2, Value t2), g''')" using lift_def a10 by (auto split:result.split_asm stackvalue.split_asm type.split_asm)
    then obtain v' t' where  a30:"vtand t1 t2 v1 v2 = Some(v', t')" using a10 a20 a25 a1 lift_def by (auto split:option.split_asm)
    then have a90:"KValue v' = v" and a95:"Value t' = t" using a30 a1 a10 a20 a25  by (auto split:result.split_asm stackvalue.split_asm type.split_asm option.split_asm)
    then have a100:"(v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<or> v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) \<and> t' = TBool" using lift_def[of expr vtand e1 e2 ev cd st] expr.simps(15)[of e1 e2 ev cd st g] vtandTypeOut  a30 a1 a10 a20 a25 by simp
    then show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      using a30 vtandTypeCon[of t1 t2 v1 v2 v' t'] a90 a95 a30 a1 a10 a20 a25 a100 by auto
  qed
next
  case (24 e1 e2 ev cd st g')
  show ?case
  proof (intros)
    fix v t g
    assume a1: "expr (OR e1 e2) ev cd st g' = Normal ((v, t), g) \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
\<and> fullyInitialised ev (Accounts st) (Stack st)"
    then have a10:"lift expr vtor e1 e2 ev cd st (g' - costs\<^sub>e (OR e1 e2) ev cd st) = Normal ((v, t), g)"  using expr.simps(16) a1 by (simp split:if_split_asm)
    then obtain v1 t1 g'' where a20:"expr e1 ev cd st (g' - costs\<^sub>e (OR e1 e2) ev cd st) = Normal((KValue v1, Value t1), g'')" using lift_def by (auto split:result.split_asm stackvalue.split_asm type.split_asm)
    then obtain v2 t2 g''' where a25:"expr e2 ev cd st g'' = Normal((KValue v2, Value t2), g''')" using lift_def a10 by (auto split:result.split_asm stackvalue.split_asm type.split_asm)
    then obtain v' t' where  a30:"vtor t1 t2 v1 v2 = Some(v', t')" using a10 a20 a25 a1 lift_def by (auto split:option.split_asm)
    then have a90:"KValue v' = v" and a95:"Value t' = t" using a30 a1 a10 a20 a25 by (auto split:result.split_asm stackvalue.split_asm type.split_asm option.split_asm)
    then have a100:"(v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<or> v' = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False) \<and> t' = TBool" using lift_def[of expr vtand e1 e2 ev cd st] expr.simps(16)[of e1 e2 ev cd st g] vtorTypeOut a30 a1 a10 a20 a25 by simp
    then show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow>  MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
      using a30 checkBool_def createBool_def  ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def a90 a95 a30 a1 a10 a20 a25 a100 by auto
  qed
next
  case (25 i ev cd st g')
  show ?case
  proof(intros)
    fix v t g4' assume a1:"local.expr (LVAL i) ev cd st g' = Normal ((v, t), g4') 
                           \<and> TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd
                           \<and> fullyInitialised ev (Accounts st) (Stack st)"
    obtain v' where "assert Gas ((<) (costs\<^sub>e (LVAL i) ev cd st)) g' = Normal (v', g')"  using a1 25 expr.simps(17) extractValueType.simps by (simp split:if_split_asm option.splits prod.splits)
    moreover obtain v''  g'' where " modify (\<lambda>g. g - costs\<^sub>e (LVAL i) ev cd st) g' = Normal (v'', g'')" using a1 25 expr.simps(17) extractValueType.simps calculation by (simp split:if_split_asm option.splits prod.splits)

    moreover have "rexp i ev cd st g'' = Normal ((v, t), g4')" using a1 25 expr.simps(17) extractValueType.simps calculation by (simp split:if_split_asm option.splits prod.splits)
    ultimately show "
       (case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx)
        | Calldata struct \<Rightarrow>
            MCon struct cd (extractValueType v) \<and>
            (\<exists>xx. v = KCDptr xx) \<and>
            (\<exists>stloc tp'' p.
                (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
                accessStore stloc (Stack st) = Some (KCDptr p) \<and>
                (tp'' = struct \<and> v = KCDptr p \<or>
                 (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
        | type.Memory struct \<Rightarrow>
            MCon struct (Memory st) (extractValueType v) \<and>
            (\<exists>xx. v = KMemptr xx) \<and>
            (\<exists>stloc tp'' p.
                (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
                accessStore stloc (Stack st) = Some (KMemptr p) \<and>
                (tp'' = struct \<and> v = KMemptr p \<or>
                 (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
            SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
            (\<exists>xx. v = KStoptr xx) \<and>
            (\<exists>stloc tp''.
                (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
                (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))"
      using a1 25(1)[of v' g' v'' g'']  by auto
  qed
next
  case (26 i xe e cd st g)
  show ?case 
  proof (intros)
    fix v t g4' assume a1:"local.expr (CALL i xe) e cd st g = Normal (( v,  t), g4')  \<and> 
                            TypeSafe e (Accounts st) (Stack st) (Memory st) (Storage st) cd
                           \<and> fullyInitialised e (Accounts st) (Stack st)" 
    then obtain v' where  a10:"assert Gas ((<) (costs\<^sub>e (CALL i xe) e cd st)) g = Normal (v', g)" using expr.simps(18) a1 by (simp split:if_split_asm option.splits prod.splits)
    then obtain v'' g'' where a20:"modify (\<lambda>g. g - costs\<^sub>e (CALL i xe) e cd st) g = Normal (v'', g'')" using expr.simps(18) by (simp split:if_split_asm option.splits prod.splits)
    then obtain vb where a30:"option Err (\<lambda>_. ep $$ Contract e) g'' = Normal (vb, g'')" using a1 expr.simps(18) by (simp split:if_split_asm option.splits prod.splits)
    then obtain ct dud where a40:"vb = (ct, dud)"  using a1 expr.simps(18) by (simp split:if_split_asm option.splits prod.splits)
    then obtain vc where a50:"(case ct $$ i of None \<Rightarrow> throw Err | Some (Function (fp, True, xa)) \<Rightarrow> throw Err | Some (Function (fp, False, xa)) \<Rightarrow> return (fp, xa) | Some _ \<Rightarrow> throw Err) g'' 
                            = Normal (vc, g'')" using a1 expr.simps(18) a30 by (simp split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits)
    then obtain fp x where a60:"vc = (fp, x)"  using a1 expr.simps(18) a30 a40 by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits)

    then obtain e' where a70:"e' = ffold_init ct (emptyEnv (Address e) (Contract e) (Sender e) (Svalue e)) (fmdom ct)" 
      using a1 expr.simps(18) by (simp split:if_split_asm option.splits prod.splits)
    then have sameAddSto:"Address e = Address e'" by simp
    then have "Storage st (Address e') = Storage st (Address e)" by simp
    have a72:"(\<exists>c. Type (Accounts st (Address e')) = Some (atype.Contract c) \<and> Contract e' = c)" using a1 unfolding fullyInitialised_def a70 by simp
    have e'IsStoreloc:"\<forall>x y . (Denvalue e' $$ x = Some y \<longrightarrow> snd y = Storeloc x)" using a70 unfolding ffold_init_def using ffoldInitAllLocsStorage[of ct e e e "Svalue e" "fmdom ct"] by simp


(* Load Denvalue from e to e' Not including the Storage variables *)
    obtain ev cda k m g''' where a80:"load False fp xe e' emptyTypedStore emptyStore (Memory st) e cd st g'' = Normal ((ev, cda, k, m), g''')" 
      using expr.simps(18) a1 a10 a20 a30 a40 a50 a60 a70 by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits)
    then have a85:"(\<exists>c. Type (Accounts st (Address ev)) = Some (atype.Contract c) \<and> Contract ev = c)" using a72 
      using expressions_with_gas.msel_ssel_expr_load_rexp_gas(4) statement_with_gas_axioms statement_with_gas_def by auto
    have a90:"ep $$ Contract e = Some(ct,dud)" using a30 a40 by (simp split:option.splits)
    have a91:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
      using a1 unfolding fullyInitialised_def by simp
    have a92:"ep $$ Contract e' = Some(ct,dud)" using a30 a40 a70 by (simp split:option.splits)
    then have a95:" (\<forall>id v'. ct $$ id = Some (Var v') \<longrightarrow> ((Denvalue e') $$ id = Some (type.Storage v', Storeloc id)))" using a70 ffold_init_fmap unfolding ffold_init_def 
      by (metis emptyEnv_denvalue fmdom_notD fmdom_notI fmempty_lookup not_Some_eq)
    have sameCont:"Contract e = Contract e' \<and> Address e = Address e'" using a30 a40 
      by (simp add: a70)
    have a97:"\<forall>id. id |\<in>| fmdom (Denvalue e') \<longrightarrow> id |\<in>| fmdom ct" using ffold_init_emptyDen a70 by auto

    obtain xa ya where  a100:"TypeSafe e' (Accounts st) emptyStore (Memory st) (Storage st) emptyTypedStore 
                              \<and> (Denvalue e' $$ xa = Some ya \<longrightarrow> snd ya = Storeloc xa) 
                              \<and> (Denvalue e' $$ xa = Some ya \<longrightarrow> (\<exists>t1. ct $$ xa = Some (Var t1) \<and> fst ya = type.Storage t1))" 
      using  ffoldInitTypeSafe[of "Accounts st" "(Storage st) " " (Svalue e)" "Memory st" e ct dud "Address e" "Sender e"]  a70 ffold_init_def a1 a90 a91
      unfolding TypeSafe_def by simp
    then have a103:"TypeSafe e' (Accounts st) emptyStore (Memory st) (Storage st) emptyTypedStore" by blast

    have a101:" \<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp (Memory st) locs" by simp
    have a102: " Memory st = Memory st" by simp

    have a104:"ncpDenvalueLimit e' e emptyStore (Stack st) (Memory st)" unfolding ncpDenvalueLimit_def 
    proof intros
      fix tp' locs p i
      assume "(type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e') \<and> accessStore locs emptyStore = Some (KMemptr p) \<and> i < Toploc (Memory st) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
      then show "\<exists>tp'' loc2 p'.
          (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue e) \<and>
          accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p))" 
        unfolding accessStore_def emptyStore_def by simp
    qed
    have a105:"ncpElementsNoSubPref (Memory st) (Memory st)" using ncpElementsNoSubPref_sameMem a1 by blast
    have a106:"  ncpOMemInDMem (Memory st) (Memory st)"
      unfolding ncpOMemInDMem_def by blast
    have ncp:"ncpNewSelfPoint (Memory st) (Memory st)" unfolding ncpNewSelfPoint_def by auto
    have "(\<exists>c. Type (Accounts st (Address e')) = Some (atype.Contract c) \<and> Contract e' = c)"
      using a72 by simp
    moreover have a96:
      "(\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id)))"
      using a70 unfolding ffold_init_def 
      by (metis ffoldInit_var_storage_mapping ffoldInit_var_storage_mapping2)
    moreover have "fullyInitialised e' (Accounts st) (Stack st)" unfolding fullyInitialised_def 
      using calculation e'IsStoreloc ncp a92 denvalue.distinct(1) fmranE snd_conv 
      by (smt (verit, best) denvalue.inject(2))
      
    moreover have "fullyInitialised e' (Accounts st) emptyStore" unfolding fullyInitialised_def 
      using calculation e'IsStoreloc 
      using fullyInitialised_def by fastforce
    ultimately have a110:"TypeSafe ev (Accounts st) k m (Storage st) cda \<and>  fullyInitialised ev (Accounts st) k
        \<and> (\<forall>locs tp. MCon tp (state.Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (state.Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e k (Stack st) (state.Memory st) \<and>
        ncpOMemInDMem (state.Memory st) m \<and>
        ncpElementsNoSubPref (Memory st) m \<and> ncpNewSelfPoint (Memory st) m"
      using "26.hyps"(1)[OF a10 _ a30 a40 a50 a60 a70 ] a20 a80 a90  a101 a102 a100 a103 a104 a105 a106 a1 ncp sameAddSto by auto


    have a120:"expr x ev cda (st\<lparr>Stack := k, Memory := m\<rparr>) g''' = Normal ((v, t), g4')" using a1 expr.simps(18) a10 a20 a30 a40 a50 a60 a70 a80 a90 by (auto split:option.split_asm stackvalue.split_asm result.split_asm if_split_asm)
    then have a125:"(case v of KValue x \<Rightarrow> return (v,t)
      | KCDptr cdloc \<Rightarrow>  throw Err
      | KMemptr memloc \<Rightarrow> return (v, t)
      | KStoptr storloc \<Rightarrow> return (v, t)) g4' = Normal ((v, t), g4')" using a1 expr.simps(18) a10 a20 a30 a40 a50 a60 a70 a80 a90 by (auto split:if_splits option.splits stackvalue.splits member.splits prod.splits result.splits bool.splits)
    then have a127:"TypeSafe ev (Accounts (st\<lparr>Stack := k, Memory := m\<rparr>))
                            (Stack (st\<lparr>Stack := k, Memory := m\<rparr>)) 
                            (Memory (st\<lparr>Stack := k, Memory := m\<rparr>)) 
                            (Storage (st\<lparr>Stack := k, Memory := m\<rparr>)) cda" using a110 by simp
    then have a128:"TypeSafe ev (Accounts st) k m (Storage st) cda" by simp
    have "(\<forall>id ct dud v. ep $$ Contract ev = Some (ct, dud) \<and> ct $$ id = Some (Var v) \<longrightarrow> (\<exists>t. Denvalue ev $$ id = Some (type.Storage t, Storeloc id)))" using a80 a95 load_denval_existing_remain
      by (metis a92 fst_eqD msel_ssel_expr_load_rexp_gas(4) option.inject)
    then have "fullyInitialised ev (Accounts st) k"using a110 by simp
    then have a130:"(case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and>  (\<exists>xx. v = KValue xx)
        | Calldata struct \<Rightarrow> MCon struct cda (extractValueType v) \<and>  (\<exists>xx. v = KCDptr xx)
              \<and> (\<exists>stloc tp'' p.
                (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
                accessStore stloc (Stack (st\<lparr>Stack := k, Memory := m\<rparr>)) = Some (KCDptr p) \<and>
                (tp'' = struct \<and> v = (KCDptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cda len arr struct p (extractValueType v))))
        | type.Memory struct \<Rightarrow> MCon struct (Memory (st\<lparr>Stack := k, Memory := m\<rparr>)) (extractValueType v) \<and>  (\<exists>xx. v = KMemptr xx)
              \<and> (\<exists>stloc tp'' p.
                (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
                accessStore stloc (Stack (st\<lparr>Stack := k, Memory := m\<rparr>)) = Some (KMemptr p) \<and>
        (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Stack := k, Memory := m\<rparr>)) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage (st\<lparr>Stack := k, Memory := m\<rparr>) (Address ev)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp'' .
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> (extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))))"
      using "26.hyps"(2) a1 a10 a20 a30 a40 a50 a60 a70 a80 a85 a90 a120  a128 by simp

    then show " case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx)
       | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) \<and> (\<exists>xx. v = KCDptr xx) \<and> (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = (KCDptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow> MCon struct (Memory st) (extractValueType v) \<and> (\<exists>xx. v = KMemptr xx)
            \<and> (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address e)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))" 
    proof(cases t) 
      case (Value x1)
      then show ?thesis using a130 by simp
    next
      case (Calldata x2)

      then show ?thesis using Calldata a1 expr.simps(18)[of i xe e cd st g ] a130 a10 a20 a30 a40 a50 a60 a70 
        by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits stackvalue.splits)
    next
      case (Memory x3)
      then have "MCon x3 (state.Memory (st\<lparr>Stack := k, Memory := m\<rparr>)) (extractValueType v)"
        using a130 by simp
      then show ?thesis using Memory a1 expr.simps(18)[of i xe e cd st g ] a130 a10 a20 a30 a40 a50 a60 a70 
        by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits stackvalue.splits)
    next
      case (Storage x4)
      have sameAddress:"Address ev = Address e" using a80 a70 by (simp add:msel_ssel_expr_load_rexp_gas(4))

      have ctype_addr_unique:
        "(\<forall>c' adv'.  Type (Accounts st adv') = Some (atype.Contract c') \<and> (Address e) = adv' \<longrightarrow> c' = Contract e)" 
        using a1 a30 unfolding TypeSafe_def  
        using fullyInitialised_def by simp

      have " ep $$ Contract e' = Some (ct, dud)" using a90 a70 by simp
      then have "(\<forall>t l. (type.Storage t, Storeloc l) |\<in>| fmran (Denvalue e') \<longrightarrow> ct $$ l = Some (Var t))" 
        by (metis a96 denvalue.inject(2) e'IsStoreloc fmranE snd_conv)
      
      have a500:"SCon x4 (extractValueType v) (Storage (st\<lparr>Stack := k, Memory := m\<rparr>) (Address ev)) \<and>
        (\<exists>xx. v = KStoptr xx) \<and>
        (\<exists>stloc tp'' .
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
            (tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v)))"
        using a130 Storage by simp 
      then obtain stloc tp'' where def:"(type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
            (tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v))" 
        using a110 by auto
      then have a550:"tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v)" using def by simp
      have "(type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev)" using  def by auto
      then have "(type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e')"
      proof -
        have fi_ev: "fullyInitialised ev (Accounts st) k" using a110 by simp
        then obtain c_ev ct_ev dud_ev where
          fi_ev1: "Type (Accounts st (Address ev)) = Some (atype.Contract c_ev)"
          and fi_ev2: "Contract ev = c_ev"
          and fi_ev3: "ep $$ c_ev = Some (ct_ev, dud_ev)"
          and fi_ev4: "\<forall>id v. (ct_ev $$ id = Some (Var v)) = (Denvalue ev $$ id = Some (type.Storage v, Storeloc id))"
          and fi_ev5: "\<forall>id v loc. Denvalue ev $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
          unfolding fullyInitialised_def by blast
        from \<open>(type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev)\<close>
        obtain id where id_def: "Denvalue ev $$ id = Some (type.Storage tp'', Storeloc stloc)"
          using fmranE 
          by fast
        then have id_eq: "id = stloc" using fi_ev5 by blast
        then have den_ev_lookup: "Denvalue ev $$ stloc = Some (type.Storage tp'', Storeloc stloc)"
          using id_def by simp
        have c_ev_eq: "c_ev = Contract e"
          using ctype_addr_unique fi_ev1 sameAddress 
          by simp
        then have ct_ev_eq: "ct_ev = ct"
          using fi_ev3 a90 by auto
        then have ct_lookup: "ct $$ stloc = Some (Var tp'')"
          using fi_ev4 den_ev_lookup by blast
        then have den_e'_lookup: "Denvalue e' $$ stloc = Some (type.Storage tp'', Storeloc stloc)"
          using a96 by blast
        then show ?thesis by (simp add: fmranI)
      qed
        
      then have "(type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e)" using a100 a1 
          member.inject(3) a90 fmranI unfolding fullyInitialised_def 
        by (metis Pair_inject \<open>\<forall>t l. (type.Storage t, Storeloc l) |\<in>| fmran (Denvalue e') \<longrightarrow> ct $$ l = Some (Var t)\<close>
            option.inject)


      then show ?thesis using Storage a130  def a550 sameAddress by fastforce
    qed
  qed

next
  case (27 ad i xe e cd st g)
  show ?case
  proof (intros)
    fix v t g4' assume a1: "local.expr (ECALL ad i xe) e cd st g = Normal ((v, t), g4') \<and>
       TypeSafe e (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and> fullyInitialised e (Accounts st) (Stack st)"

    then obtain v' where  a10:"assert Gas ((<) (costs\<^sub>e (ECALL ad i xe) e cd st)) g = Normal (v', g)" using expr.simps(19) by (simp split:if_split_asm option.splits prod.splits)
    then obtain v'' g'' where a20:"modify (\<lambda>g. g - costs\<^sub>e (ECALL ad i xe) e cd st) g = Normal (v'', g'')" using expr.simps(19) by (simp split:if_split_asm option.splits prod.splits)
    then obtain g''' kad where a30:"expr ad e cd st g'' = Normal (kad, g''')"  using expr.simps(19) a1 by (simp split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits)
    then obtain adv g'''' where a40:"(case kad of (KValue adv, Value TAddr) \<Rightarrow> return adv | _ \<Rightarrow> throw Err) g''' = Normal (adv, g'''')" using expr.simps(19) a1 a20 
      by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits type.splits)
    then have a50:"adv \<noteq> Address e" using expr.simps(19) a1 a20 a30
      by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits type.splits)
    then obtain c ga5 where a60:"(case Type (Accounts st adv) of Some (atype.Contract c) \<Rightarrow> return c | _ \<Rightarrow> throw Err) g'''' = Normal (c, ga5)" using expr.simps(19) a1 a20 a30 a40 a50
      by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits type.splits)
    then obtain vb where a70:"option Err (\<lambda>_. ep $$ c) ga5 = Normal (vb, ga5)" 
      using a1 expr.simps(19) a20 a30 a40 a50 by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits type.splits)
    then obtain ct dud where a80:"vb = (ct, dud)"  using a1 expr.simps(19)  a20 a30 a40 a50 
      by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits type.splits)
    then obtain fp x where a90:"(case ct $$ i of Some (Function (fp, True, x)) \<Rightarrow> return (fp, x) | _ \<Rightarrow> throw Err) ga5
                            = Normal ((fp ,x), ga5)" using a1 expr.simps(19)  a20 a30 a40 a50 a60 a70
      by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits type.splits)
    then obtain e' where a100:"e' = ffold_init ct (emptyEnv adv c (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t 0)) (fmdom ct)" using a1 expr.simps(19) by (simp split:if_split_asm option.splits prod.splits)
    then obtain ev cda k m ga6 where a110:"load True fp xe e' emptyTypedStore emptyStore emptyTypedStore e cd st ga5 = Normal ((ev, cda, k, m), ga6)" 
      using expr.simps(19) a1 a10 a20 a30 a40 a50 a60 a70 a80 a90 by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits)
    have a120:"ep $$  c = Some(ct,dud)" using a80 a70 by (simp split:option.splits)

    then obtain contracte::environment where a125:"c = (Contract contracte)"
      by (metis Environment.select_convs(2))
    have c1:" safeContract (Accounts st) (Storage st)" using a1 unfolding TypeSafe_def by simp
    have c2:"balanceTypes (Accounts st)" using a1 unfolding TypeSafe_def by simp   
    then have "typeCon (TUInt b256) (ShowL\<^sub>n\<^sub>a\<^sub>t 0)" 
      using checkUInt_def[of b256 "STR ''0''"] by Solidity_Symbex.solidity_symbex

    then have c3:"svalueTypes (ShowL\<^sub>n\<^sub>a\<^sub>t 0)" by (simp add: svalueTypes_def)
    have c15:"AddressTypes (Accounts st)" using a1 unfolding TypeSafe_def by simp 
    then have c5:"\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep" 
      unfolding AddressTypes_def using a125 a70 a120 by blast

    have c8:"lessThanTopLocs emptyTypedStore" using typedEmptyTopLocs by metis
    have c9:"subPrefixStructuralConsistency emptyTypedStore" 
      unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
    have c10:"SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def emptyTypedStore_def accessStore_def accessTypeStore_def by simp
    have c11:"addressFormat adv" using c5 a60 a120 by (simp split:option.splits atype.splits)
    have c12: "addressFormat (Address e)" using a1 unfolding TypeSafe_def by simp
    have c13:"Type (Accounts st adv) = Some (atype.Contract (Contract contracte))"
      using a60 a125 by (auto split:option.splits atype.splits)
    have a128:"TypeSafe e' (Accounts st) emptyStore emptyTypedStore (Storage st) emptyTypedStore"
      using  a100 a125 a120 
      unfolding ffold_init_def 
      using ffoldInitTypeSafe[OF c1 c2 c3 c8 _ c11 c12 c15 c9 c10 c13]  by metis

    have a129:"(\<forall>t l p.  (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
      using c5 c3 a1 a120 a125 a100 unfolding fullyInitialised_def by metis
    obtain xa ya where "(Denvalue e' $$ xa = Some ya \<longrightarrow> snd ya = Storeloc xa)
          \<and> (Denvalue e' $$ xa = Some ya \<longrightarrow> (\<exists>t1. ct $$ xa = Some (Var t1) \<and> fst ya = type.Storage t1))"
      using a100 by (metis(full_types) denvalue.distinct(1) option.inject snd_conv)
    then have a130:"TypeSafe e' (Accounts st) emptyStore emptyTypedStore (Storage st) emptyTypedStore
\<and> (\<forall>t l p.  (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))
\<and> (Denvalue e' $$ xa = Some ya \<longrightarrow> snd ya = Storeloc xa)
          \<and> (Denvalue e' $$ xa = Some ya \<longrightarrow> (\<exists>t1. ct $$ xa = Some (Var t1) \<and> fst ya = type.Storage t1))"
      using a128 a129 by simp
    have ttt:"(\<exists>c ct dud.
      Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
      environment.Contract e = c \<and>
      ep $$ c = Some (ct, dud) \<and>
      (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
      (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
      (\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)))" 
      using a1 unfolding fullyInitialised_def 
      using c5 by force

    have "Contract ev = Contract e'" using a110 
      by (simp add: msel_ssel_expr_load_rexp_gas(4))
    then have "Contract ev = c" using a100 by simp

    have h1:"(\<exists>c. Type (Accounts (st\<lparr>Stack := k, Memory := m\<rparr>) (Address ev)) = Some (atype.Contract c) \<and> Contract ev = c)"
    proof -
      have load_same: "Address ev = Address e' \<and> Contract ev = Contract e'"
        using a110 by (simp add: msel_ssel_expr_load_rexp_gas(4))
      have type_adv: "Type (Accounts st adv) = Some (atype.Contract c)"
        using a60 by (auto split: option.splits atype.splits)
      have "Type (Accounts (st\<lparr>Stack := k, Memory := m\<rparr>) (Address ev)) = Some (atype.Contract c) \<and> Contract ev = c"
        using load_same type_adv a100 by simp
      then show ?thesis by blast
    qed
    then have a95:" (\<forall>id v'. ct $$ id = Some (Var v') \<longrightarrow> ((Denvalue e') $$ id = Some (type.Storage v', Storeloc id)))" 
      using a100 ffold_init_fmap unfolding ffold_init_def 
      by (simp add: ffold_init_fmdom)
    then have h2:"(\<forall>id ct dud v. ep $$ Contract ev = Some (ct, dud) \<and> ct $$ id = Some (Var v) \<longrightarrow> 
                    (\<exists>t. Denvalue ev $$ id = Some (type.Storage t, Storeloc id)))" 
      using a100 a110 a90 load_denval_existing_remain(4)[of True fp xe e' emptyTypedStore emptyStore emptyTypedStore e cd st ga5 ev cda k m ga6] 
      by (metis \<open>Contract ev = c\<close> a120 option.inject prod.inject)


    have adde':"Address e' = adv" 
      by (simp add: a100)
    have e'IsC:"Contract e' = c" using a100 by simp
    have "Type (Accounts st (Address e')) = Some (atype.Contract c)" using adde' a60 by (simp split:option.splits atype.splits)
    then have "(\<exists>c. Type (Accounts st (Address e')) = Some (atype.Contract c) \<and> Contract e' = c)" using adde' e'IsC by blast
    moreover have "(\<forall>id ct dud v. ep $$ Contract e' = Some (ct, dud) \<and> ct $$ id = Some (Var v) \<longrightarrow> (Denvalue e' $$ id = Some (type.Storage v, Storeloc id)))" 
      using \<open>Contract ev = c\<close> \<open>Contract ev = Contract e'\<close> a120 a95 by simp
    moreover have "(\<forall>id v loc. Denvalue e' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
    proof (intros) 
      fix id v loc
      assume h: "Denvalue e' $$ id = Some (type.Storage v, Storeloc loc)"
      have "(Denvalue e' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id)"
        using a100 a125 unfolding ffold_init_def
        using ffoldInitAllLocsStorage[
          of ct "emptyEnv adv c (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t 0)" contracte
             "emptyEnv adv c (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t 0)" "ShowL\<^sub>n\<^sub>a\<^sub>t 0" "fmdom ct"
        ]
        by simp
      then show "id = loc" using h by simp
    qed
     

    moreover have "fullyInitialised e' (Accounts st) emptyStore"
      using calculation(1,3) \<open>Contract ev = c\<close> \<open>Contract ev = Contract e'\<close> a120 a95 a100 c5 ffold_init_emptyDen_ran ttt 
      unfolding fullyInitialised_def unfolding accessStore_def emptyStore_def using ffold_init_def fmdomI fmdom_notI fmempty_lookup store.select_convs(1) 
      by metis
      
    

    ultimately have a140:"TypeSafe ev (Accounts st) k m (Storage st) cda \<and> fullyInitialised ev (Accounts st) k"
      using "27.hyps"(2)[OF a10 _ a30 a40 _ a60 a70 a80 a90 _ a100, of v'' _ fp ] a1 a20 a50 a110 a120 a130  by auto

    have a150:"expr x ev cda (st\<lparr>Stack := k, Memory := m\<rparr>) ga6 = Normal ((v, t), g4')"
      using a1 expr.simps(19)[of ad i xe e cd st g ] a10 a20 a30 a40 a50 a60 a70 a80 a90 a100 a110 a120 a130 
      by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits atype.splits type.splits stackvalue.splits)
    then have a160:"(case v of KValue x \<Rightarrow> return (v,t)
      | KCDptr cdloc \<Rightarrow> throw Err
      | KMemptr memloc \<Rightarrow> throw Err
      | KStoptr storloc \<Rightarrow> throw Err) g4' = Normal ((v, t), g4')" using a1 expr.simps(19) a10 a20 a30 a40 a50 a60 a70 a80 a90 
      by (auto split:if_splits option.splits stackvalue.splits member.splits prod.splits result.splits bool.splits)

    then have "TypeSafe ev (Accounts (st\<lparr>Stack := k, Memory := m\<rparr>))
                            (Stack (st\<lparr>Stack := k, Memory := m\<rparr>)) 
                            (Memory (st\<lparr>Stack := k, Memory := m\<rparr>)) 
                            (Storage (st\<lparr>Stack := k, Memory := m\<rparr>)) cda" using a160 a140 by simp

    then have a170:"(case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and>  (\<exists>xx. v = KValue xx)
        | Calldata struct \<Rightarrow> MCon struct cda (extractValueType v) \<and>  (\<exists>xx. v = KCDptr xx)
\<and> (\<exists>stloc tp'' p.
                  (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
                  accessStore stloc (Stack (st\<lparr>Stack := k, Memory := m\<rparr>)) = Some (KCDptr p) \<and>
  (tp'' = struct \<and> v = (KCDptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cda len arr struct p (extractValueType v))))
        | type.Memory struct \<Rightarrow> MCon struct (Memory (st\<lparr>Stack := k, Memory := m\<rparr>)) (extractValueType v) \<and>  (\<exists>xx. v = KMemptr xx)
                \<and> (\<exists>stloc tp'' p.
                  (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
                  accessStore stloc (Stack (st\<lparr>Stack := k, Memory := m\<rparr>)) = Some (KMemptr p) \<and>
  (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Stack := k, Memory := m\<rparr>)) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
            SCon struct (extractValueType v) (Storage (st\<lparr>Stack := k, Memory := m\<rparr>) (Address ev)) \<and>
            (\<exists>xx. v = KStoptr xx) \<and>
            (\<exists>stloc tp'' .
                (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
                (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))"
      using "27.hyps"(3)[of v' g v'' g'' kad g''' adv g'''' _ _ c ga5 vb ga5 ct dud "(fp,x)" ga5 fp x e' "(ev, cda, k, m)" ga6 ev "(cda, k, m)" cda "(k,m)" k m ] 
        a1 a10 a20 a30 a40 a50 a60 a70 a80 a90 a100 a110 a120 a130 a140 a150 a160 h1 h2 by simp

    then show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx)
       | Calldata struct \<Rightarrow>
           MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = KMemptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address e)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> (extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))" 
    proof(cases t) 
      case (Value x1)
      then show ?thesis using a170 by simp
    next
      case (Calldata x2)
      then show ?thesis using Calldata a1 expr.simps(19)[of ad i xe e cd st g ] a10 a20 a30 a40 a50 a60 a70 a80 a90 a100 a110 a120 a130 a140 a150 a160 a170
        by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits atype.splits type.splits stackvalue.splits)
    next
      case (Memory x3)
      then show ?thesis using Memory a1 expr.simps(18)[of i xe e cd st g ]a10 a20 a30 a40 a50 a60 a70 a80 a90 a100 a110 a120 a130 a140 a150 a160 a170
        by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits atype.splits type.splits stackvalue.splits)
    next
      case (Storage x4)
      then show ?thesis using a1 expr.simps(18)[of i xe e cd st g ]a10 a20 a30 a40 a50 a60 a70 a80 a90 a100 a110 a120 a130 a140 a150 a160 a170
        by (auto split:if_split_asm option.splits prod.splits member.splits result.split_asm bool.splits atype.splits type.splits stackvalue.splits)
    qed

  qed

next
  case (28 cp i\<^sub>p t\<^sub>p pl ex el e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g)
  show ?case
  proof(intros)
    fix ev cda k m g' loc t ls tp locs id' v''
    assume "load cp ((i\<^sub>p, t\<^sub>p) # pl) (ex # el) e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g = Normal ((ev, cda, k, m), g') \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem' locs) \<and>
        Toploc (Memory st) \<le> Toploc mem' \<and>
        ncpDenvalueLimit e\<^sub>v' e\<^sub>v sck' (Stack st) (Memory st)  \<and>
        ncpOMemInDMem (Memory st) mem' \<and> ncpElementsNoSubPref (Memory st) mem' \<and> ncpNewSelfPoint (Memory st) mem' \<and> Address e\<^sub>v = Address e\<^sub>v'
        ) \<and>
       TypeSafe e\<^sub>v (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and>
       TypeSafe e\<^sub>v' (Accounts st) sck' mem' (Storage st) cd' \<and>
       fullyInitialised e\<^sub>v (Accounts st) (Stack st) \<and> fullyInitialised e\<^sub>v' (Accounts st) sck'"
    then have as1: "local.load cp ((i\<^sub>p, t\<^sub>p) # pl) (ex # el) e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g = Normal ((ev, cda, k, m), g')" 
      and as2:"(\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem' locs) \<and> Toploc (Memory st) \<le> Toploc mem' \<and>
        ncpDenvalueLimit e\<^sub>v' e\<^sub>v sck' (Stack st) (Memory st) \<and> ncpOMemInDMem (Memory st) mem' 
        \<and> ncpElementsNoSubPref (Memory st) mem' 
        \<and> ncpNewSelfPoint (Memory st) mem' \<and> Address e\<^sub>v = Address e\<^sub>v')" 
      and as6:"TypeSafe e\<^sub>v (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and> TypeSafe e\<^sub>v' (Accounts st) sck' mem' (Storage st) cd'" 
      and as7:"fullyInitialised e\<^sub>v (Accounts st) (Stack st)"
      and as8:"fullyInitialised e\<^sub>v' (Accounts st) sck'"by blast+
    then have a2:"TypeSafe e\<^sub>v (Accounts st) (Stack st) (Memory st) (Storage st) cd"  by blast
    then obtain x g4' where a7:"expr ex e\<^sub>v cd st g = Normal (x, g4')" 
      using as1 load.simps(1)[of cp i\<^sub>p t\<^sub>p  pl ex  el e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g] 
      by (simp split:if_splits type.splits result.splits prod.splits option.splits)
    then have  a8:"\<exists>v t. expr ex e\<^sub>v cd st g = Normal ((v, t), g4')" using as1 by simp
    then obtain v t where a10:"expr ex e\<^sub>v cd st g = Normal ((v, t), g4')"  
      using as1 load.simps(1)[of cp i\<^sub>p t\<^sub>p  pl ex  el e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g] 
      by (auto split: result.splits prod.splits option.splits)
    then obtain c m' k' e where a15:"decl i\<^sub>p t\<^sub>p (Some (v,t)) cp cd (Memory st)  (Storage st (Address e\<^sub>v)) (cd', mem',  sck', e\<^sub>v') = Some (c, m', k', e)"
      using as1 load.simps(1) by (auto split:if_splits type.splits result.splits prod.splits option.splits)
    have sameAddDecl:"Address e\<^sub>v' = Address e" using decl_env a15 by simp

    have a18: "(if \<not>cp then (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem' locs) else True)" using as1 as2 by simp
    then have a20:"load cp pl el e c k' m' e\<^sub>v cd st g4' = Normal ((ev, cda, k, m), g')"  
      using as1 load.simps(1)[of cp i\<^sub>p t\<^sub>p  pl ex  el e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g] a10 a15 
      by (simp split:type.splits if_splits option.splits)

    have adds:"Address e = Address e\<^sub>v'" using a15 
      by (simp add: decl_env)
    moreover have sameCon:"Contract e = Contract e\<^sub>v'" using a15 
      using decl_env by auto


    have none:"Denvalue e\<^sub>v' $$ i\<^sub>p = None" using as1 unfolding load.simps by (auto split:option.splits type.splits)

    then have cc0:"TypeSafe ev (Accounts st) k m (Storage st) cda                   
                  \<and> (\<not> cp \<longrightarrow> (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and> 
                                Toploc (Memory st) \<le> Toploc m \<and> ncpElementsNoSubPref (Memory st) m 
\<and> ncpOMemInDMem (Memory st) m
\<and> ncpNewSelfPoint (Memory st) m \<and> ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st))
\<and> fullyInitialised ev (Accounts st) k
"  
    proof(cases t\<^sub>p)
      case (Value x1)
      have fiE:"fullyInitialised e (Accounts st) k'"
      proof -
        obtain ct dud c''  where c''def:"
             Type (Accounts st (Address e\<^sub>v')) = Some (atype.Contract c'') \<and>
             environment.Contract e\<^sub>v' = c'' \<and>
             ep $$ c'' = Some (ct, dud) \<and>
             (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc id))) \<and>
             (\<forall>id v loc. Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
             (\<forall>t l p.
                 (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v') \<and> accessStore l sck' = Some (KStoptr p) \<longrightarrow>
                 (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v') \<and> CompStoType t' t l' p))"
            using sameAddDecl as8 sameCon unfolding fullyInitialised_def
            by presburger
          have "Type (Accounts st (Address e)) = Some (atype.Contract c'') \<and> environment.Contract e = c'' \<and>
             ep $$ c'' = Some (ct, dud)" using c''def adds 
            by (metis adds c''def sameCon)
          moreover have "(\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id)))" 
            using c''def  a15 as8 decl_env_monotonic decl_env_not_i decl_env_storlocs_unchanged 
            by fast
          moreover have "(\<forall>t l p. (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KStoptr p) 
                          \<longrightarrow> (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
          proof intros
            fix t'' l p 
            assume cc1:"(type.Storage t'', Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KStoptr p)"
            then obtain ii where iidef:"(Denvalue e) $$ ii = Some (type.Storage t'', Stackloc l)" by blast
            
            then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t'' l' p" 
            proof(cases "ii = i\<^sub>p")
              case True
              then show ?thesis 
                by (metis Value a15 decl_env_storage iidef none type.distinct(5))
            next
              case False
              then have "(Denvalue e\<^sub>v') $$ ii = Some (type.Storage t'', Stackloc l)"
                using a15 as8 decl_env_monotonic[OF a15] decl_env_not_i[OF a15] decl_env_storlocs_unchanged[OF a15] iidef by metis
              moreover have acc:"accessStore l sck' = accessStore l k'" using Value a15 decl_StorageStack_options[OF a15 _ iidef ] cc1 by simp
              ultimately obtain t2 l2 where t2Def:"((type.Storage t2, Storeloc l2) |\<in>| fmran (Denvalue e\<^sub>v') \<and> CompStoType t2 t'' l2 p)" using cc1 c''def fmranI by metis
              then have "(type.Storage t2, Storeloc l2) |\<in>| fmran (Denvalue e)" using decl_env_monotonic[OF a15] fmranI by fast
              then show ?thesis using t2Def by metis
            qed
          qed
          moreover have "(\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)" 
            by (metis (no_types, lifting) a15 c''def decl_env_not_i decl_env_storlocs_unchanged)
          ultimately show "fullyInitialised e (Accounts st) k'" unfolding fullyInitialised_def by blast
        qed
        

      then have a22:"(case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) \<and> (\<exists>xx. v = KCDptr xx) \<and> (\<exists>stloc tp'' p.
                (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                accessStore stloc (Stack st) = Some (KCDptr p) \<and>
                (tp'' = struct \<and> v = (KCDptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
        | type.Memory struct \<Rightarrow>
            MCon struct (Memory st) (extractValueType v) \<and>
            (\<exists>xx. v = KMemptr xx) \<and>
            (\<exists>stloc tp'' p.
                (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                accessStore stloc (Stack st) = Some (KMemptr p) \<and>
                (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr. (extractValueType v) \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
            SCon struct (extractValueType v) (Storage st (Address e\<^sub>v)) \<and>
            (\<exists>xx. v = KStoptr xx) \<and>
            (\<exists>stloc tp'' .
                (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))" 
        using as6 a10 "28.hyps"(1) a18 Value none as7 as8 by simp
      then have a25:" case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) | type.Memory struct \<Rightarrow> MCon struct (Memory st) (extractValueType v)
      | type.Storage struct \<Rightarrow> SCon struct (extractValueType v) (Storage st (Address e\<^sub>v))" by (simp split:type.splits)
      have a26:"\<forall>struct.
       t = type.Memory struct \<longrightarrow>
       (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore stloc (Stack st) = Some (KMemptr p) \<and> (tp'' = struct \<and> v = (KMemptr p)
      \<or> (\<exists>len arr. (extractValueType v) \<noteq> p  \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))" using a22 by auto
      have a27:"\<forall>struct. t = Calldata struct \<longrightarrow>
      
      (\<exists>stloc tp'' p.
          (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
          accessStore stloc (Stack st) = Some (KCDptr p) \<and>
          (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))" using a22 by auto
      have a28:" \<forall>struct.
       t = type.Storage struct \<longrightarrow>
       (\<exists>stloc tp'' .
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))" using a22 by auto
      have sameAddDecl:"Address e\<^sub>v' = Address e" using decl_env a15 by simp
      have a30:"TypeSafe e (Accounts st) k' m' (Storage st) c \<and>
    (\<not> cp \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
     Toploc (Memory st) \<le> Toploc m' \<and>
     ncpDenvalueLimit e e\<^sub>v k' (Stack st) (Memory st) \<and>
     ncpOMemInDMem (Memory st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m') \<and>
    Toploc mem' \<le> Toploc m' "
        using typeSafeDecl[of e\<^sub>v st cd v t  e\<^sub>v' sck' mem' cd' i\<^sub>p t\<^sub>p cp c m' k' e]  a2 as1 as2  a15 a25 Value a18 a26 as6 a27 a28 fiE by blast
      have notSto:"\<not> (case t\<^sub>p of type.Storage x \<Rightarrow> cp | _ \<Rightarrow> False)"
        using Value by simp
      have cc1:"\<forall>ev cda k m g'.
       local.load cp pl el e c k' m' e\<^sub>v cd st g4' = Normal ((ev, cda, k, m), g') \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
        Toploc (Memory st) \<le> Toploc m' \<and>
        ncpDenvalueLimit e e\<^sub>v k' (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m'\<and> Address e\<^sub>v = Address e) \<and>
       TypeSafe e\<^sub>v (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and>
       TypeSafe e (Accounts st) k' m' (Storage st) c \<and> fullyInitialised e\<^sub>v (Accounts st) (Stack st) \<and> fullyInitialised e (Accounts st) k' \<longrightarrow>
       TypeSafe ev (Accounts st) k m (Storage st) cda \<and>
      fullyInitialised ev (Accounts st) k \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m \<and> ncpElementsNoSubPref (Memory st) m \<and> ncpNewSelfPoint (Memory st) m)"   
        using "28.hyps"(2)[OF notSto none a10 _, of v t _ _ c _ m' _ k' e] as1 a15 Value a2  as2  as6 as7 as8 by force
      then have cc2:"TypeSafe ev (Accounts st) k m (Storage st) cda \<and>       
       fullyInitialised ev (Accounts st) k \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m \<and> ncpElementsNoSubPref (Memory st) m \<and> ncpNewSelfPoint (Memory st) m)"
        using a20 a2 as1 as2 a30 as7 as8 fiE sameAddDecl by simp

      moreover have "TypeSafe ev (Accounts st) k m (Storage st ) cda" using cc2 by simp

      ultimately show " TypeSafe ev (Accounts st) k m (Storage st) cda \<and>
          (\<not> cp \<longrightarrow>
           (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
           Toploc (Memory st) \<le> Toploc m \<and>
           ncpElementsNoSubPref (Memory st) m \<and>
           ncpOMemInDMem (Memory st) m \<and> ncpNewSelfPoint (Memory st) m \<and> ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st)) \<and>
          fullyInitialised ev (Accounts st) k" 
        using fmsubset_alt_def cc2 fmsubset_pred by meson
    next
      case (Calldata x2)
      have fiE:"fullyInitialised e (Accounts st) k'" proof -
        obtain ct dud c''  where c''def:"
             Type (Accounts st (Address e\<^sub>v')) = Some (atype.Contract c'') \<and>
             environment.Contract e\<^sub>v' = c'' \<and>
             ep $$ c'' = Some (ct, dud) \<and>
             (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc id))) \<and>
             (\<forall>id v loc. Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
             (\<forall>t l p.
                 (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v') \<and> accessStore l sck' = Some (KStoptr p) \<longrightarrow>
                 (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v') \<and> CompStoType t' t l' p))"
            using sameAddDecl as8 sameCon unfolding fullyInitialised_def
            by presburger
          have "Type (Accounts st (Address e)) = Some (atype.Contract c'') \<and> environment.Contract e = c'' \<and>
             ep $$ c'' = Some (ct, dud)" using c''def adds 
            by (metis adds c''def sameCon)
          moreover have "(\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id)))" 
            using c''def  a15 as8 decl_env_monotonic decl_env_not_i decl_env_storlocs_unchanged 
            by fast
          moreover have "(\<forall>t l p. (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KStoptr p) 
                          \<longrightarrow> (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
          proof intros
            fix t'' l p 
            assume cc1:"(type.Storage t'', Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KStoptr p)"
            then obtain ii where iidef:"(Denvalue e) $$ ii = Some (type.Storage t'', Stackloc l)" by blast
            
            then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t'' l' p" 
            proof(cases "ii = i\<^sub>p")
              case True
              then show ?thesis using a15 decl_env_storage iidef none type.distinct(7) Calldata by fastforce
            next
              case False
              then have "(Denvalue e\<^sub>v') $$ ii = Some (type.Storage t'', Stackloc l)"
                using a15 as8 decl_env_monotonic[OF a15] decl_env_not_i[OF a15] decl_env_storlocs_unchanged[OF a15] iidef by metis
              moreover have acc:"accessStore l sck' = accessStore l k'" using Calldata a15 decl_StorageStack_options[OF a15 _ iidef ] cc1 by simp
              ultimately obtain t2 l2 where t2Def:"((type.Storage t2, Storeloc l2) |\<in>| fmran (Denvalue e\<^sub>v') \<and> CompStoType t2 t'' l2 p)" using cc1 c''def fmranI by metis
              then have "(type.Storage t2, Storeloc l2) |\<in>| fmran (Denvalue e)" using decl_env_monotonic[OF a15] fmranI by fast
              then show ?thesis using t2Def by metis
            qed
          qed
          moreover have "(\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)" 
            by (metis (no_types, lifting) a15 c''def decl_env_not_i decl_env_storlocs_unchanged)
          ultimately show "fullyInitialised e (Accounts st) k'" unfolding fullyInitialised_def by blast
        qed
      then have a22:"(case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) \<and> (\<exists>xx. v = KCDptr xx) \<and>
            (\<exists>stloc tp'' p.
                (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                accessStore stloc (Stack st) = Some (KCDptr p) \<and>
                (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
        | type.Memory struct \<Rightarrow>
            MCon struct (Memory st) (extractValueType v) \<and>
            (\<exists>xx. v = KMemptr xx) \<and>
            (\<exists>stloc tp'' p.
                (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                accessStore stloc (Stack st) = Some (KMemptr p) \<and>
                (tp'' = struct \<and> v = KMemptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
            SCon struct (extractValueType v) (Storage st (Address e\<^sub>v)) \<and>
            (\<exists>xx. v = KStoptr xx) \<and>
            (\<exists>stloc tp''.
                (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))" 
        using as6 a10 "28.hyps"(1) a18 Calldata as7 as8 none by simp
      then have a25:" case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) | type.Memory struct \<Rightarrow> MCon struct (Memory st) (extractValueType v)
      | type.Storage struct \<Rightarrow> SCon struct (extractValueType v) (Storage st (Address e\<^sub>v))" by (simp split:type.splits)
      have a26:"\<forall>struct.
       t = type.Memory struct \<longrightarrow>
       (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore stloc (Stack st) = Some (KMemptr p) \<and> (tp'' = struct \<and> v = (KMemptr p)
      \<or> (\<exists>len arr.  extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))" using a22 by auto
      have a27:"\<forall>struct. t = Calldata struct \<longrightarrow>
      
      (\<exists>stloc tp'' p.
          (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
          accessStore stloc (Stack st) = Some (KCDptr p) \<and>
          (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))" using a22 by auto

      have a28:" \<forall>struct.
       t = type.Storage struct \<longrightarrow>
       (\<exists>stloc tp''.
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))" using a22 by auto
      have a30:"TypeSafe e (Accounts st) k' m' (Storage st) c \<and>
    (\<not> cp \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
     Toploc (Memory st) \<le> Toploc m' \<and>
     ncpDenvalueLimit e e\<^sub>v k' (Stack st) (Memory st) \<and>
     ncpOMemInDMem (Memory st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m') \<and>
    Toploc mem' \<le> Toploc m'"
        using typeSafeDecl[of e\<^sub>v st cd v t  e\<^sub>v' sck' mem' cd' i\<^sub>p t\<^sub>p cp c m' k' e] a2 as1 as2  a15 a25 Calldata a18 a26 as6  a27 a28 by blast
      have notSto:"\<not> (case t\<^sub>p of type.Storage x \<Rightarrow> cp | _ \<Rightarrow> False)"
        using Calldata by simp
      
      have cc1:"\<forall>ev cda k m g'.
       local.load cp pl el e c k' m' e\<^sub>v cd st g4' = Normal ((ev, cda, k, m), g') \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
        Toploc (Memory st) \<le> Toploc m' \<and> ncpDenvalueLimit e e\<^sub>v k' (Stack st) (Memory st) 
        \<and> ncpOMemInDMem (Memory st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m' \<and> Address e\<^sub>v = Address e) \<and>
       TypeSafe e\<^sub>v (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and> TypeSafe e (Accounts st) k' m' (Storage st) c \<and>
        fullyInitialised e\<^sub>v (Accounts st) (Stack st) \<and> fullyInitialised e (Accounts st) k'
\<longrightarrow>
       TypeSafe ev (Accounts st) k m (Storage st) cda \<and> 
       fullyInitialised ev (Accounts st) k
\<and> (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m \<and>
        ncpElementsNoSubPref (Memory st) m \<and>
        ncpNewSelfPoint (Memory st) m)"  
        using "28.hyps"(2)[OF notSto none a10 _, of v t ] a15 Calldata a2 as1 as2  as6 as7 as8 by force
      then have cc2:"TypeSafe ev (Accounts st) k m (Storage st) cda \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m \<and> ncpElementsNoSubPref (Memory st) m \<and> ncpNewSelfPoint (Memory st) m)
\<and>
       fullyInitialised ev (Accounts st) k"
        using a20 a2 as1 a30 as7 as8  fiE sameAddDecl as2 by simp
      moreover have "TypeSafe ev (Accounts st) k m (Storage st ) cda" using a20  a2 as1 a30 cc1 
        using cc2 by blast
      ultimately show "TypeSafe ev (Accounts st) k m (Storage st ) cda 
\<and> (\<not> cp \<longrightarrow>
           (\<forall>locs tp.
               MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
           Toploc (Memory st) \<le> Toploc m \<and>
           ncpElementsNoSubPref (Memory st) m \<and>  ncpOMemInDMem (Memory st) m \<and>
           ncpNewSelfPoint (Memory st) m \<and>
           ncpDenvalueLimit ev e\<^sub>v k (Stack st)(Memory st))\<and> 
          fullyInitialised ev (Accounts st) k"
        using fmsubset_alt_def cc2 fmsubset_pred 
        by meson

    next
      case (Memory x3)
      have fiE:"fullyInitialised e (Accounts st) k'"
       proof -
        obtain ct dud c''  where c''def:"
             Type (Accounts st (Address e\<^sub>v')) = Some (atype.Contract c'') \<and>
             environment.Contract e\<^sub>v' = c'' \<and>
             ep $$ c'' = Some (ct, dud) \<and>
             (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc id))) \<and>
              (\<forall>id v loc. Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
             (\<forall>t l p.
                 (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v') \<and> accessStore l sck' = Some (KStoptr p) \<longrightarrow>
                 (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v') \<and> CompStoType t' t l' p))"
            using sameAddDecl as8 sameCon unfolding fullyInitialised_def
            by presburger
          have "Type (Accounts st (Address e)) = Some (atype.Contract c'') \<and> environment.Contract e = c'' \<and>
             ep $$ c'' = Some (ct, dud)" using c''def adds 
            by (metis adds c''def sameCon)
          moreover have "(\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id)))" 
            using c''def  a15 as8 decl_env_monotonic decl_env_not_i decl_env_storlocs_unchanged 
            by fast
          moreover have "(\<forall>t l p. (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KStoptr p) 
                          \<longrightarrow> (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
          proof intros
            fix t'' l p 
            assume cc1:"(type.Storage t'', Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KStoptr p)"
            then obtain ii where iidef:"(Denvalue e) $$ ii = Some (type.Storage t'', Stackloc l)" by blast
            
            then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t'' l' p" 
            proof(cases "ii = i\<^sub>p")
              case True
              then show ?thesis using Memory a15 decl_env_storage iidef none type.distinct(11) 
                by (metis)
            next
              case False
              then have "(Denvalue e\<^sub>v') $$ ii = Some (type.Storage t'', Stackloc l)"
                using a15 as8 decl_env_monotonic[OF a15] decl_env_not_i[OF a15] decl_env_storlocs_unchanged[OF a15] iidef by metis
              moreover have acc:"accessStore l sck' = accessStore l k'" using Memory a15 decl_StorageStack_options[OF a15 _ iidef ] cc1 by simp
              ultimately obtain t2 l2 where t2Def:"((type.Storage t2, Storeloc l2) |\<in>| fmran (Denvalue e\<^sub>v') \<and> CompStoType t2 t'' l2 p)" using cc1 c''def fmranI by metis
              then have "(type.Storage t2, Storeloc l2) |\<in>| fmran (Denvalue e)" using decl_env_monotonic[OF a15] fmranI by fast
              then show ?thesis using t2Def by metis
            qed
          qed
          moreover have "(\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)" 
            by (metis (no_types, lifting) a15 c''def decl_env_not_i decl_env_storlocs_unchanged)
          ultimately show "fullyInitialised e (Accounts st) k'" unfolding fullyInitialised_def by blast
        qed
      then have a22:"(case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx) 
        | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) \<and> (\<exists>xx. v = KCDptr xx)\<and>
            (\<exists>stloc tp'' p.
                (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                accessStore stloc (Stack st) = Some (KCDptr p) \<and>
                (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
        | type.Memory struct \<Rightarrow>
            MCon struct (Memory st) (extractValueType v) \<and>
            (\<exists>xx. v = KMemptr xx) \<and>
            (\<exists>stloc tp'' p.
                (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                accessStore stloc (Stack st) = Some (KMemptr p) \<and>
                (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr.  extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
            SCon struct (extractValueType v) (Storage st (Address e\<^sub>v)) \<and>
            (\<exists>xx. v = KStoptr xx) \<and>
            (\<exists>stloc tp''.
                (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))" 
        using as6 a10 "28.hyps"(1) a18 Memory as7 as8 none by simp
      then have a25:" case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) | type.Memory struct \<Rightarrow> MCon struct (Memory st) (extractValueType v)
      | type.Storage struct \<Rightarrow> SCon struct (extractValueType v) (Storage st (Address e\<^sub>v))" by (simp split:type.splits)
      have a26:"\<forall>struct.
       t = type.Memory struct \<longrightarrow>
       (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore stloc (Stack st) = Some (KMemptr p) \<and> (tp'' = struct \<and> v = (KMemptr p)
      \<or> (\<exists>len arr.  extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))" using a22 by auto
      have a27:"\<forall>struct. t = Calldata struct \<longrightarrow>
      (\<exists>stloc tp'' p.
          (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
          accessStore stloc (Stack st) = Some (KCDptr p) \<and>
          (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))" using a22 by auto
      have a28:" \<forall>struct.
       t = type.Storage struct \<longrightarrow>
       (\<exists>stloc tp''.
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))" 
        using a22 by auto
      have a30:" TypeSafe e (Accounts st) k' m' (Storage st) c \<and>
    (\<not> cp \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
     Toploc (Memory st) \<le> Toploc m' \<and>
     ncpDenvalueLimit e e\<^sub>v k' (Stack st) (Memory st) \<and>
     ncpOMemInDMem (Memory st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m') \<and>
    Toploc mem' \<le> Toploc m'"
        using typeSafeDecl[of e\<^sub>v st cd v t  e\<^sub>v' sck' mem' cd' i\<^sub>p t\<^sub>p cp c m' k' e] a2 as1 as2  a15 a25 Memory a18 a26 as6 a27 a28 by blast

      have notSto:"\<not> (case t\<^sub>p of type.Storage x \<Rightarrow> cp | _ \<Rightarrow> False)"
        using Memory by simp
      have cc1:"\<forall>ev cda k m g'.
       local.load cp pl el e c k' m' e\<^sub>v cd st g4' = Normal ((ev, cda, k, m), g') \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
        Toploc (Memory st) \<le> Toploc m' \<and> ncpDenvalueLimit e e\<^sub>v k' (Stack st) (Memory st) 
\<and> ncpOMemInDMem (Memory st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m'\<and> Address e\<^sub>v = Address e) \<and>
       TypeSafe e\<^sub>v (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and> TypeSafe e (Accounts st) k' m' (Storage st) c 
\<and> fullyInitialised e\<^sub>v (Accounts st) (Stack st) \<and> fullyInitialised e (Accounts st) k'  \<longrightarrow>
       TypeSafe ev (Accounts st) k m (Storage st) cda  \<and>
       fullyInitialised ev (Accounts st) k
\<and> (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m \<and>
        ncpElementsNoSubPref (Memory st) m \<and>
        ncpNewSelfPoint (Memory st) m)"  
        using "28.hyps"(2)[OF notSto none a10 _, of v t] a15 Memory a2 as1 as2  as6 as7 as8 by force
      then have cc2:"TypeSafe ev (Accounts st) k m (Storage st) cda \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m \<and> ncpElementsNoSubPref (Memory st) m \<and> ncpNewSelfPoint (Memory st) m)
\<and> fullyInitialised ev (Accounts st) k "
        using a20 a2 as1 a30 as7 as8  fiE sameAddDecl as2 by simp
      moreover have "TypeSafe ev (Accounts st) k m (Storage st ) cda" using a20  a2 as1 a30 cc1 cc2 by blast

      ultimately show "TypeSafe ev (Accounts st) k m (Storage st ) cda 
\<and> (\<not> cp \<longrightarrow>
           (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
           Toploc (Memory st) \<le> Toploc m \<and>
           ncpElementsNoSubPref (Memory st) m \<and>  ncpOMemInDMem (Memory st) m \<and>
           ncpNewSelfPoint (Memory st) m \<and>
           ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st))
\<and> fullyInitialised ev (Accounts st) k" 
        using fmsubset_alt_def cc2 fmsubset_pred by meson
    next
      case (Storage x4)
      then have ncp:"\<not>cp" using as1 load.simps by (auto split:if_splits)
      have a22:"(case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx)
        | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) \<and> (\<exists>xx. v = KCDptr xx)\<and>
            (\<exists>stloc tp'' p.
                (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                accessStore stloc (Stack st) = Some (KCDptr p) \<and>
                (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
        | type.Memory struct \<Rightarrow>
            MCon struct (Memory st) (extractValueType v) \<and>
            (\<exists>xx. v = KMemptr xx) \<and>
            (\<exists>stloc tp'' p.
                (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                accessStore stloc (Stack st) = Some (KMemptr p) \<and>
                (tp'' = struct \<and> v = (KMemptr p) \<or> (\<exists>len arr.  extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
        | type.Storage struct \<Rightarrow>
            SCon struct (extractValueType v) (Storage st (Address e\<^sub>v)) \<and>
            (\<exists>xx. v = KStoptr xx) \<and>
            (\<exists>stloc tp''.
                (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))"
        using as6 a10 "28.hyps"(1) a18 as7 as8 none ncp Storage by simp
      then have a25:" case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) | type.Memory struct \<Rightarrow> MCon struct (Memory st) (extractValueType v)
      | type.Storage struct \<Rightarrow> SCon struct (extractValueType v) (Storage st (Address e\<^sub>v))" by (simp split:type.splits)
      have a26:" \<forall>struct.
       t = Calldata struct \<longrightarrow>
       (\<exists>stloc tp'' p.
          (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
          accessStore stloc (Stack st) = Some (KCDptr p) \<and>
          (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))" using a22 by auto
      have a27:" \<forall>struct.
       t = type.Memory struct \<longrightarrow>
       (\<exists>stloc tp'' p.
          (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
          accessStore stloc (Stack st) = Some (KMemptr p) \<and>
          (tp'' = struct \<and> v = KMemptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))" using a22 by auto
      have a28:" \<forall>struct.
       t = type.Storage struct \<longrightarrow>
       (\<exists>stloc tp'' .
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))" using a22 by auto
      have tEq:"t = type.Storage x4" using Storage a15 decl_storage_tp_params
        by (metis decl_Calldata_tp_match decl_KValue_tp_match decl_Memory_tp_match type.distinct(11,5,9) type.exhaust)
      have fiE:"fullyInitialised e (Accounts st) k'"
       proof -
        obtain ct dud c''  where c''def:"
             Type (Accounts st (Address e\<^sub>v')) = Some (atype.Contract c'') \<and>
             environment.Contract e\<^sub>v' = c'' \<and>
             ep $$ c'' = Some (ct, dud) \<and>
             (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc id))) \<and>
             (\<forall>id v loc. Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
             (\<forall>t l p.
                 (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v') \<and> accessStore l sck' = Some (KStoptr p) \<longrightarrow>
                 (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v') \<and> CompStoType t' t l' p))"
            using sameAddDecl as8 sameCon unfolding fullyInitialised_def
            by presburger
          have "Type (Accounts st (Address e)) = Some (atype.Contract c'') \<and> environment.Contract e = c'' \<and>
             ep $$ c'' = Some (ct, dud)" using c''def adds
            by (metis adds c''def sameCon)
          moreover have "(\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id)))"
            using c''def  a15 as8 decl_env_monotonic decl_env_not_i decl_env_storlocs_unchanged
            by fast
          moreover have "(\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)" 
            by (metis (no_types, lifting) a15 c''def decl_env_not_i decl_env_storlocs_unchanged)
          moreover have "(\<forall>t'' l p. (type.Storage t'', Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KStoptr p)
                          \<longrightarrow> (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t'' l' p))" 
          proof intros
            fix t'' l p
            assume cc1:"(type.Storage t'', Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KStoptr p)"
            then obtain ii where iidef:"(Denvalue e) $$ ii = Some (type.Storage t'', Stackloc l)" by blast
            then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t'' l' p"
            proof(cases "ii = i\<^sub>p")
              case True
              then have iipEq:"Denvalue e $$ i\<^sub>p = Some (type.Storage t'', Stackloc l)" using iidef by simp
              obtain stloc' tp''' where stdef_fi:"
                   (type.Storage tp''', Storeloc stloc') |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                   (tp''' = x4 \<and> v = KStoptr stloc' \<or> extractValueType v \<noteq> stloc' \<and> CompStoType tp''' x4 stloc' (extractValueType v))"
                using a28 tEq by blast
              then have "(type.Storage tp''', Storeloc stloc') |\<in>| fmran (Denvalue e\<^sub>v')"
              proof -
                obtain c_ev ct_ev dud_ev where ev_fi:"
                     Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_ev) \<and>
                     environment.Contract e\<^sub>v = c_ev \<and>
                     ep $$ c_ev = Some (ct_ev, dud_ev) \<and>
                     (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
                     (\<forall>id vv. (ct_ev $$ id = Some (Var vv)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage vv, Storeloc id)))"
                  using as7 unfolding fullyInitialised_def by blast
                obtain c_ev' ct_ev' dud_ev' where ev'_fi:"
                     Type (Accounts st (Address e\<^sub>v')) = Some (atype.Contract c_ev') \<and>
                     environment.Contract e\<^sub>v' = c_ev' \<and>
                     ep $$ c_ev' = Some (ct_ev', dud_ev') \<and>
                     (\<forall>id vv. (ct_ev' $$ id = Some (Var vv)) = (Denvalue e\<^sub>v' $$ id = Some (type.Storage vv, Storeloc id)))"
                  using as8 unfolding fullyInitialised_def by blast
                have sameADD':"Address e\<^sub>v = Address e\<^sub>v'" using as2 sameAddDecl ncp by blast
                have eq_c:"c_ev = c_ev'" using ev_fi ev'_fi sameADD' by simp
                hence eq_ct:"ct_ev = ct_ev'" using ev_fi ev'_fi eq_c by (metis option.inject prod.inject)
                from stdef_fi obtain k_ev where k_def:"Denvalue e\<^sub>v $$ k_ev = Some (type.Storage tp''', Storeloc stloc')"
                  using fmlookup_ran_iff by blast
                hence "ct_ev $$ stloc' = Some (Var tp''')"
                  using ev_fi by auto
                hence "Denvalue e\<^sub>v' $$ stloc' = Some (type.Storage tp''', Storeloc stloc')"
                  using ev'_fi eq_ct by meson
                thus ?thesis using fmranI by meson
              qed
              then have inE:"(type.Storage tp''', Storeloc stloc') |\<in>| fmran (Denvalue e)"
                using decl_env_monotonic[OF a15] fmranI by fast
              have pVal:"p = extractValueType v"
              proof -
                have lEq:"l = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')"
                proof -
                  obtain tt where topDen:"Denvalue e $$ i\<^sub>p = Some (tt, Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))"
                    using decl_stack_top[OF a15 none] by blast
                  show ?thesis using iipEq topDen by simp
                qed
                from a22 tEq have vStop:"\<exists>xx. v = KStoptr xx" by simp
                then obtain xx where vDef:"v = KStoptr xx" by blast
                have a15Stop:"
                  decl i\<^sub>p (type.Storage x4) (Some (KStoptr (extractValueType v), type.Storage x4)) cp cd (Memory st)
                    (Storage st (Address e\<^sub>v)) (cd', mem', sck', e\<^sub>v') = Some (c, m', k', e)"
                  using a15 tEq Storage vDef by simp
                have topSome:"\<exists>pp. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KStoptr pp)"
                  using cc1 lEq by blast
                have topEq:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KStoptr (extractValueType v))"
                  using decl_stack_topLoc[OF a15Stop none topSome] .
                have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KStoptr p)"
                  using cc1 lEq by simp
                with topEq show ?thesis by simp
              qed
              have "t'' = x4"
              proof -
                have lEq:"l = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')"
                proof -
                  obtain tt where topDen:"Denvalue e $$ i\<^sub>p = Some (tt, Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))"
                    using decl_stack_top[OF a15 none] by blast
                  show ?thesis using iipEq topDen by simp
                qed
                have denTop:"Denvalue e $$ i\<^sub>p = Some (type.Storage t'', Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))"
                  using iipEq lEq by simp
                then obtain p0 where a3Eq:"Some (v, t) = Some (KStoptr p0, type.Storage t'')"
                  using decl_storage_tp[OF a15 none] by blast
                then have "t = type.Storage t''" by simp
                with tEq show ?thesis by simp
              qed
              then show ?thesis using pVal stdef_fi inE CompStoType_sameLocNdTyp fmranI by fastforce
            next
              case False
              then have evp':"(Denvalue e\<^sub>v') $$ ii = Some (type.Storage t'', Stackloc l)"
                using a15 decl_env_monotonic[OF a15] decl_env_not_i[OF a15] iidef by metis
              moreover have acc:"accessStore l sck' = accessStore l k'"
              proof -
                have ts':"TypeSafe e\<^sub>v' (Accounts st) sck' mem' (Storage st) cd'" using as6 by blast
                have lSome:"\<exists>sv. accessStore l sck' = Some sv"
                  using ts' typeSafeAllStacklocsExist fmranI evp' by metis
                then have lNeTop:"l \<noteq> ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')"
                  using ts' unfolding TypeSafe_def lessThanTopLocs_def LSubPrefL2_def
                  by fastforce
                show ?thesis using decl_stack_change[OF a15 lNeTop] by simp
              qed
              ultimately obtain t2 l2 where t2Def:"((type.Storage t2, Storeloc l2) |\<in>| fmran (Denvalue e\<^sub>v') \<and> CompStoType t2 t'' l2 p)" using cc1 c''def fmranI by metis
              then have "(type.Storage t2, Storeloc l2) |\<in>| fmran (Denvalue e)" using decl_env_monotonic[OF a15] fmranI by fast
              then show ?thesis using t2Def by metis
            qed
          qed
          ultimately show "fullyInitialised e (Accounts st) k'" unfolding fullyInitialised_def by blast
        qed
      have sameADD:"(Address e\<^sub>v) = (Address e\<^sub>v')" using as2 sameAddDecl ncp by blast

      from tEq obtain stloc tp'' where stdef:"
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           (tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v))"
        using a28 by blast
      then have evd:"(type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v')"
      proof -
        obtain c_ev ct_ev dud_ev where ev_fi:"
             Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_ev) \<and>
             environment.Contract e\<^sub>v = c_ev \<and>
             ep $$ c_ev = Some (ct_ev, dud_ev) \<and>
            (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
             (\<forall>id vv. (ct_ev $$ id = Some (Var vv)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage vv, Storeloc id)))"
          using as7 unfolding fullyInitialised_def by blast
        obtain c_ev' ct_ev' dud_ev' where ev'_fi:"
             Type (Accounts st (Address e\<^sub>v')) = Some (atype.Contract c_ev') \<and>
             environment.Contract e\<^sub>v' = c_ev' \<and>
             ep $$ c_ev' = Some (ct_ev', dud_ev') \<and>
             (\<forall>id v loc. Denvalue e\<^sub>v' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
             (\<forall>id vv. (ct_ev' $$ id = Some (Var vv)) = (Denvalue e\<^sub>v' $$ id = Some (type.Storage vv, Storeloc id)))"
          using as8 unfolding fullyInitialised_def by blast
        have eq_c:"c_ev = c_ev'" using ev_fi ev'_fi sameADD by simp
        hence eq_ct:"ct_ev = ct_ev'" using ev_fi ev'_fi eq_c by (metis option.inject prod.inject)
        from stdef obtain k_ev where k_def:"Denvalue e\<^sub>v $$ k_ev = Some (type.Storage tp'', Storeloc stloc)"
          using fmlookup_ran_iff by blast
        hence "ct_ev $$ stloc = Some (Var tp'')"
        proof -
          have ct_k:"ct_ev $$ k_ev = Some (Var tp'')" using ev_fi k_def by metis
          have den_k:"Denvalue e\<^sub>v $$ k_ev = Some (type.Storage tp'', Storeloc k_ev)"
            using ev_fi ct_k by auto
          have "stloc = k_ev" using k_def den_k by simp
          thus ?thesis using ct_k by simp
        qed
        hence "Denvalue e\<^sub>v' $$ stloc = Some (type.Storage tp'', Storeloc stloc)"
          using ev'_fi eq_ct by meson
        thus ?thesis using fmranI by meson
      qed

      have scon:"(\<forall>locs tp. SCon tp locs (state.Storage st (Address e\<^sub>v)) \<longrightarrow> SCon tp locs (state.Storage st (Address e\<^sub>v')))"  
        using sameADD by simp

      then have "
       (\<exists>loc tp'' p.
           (type.Storage tp'', loc) |\<in>| fmran (Denvalue e\<^sub>v') \<and>
           (case loc of
            Stackloc stloc \<Rightarrow>
              accessStore stloc sck' = Some (KStoptr p) \<and>
              (tp'' = x4 \<and> v = KStoptr p \<or> extractValueType v \<noteq> p \<and> CompStoType tp'' x4 p (extractValueType v))
            | Storeloc stloc \<Rightarrow>
                tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v)))" 
        using evd stdef by force
      
      then have a30:"TypeSafe e (Accounts st) k' m' (Storage st) c \<and>
    (\<not> cp \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
     Toploc (Memory st) \<le> Toploc m' \<and>
     ncpDenvalueLimit e e\<^sub>v k' (Stack st) (Memory st) \<and>
     ncpOMemInDMem (Memory st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m') \<and>
    Toploc mem' \<le> Toploc m'"
        using typeSafeDecl[OF a2 a25 _ a15 ] as1 Storage a18 a26 as6 a27 a28 scon 
        by (simp add:
            \<open>local.load cp ((i\<^sub>p, t\<^sub>p) # pl) (ex # el) e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g = Normal ((ev, cda, k, m), g') \<and> (\<not> cp \<longrightarrow> (\<forall>locs tp. MCon tp (state.Memory st) locs \<longrightarrow> MCon tp mem' locs) \<and> Toploc (state.Memory st) \<le> Toploc mem' \<and> ncpDenvalueLimit e\<^sub>v' e\<^sub>v sck' (Stack st) (state.Memory st) \<and> ncpOMemInDMem (state.Memory st) mem' \<and> ncpElementsNoSubPref (state.Memory st) mem' \<and> ncpNewSelfPoint (state.Memory st) mem' \<and> Address e\<^sub>v = Address e\<^sub>v') \<and> TypeSafe e\<^sub>v (Accounts st) (Stack st) (state.Memory st) (state.Storage st) cd \<and> TypeSafe e\<^sub>v' (Accounts st) sck' mem' (state.Storage st) cd' \<and> fullyInitialised e\<^sub>v (Accounts st) (Stack st) \<and> fullyInitialised e\<^sub>v' (Accounts st) sck'\<close>
            \<open>t = type.Storage x4\<close>)
                      
      have notSto:"\<not> (case t\<^sub>p of type.Storage x \<Rightarrow> cp | _ \<Rightarrow> False)"
        using Storage ncp by simp
      have cc1:"\<forall>ev cda k m g'.
       local.load cp pl el e c k' m' e\<^sub>v cd st g4' = Normal ((ev, cda, k, m), g') \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
        Toploc (Memory st) \<le> Toploc m' \<and> ncpDenvalueLimit e e\<^sub>v k' (Stack st) (Memory st) \<and> ncpOMemInDMem (Memory st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m') \<and>
       TypeSafe e\<^sub>v (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and> TypeSafe e (Accounts st) k' m' (Storage st) c \<and> Address e = Address e\<^sub>v'
\<and> fullyInitialised e\<^sub>v (Accounts st) (Stack st) \<and> fullyInitialised e (Accounts st) k' \<longrightarrow>
       TypeSafe ev (Accounts st) k m (Storage st) cda  \<and>
       fullyInitialised ev (Accounts st) k
\<and> (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m \<and>
        ncpElementsNoSubPref (Memory st) m \<and>
        ncpNewSelfPoint (Memory st) m)"
        using "28.hyps"(2)[OF notSto none a10 _, of v t ] a15 Storage a2 as1 as2  as6 as7 as8 adds by force
      then have cc2:"TypeSafe ev (Accounts st) k m (Storage st) cda \<and>
       (\<not> cp \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
        Toploc (Memory st) \<le> Toploc m \<and>
        ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) m \<and> ncpElementsNoSubPref (Memory st) m \<and> ncpNewSelfPoint (Memory st) m)
\<and> fullyInitialised ev (Accounts st) k "
        using a20 a2 as1 a30 as7 as8  fiE adds by blast
      moreover have "TypeSafe ev (Accounts st) k m (Storage st ) cda" using a20  a2 as1 a30 cc1 cc2 by blast

      ultimately show "TypeSafe ev (Accounts st) k m (Storage st ) cda
\<and> (\<not> cp \<longrightarrow>
           (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m locs) \<and>
           Toploc (Memory st) \<le> Toploc m \<and>
           ncpElementsNoSubPref (Memory st) m \<and>  ncpOMemInDMem (Memory st) m \<and>
           ncpNewSelfPoint (Memory st) m \<and>
           ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st))
\<and> fullyInitialised ev (Accounts st) k"
        using fmsubset_alt_def cc2 fmsubset_pred by meson
    qed
    then show "TypeSafe ev (Accounts st) k m (Storage st) cda" by simp
    then show "\<not> cp \<Longrightarrow> MCon tp (Memory st) locs \<Longrightarrow> MCon tp m locs" using cc0 by simp
    show "\<not> cp \<Longrightarrow> Toploc (Memory st) \<le> Toploc m" using cc0 by simp
    show "\<not> cp \<Longrightarrow> ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st)" using cc0 by simp
    show "\<not> cp \<Longrightarrow> ncpOMemInDMem (Memory st) m" using cc0 by simp
    show "\<not> cp \<Longrightarrow> ncpElementsNoSubPref (Memory st) m" using cc0 by simp
    show "\<not> cp \<Longrightarrow> ncpNewSelfPoint (Memory st) m " using cc0 by simp
    show "fullyInitialised ev (Accounts st) k" using cc0 by simp
  qed
next
  case (29 vt vu vv vw vx vy vz wa wb wc g)
  show ?case
  proof(intros)
    fix ev cd k m g' locs ls tp ct dud id' v
    assume a1: "local.load vt [] (vu # vv) vw vx vy vz wa wb wc g =
       Normal ((ev, cd, k, m), g') \<and>
       (\<not> vt \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory wc) locs \<longrightarrow> MCon tp vz locs) \<and>
        Toploc (Memory wc) \<le> Toploc vz \<and>
        ncpDenvalueLimit vw wa vy (Stack wc) (Memory wc) \<and>
        ncpOMemInDMem (Memory wc) vz \<and>
        ncpElementsNoSubPref (Memory wc) vz \<and>
        ncpNewSelfPoint (Memory wc) vz \<and> Address wa = Address vw) \<and>
       TypeSafe wa (Accounts wc) (Stack wc) (Memory wc) (Storage wc) wb \<and>
       TypeSafe vw (Accounts wc) vy vz (Storage wc) vx \<and>
       fullyInitialised wa (Accounts wc) (Stack wc) \<and> fullyInitialised vw (Accounts wc) vy"
    then show "TypeSafe ev (Accounts wc) k m (Storage wc) cd" using load.simps(2) by (auto split:if_split_asm result.splits)
    show "\<not> vt \<Longrightarrow> MCon tp (Memory wc) locs \<Longrightarrow> MCon tp m locs"  using a1 using load.simps(2) by simp
    show "\<not> vt \<Longrightarrow> Toploc (Memory wc) \<le> Toploc m"  using a1 using load.simps(2) by simp
    show "\<not> vt \<Longrightarrow> ncpDenvalueLimit ev wa k (Stack wc) (Memory wc)" using a1 using load.simps by simp
    show "\<not> vt \<Longrightarrow> ncpOMemInDMem (Memory wc) m" using a1 using load.simps by simp
    show "\<not> vt \<Longrightarrow> ncpElementsNoSubPref (Memory wc) m" using a1 using load.simps by simp
    show "\<not> vt \<Longrightarrow> ncpNewSelfPoint (Memory wc) m " using a1 using load.simps by simp
    show "fullyInitialised ev (Accounts wc) k" using a1 using load.simps(2) by simp
  qed
next
  case (30 wd we wf wg wh wi wj wk wl wm g)
  show ?case
  proof(intros)
    fix ev cd k m g' locs ls tp ct dud id' v
    assume a1: "local.load wd (we # wf) [] wg wh wi wj wk wl wm g =
       Normal ((ev, cd, k, m), g') \<and>
       (\<not> wd \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory wm) locs \<longrightarrow> MCon tp wj locs) \<and>
        Toploc (Memory wm) \<le> Toploc wj \<and>
        ncpDenvalueLimit wg wk wi (Stack wm) (Memory wm) \<and>
        ncpOMemInDMem (Memory wm) wj \<and>
        ncpElementsNoSubPref (Memory wm) wj \<and>
        ncpNewSelfPoint (Memory wm) wj\<and> Address wk = Address wg) \<and>
       TypeSafe wk (Accounts wm) (Stack wm) (Memory wm) (Storage wm) wl \<and>
       TypeSafe wg (Accounts wm) wi wj (Storage wm) wh \<and>  fullyInitialised wk (Accounts wm) (Stack wm) \<and> fullyInitialised wg (Accounts wm) wi"
    then show "TypeSafe ev (Accounts wm) k m (Storage wm) cd" using load.simps(3) by (auto split:if_split_asm result.splits)
    show "\<not> wd \<Longrightarrow> MCon tp (Memory wm) locs \<Longrightarrow> MCon tp m locs"  using a1 using load.simps(3) by simp
    show "\<not> wd \<Longrightarrow> Toploc (Memory wm) \<le> Toploc m"  using a1 using load.simps(3) by simp
    show "\<not> wd \<Longrightarrow> ncpDenvalueLimit ev wk k (Stack wm) (Memory wm)" using a1 using load.simps by simp
    show "\<not> wd \<Longrightarrow> ncpOMemInDMem (Memory wm) m" using a1 using load.simps by simp
    show "\<not> wd \<Longrightarrow> ncpElementsNoSubPref (Memory wm) m" using a1 using load.simps by simp
    show "\<not> wd \<Longrightarrow> ncpNewSelfPoint (Memory wm) m " using a1 using load.simps by simp
    show "fullyInitialised ev (Accounts wm) k" using a1 using load.simps(3) by simp
  qed
next
  case (31 wn e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g)
  show ?case
  proof(intros)
    fix ev cda k m g' locs ls tp ct dud id' v
      (* cd' = cda \<Longrightarrow> sck' = k \<Longrightarrow> mem' = m*)
    assume a1: "local.load wn [] [] e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g =
       Normal ((ev, cda, k, m), g') \<and>
       (\<not> wn \<longrightarrow>
        (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem' locs) \<and>
        Toploc (Memory st) \<le> Toploc mem' \<and>
        ncpDenvalueLimit e\<^sub>v' e\<^sub>v sck' (Stack st) (Memory st) \<and>
        ncpOMemInDMem (Memory st) mem' \<and>
        ncpElementsNoSubPref (Memory st) mem' \<and>
        ncpNewSelfPoint (Memory st) mem'\<and> Address e\<^sub>v = Address e\<^sub>v') \<and>
       TypeSafe e\<^sub>v (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and>
       TypeSafe e\<^sub>v' (Accounts st) sck' mem' (Storage st) cd' \<and>
       fullyInitialised e\<^sub>v (Accounts st) (Stack st) \<and> fullyInitialised e\<^sub>v' (Accounts st) sck'"
    then have fi1:"fullyInitialised e\<^sub>v (Accounts st) (Stack st)" and fi2:"fullyInitialised e\<^sub>v' (Accounts st) sck'" by blast+
    then show "TypeSafe ev (Accounts st) k m (Storage st) cda" using load.simps(4)[of wn e\<^sub>v' cd' sck' mem' e\<^sub>v cd st g] a1 by (auto split:if_split_asm result.splits)
    show "\<not> wn \<Longrightarrow> MCon tp (Memory st) locs \<Longrightarrow> MCon tp m locs"  using a1 using load.simps(4) by auto
    show "\<not> wn \<Longrightarrow> Toploc (Memory st) \<le> Toploc m"  using a1 using load.simps(4) by auto
    show "\<not> wn \<Longrightarrow> ncpDenvalueLimit ev e\<^sub>v k (Stack st) (Memory st)" using a1 using load.simps(4) by auto
    show "\<not> wn \<Longrightarrow> ncpOMemInDMem (Memory st) m" using a1 using load.simps(4) by auto
    show "\<not> wn \<Longrightarrow> ncpElementsNoSubPref (Memory st) m" using a1 using load.simps(4) by auto
    show "\<not> wn \<Longrightarrow> ncpNewSelfPoint (Memory st) m " using a1 using load.simps(4) by auto
    have eq:"(e\<^sub>v', cd', sck', mem') = (ev, cda, k, m)" using a1 load.simps(4) by simp
    then show "fullyInitialised ev (Accounts st) k" using fi2 by simp 
  qed
next
  case (32 i e cd st g)
  show ?case 
  proof(intros)
    fix v3' t3' g3' assume a1:"rexp (l.Id i) e cd st g = Normal (( v3',  t3'), g3') \<and> TypeSafe e (Accounts st) (Stack st) (Memory st) (Storage st) cd
                                \<and> fullyInitialised e (Accounts st) (Stack st)"
    then consider 
      (Stack) tp l where "fmlookup (Denvalue e) i = Some (tp, Stackloc l)"
    |(store) tp l where "fmlookup (Denvalue e) i = Some (tp, Storeloc l)" using rexp.simps(1) a1 
      by (simp split:option.splits prod.splits  type.splits denvalue.splits stypes.splits)
    then show "case t3' of Value typ \<Rightarrow> typeCon typ (extractValueType v3') \<and> (\<exists>xx. v3' = KValue xx)
       | Calldata struct \<Rightarrow>
           MCon struct cd (extractValueType v3') \<and>
           (\<exists>xx. v3' = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v3' = KCDptr p \<or>
                (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v3'))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v3') \<and>
           (\<exists>xx. v3' = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v3' = KMemptr p \<or>
                (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v3'))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v3') (Storage st (Address e)) \<and>
           (\<exists>xx. v3' = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
               (tp'' = struct \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v3')))"      
    proof (cases)
      case Stack
      then have a7:"(tp, Stackloc l) |\<in>| fmran (Denvalue e)" using Finite_Map.fmranI  by fast
      then consider 
        (kval) v where "accessStore l (Stack st) = Some(KValue v)"
      | (cdptr) p where "accessStore l (Stack st) = Some (KCDptr p)"
      | (memptr) p where "accessStore l (Stack st) = Some (KMemptr p)"
      | (stoptr) p where "accessStore l (Stack st) = Some (KStoptr p)"
        using rexp.simps(1) a1 Stack by (simp split:option.splits prod.splits  type.splits denvalue.splits stypes.splits stackvalue.splits )
      then show "case t3' of Value typ \<Rightarrow> typeCon typ (extractValueType v3') \<and> (\<exists>xx. v3' = KValue xx)
       | Calldata struct \<Rightarrow>
           MCon struct cd (extractValueType v3') \<and>
           (\<exists>xx. v3' = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v3' = KCDptr p \<or>
                (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v3'))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v3') \<and>
           (\<exists>xx. v3' = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v3' = KMemptr p \<or>
                (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v3'))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v3') (Storage st (Address e)) \<and>
           (\<exists>xx. v3' = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
               (tp'' = struct \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v3')))"
      proof(cases)
        case kval
        then show ?thesis using a1 Stack  a7 unfolding rexp.simps(1) TypeSafe_def typeCompat_def by (cases tp; force)
      next
        case cdptr
        then show ?thesis using a1 Stack  a7 unfolding TypeSafe_def rexp.simps(1) typeCompat_def by (cases tp; force)
      next
        case memptr
        show ?thesis 
        proof(cases tp)
          case (Value x1)
          then show ?thesis using a1  Stack a7 memptr unfolding TypeSafe_def typeCompat_def rexp.simps(1) by force
        next
          case (Calldata x2)
          then show ?thesis using a1  Stack a7 memptr unfolding TypeSafe_def rexp.simps(1) typeCompat_def by force
        next
          case (Memory x3)
          then have a10:"(v3', t3') = (KMemptr p, type.Memory x3)" using a1 Stack rexp.simps(1)[of i e cd st g ]  Stack a7 memptr 
            by (auto split:option.splits type.splits mtypes.splits stypes.splits)
          then have a20:"MCon x3 (Memory st) (extractValueType v3')" using a1 Stack a7 memptr Memory unfolding rexp.simps(1) TypeSafe_def typeCompat_def by force
          have a30:"(\<exists>xx. v3' = KMemptr xx)"  using a1 Stack rexp.simps(1) a7 memptr Memory by auto
          have a35:"extractValueType v3' = p" using a10 by simp
          then show ?thesis using a20 a30 a1 Stack a7 memptr Memory a35 unfolding rexp.simps(1) by force
        next
          case (Storage x4)
          then show ?thesis using a1 Stack a7 memptr unfolding TypeSafe_def rexp.simps(1) typeCompat_def by force
        qed
      next 
        case stoptr
        then show ?thesis   
        proof (cases tp)
          case (Value x1)
          then show ?thesis using a1 stoptr Stack a7 unfolding TypeSafe_def rexp.simps(1) typeCompat_def by force
        next
          case (Calldata x2)
          then show ?thesis using a1 stoptr Stack a7 unfolding TypeSafe_def typeCompat_def by force
        next
          case (Memory x3)
          then show ?thesis using a1 stoptr Stack a7 unfolding TypeSafe_def typeCompat_def by force
        next
          case (Storage x4)
          then have a30: "t3' = type.Storage x4"  and a40:"v3' = KStoptr p" using a1 Stack stoptr unfolding rexp.simps(1) 
            by (simp split:option.splits prod.splits  type.splits denvalue.splits stypes.splits stackvalue.splits)+
          have "SCon x4 (extractValueType v3') (Storage st (Address e)) \<and>
        (\<exists>xx. v3' = KStoptr xx) \<and>
        (\<exists>stloc tp''.
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
            (tp'' = x4 \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v3')))" 
          proof intros
            show "SCon x4 (extractValueType v3') (Storage st (Address e))" using stoptr Stack a7 Storage a30 a40 using a1 unfolding TypeSafe_def typeCompat_def by force
            show "\<exists>xx. v3' = KStoptr xx" using a40 by simp
            show "\<exists>stloc tp''.
       (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
       (tp'' = x4 \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v3'))"
              using a1 unfolding fullyInitialised_def 
              by (metis CompStoType_sameLoc_sameType Storage a40 a7 extractValueType.simps(4) stoptr)
          qed
          then show ?thesis using a1 stoptr Stack a7 Storage a30 a40 unfolding TypeSafe_def typeCompat_def by simp
        qed
      qed
    next
      case store
      then have a7:"(tp, Storeloc l) |\<in>| fmran (Denvalue e)" using Finite_Map.fmranI store by simp
      then consider 
        (stval) t where "tp = type.Storage (STValue t)"
      | (stary) t x where "tp = type.Storage (STArray x t)"        
        using rexp.simps(1) a1 store by (simp split:option.splits prod.splits  type.splits denvalue.splits stypes.splits stackvalue.splits)

      then show "case t3' of Value typ \<Rightarrow> typeCon typ (extractValueType v3') \<and> (\<exists>xx. v3' = KValue xx)
       | Calldata struct \<Rightarrow>
           MCon struct cd (extractValueType v3') \<and>
           (\<exists>xx. v3' = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v3' = KCDptr p \<or>
                (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v3'))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v3') \<and>
           (\<exists>xx. v3' = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v3' = KMemptr p \<or>
                (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v3'))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v3') (Storage st (Address e)) \<and>
           (\<exists>xx. v3' = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
               (tp'' = struct \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v3')))"
      proof(cases)
        case stval
        then have a20:"accessStorage t l (Storage st (Address e)) = (case (Storage st (Address e)) $$ l of
              Some v \<Rightarrow> v
            | None \<Rightarrow> ival t)" using accessStorage_def by auto
        then show ?thesis
        proof(cases "(Storage st (Address e)) $$ l")
          case None
          then have "accessStorage t l (Storage st (Address e)) = ival t" using a20 by simp
          then have "KValue (ival t) = v3'" using a20 stval store rexp.simps(1) None a1 by simp
          then show ?thesis using ivalTypeCon[of t "extractValueType v3'"] a20 stval store rexp.simps(1) None a1 by auto
        next
          case (Some a)
          then have a30:"SCon (STValue t) l ((Storage st) (Address e))" using a20 stval store a1 a7 unfolding TypeSafe_def typeCompat_def by force
          moreover have "SCon (STValue t) l ((Storage st) (Address e)) = (typeCon t a)" using Some SCon.simps(1) accessStorage_def by simp
          moreover have "extractValueType v3' = a"  using a20 stval store a1 a7  rexp.simps(1) Some by auto
          ultimately show ?thesis  using stval store a1 rexp.simps(1) by auto
        qed
      next
        case stary
        then have a30: "t3' = type.Storage (STArray x t)"  and "v3' = KStoptr l" using a1 store  unfolding rexp.simps(1) 
          by (simp split:option.splits prod.splits  type.splits denvalue.splits stypes.splits stackvalue.splits)+
        then have a35:"SCon (STArray x t) l ((Storage st) (Address e))" using store a1 a7 stary unfolding TypeSafe_def typeCompat_def by force
        then show ?thesis using stary store a1 a30 unfolding rexp.simps(1) 
          using a7 by auto 
      qed
    qed
  qed
next
  case (33 i r e cd st g)
  show ?case
  proof(intros)
    fix v3' t3' g3' assume a1:" local.rexp (Ref i r) e cd st g = Normal ((v3', t3'), g3') \<and>
       TypeSafe e (Accounts st) (Stack st) (Memory st) (Storage st) cd 
       \<and> fullyInitialised e (Accounts st) (Stack st) " 
    then consider
      (stloc) tp l  where "fmlookup (Denvalue e) i = Some (tp, Stackloc l)" 
    |(stoloc) tp l where "fmlookup (Denvalue e) i = Some (tp, Storeloc l)" 
      using a1 by (simp add: rexp.simps  split:option.split_asm prod.split_asm denvalue.split_asm)
    then show "case t3' of Value typ \<Rightarrow> typeCon typ (extractValueType v3') \<and> (\<exists>xx. v3' = KValue xx)
       | Calldata struct \<Rightarrow>
           MCon struct cd (extractValueType v3') \<and>
           (\<exists>xx. v3' = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v3' = KCDptr p \<or>
                (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v3'))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v3') \<and>
           (\<exists>xx. v3' = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v3' = KMemptr p \<or>
                (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v3'))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v3') (Storage st (Address e)) \<and>
           (\<exists>xx. v3' = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
               (tp'' = struct \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v3')))" 
    proof (cases)
      case stloc
      then have a7:"(tp, Stackloc l) |\<in>| fmran (Denvalue e)" using Finite_Map.fmranI[of "Denvalue e"] by simp
      then consider 
        (cdptr) l' where "accessStore l (Stack st) = Some (KCDptr l')"
      | (memptr) l' where "accessStore l (Stack st) = Some (KMemptr l')"
      | (stoptr) l' where "accessStore l (Stack st) = Some (KStoptr l')"      
        using a1 stloc by (simp add: rexp.simps  split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm)
      then show ?thesis 
      proof(cases)
        case cdptr
        then obtain t where a10:"tp = Calldata t" using stloc a1 by (simp add: rexp.simps  split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm)
        then obtain l'' t' g' where a20:"msel False t l' r e cd st g = Normal ((l'',t'), g')" 
          using stloc a1 cdptr by (simp add: rexp.simps split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm mtypes.split_asm result.split_asm)
        then have a22:"r \<noteq> []" using msel.simps by auto

        have a25:"MCon t cd l'" using a1 a7 cdptr stloc a10 a1 unfolding TypeSafe_def typeCompat_def 
          by (auto split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm stackvalue.split_asm type.split_asm )

        then show ?thesis
        proof(cases t')
          case (MTArray x11 t'')
          then obtain p where a30:"accessStore l'' cd = Some(MPointer p)" using MTArray stloc a1 cdptr a10 a20  rexp.simps(2)[of i r e cd st g ] by (auto  split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm mtypes.split_asm result.split_asm memoryvalue.split_asm)

          then have a40:"v3' = KCDptr p" using stloc a1 cdptr a10 a20 by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
          moreover have a45:"t3' = Calldata (MTArray x11 t'')" using stloc a1 cdptr a10 a20 MTArray by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
          moreover have a60:"r \<noteq> [] \<longrightarrow>
       (\<exists>len arr.
           t = MTArray len arr \<and>
           (case t' of
            MTArray l'a ar' \<Rightarrow>
              \<exists>p. accessStore l'' (if False then Memory st else cd) = Some (MPointer p) \<and>
                  CompMemType (if False then Memory st else cd) len arr t' l' p
            | MTValue val \<Rightarrow>
                CompMemType (if False then Memory st else cd) len arr t' l' l''))" 
            using "33.hyps"(1)[of "(tp, Stackloc l)" tp "Stackloc l" l "KCDptr l'" l' t g] 
              stloc cdptr a10 a20 a30 a25 a1 by simp
          then obtain len arr where a35:"t = MTArray len arr" using a25 MTArray 
            using a22 by blast
          moreover have "CompMemType cd len arr t' l' p"
            using MTArray a40 extractValueType.simps(2) calculation a22 a30 a25 a35 a60 by simp
          moreover have "MCon (MTArray x11 t'') cd (extractValueType v3')"
            using MTArray a40 extractValueType.simps(2) calculation 
            using a22 a30 a25 a35 CompTypeRemainsMCon by presburger
          moreover have a70:"(\<exists>len arr.
            t = MTArray len arr \<and> (\<exists>p. accessStore l'' (if False then Memory st else cd) = Some (MPointer p) \<and> CompMemType (if False then Memory st else cd) len arr t' l' p))" 
            using a60 a20 a22 MTArray by auto
          moreover have a80:"(Calldata t, Stackloc l) |\<in>| fmran (Denvalue e)" using a10 a7 by blast
          moreover have a90:"accessStore l (Stack st) = Some (KCDptr l')" using cdptr by blast
          moreover have a100:"extractValueType v3' = p" using a40 by auto
          ultimately have " MCon (MTArray x11 t'') cd (extractValueType v3') \<and>
        (\<exists>xx. v3' = KCDptr xx) \<and>
        (\<exists>stloc tp'' p.
            (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
            accessStore stloc (Stack st) = Some (KCDptr p) \<and>
            (tp'' = (MTArray x11 t'') \<and> v3' = KCDptr p \<or> (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x11 t'') p (extractValueType v3'))))" 
            by (metis (no_types, lifting) BothMConImpsNotCompMemType MTArray memoryvalue.inject(2) a25 a30 option.inject)
          then show ?thesis using a45 
            by (auto split:type.splits if_splits)
        next
          case (MTValue x2)
          then obtain v where a30:"accessStore l'' cd = Some(MValue v)" using MTValue stloc a1 cdptr a10 a20  rexp.simps(2)[of i r e cd st g ] by (auto  split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm mtypes.split_asm result.split_asm memoryvalue.split_asm)
          then have a40:"v3' = KValue v" using stloc a1 cdptr a10 a20 by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
          moreover have "t3' = Value x2" using stloc a1 cdptr a10 a20 MTValue by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
          moreover have a60:"MCon t' cd l''" 
            using "33.hyps"(1)[of "(tp, Stackloc l)" tp "Stackloc l" l "KCDptr l'" l' t g] 
              stloc cdptr a10 a20 a30 a25 a1 a22 a30 MTValue 
            by (metis (no_types, lifting) CompTypeRemainsMCon mtypes.simps(6) type.simps(18) return.simps)
          then have "typeCon x2 (extractValueType v3')" using extractValueType.simps(1)[of v] a40 a60 a30 MTValue by simp
          ultimately show ?thesis by simp
        qed
      next
        case memptr
        then obtain t where a10:"tp = type.Memory  t" using stloc a1 
          by (simp add: rexp.simps  split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm)
        then obtain l'' t' g' where a20:"msel True t l' r e cd st g = Normal ((l'',t'), g')" 
          using stloc a1 memptr by (simp add: rexp.simps split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm mtypes.split_asm result.split_asm)
        then have a22:"r \<noteq> []" using msel.simps by auto
        have a25:"MCon t (Memory st) l'" using a1 a7 memptr stloc a10 a1 unfolding TypeSafe_def typeCompat_def by (auto split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm stackvalue.split_asm type.split_asm )
        then show ?thesis
        proof(cases t')
          case (MTArray x11 t'')
          then obtain p where a30:"accessStore l'' (Memory st) = Some(MPointer p)" using MTArray stloc a1 memptr a10 a20  rexp.simps(2)[of i r e cd st g ] by (auto split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm mtypes.split_asm result.split_asm memoryvalue.split_asm)
          then have a40:"v3' = KMemptr p" using stloc a1 memptr a10 a20 by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
          moreover have a45:"t3' = type.Memory (MTArray x11 t'')" using stloc a1 memptr a10 a20 MTArray by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
          moreover have a60:"r \<noteq> [] \<longrightarrow>
       (\<exists>len arr.
           t = MTArray len arr \<and>
           (case t' of
            MTArray l'a ar' \<Rightarrow>
              \<exists>p. accessStore l'' (if True then Memory st else cd) = Some (MPointer p) \<and>
                  CompMemType (if True then Memory st else cd) len arr t' l' p 
            | MTValue val \<Rightarrow> CompMemType (if True then Memory st else cd) len arr t' l' l''))" 
            using "33.hyps"(2)[of "(tp, Stackloc l)" tp "Stackloc l" l "KMemptr l'" l' t g] stloc memptr a10 a20 a30 a25 a1 by simp+
          then obtain len arr where a35:"t = MTArray len arr" using a25 MTArray 
            using a22 by blast
          then have a65:"CompMemType (Memory st) len arr t' l' p "
            using MTArray a40 extractValueType.simps(2) calculation a22 a30 a60 a35 a25 by simp
          moreover have "MCon (MTArray x11 t'') (Memory st) (extractValueType v3')" 
            using MTArray a40 extractValueType.simps(2) calculation a22 a30 a60 a35 a25 a65 
            using CompTypeRemainsMCon extractValueType.simps(3) by presburger
          moreover have a70:"(\<exists>len arr.
            t = MTArray len arr \<and> (\<exists>p. accessStore l'' (if True then Memory st else cd) = Some (MPointer p) \<and> CompMemType (if True then Memory st else cd) len arr t' l' p))" 
            using a60 a20 a22 MTArray by auto
          moreover have a80:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e)" using a10 a7 by auto
          moreover have a90:"accessStore l (Stack st) = Some (KMemptr l')" using memptr by blast
          moreover have a100:"extractValueType v3' = p" using a40 by auto

          ultimately have " MCon  (MTArray x11 t'') (Memory st) (extractValueType v3') \<and>
        (\<exists>xx. v3' = KMemptr xx) \<and>
        (\<exists>stloc tp'' p.
            (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
            accessStore stloc (Stack st) = Some (KMemptr p) \<and>
            (tp'' =  (MTArray x11 t'') \<and> v3' = KMemptr p \<or> (\<exists>len arr. extractValueType v3' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr  (MTArray x11 t'') p (extractValueType v3'))))" 
            by (metis (no_types, lifting) BothMConImpsNotCompMemType MTArray memoryvalue.inject(2) a25 a30 option.inject)
          then show ?thesis using a45 by (auto split:type.splits if_splits)
        next
          case (MTValue x2)
          then obtain v where a30:"accessStore l'' (Memory st) = Some(MValue v)" 
            using MTValue stloc a1 memptr a10 a20 rexp.simps(2)[of i r e cd st g ] 
            by (auto  split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm mtypes.split_asm result.split_asm memoryvalue.split_asm)
          then have a40:"v3' = KValue v" 
            using stloc a1 memptr a10 a20 
            by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
          moreover have "t3' = Value x2" 
            using stloc a1 memptr a10 a20 MTValue 
            by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
          moreover have a60:"MCon t' (Memory st) l''" 
            using "33.hyps"(2)[of "(tp, Stackloc l)" tp "Stackloc l" l "KMemptr l'" l' t g] 
              stloc memptr a10 a20 a30 a25 a1 MTValue a22 
            by (metis (lifting) mtypes.simps(6) type.case(3) return.simps CompTypeRemainsMCon)
          then have "typeCon x2 (extractValueType v3')" using extractValueType.simps(1)[of v] a40 a60 a30 MTValue by simp
          ultimately show ?thesis by simp
        qed
      next
        case stoptr
        then obtain t where a10:"tp = type.Storage  t" using stloc a1 
          by (simp add: rexp.simps split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm)
        then obtain l'' t' g' where a20:"ssel t l' r e cd st g = Normal ((l'',t'), g')" 
          using stloc a1 stoptr 
          by (simp add: rexp.simps split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm 
              type.split_asm mtypes.split_asm result.split_asm)
        have a25:"SCon t l' (Storage st (Address e))" 
          using a1 a7 stoptr stloc a10 a1 
          unfolding TypeSafe_def typeCompat_def 
          by (auto split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm stackvalue.split_asm type.split_asm )
        then show ?thesis
        proof(cases t')
          case (STArray x11 t'')
          have ret:"(KStoptr l'', type.Storage t') = (v3', t3')" using a1 rexp.simps(2)[of i r e cd st g ] stoptr stloc a10 a20 STArray  
            by (simp split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)

          have "(t = t' \<and> v3' = KStoptr l' \<or> extractValueType v3' \<noteq> l' \<and> CompStoType t t' l' (extractValueType v3'))" 
          proof(cases "r = []")
            case True
            then have "l'' = l'" using a20 ssel.simps by simp
            moreover have "t' = t" using a20 ssel.simps(1)[of t l' e cd st g] True by simp
            ultimately show ?thesis using ret by simp
          next
            case False
            then have "CompStoType t t' l' l''" 
              using "33.hyps"(3)[of "(tp, Stackloc l)" tp "Stackloc l" l "KStoptr l'" l' t g] stloc stoptr a10 a20  a25 a1 STArray by simp
            then show ?thesis using ret 
              using CompStoType_sameLoc_sameType by force
          qed
          then have "SCon t' (l'') (Storage st (Address e))" using a25 SCon_imps_sublocs ret by fastforce
          then have g1:"SCon (STArray x11 t'') (extractValueType v3') (Storage st (Address e))" using STArray ret by auto
          have "SCon (STArray x11 t'') (extractValueType v3') (Storage st (Address e)) \<and>
        (\<exists>xx. v3' = KStoptr xx) \<and>
        (\<exists>stloc tp''.
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
            (tp'' = (STArray x11 t'') \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' (STArray x11 t'') stloc (extractValueType v3')))"

          proof intros
            show " SCon (STArray x11 t'') (extractValueType v3') (Storage st (Address e))" using g1 by simp
            show "\<exists>xx. v3' = KStoptr xx" using ret by blast
            show "\<exists>stloc tp''.
       (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
       (tp'' = STArray x11 t'' \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' (STArray x11 t'') stloc (extractValueType v3')) " 
              by (smt (verit, ccfv_threshold) CompStoType_trns STArray \<open>\<exists>xx. v3' = KStoptr xx\<close>
                  \<open>t = t' \<and> v3' = KStoptr l' \<or> extractValueType v3' \<noteq> l' \<and> CompStoType t t' l' (extractValueType v3')\<close> a1 a10 a7 extractValueType.simps(4)
                  CompStoType_sameLoc_sameType fullyInitialised_def stoptr)
          qed
          then show ?thesis using a20 a10 stoptr a7 g1 ret STArray stloc  by fastforce
        next
          case (STMap x21 x22)
          then have a40:"v3' = KStoptr l''" 
            using stloc a1 stoptr a10 a20 by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
          moreover have a50:"t3' = type.Storage (STMap x21 x22)" 
            using stloc a1 stoptr a10 a20 STMap 
            by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
          have "(t = t' \<and> v3' = KStoptr l' \<or> extractValueType v3' \<noteq> l' \<and> CompStoType t t' l' (extractValueType v3'))" 
          proof(cases "r = []")
            case True
            then have "l'' = l'" using a20 ssel.simps by simp
            moreover have "t' = t" using a20 ssel.simps(1)[of t l' e cd st g] True by simp
            ultimately show ?thesis using a40 a50 by simp
          next
            case False
            then have "CompStoType t t' l' l''" 
              using "33.hyps"(3)[of "(tp, Stackloc l)" tp "Stackloc l" l "KStoptr l'" l' t g] stloc stoptr a10 a20  a25 a1 STMap by simp
            then show ?thesis using a40 a50 using CompStoType_sameLoc_sameType by force
          qed
          then have "SCon t' (l'') (Storage st (Address e))" using a25
            using SCon_imps_sublocs calculation by fastforce 
          then have g1:"SCon (STMap x21 x22) (extractValueType v3') (Storage st (Address e))" using STMap a40 by simp

          have "SCon (STMap x21 x22) (extractValueType v3') (Storage st (Address e)) \<and>
        (\<exists>xx. v3' = KStoptr xx) \<and>
        (\<exists>stloc tp''.
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
            (tp'' = (STMap x21 x22) \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' (STMap x21 x22) stloc (extractValueType v3')))"

          proof intros
            show " SCon (STMap x21 x22) (extractValueType v3') (Storage st (Address e))" using g1 by simp
            show "\<exists>xx. v3' = KStoptr xx" using a40 by auto
            show "\<exists>stloc tp''.
       (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
       (tp'' = STMap x21 x22 \<and> v3' = KStoptr stloc \<or> extractValueType v3' \<noteq> stloc \<and> CompStoType tp'' (STMap x21 x22) stloc (extractValueType v3')) " 
              by (smt (verit, ccfv_threshold) CompStoType_trns STMap \<open>\<exists>xx. v3' = KStoptr xx\<close>
                  \<open>t = t' \<and> v3' = KStoptr l' \<or> extractValueType v3' \<noteq> l' \<and> CompStoType t t' l' (extractValueType v3')\<close> a1 a10 a7 extractValueType.simps(4)
                  CompStoType_sameLoc_sameType fullyInitialised_def stoptr)
          qed

          then show ?thesis using a20 a10 stoptr a7 g1 a40 a50 STMap stloc by force
        next
          case (STValue t'')
          then have a40:"v3' = KValue (accessStorage t'' l'' (Storage st (Address e)))" using stloc a1 stoptr a10 a20 by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
          moreover have "t3' = Value t''" using stloc a1 stoptr a10 a20 STValue by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
          moreover have a60:"SCon t (l') (Storage st (Address e))" using "33.hyps"(3) stloc stoptr a10 a20 a25 a1 STValue by simp 
          then have cc0:"(t = t' \<and> l' = l'' \<or> CompStoType t t' l' l'')" 
          proof(cases "r = []")
            case True
            then have "l'' = l'" using a20 ssel.simps by auto 
            moreover have "t' = t" using a20 ssel.simps(1)[of t l' e cd st g] True by simp
            ultimately show ?thesis using a40 by simp
          next
            case False
            then have "CompStoType t t' l' l''" 
              using  a10 a20  a25 a1 STValue "33.hyps"(3) stoptr 
              by (simp add: stloc)
            then show ?thesis using a40 using CompStoType_sameLoc_sameType by simp
          qed
          then have "typeCon t'' (accessStorage t'' l'' (Storage st (Address e)))" 
            using a60 SCon_imps_sublocs STValue SCon.simps(1) by blast
          ultimately show ?thesis by simp
        qed
      qed
    next
      case stoloc
      then have a7:"(tp, Storeloc l) |\<in>| fmran (Denvalue e)" using Finite_Map.fmranI[of "Denvalue e"] by simp

      then obtain t where a10:"tp = type.Storage  t" using stoloc a1 by (simp add: rexp.simps  split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm)
      then obtain l'' t' g' where a20:"ssel t  l r e cd st g = Normal ((l'',t'), g')" 
        using  a1 stoloc  by (simp add: rexp.simps split:option.split_asm prod.split_asm denvalue.split_asm stackvalue.split_asm type.split_asm mtypes.split_asm result.split_asm)
      have a25:"SCon t  l (Storage st (Address e))" using a1 a7  stoloc a10 a1 unfolding TypeSafe_def typeCompat_def by (auto split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm stackvalue.split_asm type.split_asm )
      then show ?thesis
      proof(cases t')
        case (STArray x11 t'')
        then have a40:"v3' = KStoptr l''" 
          using a1 stoloc a10 a20 by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
        moreover have a50:"t3' = type.Storage (STArray x11 t'')" 
          using stoloc a1  a10 a20 STArray 
          by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
        have cc0:"(t = t' \<and> v3' = KStoptr l \<or> extractValueType v3' \<noteq> l \<and> CompStoType t t' l (extractValueType v3'))" 
        proof(cases "r = []")
          case True
          then have "l'' = l" using a20 ssel.simps by simp
          moreover have "t' = t" using a20 ssel.simps(1)[of t l e cd st g] True by simp
          ultimately show ?thesis using a40 a50 by simp
        next
          case False
          then have "CompStoType t t' l l''" 
            using stoloc a10 a20  a25 a1 STArray "33.hyps"(4) by auto
          then show ?thesis using a40 a50 using CompStoType_sameLoc_sameType by force
        qed
        then have "SCon t' (l'') (Storage st (Address e))" using a25 
          by (metis SCon_imps_sublocs calculation extractValueType.simps(4)) 
        then have g1:"SCon (STArray x11 t'') (extractValueType v3') (Storage st (Address e))" using STArray a40 by simp
        then show ?thesis using a20 a10 stoloc a7 g1 a40 a50 STArray cc0 by force
      next
        case (STMap x21 x22)
        then have a40:"v3' = KStoptr l''" using stoloc a1  a10 a20 by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
        moreover have a50:"t3' = type.Storage (STMap x21 x22)" using stoloc a1  a10 a20 STMap by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
        have cc0:"(t = t' \<and> v3' = KStoptr l \<or> extractValueType v3' \<noteq> l \<and> CompStoType t t' l (extractValueType v3'))" 
        proof(cases "r = []")
          case True
          then have "l'' = l" using a20 ssel.simps by simp
          moreover have "t' = t" using a20 ssel.simps(1)[of t l e cd st g] True by simp
          ultimately show ?thesis using a40 a50 by simp
        next
          case False
          then have "CompStoType t t' l l''" 
            using stoloc a10 a20  a25 a1 STMap "33.hyps"(4) by auto
          then show ?thesis using a40 a50 using CompStoType_sameLoc_sameType by force
        qed
        then have "SCon t' (l'') (Storage st (Address e))" using a25 
          using SCon_imps_sublocs calculation by fastforce
        then have g1:"SCon (STMap x21 x22) (extractValueType v3') (Storage st (Address e))" using STMap a40 by simp
        then show ?thesis using a20 a10 stoloc a7 g1 a40 a50 STMap cc0 by auto
      next
        case (STValue t'')
        then have a40:"v3' = KValue (accessStorage t'' l'' (Storage st (Address e)))" using stoloc a1  a10 a20 by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm)
        moreover have "t3' = Value t''" using stoloc a1  a10 a20 STValue by (simp add:rexp.simps(2) split:option.split_asm prod.split_asm denvalue.split_asm mtypes.split_asm memoryvalue.split_asm)
        moreover have a60:"SCon t (l) (Storage st (Address e))" using "33.hyps"(4) stoloc  a10 a20 a25 a1 STValue by simp 
        then have "r \<noteq> [] \<longrightarrow> CompStoType t t' l l''"
          using "33.hyps"(4)[OF stoloc, of tp "Storeloc l" l t g] stoloc  a10 a20 a25 a1 STValue a40  by simp
        then have cc0:"(t = t' \<and> l =l'' 
                        \<or> CompStoType t t' l l'')" 
        proof(cases "r = []")
          case True
          then have "l'' = l" using a20 ssel.simps by simp
          moreover have "t' = t" using a20 ssel.simps(1)[of t l e cd st g] True by simp
          ultimately show ?thesis using a40 by simp
        next
          case False
          then have "CompStoType t t' l l''" 
            using stoloc a10 a20  a25 a1 STValue "33.hyps"(4) by auto
          then show ?thesis using a40 using CompStoType_sameLoc_sameType by simp
        qed
        then have "typeCon t'' (accessStorage t'' l'' (Storage st (Address e)))" using a60
          using SCon_imps_sublocs STValue SCon.simps(1) by blast
        ultimately show ?thesis by simp
      qed
    qed
  qed
next
  case (34 e cd st g)
  show ?case 
  proof (intros)
    fix v t g4' assume a1:"local.expr CONTRACTS e cd st g = Normal ((v, t), g4') \<and>
       TypeSafe e (Accounts st) (Stack st) (Memory st) (Storage st) cd \<and> fullyInitialised e (Accounts st) (Stack st)"
    then have "t = Value TAddr" using a1 expr.simps(20)[of e cd st g ] by (simp split:if_split_asm result.split_asm prod.split_asm )
    moreover obtain n where  a2:"(Contracts (Accounts st (Address e))) = Suc n" using a1 expr.simps(20) by (simp split:if_splits result.splits prod.splits nat.splits)
    moreover have vdef:"v = KValue (hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t  n))" using expr.simps(20)[of e cd st g ] a1 a2 by (auto split:if_split_asm result.splits prod.split_asm nat.splits)
    moreover have "typeCon TAddr (extractValueType v)" unfolding typeCon.simps
    proof -
      have in1:"extractValueType v = (hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t  n))" 
        using vdef extractValueType.simps by auto
      then have in2:"extractValueType v = (ShowL\<^sub>n\<^sub>a\<^sub>t (n)) + (STR ''-'' + Address e)" unfolding hash_version_def
        by blast
      have "CHR ''.'' \<notin> set (literal.explode (Address e))" 
        using a1 unfolding TypeSafe_def addressFormat_def typeCon.simps checkAddress_def by blast
      then have "CHR ''.'' \<notin> set (literal.explode (STR ''-'' + Address e))" 
        by (simp add: Literal.rep_eq add_Literal_assoc)
      moreover have "CHR ''.'' \<notin> set (literal.explode (ShowL\<^sub>n\<^sub>a\<^sub>t (n)))" using ShowLNatDot by blast

      ultimately have "CHR ''.'' \<notin> set (literal.explode ((ShowL\<^sub>n\<^sub>a\<^sub>t (n)) + (STR ''-'' + Address e)))" 
        by (simp add: plus_literal.rep_eq)
      then show "checkAddress (extractValueType v) " using in2  unfolding checkAddress_def  by auto

    qed


    ultimately show "case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx)
       | Calldata struct \<Rightarrow>
           MCon struct cd (extractValueType v) \<and>
           (\<exists>xx. v = KCDptr xx) \<and>
           (\<exists>stloc tp'' p.
               (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KCDptr p) \<and>
               (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
       | type.Memory struct \<Rightarrow>
           MCon struct (Memory st) (extractValueType v) \<and>
           (\<exists>xx. v = KMemptr xx) \<and>
           (\<exists>stloc tp'' p.
               (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e) \<and>
               accessStore stloc (Stack st) = Some (KMemptr p) \<and>
               (tp'' = struct \<and> v = KMemptr p \<or>
                (\<exists>len arr. extractValueType v \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
       | type.Storage struct \<Rightarrow>
           SCon struct (extractValueType v) (Storage st (Address e)) \<and>
           (\<exists>xx. v = KStoptr xx) \<and>
           (\<exists>stloc tp''.
               (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e) \<and>
               (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))" 
      unfolding checkAddress_def a1 extractValueType.simps by simp
  qed
qed

end
end
