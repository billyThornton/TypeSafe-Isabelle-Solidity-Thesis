theory TypeSafe_Mem_Sto_Comp
  imports TypeSafe_Memory TypeSafe_Storage
begin




lemma convertComp:
  assumes "cps2mTypeCompatible t'  tp"
  shows "cps2mTypeConvert t' = Some tp" using assms
proof(induction t' arbitrary:tp)
  case (STArray x1 t')
  then obtain x12 where tpDef:"tp = MTArray x1 x12 \<and> cps2mTypeCompatible t' x12"
    using cps2mTypeCompatible.simps
    by (metis extractType.cases)
  then show ?case using STArray.IH by auto
next
  case (STMap x1 t')
  then show ?case by simp
next
  case (STValue x)
  then show ?case
    by (metis mtypes.exhaust cps2mTypeCompatible.simps(1,6) cps2mTypeConvert.simps(1))
qed


lemma compatible_TypedStoSubpref_imps_TypedMemSubPref:
  assumes "cps2mTypeCompatible st mt"
  shows "TypedStoSubpref x' l st \<longleftrightarrow> TypedMemSubPref x' l mt \<or> x' = l"
proof
  assume "TypedStoSubpref x' l st"
  then show "TypedMemSubPref x' l mt \<or> x' = l" using assms
  proof(induction st arbitrary:mt l)
    case (STArray x1 st)
    then show ?case
      by (smt (verit) stypes.inject(1) TypedMemSubPref.simps(2) TypedStoSubpref.simps(2)
          cps2mTypeCompatible.elims(2) cps2mTypeCompatible.simps(3))
  next
    case (STMap x1 st)
    then show ?case by simp
  next
    case (STValue x)
    then show ?case
      by (metis TypedStoSubpref.simps(1))
  qed
next
  assume "TypedMemSubPref x' l mt \<or> x' = l"
  then show "TypedStoSubpref x' l st" using assms
  proof(cases "x' = l")
    case True
    then show "TypedStoSubpref x' l st" using TypedStoSubpref_sameLoc by simp
  next
    case False
    then have a1:"TypedMemSubPref x' l mt" 
      using \<open>TypedMemSubPref x' l mt \<or> x' = l\<close> by blast
    then show "TypedStoSubpref x' l st" using assms
    proof(induction mt arbitrary: st l)
      case (MTArray x1 mt)
      then obtain st' where st_def: "st = STArray x1 st'" and compat: "cps2mTypeCompatible st' mt"
        using cps2mTypeCompatible.elims(2) by blast
      then obtain i where idef: "i<x1 \<and> (TypedMemSubPref x' (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mt \<or> x' = hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
        unfolding TypedMemSubPref.simps 
        using MTArray.prems(1) by fastforce
      then show ?case 
      proof(cases "x' = hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)")
        case True
        then show ?thesis using st_def 
          using TypedStoSubpref_sameLoc idef by auto
      next
        case False
        then have sub: "TypedMemSubPref x' (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mt" using idef by blast
        then have "TypedStoSubpref x' (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) st'" using MTArray.IH compat by blast
        then show ?thesis using idef st_def 
          by auto
      qed
    next
      case (MTValue x)
      then show ?case
        by (metis stypes.exhaust TypedMemSubPref.simps(1) TypedStoSubpref.simps(1) cps2mTypeCompatible.simps(3,4))
    qed
  qed
qed

lemma compatible_TypedStoSubpref_imps_TypedMemSubPref_neg:
  assumes "cps2mTypeCompatible st mt"
  shows "\<not> TypedStoSubpref x' l st \<longleftrightarrow> \<not> TypedMemSubPref x' l mt \<and> x' \<noteq> l"
  using assms compatible_TypedStoSubpref_imps_TypedMemSubPref by auto

end
