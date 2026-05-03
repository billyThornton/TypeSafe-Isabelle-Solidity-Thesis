theory TypeSafe_Copies
  imports TypeSafe_Support TypeSafe_Def
begin
context typesafe_base
begin
lemma copyRec_preserves_dest_root:
  shows "\<forall>t'. (copyRec (hash ls suffixa) (hash ld suffix') t m' = Some v'')\<longrightarrow> accessStorage t' ld v'' = accessStorage t' ld m'"
proof intros
  fix t'
  assume **:"copyRec (hash ls suffixa) (hash ld suffix') t m' = Some v''"
  then show "accessStorage t' ld v'' = accessStorage t' ld m'"
  proof (induction t arbitrary: m' v'' suffixa suffix' ls)
    case (STArray x1 t)
    then have a60:"Some v'' = iter' (\<lambda>i. copyRec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m' x1"
      unfolding copyRec.simps by simp
    show ?case
    proof (induction rule: iter'_induct[OF _ _ a60[symmetric]])
      case (1 v')
      then have "v' = m'" using iter'.simps by simp
      then show ?case by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. copyRec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m' x = Some v'"
          and a20:"accessStorage t' ld v' = accessStorage t' ld m'"
          and a30:"copyRec (hash (hash ls suffixa) (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash (hash ld suffix') (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = Some v''" by blast
      then show ?case using STArray.IH hash_suffixes_associative by auto
    qed
  next
    case (STMap x1 t)
    then show ?case
      using copyRec.simps(3) by auto
  next
    case (STValue x)
    then show ?case using accessStorage_def hash_suffixes_associative
      using copyRec.simps(2) hash_inequality by force
  qed
qed

lemma copyrec_SubPrefixes:
  "copyRec srcl destl tp a = Some v''' \<longrightarrow>
  (\<forall>destl' t. (\<not>LSubPrefL2 destl' destl) \<longrightarrow> accessStorage t destl' a = accessStorage t destl' v''')"
proof(induction tp arbitrary:srcl destl a v''' )
  case (STArray x1 t)
  show ?case
  proof intros
    fix destl' ta
    assume **:" copyRec srcl destl (STArray x1 t) a = Some v'''"

    then have a5:"Some v''' = iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) a x1"
      using ** copyRec.simps(1)[of srcl destl x1 t a ] by simp

    show "\<not> LSubPrefL2 destl' destl \<Longrightarrow> accessStorage ta destl' a = accessStorage ta destl' v'''"
    proof(induction rule: iter'_induct[OF _ _ a5[symmetric]])
      case (1 v')
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) a x = Some v' "
          and a20:"(\<not> LSubPrefL2 destl' destl \<longrightarrow> accessStorage ta destl' a = accessStorage ta destl' v')"
          and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = Some v''" by blast

      then show ?case
      proof(cases t)
        case mtr:(STArray x11 x12)
        then show ?thesis  using accessStorage_def "2.IH" "2.prems" Not_Sub_More_Specific
          using STArray by force
      next
        case (STValue x2)
        then have "copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (STValue x2) v' = Some v''" using a30 by simp
        then have "(let e = accessStorage x2 (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v' in Some (v'(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) $$:= e))) = Some v''"
          unfolding copyRec.simps by simp
        then show ?thesis using accessStorage_def
          using "2.IH" "2.prems" STArray Not_Sub_More_Specific by fastforce
      next
        case (STMap x3 x4)
        then show ?thesis using a30 by (simp add: copyRec.simps(3))
      qed
    qed
  qed
next
  case (STValue x)
  show ?case
  proof intros
    fix destl' t
    assume "copyRec srcl destl (STValue x) a = Some v'''" and "\<not> LSubPrefL2 destl' destl"
    then show "accessStorage t destl' a = accessStorage t destl' v'''"
      using accessStorage_def LSubPrefL2_def copyRec.simps(2) by auto
  qed
next
  case (STMap x1 tp)
  then show ?case using copyRec.simps(3) by auto
qed

lemma copyrec_SubPrefixes2:
  "copyRec srcl destl tp a = Some v''' \<longrightarrow>
  (\<forall>destl' t.  \<not> TypedStoSubpref destl' destl tp \<longrightarrow> accessStorage t destl' a = accessStorage t destl' v''')"
proof(induction tp arbitrary:srcl destl a v''' )
  case (STArray x1 tp)
  show ?case
  proof intros
    fix destl' t
    assume **:"copyRec srcl destl (STArray x1 tp) a = Some v'''"
      and ***:"\<not> TypedStoSubpref destl' destl (STArray x1 tp)"
    have a5:"Some v''' = iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp) a x1"
      using ** unfolding copyRec.simps by simp

    show "accessStorage t destl' a = accessStorage t destl' v'''" using ***
    proof(induction rule: iter'_induct[OF _ _ a5[symmetric]])
      case (1 v')
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp) a x = Some v'"
          and a20:"(\<not> TypedStoSubpref destl' destl (STArray x tp) \<longrightarrow> accessStorage t destl' a = accessStorage t destl' v')"
          and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) tp v' = Some v''" by blast
      then show ?case
      proof(cases tp)
        case (STArray x11 x12)
        then show ?thesis
          using "2.prems" STArray.IH a20 a30 by force
      next
        case (STMap x21 x22)
        then show ?thesis
          using a30 copyRec.simps(3) by auto
      next
        case (STValue x3)
        then show ?thesis
          using "2.prems" STArray a20 a30 by auto
      qed
    qed
  qed
next
  case (STMap x1 tp)
  then show ?case
    by (simp add: copyRec.simps(3))
next
  case (STValue x)
  show ?case
  proof intros
    fix destl' t
    assume *:"copyRec srcl destl (STValue x) a = Some v'''"
      and **:"\<not> TypedStoSubpref destl' destl (STValue x)"
    then show " accessStorage t destl' a = accessStorage t destl' v'''" using accessStorage_def
      using copyRec.simps(2) by auto
  qed
qed

lemma copyrec_SubPrefixes2_rev:
  "copyRec srcl destl tp a = Some v''' \<longrightarrow>
  (\<forall>destl' t.   accessStorage t destl' a \<noteq> accessStorage t destl' v''' \<longrightarrow> TypedStoSubpref destl' destl tp)"
proof(induction tp arbitrary:srcl destl a v''' )
  case (STArray x1 tp)
  show ?case
  proof intros
    fix destl' t
    assume **:"copyRec srcl destl (STArray x1 tp) a = Some v'''"
      and ***:"accessStorage t destl' a \<noteq> accessStorage t destl' v''' "
    have a5:"Some v''' = iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp) a x1"
      using ** unfolding copyRec.simps by simp

    show " TypedStoSubpref destl' destl (STArray x1 tp)" using ***
    proof(induction rule: iter'_induct[OF _ _ a5[symmetric]])
      case (1 v')
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp) a x = Some v'"
          and a20:"(accessStorage t destl' a \<noteq> accessStorage t destl' v' \<longrightarrow> TypedStoSubpref destl' destl (STArray x tp))"
          and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) tp v' = Some v''" by blast
      then show ?case
      proof(cases tp)
        case (STArray x11 x12)
        then show ?thesis
          using "2.prems" STArray.IH a20 a30
          by (metis less_Suc_eq TypedStoSubpref.simps(2))
      next
        case (STMap x21 x22)
        then show ?thesis
          using a30 copyRec.simps(3) by auto
      next
        case (STValue x3)
        then show ?thesis
          using "2.prems" STArray a20 a30
          using less_Suc_eq by fastforce
      qed
    qed
  qed
next
  case (STMap x1 tp)
  then show ?case
    by (simp add: copyRec.simps(3))
next
  case (STValue x)
  show ?case
  proof intros
    fix destl' t
    assume *:"copyRec srcl destl (STValue x) a = Some v'''"
      and **:" accessStorage t destl' a \<noteq> accessStorage t destl' v''' "
    then show "TypedStoSubpref destl' destl (STValue x)" using accessStorage_def
      using copyRec.simps(2)
      using copyrec_SubPrefixes2 by blast
  qed
qed

lemma copySingleChange:
  assumes "iter' (\<lambda>i m. copyRec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m) md x = Some updM"
  shows "\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStorage t' locs md = accessStorage t' locs updM"
proof (rule iter'_invariant[OF assms(1)])
  show "\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStorage t' locs md = accessStorage t' locs md" by simp
next
  fix i m m'
  assume IH:"\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStorage t' locs md = accessStorage t' locs m"
    and step:"copyRec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m = Some m'"
  show "\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStorage t' locs md = accessStorage t' locs m'"
  proof intros
    fix t' locs
    assume *:"\<not>LSubPrefL2 locs ld \<or> locs = ld"
    then have "accessStorage t' locs md = accessStorage t' locs m" using IH by simp
    moreover have "accessStorage t' locs m = accessStorage t' locs m'"
      using copyrec_SubPrefixes[of "(hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" t m m']
      using step * Not_Sub_More_Specific by (metis copyRec_preserves_dest_root)
    ultimately show "accessStorage t' locs md = accessStorage t' locs m'" by simp
  qed
qed

lemma copySingleChange2:
  assumes "iter' (\<lambda>i m. copyRec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m) md x = Some updM"
  shows "\<forall>locs t''.  \<not>TypedStoSubpref locs ld (STArray x t) \<longrightarrow> accessStorage t'' locs md = accessStorage t'' locs updM"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. copyRec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) md x = Some v'"
      and a20:"(\<forall>locs t''. \<not> TypedStoSubpref locs ld (STArray x t) \<longrightarrow> accessStorage t'' locs md = accessStorage t'' locs v')"
      and a30:"copyRec (hash ls (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = Some v''" by blast
  show ?case
  proof intros
    fix locs t''
    assume *:"\<not> TypedStoSubpref locs ld (STArray (Suc x) t) "
    then show "accessStorage t'' locs md = accessStorage t'' locs v''"
    proof(cases "x = 0")
      case True
      then have "accessStorage t'' locs md = accessStorage t'' locs v'"  using a10 by simp
      then show ?thesis using copyrec_SubPrefixes2 a30
        using "*" by simp
    next
      case False
      then show ?thesis using a30 copyrec_SubPrefixes2 *
        by (metis "2.hyps" copyRec.simps(1))
    qed
  qed
qed

lemma copyAccessPrePost:
  shows "\<forall>t''. Some v'' = iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') m x1
          \<and> (\<forall>suffix. hash destl suffix \<noteq> destl)  \<longrightarrow> accessStorage t''  destl m = accessStorage t'' destl v'' "
proof intros
  fix t''
  assume " Some v'' = iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') m x1 \<and>   (\<forall>suffix. hash destl suffix \<noteq> destl)"
  then have *:"Some v'' = iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') m x1"
    and **: "(\<forall>suffix. hash destl suffix \<noteq> destl)" by simp+
  then show " accessStorage t'' destl m = accessStorage t'' destl v''"
  proof(induction rule: iter'_induct[OF _ _ *[symmetric]])
    case (1 v')
    then show ?case by simp
  next
    case (2 x v'')
    then obtain v'
      where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') m x = Some v'"
        and a20:" (Some v' = iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') m x \<longrightarrow>
          (\<forall>suffix. hash destl suffix \<noteq> destl) \<longrightarrow> accessStorage t'' destl m = accessStorage t'' destl v')"
        and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'  v' = Some v''" by blast
    then show ?case using copyRec_preserves_dest_root
      using "**" by simp
  qed
qed

lemma copyRec_nonZero_Arrays:
  assumes "copyRec srcl destl t' srcMem = Some v'''"
    and  "subStoTp (STArray len t) t'"
    and "len = 0"
  shows "srcMem = v'''" using assms
proof(induction t' arbitrary:srcl destl srcMem v''' len t)
  case (STArray x1 t')
  have a5:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x1 = Some v'''"
    using STArray.prems(1) unfolding copyRec.simps by simp
  show ?case using STArray.prems(2)
  proof(induction rule: iter'_induct[OF _ _ a5])
    case (1 v')
    then show ?case by auto
  next
    case (2 x v'')
    then obtain v'
      where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
        and a20:"(subStoTp (STArray len t) (STArray x t') \<longrightarrow> srcMem = v')"
        and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast
    then show ?case
      using "2.prems" STArray.IH STArray.prems(3) by force
  qed
next
  case (STMap x1 t')
  then show ?case
    by (simp add: copyRec.simps(3))
next
  case (STValue x)
  then show ?case by simp
qed

lemma iter'Copy_nonZero_Arrays:
  assumes "iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
    and  "subStoTp (STArray len t) t'"
    and "len = 0"
  shows "srcMem = v'" using assms
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by auto
next
  case (2 x v'')
  then show ?case
    using copyRec_nonZero_Arrays by blast
qed

lemma copyRec_subT_mustNotBeArray:
  assumes "copyRec srcl destl t' srcMem = Some v'''"
    and "\<forall>len t. subStoTp (STArray len t) t' \<longrightarrow> len > 0"
  shows "\<forall>k v. \<not>subStoTp (STMap k v) t'" using assms
proof(induction t' arbitrary:srcl destl srcMem v''')
  case (STArray x1 t')
  have a5:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x1 = Some v'''"
    using STArray.prems(1) unfolding copyRec.simps by simp
  show ?case using STArray.prems(2)
  proof(induction rule: iter'_induct[OF _ _ a5])
    case (1 v')
    then show ?case by auto
  next
    case (2 x v'')
    then obtain v'
      where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
        and a20:"((\<forall>len t. subStoTp (STArray len t) (STArray x t') \<longrightarrow> 0 < len) \<longrightarrow> (\<forall>k v. \<not> subStoTp (STMap k v) (STArray x t'))) "
        and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  destl  (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast
    then show ?case
      by (metis STArray.IH STArray.prems(2) stypes.distinct(1) subStoTp.simps(2))
  qed
next
  case (STMap x1 t')
  then show ?case
    by (simp add: copyRec.simps(3))
next
  case (STValue x)
  then show ?case by simp
qed

lemma copy_unchanged:
  assumes "iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
    and "SCon (STArray x t') srcl srcMem"
    and "SCon (STArray x t') destl srcMem"
  shows "\<forall>destl' t i' . i'\<ge>x \<and>  LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i')) \<longrightarrow> accessStorage t destl' srcMem = accessStorage t destl' v'" using assms(2,3)
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by auto
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
      and a20:"(SCon (STArray x t') srcl srcMem \<longrightarrow>
          SCon (STArray x t') destl srcMem \<longrightarrow> (\<forall>destl' t i'. x \<le> i' \<and> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i'))
          \<longrightarrow> accessStorage t destl' srcMem = accessStorage t destl' v'))"
      and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  destl  (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast

  show ?case
  proof intros
    fix destl' t i'
    assume as1:"Suc x \<le> i' \<and> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i'))"
    then have g1:"accessStorage t destl' srcMem = accessStorage t destl' v'" using a20 2 by (metis Suc_leD subSCon)
    have g5:"(\<forall>destl' t. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStorage t destl' v' = accessStorage t destl' v'')"
      using a30 copyrec_SubPrefixes[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' v' v''] by simp
    have "\<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using as1
      by (smt (verit) LSubPrefL2_def Suc_le_eq hash_suffixes_associative hashesInts less_irrefl_nat)
    then have g10:" accessStorage t destl' v' = accessStorage t destl' v''" using g5 by simp
    then show "accessStorage t destl' srcMem = accessStorage t destl' v''" using g1 by simp
  qed
qed

lemma copy_unchanged_limit:
  assumes "iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
  shows "\<forall>destl' . \<not>TypedStoSubpref destl' destl (STArray (Suc x) t') \<longrightarrow>
                    (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by auto
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
      and a20:" (\<forall>destl'. \<not> TypedStoSubpref destl' destl (STArray (Suc x) t') \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v'))"
      and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast

  show ?case
  proof intros
    fix destl' t
    assume as1:"\<not> TypedStoSubpref destl' destl (STArray (Suc (Suc x)) t')"
    then have g1:"accessStorage t destl' srcMem = accessStorage t destl' v'" using a20 2 by simp
    have "(\<forall>destl' t. \<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> accessStorage t destl' v' = accessStorage t destl' v'')"
      using a30 as1 copyrec_SubPrefixes2[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' v' v'']  by simp
    then have g10:" accessStorage t destl' v' = accessStorage t destl' v''" using as1 by simp
    then show "accessStorage t destl' srcMem = accessStorage t destl' v''" using g1 by simp
  qed
qed

lemma copy_unchanged_limit_2:
  assumes "iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
  shows "\<forall>destl' . \<not>TypedStoSubpref destl' destl (STArray (x) t') \<longrightarrow>
                    (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by auto
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
      and a20:" (\<forall>destl'. \<not> TypedStoSubpref destl' destl (STArray (x) t') \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v'))"
      and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast

  show ?case
  proof intros
    fix destl' t
    assume as1:"\<not> TypedStoSubpref destl' destl (STArray (Suc ( x)) t')"
    then have g1:"accessStorage t destl' srcMem = accessStorage t destl' v'" using a20 2 by simp
    have "(\<forall>destl' t. \<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> accessStorage t destl' v' = accessStorage t destl' v'')"
      using a30 as1 copyrec_SubPrefixes2[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' v' v'']  by simp
    then have g10:" accessStorage t destl' v' = accessStorage t destl' v''" using as1 by simp
    then show "accessStorage t destl' srcMem = accessStorage t destl' v''" using g1 by simp
  qed
qed

lemma copyRec_unchanged_limit:
  assumes "copyRec srcl destl t' srcMem  = Some v'"
  shows "\<forall>destl'. \<not>TypedStoSubpref destl' destl t' \<longrightarrow>
                    (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"  using assms
proof(induction t' arbitrary:srcl destl srcMem v')
  case (STArray x1 t')
  have a5:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x1 = Some v'"
    using STArray.prems(1) unfolding copyRec.simps by simp
  show ?case
  proof(induction rule: iter'_induct[OF _ _ a5])
    case (1 v')
    then show ?case by auto
  next
    case (2 x v'')
    then obtain v'
      where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
        and a20:"(\<forall>destl'. \<not> TypedStoSubpref destl' destl (STArray x t') \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v'))"
        and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast
    then show ?case
      by (metis "2.hyps" copyRec.simps(1) copyrec_SubPrefixes2_rev)
  qed
next
  case (STMap x1 t')
  then show ?case
    using copyrec_SubPrefixes2_rev by blast
next
  case (STValue x)
  then show ?case
    by (simp add: copyrec_SubPrefixes2)
qed

lemma copy_unchanged_limit22:
  assumes "iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
  shows "\<forall>destl' . TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow>
                    (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by auto
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
      and a20:"(\<forall>destl'. TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v'))"
      and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast

  show ?case
  proof intros
    fix destl' t
    assume as1:"TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t (Suc x))) t'"
    then have g1:"accessStorage t destl' srcMem = accessStorage t destl' v'" using a20 2
      by (meson NotRelatedPrnt_imps_notRelatedChild Sto_divergence_imps_notsubloc TypedStoSubpref_hashes a10 copy_unchanged_limit)
    have "(\<forall>destl' t. \<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> accessStorage t destl' v' = accessStorage t destl' v'')"
      using a30 as1 copyrec_SubPrefixes2[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' v' v'']  by simp
    then have "accessStorage t destl' v' = accessStorage t destl' v''" using as1
      by (metis "2.hyps" NotRelatedPrnt_imps_notRelatedChild Sto_divergence_imps_notsubloc TypedStoSubpref_hashes copyRec.simps(1) copyrec_SubPrefixes2 g1)
    then show "accessStorage t destl' srcMem = accessStorage t destl' v''" using g1 by simp
  qed
qed

lemma single_STValue:
  assumes "SCon (STArray x t') srcl srcMem"
  shows "\<exists>!x'. subStoTp (STValue x') (STArray x t')" using assms
proof(induction t' arbitrary:x srcl)
  case (STArray x1 t')
  then show ?case by fastforce
next
  case (STMap x1 t')
  then show ?case by fastforce
next
  case (STValue x)
  then show ?case by simp
qed

lemma copy_unchanged_limit_rev:
  assumes "iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
    and "SCon (STArray x t') srcl srcMem"
    and "SCon (STArray x t') destl srcMem"
  shows "\<forall>destl' t. accessStorage t destl' srcMem \<noteq> accessStorage t destl' v'
                    \<longrightarrow> TypedStoSubpref destl' destl (STArray (Suc x) t')" using assms(2,3)
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by auto
next
  case (2 x v'')
  then obtain v'
    where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
      and a20:" (SCon (STArray x t') srcl srcMem \<longrightarrow>
          SCon (STArray x t') destl srcMem \<longrightarrow>
          (\<forall>destl' t. accessStorage t destl' srcMem \<noteq> accessStorage t destl' v' \<longrightarrow> TypedStoSubpref destl' destl (STArray (Suc x) t')))"
      and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast
  show ?case
  proof intros
    fix destl' t
    assume as1:" accessStorage t destl' srcMem \<noteq> accessStorage t destl' v'' "
    then have g1:"TypedStoSubpref destl' destl (STArray (Suc x) t')" using a20 2
      by (metis copyrec_SubPrefixes2 lessI TypedStoSubpref.simps(2) subSCon)
    have "(\<forall>destl' t. accessStorage t destl' v' \<noteq> accessStorage t destl' v'' \<longrightarrow> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t')"
      using a30 as1 copyrec_SubPrefixes2_rev[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t' v' v'']  by simp
    then show "TypedStoSubpref destl' destl (STArray (Suc (Suc x)) t')" using g1 by auto
  qed
qed

lemma copyRec_notSub_Scon:
  assumes "copyRec srcl  destl t' srcMem = Some v'"
    and "SCon t' srcl srcMem"
    and "\<not>TypedStoSubpref destl srcl t'"
    and "\<not>TypedStoSubpref srcl destl t'"
    and "SCon t' destl srcMem"
    and "\<forall>subL. TypedStoSubpref subL srcl t' \<longrightarrow> \<not> TypedStoSubpref subL destl t'"
    and "\<forall>subL. TypedStoSubpref subL destl t' \<longrightarrow> \<not> TypedStoSubpref subL srcl t'"
  shows "SCon t' destl v'" using assms
proof(induction t' arbitrary:srcl destl srcMem v')
  case (STArray x1 t')
  have a5:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x1 = Some v'"
    using STArray.prems(1) unfolding copyRec.simps by simp
  show ?case using STArray.prems(2,3,4,5,6,7)
  proof(induction rule: iter'_induct[OF _ _ a5])
    case (1 v')
    then show ?case by simp
  next
    case (2 x v'')
    then obtain v' where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
      and a20:" (SCon (STArray x t') srcl srcMem \<longrightarrow> \<not> TypedStoSubpref destl srcl (STArray x t')
            \<longrightarrow> \<not> TypedStoSubpref srcl destl (STArray x t') \<longrightarrow> SCon (STArray x t') destl srcMem
            \<longrightarrow> (\<forall>subL. TypedStoSubpref subL srcl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL destl (STArray x t')) \<longrightarrow>
              (\<forall>subL. TypedStoSubpref subL destl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL srcl (STArray x t'))
              \<longrightarrow> SCon (STArray x t') destl v' )"
      and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast

    moreover have p1:"(\<forall>subL. TypedStoSubpref subL srcl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL destl (STArray x t'))"
      using TypedStoSubpref_arr_longer 2(7) by blast
    moreover have "(\<forall>subL. TypedStoSubpref subL destl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL srcl (STArray x t'))"
      using TypedStoSubpref_arr_longer 2(8) by blast
    ultimately have a40:"SCon (STArray x t') destl v'" using 2
      using TypedStoSubpref_sameLoc subSCon by presburger

    have g11:"\<forall>destl'. \<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> (\<forall>t. accessStorage t destl' v' = accessStorage t destl' v'')"
      using copyRec_unchanged_limit[OF a30] by blast
    have g12:"\<forall>destl'. TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
      using copy_unchanged_limit22[OF a10] by simp
    have g13:"\<forall>destl'. \<not> TypedStoSubpref destl' destl (STArray x t') \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
      using copy_unchanged_limit_2[OF a10] by blast

    have scSrc:"SCon (STArray (Suc x) t') srcl v'" using g13  p1 "2.prems"(5) 2(3) SCon_preserved_disjoint_change
      by (meson NotRelatedPrnt_imps_notRelatedChild Scon_NoChange TypedStoSubpref_sameLoc)

    show ?case
    proof(cases "\<forall>len t. subStoTp (STArray len t) t' \<longrightarrow> 0 < len")
      case True
      have a45:"SCon (STArray x t') destl v''" unfolding SCon.simps
      proof intros
        fix i assume a1:"i<x"
        then have a41:"SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" using a40 by simp
        then have g10:" \<forall>k v. \<not> subStoTp (STMap k v) t'"
          using copyRec_subT_mustNotBeArray a30 True by simp
        then have g12:"\<not> TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'" using a1
          by (meson NotRelatedPrnt_imps_notRelatedChild Sto_divergence_imps_notsubloc TypedStoSubpref_hashes TypedStoSubpref.simps(2))
        then have "\<forall>l. \<not> TypedStoSubpref (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
          by (metis (full_types) TypedStoSubpref_b a1 hash_suffixes_associative hashesInts nat_neq_iff)
        then show "SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using g11 a41 g10 g12
        proof(induction t' arbitrary:destl i)
          case (STArray x1 t')
          then show ?case
            using NoSubChanged_Scon_Preserved by presburger
        next
          case (STMap x1 t')
          then show ?case by auto
        next
          case (STValue x')
          then show ?case by simp
        qed
      qed

      show ?thesis unfolding SCon.simps
      proof intros
        fix i
        assume as1:"i<Suc x"
        show "SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' "
        proof(cases "i = x")
          case True
          have "SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem" using 2(6) by simp
          then have cc1:"SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'" using g12 Scon_NoChange by simp
          have cc2:"SCon t' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'"  using scSrc by simp
          have cc3:"\<not>TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))  t'" using 2
            by (metis True TypedStoSubpref_specific_unreachanble_arry as1 TypedStoSubpref.simps(2))
          have cc4:"\<not>TypedStoSubpref (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))  t'" using 2
            by (metis True TypedStoSubpref_specific_unreachanble_arry as1 TypedStoSubpref.simps(2))
          have cc5:"\<forall>subL. TypedStoSubpref subL (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> \<not> TypedStoSubpref subL (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
            using 2 NotRelatedPrnt_imps_notRelatedChild cc3 cc4 by blast
          have cc6:"\<forall>subL. TypedStoSubpref subL (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> \<not> TypedStoSubpref subL  (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
            using 2 NotRelatedPrnt_imps_notRelatedChild cc3 cc4 by blast
          then show ?thesis using STArray.IH[OF a30 cc2 cc3 cc4 cc1 cc5 cc6] True by blast
        next
          case False
          then have "i<x" using as1 by simp
          then show ?thesis using a45 by simp
        qed
      qed
    next
      case False
      then have a9:"\<exists>len t. subStoTp (STArray len t) t' \<and> 0 = len" by simp
      then have "v' = v''" using copyRec_nonZero_Arrays a30 by blast
      moreover have "srcMem = v'" using iter'Copy_nonZero_Arrays[OF a10] a9 by auto
      ultimately show ?thesis using a40 2(6) by simp
    qed
  qed
next
  case (STMap x1 t')
  then show ?case
    by (metis copyRec.simps(3) option.distinct(1))
next
  case (STValue x)
  have "(let e = accessStorage x srcl srcMem in Some (srcMem(destl $$:= e))) = Some v'" using STValue(1) unfolding copyRec.simps by simp
  then have "(accessStorage x destl v') = (accessStorage x srcl srcMem)" unfolding accessStorage_def by auto
  moreover have "typeCon x (accessStorage x srcl srcMem)" using STValue(2) unfolding SCon.simps by simp
  ultimately show ?case unfolding SCon.simps by simp
qed

lemma copy_notSub_Scon:
  assumes "iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
    and "SCon (STArray x t') srcl srcMem"
    and "\<not>TypedStoSubpref destl srcl (STArray x t')"
    and "\<not>TypedStoSubpref srcl destl (STArray x t')"
    and "SCon (STArray x t') destl srcMem"
    and "\<forall>subL. TypedStoSubpref subL srcl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL destl (STArray x t')"
    and "\<forall>subL. TypedStoSubpref subL destl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL srcl (STArray x t')"
  shows "SCon (STArray x t') destl v'" using assms(2,3,4,5,6,7)
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by simp
next
  case (2 x v'')
  then obtain v' where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
    and a20:" (SCon (STArray x t') srcl srcMem \<longrightarrow> \<not> TypedStoSubpref destl srcl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref srcl destl (STArray x t') \<longrightarrow> SCon (STArray x t') destl srcMem
        \<longrightarrow> (\<forall>subL. TypedStoSubpref subL srcl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL destl (STArray x t')) \<longrightarrow>
          (\<forall>subL. TypedStoSubpref subL destl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL srcl (STArray x t'))
          \<longrightarrow> SCon (STArray x t') destl v' )"
    and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast

  moreover have p1:"(\<forall>subL. TypedStoSubpref subL srcl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL destl (STArray x t'))"
    using TypedStoSubpref_arr_longer 2(7) by blast
  moreover have "(\<forall>subL. TypedStoSubpref subL destl (STArray x t') \<longrightarrow> \<not> TypedStoSubpref subL srcl (STArray x t'))"
    using TypedStoSubpref_arr_longer 2(8) by blast
  ultimately have a40:"SCon (STArray x t') destl v'" using 2
    using TypedStoSubpref_sameLoc subSCon by presburger

  have g11:"\<forall>destl'. \<not> TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> (\<forall>t. accessStorage t destl' v' = accessStorage t destl' v'')"
    using copyRec_unchanged_limit[OF a30] by blast
  have g12:"\<forall>destl'. TypedStoSubpref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
    using copy_unchanged_limit22[OF a10] by simp
  have g13:"\<forall>destl'. \<not> TypedStoSubpref destl' destl (STArray x t') \<longrightarrow> (\<forall>t. accessStorage t destl' srcMem = accessStorage t destl' v')"
    using copy_unchanged_limit_2[OF a10] by blast

  have scSrc:"SCon (STArray (Suc x) t') srcl v'" using g13  p1 "2.prems"(5) 2(3) SCon_preserved_disjoint_change
    by (meson NotRelatedPrnt_imps_notRelatedChild Scon_NoChange TypedStoSubpref_sameLoc)

  show ?case
  proof(cases "\<forall>len t. subStoTp (STArray len t) t' \<longrightarrow> 0 < len")
    case True
    have a45:"SCon (STArray x t') destl v''" unfolding SCon.simps
    proof intros
      fix i assume a1:"i<x"
      then have a41:"SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" using a40 by simp
      then have g10:" \<forall>k v. \<not> subStoTp (STMap k v) t'"
        using copyRec_subT_mustNotBeArray a30 True by simp
      then have g12:"\<not> TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'" using a1
        by (meson NotRelatedPrnt_imps_notRelatedChild Sto_divergence_imps_notsubloc TypedStoSubpref_hashes TypedStoSubpref.simps(2))
      then have "\<forall>l. \<not> TypedStoSubpref (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
        by (metis (full_types) TypedStoSubpref_b a1 hash_suffixes_associative hashesInts nat_neq_iff)
      then show "SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using g11 a41 g10 g12
      proof(induction t' arbitrary:destl i)
        case (STArray x1 t')
        then show ?case
          using NoSubChanged_Scon_Preserved by presburger
      next
        case (STMap x1 t')
        then show ?case by auto
      next
        case (STValue x')
        then show ?case by simp
      qed
    qed

    show ?thesis unfolding SCon.simps
    proof intros
      fix i
      assume as1:"i<Suc x"
      show "SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' "
      proof(cases "i = x")
        case True
        have "SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem" using 2(6) by simp
        then have cc1:"SCon t' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'" using g12 Scon_NoChange by simp
        have cc2:"SCon t' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'"  using scSrc by simp
        have cc3:"\<not>TypedStoSubpref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))  t'" using 2
          by (metis True TypedStoSubpref_specific_unreachanble_arry as1 TypedStoSubpref.simps(2))
        have cc4:"\<not>TypedStoSubpref (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))  t'" using 2
          by (metis True TypedStoSubpref_specific_unreachanble_arry as1 TypedStoSubpref.simps(2))
        have cc5:"\<forall>subL. TypedStoSubpref subL (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> \<not> TypedStoSubpref subL (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
          using 2 NotRelatedPrnt_imps_notRelatedChild cc3 cc4 by blast
        have cc6:"\<forall>subL. TypedStoSubpref subL (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> \<not> TypedStoSubpref subL  (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
          using 2 NotRelatedPrnt_imps_notRelatedChild cc3 cc4 by blast
        then show ?thesis using copyRec_notSub_Scon[OF a30 cc2 cc3 cc4 cc1 cc5 cc6] True by blast
      next
        case False
        then have "i<x" using as1 by simp
        then show ?thesis using a45 by simp
      qed
    qed
  next
    case False
    then have a9:"\<exists>len t. subStoTp (STArray len t) t' \<and> 0 = len" by simp
    then have "v' = v''" using copyRec_nonZero_Arrays a30 by blast
    moreover have "srcMem = v'" using iter'Copy_nonZero_Arrays[OF a10] a9 by auto
    ultimately show ?thesis using a40 2(6) by simp
  qed
qed

lemma copyrec_same_Scon:
  assumes "SCon t' srcl srcMem"
    and "copyRec srcl srcl t' srcMem = Some v'''"
  shows "SCon t' srcl v'''" using assms
proof (induction t' arbitrary:srcl srcMem v''' )
  case (STArray x1 t')
  have a5:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x1 = Some v'''"
    using STArray.prems(2) unfolding copyRec.simps by simp
  show ?case using STArray.prems(1)
  proof(induction rule: iter'_induct[OF _ _ a5])
    case (1 v')
    then show ?case by simp
  next
    case (2 x v'')
    then obtain v' where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
      and a20:"(SCon (STArray x t') srcl srcMem  \<longrightarrow> SCon (STArray x t') srcl v')"
      and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  srcl  (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast
    then have a40:" SCon (STArray x t') srcl v'" using 2 by auto
    have a50:"\<forall>l t. LSubPrefL2 l (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStorage t l srcMem = accessStorage t l v'" using a10
      using "2.prems" copy_unchanged subSCon by blast
    then show ?case
    proof(cases "\<forall>len t. subStoTp (STArray len t) t' \<longrightarrow> 0 < len")
      case t2:True
      then have g10:" \<forall>k v. \<not> subStoTp (STMap k v) t'" 
        using copyRec_subT_mustNotBeArray a30 by blast
      then have "SCon t' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'" using 2(3) a50
      proof(induction t' arbitrary:srcl  x)
        case (STArray x1 t')
        have " \<forall>i<x1. SCon t' (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'"
        proof(intros)
          fix i
          assume asi1:"i<x1"
          then show "SCon t' (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" using STArray.IH STArray.prems
            by (meson LSubPrefL2_def NoSubChanged_Scon_Preserved lessI SCon.simps(2))
        qed
        then show ?case unfolding SCon.simps by blast
      next
        case (STMap x1 t')
        then show ?case by auto
      next
        case (STValue x')
        then show ?case
          by (metis LSubPrefL2_def lessI SCon.simps(1,2))
      qed
      have g11:"\<forall>destl'. \<not> TypedStoSubpref destl' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' \<longrightarrow> (\<forall>t. accessStorage t destl' v' = accessStorage t destl' v'')"
        using copyRec_unchanged_limit[OF a30] by blast
      have a55:"SCon (STArray x t') srcl v''" unfolding SCon.simps
      proof intros
        fix i assume a1:"i<x"
        then have a41:"SCon t' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" using a40 by simp
        then have g12:"\<not> TypedStoSubpref (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'" using a1
          by (meson NotRelatedPrnt_imps_notRelatedChild Sto_divergence_imps_notsubloc TypedStoSubpref_hashes TypedStoSubpref.simps(2))
        then have "\<forall>l. \<not> TypedStoSubpref (hash (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l) (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
          by (metis (full_types) TypedStoSubpref_b a1 hash_suffixes_associative hashesInts nat_neq_iff)
        then show "SCon t' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using g11 a41 g10 g12
        proof(induction t' arbitrary:srcl i)
          case (STArray x1 t')
          then show ?case
            using NoSubChanged_Scon_Preserved by presburger
        next
          case (STMap x1 t')
          then show ?case by auto
        next
          case (STValue x')
          then show ?case by simp
        qed
      qed

      then have a60:"SCon t' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v''"
        using STArray.IH[OF _ a30]
        by (simp add: \<open>SCon t' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'\<close>)
      show ?thesis unfolding SCon.simps
      proof intros
        fix i assume as1:"i<Suc x"
        show "SCon t' (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''"
        proof(cases "i \<noteq> x")
          case True
          then show ?thesis using a55 as1 by auto
        next
          case False
          then show ?thesis using a60 by simp
        qed
      qed
    next
      case False
      then have a9:"\<exists>len t. subStoTp (STArray len t) t' \<and> 0 = len" by simp
      then have "v' = v''" using copyRec_nonZero_Arrays a30 by blast
      moreover have "srcMem = v'" using iter'Copy_nonZero_Arrays[OF a10] a9 by auto
      ultimately show ?thesis using a40 2(3) by blast
    qed
  qed
next
  case (STMap x1 t')
  then show ?case
    by (metis copyRec_nonZero_Arrays copyRec_subT_mustNotBeArray neq0_conv subStoTp.simps(3))
next
  case (STValue x)
  then have " (let e = accessStorage x srcl srcMem in Some (srcMem(srcl $$:= e))) = Some v'''"
    unfolding copyRec.simps by blast
  then show ?case
    using STValue(1) using accessStorage_def by fastforce
qed

lemma copy_same_Scon:
  assumes "iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
    and "SCon (STArray x t') srcl srcMem"
  shows "SCon (STArray x t') srcl v'" using assms(2)
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1 v')
  then show ?case by simp
next
  case (2 x v'')
  then obtain v' where a10:"iter' (\<lambda>i. copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t') srcMem x = Some v'"
    and a20:"(SCon (STArray x t') srcl srcMem  \<longrightarrow> SCon (STArray x t') srcl v')"
    and a30:"copyRec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash  srcl  (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t' v' = Some v''" by blast
  then show ?case using copyrec_same_Scon
    using "2.hyps" "2.prems" copyRec.simps(1) by presburger
qed

end
end

