theory TypeSafe_Memory_Init
  imports TypeSafe_Support TypeSafe_Hashing_Subs TypeSafe_Storage TypeSafe_Memory

begin

lemma minitRec_SubPrefixes:
  "minitRec destl tp v' = v''' \<longrightarrow>
  (\<forall>destl'. (\<not>LSubPrefL2 destl' destl) \<longrightarrow> accessStore destl' v' = accessStore destl' v''')"
proof(induction tp arbitrary:destl v' v''' )
  case (MTArray x1 t)
  show ?case
  proof intros
    fix destl'
    assume **:" minitRec destl (MTArray x1 t) v' = v'''"

    then have a5:"v''' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) v' in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1)"
      using **  unfolding minitRec.simps by (simp )
    then obtain m where mdef:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t) v'" by auto
    have a20:"\<not> LSubPrefL2 destl' destl \<Longrightarrow> accessStore destl' v' = accessStore destl' m"
    proof -
      assume "\<not> LSubPrefL2 destl' destl"
      then have "\<not>((\<exists>i. destl' = hash destl i) \<or> destl' = destl)" using LSubPrefL2_def[of destl' destl] by auto
      then have "(\<forall>i. destl' \<noteq> hash destl i) \<and> destl' \<noteq> destl" by simp
      then show "accessStore destl' v' = accessStore destl' m" 
        using mdef unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
    qed

    then have v''def:"v''' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" using a5 mdef by metis 
    show "\<not> LSubPrefL2 destl' destl \<Longrightarrow> accessStore destl' v' = accessStore destl' v'''" using a20
    proof(induction rule: iter_ind[OF _ _ v''def[symmetric]]) 
      case (1)
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v2
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v2"
          and a20:"(\<not> LSubPrefL2 destl' destl \<longrightarrow>
          (\<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' m) \<longrightarrow> accessStore destl' v' = accessStore destl' v2)"
          and a30:"  minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v2 = v''" by blast
      then have b40:"accessStore destl' v' = accessStore destl' v2" using 2 by blast
      then show ?case
      proof(cases t)
        case mtr:(MTArray x11 x12)
        then have b10:"v'' = (let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v2 
                               in iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12) m x11)"
          using a30 minitRec.simps(1)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12] by simp

        then have b45:"(\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v2 = accessStore destl' v'')" 
          using MTArray mtr a30 by blast
        have "\<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using Not_Sub_More_Specific 2 by blast
        then show ?thesis using b45 b40 by simp
      next
        case (MTValue x2)
        then have "v'' = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue (ival x2)) (MTValue x2) v2" 
          using minitRec.simps(2)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2] a30 by simp

        then have b45:"(\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v2 = accessStore destl' v'')" 
          using MTArray MTValue a30 by blast
        have "\<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using Not_Sub_More_Specific 2 by blast
        then have b50:"accessStore destl' v' = accessStore destl' v''" using b45 
          using b40 by auto
        then show ?thesis using b40 by simp
      qed
    qed
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix destl'
    assume **:" minitRec destl (MTValue x) v' = v'''"
      and ***:"\<not> LSubPrefL2 destl' destl"

    then have mdef:"v''' = updateTypedStore destl (MValue (ival x)) (MTValue x) v'" using minitRec.simps(2)[of destl x ] by simp
    then have "\<not>((\<exists>i. destl' = hash destl i) \<or> destl' = destl)" using LSubPrefL2_def[of destl' destl] *** by auto
    then have "(\<forall>i. destl' \<noteq> hash destl i) \<and> destl' \<noteq> destl" by simp
    then show " accessStore destl' v' = accessStore destl' v'''" 
      using mdef unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def 
      by (auto split:option.splits memoryvalue.splits)
  qed
qed

lemma minitRec_SubPrefixes_typed:
  "minitRec destl tp v' = v''' \<longrightarrow>
  (\<forall>destl'. (\<not>LSubPrefL2 destl' destl) \<longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' v''')"
proof(induction tp arbitrary:destl v' v''' )
  case (MTArray x1 t)
  show ?case
  proof intros
    fix destl'
    assume **:" minitRec destl (MTArray x1 t) v' = v'''"

    then have a5:"v''' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) v' in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1)"
      using **  unfolding minitRec.simps by (simp )
    then obtain m where mdef:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t) v'" by auto
    have a20:"\<not> LSubPrefL2 destl' destl \<Longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' m"
    proof -
      assume "\<not> LSubPrefL2 destl' destl"
      then have "\<not>((\<exists>i. destl' = hash destl i) \<or> destl' = destl)" using LSubPrefL2_def[of destl' destl] by auto
      then have "(\<forall>i. destl' \<noteq> hash destl i) \<and> destl' \<noteq> destl" by simp
      then show "accessTypeStore destl' v' = accessTypeStore destl' m" 
        using mdef unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
    qed

    then have v''def:"v''' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" using a5 mdef by metis 
    show "\<not> LSubPrefL2 destl' destl \<Longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' v'''" using a20
    proof(induction rule: iter_ind[OF _ _ v''def[symmetric]]) 
      case (1)
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v2
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v2"
          and a20:"(\<not> LSubPrefL2 destl' destl \<longrightarrow>
          (\<not> LSubPrefL2 destl' destl \<longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' m) \<longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' v2)"
          and a30:"  minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v2 = v''" by blast
      then have b40:"accessTypeStore destl' v' = accessTypeStore destl' v2" using 2 by blast
      then show ?case
      proof(cases t)
        case mtr:(MTArray x11 x12)
        then have b10:"v'' = (let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v2 
                               in iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12) m x11)"
          using a30 minitRec.simps(1)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12] by simp

        then have b45:"(\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessTypeStore destl' v2 = accessTypeStore destl' v'')" 
          using MTArray mtr a30 by blast
        have "\<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using Not_Sub_More_Specific 2 by blast
        then show ?thesis using b45 b40 by simp
      next
        case (MTValue x2)
        then have "v'' = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue (ival x2)) (MTValue x2) v2" 
          using minitRec.simps(2)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2] a30 by simp

        then have b45:"(\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessTypeStore destl' v2 = accessTypeStore destl' v'')" 
          using MTArray MTValue a30 by blast
        have "\<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using Not_Sub_More_Specific 2 by blast
        then have b50:"accessTypeStore destl' v' = accessTypeStore destl' v''" using b45 
          using b40 by auto
        then show ?thesis using b40 by simp
      qed
    qed
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix destl'
    assume **:" minitRec destl (MTValue x) v' = v'''"
      and ***:"\<not> LSubPrefL2 destl' destl"

    then have mdef:"v''' = updateTypedStore destl (MValue (ival x)) (MTValue x) v'" using minitRec.simps(2)[of destl x ] by simp
    then have "\<not>((\<exists>i. destl' = hash destl i) \<or> destl' = destl)" using LSubPrefL2_def[of destl' destl] *** by auto
    then have "(\<forall>i. destl' \<noteq> hash destl i) \<and> destl' \<noteq> destl" by simp
    then show " accessTypeStore destl' v' = accessTypeStore destl' v'''" 
      using mdef unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def 
      by (auto split:option.splits memoryvalue.splits)
  qed
qed

lemma minitSingleChange:
  assumes "iter (\<lambda>i m'' . minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x = updM"
  shows "\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStore locs m = accessStore locs updM"
proof(induction rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter (\<lambda>i. minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20:"(\<forall>t' locs. \<not> LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessStore locs m = accessStore locs v') "
      and a30:"minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
  show ?case 
  proof intros
    fix locs t'
    assume *:"\<not> LSubPrefL2 locs ld \<or> locs = ld"
    then have "accessStore locs m = accessStore locs v'" using a20  by simp
    then show "accessStore locs m = accessStore locs v''" 
      using minitRec_SubPrefixes  a30 * Not_Sub_More_Specific 
      by (metis LSubPrefL2_def hash_inequality hash_suffixes_associative)
  qed
qed

lemma minitSingleChange_typed:
  assumes "iter (\<lambda>i m'' . minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x = updM"
  shows "\<forall>t' locs. \<not>LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessTypeStore locs m = accessTypeStore locs updM"
proof(induction rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter (\<lambda>i. minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20:"(\<forall>t' locs. \<not> LSubPrefL2 locs ld \<or> locs = ld \<longrightarrow> accessTypeStore locs m = accessTypeStore locs v') "
      and a30:"minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
  show ?case 
  proof intros
    fix locs t'
    assume *:"\<not> LSubPrefL2 locs ld \<or> locs = ld"
    then have "accessTypeStore locs m = accessTypeStore locs v'" using a20  by simp
    then show "accessTypeStore locs m = accessTypeStore locs v''" 
      using minitRec_SubPrefixes_typed  a30 * Not_Sub_More_Specific 
      by (metis LSubPrefL2_def hash_inequality hash_suffixes_associative)
  qed
qed

lemma minitRec_SubPrefixes2:
  "minitRec destl tp a = v''' \<longrightarrow>
  (\<forall>destl'. destl' \<noteq> destl \<and> (\<not> TypedMemSubPref destl' destl tp) \<longrightarrow> accessStore destl' a = accessStore destl' v''')" 
proof(induction tp arbitrary:destl a v''' )
  case (MTArray x1 t)
  show ?case
  proof intros
    fix destl'
    assume **:"minitRec destl (MTArray x1 t) a = v'''"

    have a5:"(let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1) = v'''" 
      using **  unfolding minitRec.simps by simp
    then obtain m where mdef:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a" by auto
    have a20:"destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x1 t) \<Longrightarrow> accessStore destl' a = accessStore destl' m"
    proof -
      assume asm:"destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x1 t)"
      then have "\<not>(\<exists>i<x1. TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
        using TypedMemSubPref.simps(2)[of destl' destl x1 t] by auto
      then have "(\<forall>i<x1. \<not>TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" by simp
      then show "accessStore destl' a = accessStore destl' m" using mdef asm unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
    qed

    then have v''def:"v''' =  iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" 
      using a5 mdef by metis 
    show "destl'  \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x1 t) \<Longrightarrow> accessStore destl' a = accessStore destl' v'''" using a20 
    proof(induction rule: iter_ind[OF _ _ v''def[symmetric]]) 
      case (1)
      then show ?case using 1 by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
          and a20:"(destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
          (destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow> accessStore destl' a = accessStore destl' m) \<longrightarrow>
          accessStore destl' a = accessStore destl' v')"
          and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
      then have b40:"accessStore destl' a = accessStore destl' v'" using 2 
        by (metis less_Suc_eq TypedMemSubPref.simps(2))
      then show ?case
      proof(cases t)
        case mtr:(MTArray x11 x12)
        then have b10:"v'' = (let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v' 
                              in iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12) m x11)"
          using a30 minitRec.simps(1)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12] by simp

        then have b45:"(\<forall>destl'. destl' \<noteq> (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<and> \<not> TypedMemSubPref destl'(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
          using MTArray mtr a30 by blast
        have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using 2 
          using Not_Sub_More_Specific_more_speific by blast
        then show ?thesis using b45 b40  
          using "2.prems"(1) by force
      next
        case (MTValue x2)
        then have "v'' = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue (ival x2)) (MTValue x2) v'" 
          using minitRec.simps(2)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2] using a30 by simp
        then have b45:"(\<forall>destl'. destl' \<noteq>  (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) 
                        \<and> \<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t 
                        \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
          using MTArray MTValue a30 by blast
        have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using Not_Sub_More_Specific_more_speific 2 by blast
        then have b50:"accessStore destl' v' = accessStore destl' v''" using b45
          by (simp add: MTValue)
        then show ?thesis using b40  by simp
      qed
    qed
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix destl'
    assume **:" minitRec destl (MTValue x) a = v'''"
    assume ***:"destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTValue x)"
    then have mdef:"v''' = updateTypedStore destl (MValue (ival x)) (MTValue x) a" 
      using ** minitRec.simps(2)[of destl x] by simp
    assume ***:" destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTValue x)"
    then show "accessStore destl' a = accessStore destl' v'''" 
      using mdef unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
      by (auto split:option.splits memoryvalue.splits)
  qed
qed

lemma minitRec_SubPrefixes2_typed:
  "minitRec destl tp a = v''' \<longrightarrow>
  (\<forall>destl'. destl' \<noteq> destl \<and> (\<not> TypedMemSubPref destl' destl tp) \<longrightarrow> accessTypeStore destl' a = accessTypeStore destl' v''')" 
proof(induction tp arbitrary:destl a v''' )
  case (MTArray x1 t)
  show ?case
  proof intros
    fix destl'
    assume **:"minitRec destl (MTArray x1 t) a = v'''"

    have a5:"(let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1) = v'''" 
      using **  unfolding minitRec.simps by simp
    then obtain m where mdef:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a" by auto
    have a20:"destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x1 t) \<Longrightarrow> accessTypeStore destl' a = accessTypeStore destl' m"
    proof -
      assume asm:"destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x1 t)"
      then have "\<not>(\<exists>i<x1. TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" 
        using TypedMemSubPref.simps(2)[of destl' destl x1 t] by auto
      then have "(\<forall>i<x1. \<not>TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" by simp
      then show "accessTypeStore destl' a = accessTypeStore destl' m" 
        using mdef asm unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
    qed

    then have v''def:"v''' =  iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" 
      using a5 mdef by metis 
    show "destl'  \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x1 t) \<Longrightarrow> accessTypeStore destl' a = accessTypeStore destl' v'''" using a20 
    proof(induction rule: iter_ind[OF _ _ v''def[symmetric]]) 
      case (1)
      then show ?case using 1 by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
          and a20:"(destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
          (destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow> accessTypeStore destl' a = accessTypeStore destl' m) \<longrightarrow>
          accessTypeStore destl' a = accessTypeStore destl' v')"
          and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
      then have b40:"accessTypeStore destl' a = accessTypeStore destl' v'" using 2 
        by (metis less_Suc_eq TypedMemSubPref.simps(2))
      then show ?case
      proof(cases t)
        case mtr:(MTArray x11 x12)
        then have b10:"v'' = (let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v' 
                              in iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12) m x11)"
          using a30 minitRec.simps(1)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12] by simp

        then have b45:"(\<forall>destl'. destl' \<noteq> (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<and> \<not> TypedMemSubPref destl'(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t 
                        \<longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' v'')" 
          using MTArray mtr a30 by blast
        have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using 2 
          using Not_Sub_More_Specific_more_speific by blast
        then show ?thesis using b45 b40  
          using "2.prems"(1) by force
      next
        case (MTValue x2)
        then have "v'' = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue (ival x2)) (MTValue x2) v'" 
          using minitRec.simps(2)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2] using a30 by simp
        then have b45:"(\<forall>destl'. destl' \<noteq>  (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) 
                        \<and> \<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t 
                        \<longrightarrow> accessTypeStore destl' v' = accessTypeStore destl' v'')" 
          using MTArray MTValue a30 by blast
        have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using Not_Sub_More_Specific_more_speific 2 by blast
        then have b50:"accessTypeStore destl' v' = accessTypeStore destl' v''" using b45
          by (simp add: MTValue)
        then show ?thesis using b40  by simp
      qed
    qed
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix destl'
    assume **:" minitRec destl (MTValue x) a = v'''"
    assume ***:"destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTValue x)"
    then have mdef:"v''' = updateTypedStore destl (MValue (ival x)) (MTValue x) a" 
      using ** minitRec.simps(2)[of destl x] by simp
    assume ***:" destl' \<noteq> destl \<and> \<not> TypedMemSubPref destl' destl (MTValue x)"
    then show "accessTypeStore destl' a = accessTypeStore destl' v'''" 
      using mdef unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
      by (auto split:option.splits memoryvalue.splits)
  qed
qed

lemma minitSingleChange2:
  assumes "iter (\<lambda>i m'' . minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x = updM"
  shows "\<forall>locs.  \<not>TypedMemSubPref locs ld (MTArray x t) \<or> locs = ld \<longrightarrow> accessStore locs m = accessStore locs updM"
proof(induction rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter (\<lambda>i. minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20:"(\<forall>locs. \<not> TypedMemSubPref locs ld (MTArray x t) \<or> locs = ld \<longrightarrow> accessStore locs m = accessStore locs v')"
      and a30:"minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
  show ?case 
  proof intros
    fix locs 
    assume *:"\<not> TypedMemSubPref locs ld (MTArray (Suc x) t) \<or> locs = ld"
    then have "accessStore locs m =  accessStore locs v'" using a20 by auto
    then show "accessStore locs m = accessStore locs v''" using minitRec_SubPrefixes2 
      using "*" a30 
      by (metis LSubPrefL2_def hash_inequality hash_suffixes_associative lessI minitRec_SubPrefixes TypedMemSubPref.simps(2))
  qed
qed

lemma minitSingleChange2_typed:
  assumes "iter (\<lambda>i m'' . minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x = updM"
  shows "\<forall>locs.  \<not>TypedMemSubPref locs ld (MTArray x t) \<or> locs = ld \<longrightarrow> accessTypeStore locs m = accessTypeStore locs updM"
proof(induction rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter (\<lambda>i. minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20:"(\<forall>locs. \<not> TypedMemSubPref locs ld (MTArray x t) \<or> locs = ld \<longrightarrow> accessTypeStore locs m = accessTypeStore locs v')"
      and a30:"minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
  show ?case 
  proof intros
    fix locs 
    assume *:"\<not> TypedMemSubPref locs ld (MTArray (Suc x) t) \<or> locs = ld"
    then have "accessTypeStore locs m =  accessTypeStore locs v'" using a20 by auto
    then show "accessTypeStore locs m = accessTypeStore locs v''" using minitRec_SubPrefixes2_typed 
      using "*" a30 
      by (metis LSubPrefL2_def TypedMemSubPref.simps(2) hash_flatten_right hash_inequality lessI neg_MemLSubPrefL2_imps_TypedMemSubPref)
  qed
qed

lemma minitRec_array_root_both:
  assumes step: "minitRec destl (MTArray x t) m0 = v"
  shows "accessTypeStore destl v = Some (MTArray x t)
    \<and> accessStore destl v = Some (MPointer destl)"
proof -
  let ?m = "updateTypedStore destl (MPointer destl) (MTArray x t) m0"
  have run: "iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) ?m x = v"
    using step unfolding Let_def minitRec.simps(1) 
    by blast 
  have keep_type:
    "accessTypeStore destl ?m = accessTypeStore destl v"
    using minitSingleChange2_typed[OF run] by simp
  have keep_store:
    "accessStore destl ?m = accessStore destl v"
    using minitSingleChange[OF run] by simp
  show ?thesis
    using keep_type keep_store 
    unfolding accessTypeStore_def accessStore_def updateTypeStore_def updateTypedStore_def updateStore_def 
    by simp
qed


lemma minitRecPtrsPointToSelf:
  shows "minitRec destl t destm = v'
          \<longrightarrow>  (\<forall>l l'. (TypedMemSubPref l destl t \<or> l = destl) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
proof(induction t arbitrary: destl destm v')
  case (MTArray x1 t)
  show ?case
  proof intros
    fix l l'
    assume *:"minitRec destl (MTArray x1 t) destm = v'"
      and **:"(TypedMemSubPref l destl (MTArray x1 t) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l')"
    have a10:"v' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) destm in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1)"
      using * minitRec.simps(1)[of destl x1 t ] by simp
    then obtain m where a40:"m =  updateTypedStore destl (MPointer destl) (MTArray x1 t) destm" by auto
    then have a45:"accessStore destl m = Some(MPointer destl)" unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then have a50:"v' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" using a10 a40 by presburger
    show "l' = l" using a45 **
    proof(induction rule: iter_ind[OF _ _ a50[symmetric]])
      case (1)
      then show ?case by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
          and a20:"(accessStore destl m = Some (MPointer destl) \<longrightarrow>
          (TypedMemSubPref l destl (MTArray x t) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
          and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
      then have "accessStore destl m = Some (MPointer destl)" using 2 by blast
      then show ?case 
      proof(cases "l = destl")
        case True
        then show ?thesis using 2(1,3,4) 
          by (metis MTArray minitRec_SubPrefixes2)
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
            using * a30 by (meson minitRec_SubPrefixes)
          then show ?thesis using a20 2 using True by argo
        next
          case False
          then have b5:"TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using 2(4) TypedMemSubPref.simps(2)[of l destl "(Suc x)" t] f1 
            using less_Suc_eq by auto
          have b10:"accessStore l v'' = Some (MPointer l')" using 2(4) by auto

          have "(\<forall>l l'. (TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<and> accessStore l v'' = Some (MPointer l') \<longrightarrow> l' = l)" 
            using  MTArray[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"] a30 by simp
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
    assume *:"minitRec destl (MTValue x) destm = v'" 
      and **:"(TypedMemSubPref l destl (MTValue x) \<or> l = destl) \<and> accessStore l v' = Some (MPointer l')"
    have "v' = updateTypedStore destl (MValue (ival x)) (MTValue x) destm" 
      using minitRec.simps(2)[of destl x ] * by simp
    then obtain v where b10: "accessStore destl v' = Some (MValue v)" 
      unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
      by (auto split:option.splits memoryvalue.splits)
    show "l' = l" using b10 ** by auto
  qed
qed

lemma minitSelfPointers:
  assumes "iter (\<lambda>i m''. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x1 = v'"
  shows "(\<forall>l l'. TypedMemSubPref l destl (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"  using assms(1)
proof(induction  rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20: "(iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v' \<longrightarrow>
          (\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l))"
      and a30: "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
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
          using * minitRec_SubPrefixes a30 by blast
        then show ?thesis using a20 True *  b50 
          using a10 by presburger
      next
        case False
        then have "TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
          using TypedMemSubPref.simps(2)[of l destl "(Suc x)" t] *
          using less_Suc_eq by auto
        then show ?thesis using a30 minitRecPtrsPointToSelf * by blast
      qed
    next
      case (MTValue x2)
      then have b390:"v'' = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue (ival x2)) (MTValue x2) v'" 
        using a30 minitRec.simps(2)[of   "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 ] by simp
      have "(\<exists>i<Suc x. TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t  \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using TypedMemSubPref.simps(2)[of l destl "Suc x" t] * by auto
      then obtain i where b400:"i< Suc x \<and> TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (MTValue x2)" using MTValue by auto
      then have "l =  (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" by simp

      then show ?thesis using * 
        by (metis "2.IH" TypedMemSubPref.simps(2) less_SucE minitRecPtrsPointToSelf minitRec_SubPrefixes2) 

    qed
  qed
qed

lemma minitRecValueTypeCon:
  shows "\<forall>st. minitRec destl t destm = v' \<longrightarrow> CompMemJustType t (MTValue st)
          \<longrightarrow>  (\<forall>l l'. (TypedMemSubPref l destl t \<or> l = destl) \<and> accessStore l v' = Some (MValue l') \<longrightarrow> typeCon st l')"
proof(induction t arbitrary: destl destm v')
  case (MTArray x1 t)
  show ?case
  proof intros
    fix l l' st
    assume *:"minitRec destl (MTArray x1 t) destm = v'"
      and ***:"CompMemJustType (MTArray x1 t) (MTValue st)"
      and **:"(TypedMemSubPref l destl (MTArray x1 t) \<or> l = destl) \<and> accessStore l v' = Some (MValue l')"
    have a10:"v' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) destm in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1)"
      using * minitRec.simps(1)[of destl x1 t ] by simp
    then obtain m where a40:"m =  updateTypedStore destl (MPointer destl) (MTArray x1 t) destm" by auto
    then have a45:"accessStore destl m = Some(MPointer destl)" unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then have a50:"v' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" using a10 a40 by presburger
    show "typeCon st l'" using a45 ** ***
    proof(induction rule: iter_ind[OF _ _ a50[symmetric]])
      case (1)
      then show ?case by auto
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
          and a20:"(accessStore destl m = Some (MPointer destl) \<longrightarrow>
          (TypedMemSubPref l destl (MTArray x t) \<or> l = destl) \<and> accessStore l v' = Some (MValue l') \<longrightarrow>
          CompMemJustType (MTArray x t) (MTValue st) \<longrightarrow> typeCon st l')"
          and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
      then have "accessStore destl m = Some (MPointer destl)" using 2 by blast
      then show ?case 
      proof(cases "l = destl")
        case True
        then show ?thesis using a20 2 
          by (metis MTArray mtypes.distinct(1) minitRec_SubPrefixes2 CompMemJustType.simps(2))
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
            using * a30 by (meson minitRec_SubPrefixes)
          then show ?thesis using a20 2 using True 
            by (metis mtypes.distinct(1) CompMemJustType.simps(2))
        next
          case False
          then have b5:"TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t 
          \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using 2(4) TypedMemSubPref.simps(2)[of l destl "(Suc x)" t] f1 
            using less_Suc_eq by auto
          have b10:"accessStore l v'' = Some (MValue l')" using 2(4) by auto

          have "(\<forall>l l'. (TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<and> accessStore l v'' = Some (MValue l') \<longrightarrow> typeCon st l')" 
            using  MTArray[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] a30 
            using "***" CompMemJustType.simps(2) by blast
          then show ?thesis using b5 b10 by blast
        qed
      qed
    qed
  qed
next
  case (MTValue x)
  then show ?case 
  proof intros
    fix l l' st
    assume *:"minitRec destl (MTValue x) destm = v'" 
      and ***:"CompMemJustType (MTValue x) (MTValue st)"
      and **:"(TypedMemSubPref l destl (MTValue x) \<or> l = destl) \<and> accessStore l v' = Some (MValue l')"
    have "v' =updateTypedStore destl (MValue (ival x)) (MTValue x) destm" 
      using minitRec.simps(2)[of destl x ] * by simp
    moreover obtain v where b10: "accessStore destl v' = Some (MValue v)" 
      using calculation
      unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
      by (auto split:option.splits memoryvalue.splits)
    moreover have "v = ival x" using calculation unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    moreover have "typeCon x v" using ivalTypeCon calculation by simp
    ultimately show " typeCon st l' " using b10 ** MTValue 
      using "*" "***" ivalTypeCon minitRec.simps(2) by auto
  qed
qed

lemma minitRecMCon :
  "minitRec destl tp a = v''' \<longrightarrow> arraysGreaterZero tp
          \<longrightarrow> MCon tp v''' destl"
proof (induction tp arbitrary:destl a v''')
  case (MTArray x1 t)
  show ?case
  proof intros
    assume **:"minitRec destl (MTArray x1 t) a = v'''"
      and ***:"arraysGreaterZero (MTArray x1 t)"
    then have a5:"(let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1) = v'''" 
      using **  minitRec.simps(1)[of destl x1 t ] by simp
    then obtain m where mdef:"m =  updateTypedStore destl (MPointer destl) (MTArray x1 t) a" by auto

(*We know this specific subset of srcMem is Mcon*)
    then show " MCon (MTArray x1 t) v''' destl"
    proof(cases "x1>0")
      case True
      then have agt:"arraysGreaterZero t" 
        using *** unfolding arraysGreaterZero.simps by auto
      have v''def:"v''' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" using a5 mdef by metis 

      have "\<forall>i<x1. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' of None \<Rightarrow> False 
             | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v''' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v''' loc2 | MTValue Types \<Rightarrow> False)"

      proof(induction rule: iter_ind[OF _ _ v''def[symmetric]])
        case (1)
        then show ?case by simp
      next
        case (2 x v'')
        then obtain v'
          where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
            and a20:"(\<forall>i<x. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False
                | Some (MValue val) \<Rightarrow> (case t of MTArray n MTypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v' loc2 | MTValue Types \<Rightarrow> False))"
            and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
        then have a40:"(\<forall>i<x. case accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False 
                            | Some (MValue val) \<Rightarrow> (case t of  MTValue typ \<Rightarrow> MCon t v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
                            | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v' loc2 | MTValue Types \<Rightarrow> False))" 
          using 2 by fastforce
        have a55:"(\<exists>p. accessStore destl v' = Some (MPointer p)) \<or> accessStore destl v' = None" 
          using mdef minitSingleChange2[OF a10] unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by fastforce

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
            proof(cases t)
              case mtr:(MTArray x11 x12)
              then have b10:"MCon t v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<and> 
                          (\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
                using MTArray a30 minitRec_SubPrefixes agt by blast
              then have b15:"(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) 
                              \<and> \<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) 
                              \<longrightarrow> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'')" by simp
              have " (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq>  (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using True 
                by (metis Read_Show_nat'_id less_irrefl_nat)
              then have b16:"hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
                by (simp add: hash_never_equal_sufix)
              have b17:"\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using ShowLNatDot hash_int_prefix b16 by simp
              have b18:"\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using ShowLNatDot hash_int_prefix b16 by simp
              have b19:"\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v''" 
                using b10 by auto
              have accessSt:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))  v'  = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))  v''" 
                by (simp add: b15 b16 b17)
              then obtain val where valdef:" accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer val)" 
                using MConArrayPointers[of x x11 x12 v' destl i] a40 MCondestl True mtr by auto
              have "Suc x - 1 = x" by simp
              then have subPref:"TypedMemSubPref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl (MTArray x t)" 
                using  MConIndexMin1[of "Suc x" t ]  True by auto
              then have b30:"( \<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)" 
                using minitSelfPointers a10 by blast
              then have valeq:"val = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using True valdef subPref by simp
              then have b20:"MCon t v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))"  using a40  mtr True valdef by fastforce 
              then have " \<forall>l l'. TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l" 
                using b30 moreSpecificTypedSubPref[of destl x t v' ] True by blast
              then have "MCon t v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MCon_mem_preserved_disjoint_update[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"  t v' v'' ] a10 b17 b18 b20 b19 by blast
              then show ?thesis using accessSt valdef mtr valeq by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5))
            next
              case (MTValue x2)
              then have b10:"MCon t v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<and>
                          (\<forall>destl'. \<not> LSubPrefL2 destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
                using MTArray a30 minitRec_SubPrefixes agt by blast
              then have b15:"(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) 
                              \<and> \<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) 
                              \<longrightarrow> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'')" by simp
              have " (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq>  (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using True 
                by (metis Read_Show_nat'_id less_irrefl_nat)
              then have b16:"hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
                by (simp add: hash_never_equal_sufix)

              have b17:"\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using ShowLNatDot hash_int_prefix b16 by simp
              have b18:"\<not> LSubPrefL2 (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using ShowLNatDot hash_int_prefix b16 by simp
              have b20:"MCon t v' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a40  MTValue True by (auto split:option.splits memoryvalue.splits mtypes.splits)
              then have "MCon t v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MCon_mem_preserved_disjoint_update[of "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" "hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" t v' v''] using MTValue b10 b17 b18 by simp
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
            proof(cases t)
              case mtr:(MTArray x11 x12)
              then have b25:"v'' = (let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v' 
                              in iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12) m x11)"
                using a30 minitRec.simps(1)[of " (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12] by simp
              have mc:"MCon t v'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using MTArray[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] a30 agt by simp
              then obtain m' where b30:"m' = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v'" by auto
              then have b40:"v'' = iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12) m' x11" using b25 by metis
              have b50:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))" using b30 iIsx 
                unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
                by auto
              have "\<forall>suffs. hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) suffs \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using hash_inequality by simp
              then have b60:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' =  accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' " 
                using  b40  iIsx 
                by (metis minitSingleChange2)

              then show ?thesis using b50 b60 mtr mc by simp 
            next
              case (MTValue x2)
              then have b10:"v'' = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue (ival x2)) (MTValue x2) v'"
                using a30 minitRec.simps(2)[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2] by simp
              then have b40:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some ((MValue (ival x2)))" 
                using iIsx unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
              then have "typeCon x2 (ival x2)" 
                using ivalTypeCon by auto
              then show ?thesis  using iIsx MTValue iless MCon.simps(1) b40 by simp
            qed
          qed
        qed
      qed

      moreover have "(\<exists>p. accessStore destl v''' = Some (MPointer p)) \<or> accessStore destl v''' = None" 

        using "**" accessStore_updateStore minitRec.simps(1) minitSingleChange2
        unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
        by (metis (lifting) store.select_convs(1) typedstore.surjective typedstore.update_convs(1) minitRec.simps(1) updateStore_def updateTypeStore_def
            updateTypedStore_def)
      ultimately show ?thesis using MCon.simps(2)[of x1 t v''' destl]  by (simp add: True)
    next
      case False
      then show ?thesis using ***  by simp
    qed
  qed
next
  case (MTValue x)
  then show ?case
  proof intros
    assume ***:"minitRec destl (MTValue x) a = v'''"
      and *:"arraysGreaterZero (MTValue x)"
    have v''Def:"updateTypedStore destl (MValue (ival x)) (MTValue x) a = v'''" using *** unfolding minitRec.simps by simp
    moreover have "accessStore destl v''' = Some (MValue (ival x))" using calculation
      unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by auto
    moreover have "typeCon x (ival x)" 
      by (simp add: ivalTypeCon)
    ultimately show "MCon (MTValue x) v''' destl" unfolding MCon.simps
      using  v''Def by (auto split:option.splits memoryvalue.splits)
  qed
qed

lemma MConMinit: 
  assumes "iter (\<lambda>i m''. minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') md x = updM"
    and "accessStore (ld) md = None"
    and "arraysGreaterZero (MTArray x t)"
  shows " MCon (MTArray x t) updM ld" using assms(2,3) 
proof(induction rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10:"iter (\<lambda>i. minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) md x = v'"
      and a20:"(accessStore ld md = None \<longrightarrow> arraysGreaterZero (MTArray x t) \<longrightarrow> MCon (MTArray x t) v' ld)"
      and a30:"minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast

  have sameACC:" (\<forall>destl'. \<not> LSubPrefL2 destl' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore destl' v' = accessStore destl' v'')" 
    using minitRec_SubPrefixes a30 by blast
  then have "accessStore ld v' = accessStore ld v''" 
    using a30 
    by (metis LSubPrefL2_def hash_inequality hash_suffixes_associative)


  then have ld:"(\<exists>p. accessStore (ld) v'' = Some (MPointer p)) \<or> accessStore (ld) v'' = None" 
  proof(cases "x =0")
    case True
    then have v'MD:"v' = md" using a10 by auto
    then have "minitRec (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t md = v''" using a30 by blast
    then have "accessStore ld md = accessStore ld v''" 
      using v'MD using \<open>accessStore ld v' = accessStore ld v''\<close> by blast
    then show ?thesis using assms(2) by simp
  next
    case False
    then have "arraysGreaterZero (MTArray x t)" using 2(4) by simp
    then have "MCon (MTArray x t) v' ld" using a20 2 False by blast
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
        then have "arraysGreaterZero (MTArray x t)" using 2(4) by simp
        then have b10: "MCon (MTArray x t) v' ld" using a20 2
          using True by fastforce
        then obtain loc2 where l2Def:"accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' =  Some (MPointer loc2)"
          using True MCon.simps(2) MTArray MConArrayPointers
          by meson 
        have b50:"\<not> LSubPrefL2 (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using True 
          by (metis Read_Show_nat'_id ShowLNatDot hash_int_prefix hash_never_equal_sufix nat_neq_iff)
        have b60:" \<not> LSubPrefL2 (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using True 
          using b50 ShowLNatDot hash_int_prefix by force
        then have b65:"accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" 
          using minitRec_SubPrefixes a30 b50 by blast
        then have "accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' =  Some (MPointer loc2)" using l2Def by simp
        have b70:" (\<forall>l l'. TypedMemSubPref l ld  (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)" 
          using minitSelfPointers a10 by blast
        have "\<forall>i<x. case accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False 
                | Some (MValue val) \<Rightarrow> (case t of MTArray n MTypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t v' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v' loc2 | MTValue Types \<Rightarrow> False)" 
          using b10 by auto
        then have b80:"MCon t v' loc2" using b10 MCon.simps(2)[of x t v' ld] True l2Def MTArray True 
          by fastforce
        have "TypedMemSubPref (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) ld (MTArray x t)" 
          using True by auto
        then have loc2Same:"loc2 = (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using b70 l2Def by metis
        then have "MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MCon_mem_preserved_disjoint_update[of "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "t" v' v''] b50 b60 b70 b80 b65
          using True a30 minitRec_SubPrefixes TypedMemSubPref.simps(2) by blast
        moreover have "accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' =  Some (MPointer loc2)" using b65 l2Def by auto
        ultimately show ?thesis using MTArray True loc2Same by (auto split:memoryvalue.splits option.splits mtypes.splits)
      next
        case False
        then have iIsx:"i = x" using * by auto
        have "arraysGreaterZero t" using 2(4) by simp
        then have MCON:"MCon t v'' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
          using minitRecMCon[of "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] a30 iIsx by simp
        have v''Def:" (let m = updateTypedStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v' 
                        in iter (\<lambda>i. minitRec (hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12) m x11) 
                          = v''" 
          using a30 minitRec.simps(1)[of "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12]  iIsx
          by (simp add: MTArray)
        then obtain m where mDef:"m = updateTypedStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v'" by simp
        then have v''Def:"v'' = iter (\<lambda>i. minitRec (hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12) m x11" 
          using v''Def by presburger
        have "(\<forall>suffix. hash (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) suffix \<noteq> hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using hash_inequality by simp
        then have "accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) m = accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v''" 
          using minitSingleChange2 v''Def by blast 
        then have "accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some (MPointer (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)))" 
          using iIsx mDef unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
        then show ?thesis using MCON MTArray iIsx by (auto split:memoryvalue.splits option.splits mtypes.splits)
      qed
    next
      case (MTValue x2)
      then show ?thesis 
      proof(cases "i<x")
        case True
        then have "arraysGreaterZero (MTArray x t)" using 2(4) by simp
        then have "MCon (MTArray x t)  v' ld" using a20 2 
          using True by blast
        then have MCON:"case accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False 
              | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v' (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
              | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v' loc2 | MTValue Types \<Rightarrow> False)" 
          using True MCon.simps(2)[of "x" t v' ld] 
          by simp
        then obtain v where vdef:"accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MValue v)" 
          using True MTValue by (auto split:option.splits memoryvalue.splits mtypes.splits)
        then have tc:"typeCon x2 v" using  MCon.simps vdef True MTValue MCON by auto
        have b10:"(ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using True 
          by (simp add: Read_Show_nat'_id readLintNotEqual)
        then have b20:"(\<forall>x'. (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) x')" using True 
          by (metis LSubPrefL2_def hash_inequality ShowLNatDot hash_int_prefix hash_suffixes_associative)
        then have "accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" 
          using a30 b10 MTValue accessStore_non_changed hash_never_equal_sufix minitRec.simps(2)
          using ShowLNatDot hash_int_prefix sameACC by presburger
        then have v''Store:"accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some (MValue v)" 
          using vdef by simp
        then show ?thesis using  MCon.simps vdef True  MTValue v''Store tc by auto
      next
        case False

        then have iIsx: "i = x" using * by simp
        have sv'':"v'' = updateTypedStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue (ival x2)) (MTValue x2) v'" 
          using minitRec.simps(2)[of "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2] a30 MTValue by simp
        then have v''Store:"accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some (MValue (ival x2))" 
          using sv'' iIsx unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def 
          by (auto split:option.splits memoryvalue.splits mtypes.splits)
        have "typeCon x2 ((ival x2))" 
          by (simp add: ivalTypeCon)
        then show ?thesis using  MCon.simps iIsx  MTValue v''Store by auto
      qed
    qed
  qed
  then show ?case using MCon.simps(2)[of "Suc x" t v'' "(hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t x))"] ld by simp
qed

lemma minitRecSomeOldNew:
  shows "minitRec destl t destm = v' 
          \<longrightarrow> (\<forall>l. (TypedMemSubPref l destl t \<or> l = destl) \<longrightarrow> accessStore l destm = None)
          \<longrightarrow>  (\<forall>l accx. accessStore l destm = Some accx \<longrightarrow> accessStore l v' = Some accx)"
proof(induction t arbitrary: destl destm v')
  case (MTArray x1 t)
  show ?case
  proof intros
    fix l accx
    assume *:"minitRec destl (MTArray x1 t) destm = v'"
      and ***:"\<forall>l. TypedMemSubPref l destl (MTArray x1 t) \<or> l = destl \<longrightarrow> accessStore l destm = None"
      and **:"accessStore l destm = Some accx "
    have a10:"v' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) destm in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1)"
      using * minitRec.simps(1)[of destl x1 t ] by simp
    then obtain m where a40:"m = updateTypedStore destl (MPointer destl) (MTArray x1 t) destm" by auto
    then have a45:"accessStore destl m = Some(MPointer destl)" unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then have a50:"v' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" using a10 a40 by presburger
    show "accessStore l v' = Some accx" using a45 ** ***
    proof(induction rule: iter_ind[OF _ _ a50[symmetric]])
      case (1)
      then show ?case
        by (metis "***" a40 minitRec.simps(1) minitRec_SubPrefixes2 minitSingleChange2 option.distinct(1))
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
          and a20:"(accessStore destl m = Some (MPointer destl) \<longrightarrow>
          accessStore l destm = Some accx \<longrightarrow>
          (\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<or> l = destl \<longrightarrow> accessStore l destm = None) \<longrightarrow> accessStore l v' = Some accx)"
          and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by metis
      then have "accessStore destl m = Some (MPointer destl)" using 2 by blast
      then show ?case 
      proof(cases "l = destl")
        case True
        then show ?thesis using a20 2 
          by fastforce
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
            using * a30 by (meson minitRec_SubPrefixes)
          then show ?thesis using a20 2 using True 
            by (metis less_Suc_eq TypedMemSubPref.simps(2))
        next
          case False
          have b10:"accessStore l destm = Some accx" using 2(4) by auto

          then show ?thesis 
            by (metis "2.IH" "2.prems"(3) TypedMemSubPref.simps(2) a45 less_Suc_eq minitRec_SubPrefixes2 option.distinct(1))
        qed
      qed
    qed
  qed
next
  case (MTValue x)
  then show ?case 
  proof intros
    fix l accx
    assume *:"minitRec destl (MTValue x) destm = v'" 
      and ***:"\<forall>l. TypedMemSubPref l destl (MTValue x) \<or> l = destl \<longrightarrow> accessStore l destm = None"
      and **:" accessStore l destm = Some accx"
    have "v' = updateTypedStore destl (MValue (ival x)) (MTValue x) destm" 
      using minitRec.simps(2)[of destl x ] * by simp
    then obtain v where b10: "accessStore destl v' = Some (MValue v)" 
      unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
      by (auto split:option.splits memoryvalue.splits)
    show "accessStore l v' = Some accx"  
      by (metis "*" "**" "***" is_none_code(2) is_none_simps(1) minitRec_SubPrefixes2)
  qed
qed


lemma minitSomeOldNew:
  assumes "iter (\<lambda>i m''. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x1 = v'"
    and "\<forall>l. (TypedMemSubPref l destl (MTArray x1 t) \<or> l = destl) \<longrightarrow> accessStore l m = None"
  shows "(\<forall>l accx. accessStore l m = Some accx \<longrightarrow> accessStore l v' = Some accx)" using assms(2)
proof(induction  rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20: "((\<forall>l. TypedMemSubPref l destl (MTArray x t) \<or> l = destl \<longrightarrow> accessStore l m = None) \<longrightarrow>
          (\<forall>l accx. accessStore l m = Some accx \<longrightarrow> accessStore l v' = Some accx))"
      and a30: "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by metis
  show ?case 
  proof intros
    fix l accx
    assume *:"accessStore l m = Some accx "
    show "accessStore l v'' = Some accx"
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
          using * minitRec_SubPrefixes a30 by blast
        then show ?thesis using a20 True *  b50 
          using a10 
          by (metis "2.prems" less_Suc_eq TypedMemSubPref.simps(2))
      next
        case False
        have "\<forall>l. TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<longrightarrow> \<not> TypedMemSubPref l destl (MTArray x t)"
          by (smt (verit) LSubPrefL2_def TypedMemSubPref.simps(2) hash_flatten_right hashesInts nat_neq_iff
              neg_MemLSubPrefL2_imps_TypedMemSubPref)
        then have cc1:"\<forall>l . TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<longrightarrow> accessStore l m = accessStore l v'" 
          using minitSingleChange2[OF a10] by blast
        then have cc2:"(\<forall>l. TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> l = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<longrightarrow> accessStore l v' = None)"
          using 2(3) MTArray 
          by (metis lessI TypedMemSubPref.simps(2))
        have cc3:"(\<forall>l accx. accessStore l v' = Some accx \<longrightarrow> accessStore l v'' = Some accx)"
          using a30 minitRecSomeOldNew[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] cc2 by blast
        then have "accessStore l v' = Some accx" using * cc1 
          by (metis False a10 minitSingleChange2)
        then have "accessStore l v'' = Some accx" using cc3 by simp
        then show ?thesis by blast
      qed
    next
      case (MTValue x2)
      then have "v'' = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue (ival x2)) (MTValue x2) v'" 
        using a30 minitRec.simps(2)[of   "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 ] by simp
      then show ?thesis using  * 
        by (metis "2.hyps" "2.prems" minitSingleChange2 option.distinct(1))
    qed
  qed
qed

lemma minitRectoploc:
  shows "minitRec destl t destm = v'
          \<longrightarrow>  Toploc destm = Toploc v'"
proof(induction t arbitrary: destl destm v')
  case (MTArray x1 t)
  show ?case
  proof intros
    assume *:"minitRec destl (MTArray x1 t) destm = v'"
    have a10:"v' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) destm in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1)"
      using * minitRec.simps(1)[of destl x1 t ] by simp
    then obtain m where a40:"m =  updateTypedStore destl (MPointer destl) (MTArray x1 t) destm" by auto
    then have a45:"accessStore destl m = Some(MPointer destl)" unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    have a46:"Toploc destm = Toploc m" using a40 unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then have a50:"v' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" using a10 a40 by presburger
    show "Toploc destm = Toploc v'" using a46
    proof(induction rule: iter_ind[OF _ _ a50[symmetric]])
      case (1)
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
          and a20:"(Toploc destm = Toploc m \<longrightarrow> Toploc destm = Toploc v')"
          and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
      then have "Toploc destm = Toploc v'" using 2 by blast
      then show ?case 
        by (metis "2.IH" MTArray a46)
    qed
  qed
next
  case (MTValue x)
  then show ?case 
  proof intros
    fix l l' st
    assume *:"minitRec destl (MTValue x) destm = v'" 

    have "v' = updateTypedStore destl (MValue (ival x)) (MTValue x) destm" 
      using minitRec.simps(2)[of destl x ] * by simp
    then show "Toploc destm = Toploc v'" unfolding updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
  qed
qed

lemma minitToploc:
  assumes "iter (\<lambda>i m''. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x1 = v'"
  shows "Toploc m = Toploc v'"
proof(induction  rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by fastforce
next
  case (2 x v'')
  then obtain v'
    where a10: "iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20: " Toploc m = Toploc v'"
      and a30: "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
  then show ?case using minitRectoploc by metis
qed



lemma minit_TypeCompChangeIndexs:
  assumes "iter (\<lambda>i m''. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x1 = v'"
  shows "\<forall>i<x1. accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some t"
proof (rule iter_indexed_type_writes[
    where loc = "\<lambda>i. hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)" and tp = t, OF assms])
  fix i j v1 v2
  assume j_less: "j < i"
    and step: "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t v1 = v2"
  show "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t j)) v2 =
      accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t j)) v1"
    using j_less step
    by (metis ShowLNatDot hash_int_prefix hashesIntSame minitRec_SubPrefixes_typed nat_neq_iff)
next
  fix i v1 v2
  assume step: "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t v1 = v2"
  show "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v2 = Some t"
  proof (cases t)
    case (MTArray x11 x12)
    have step_arr:
      "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (MTArray x11 x12) v1 = v2"
      using step MTArray by simp
    from minitRec_array_root_both[OF step_arr]
    show ?thesis 
      using MTArray by force
  next
    case (MTValue x2)
    then show ?thesis
      using step minitRec.simps(2) by force
  qed
qed


lemma minitRec_TypeCompChange:
  "minitRec destl tp a = v''' \<longrightarrow>
  (\<forall>destl'. 
TypedMemSubPref destl' destl tp \<longrightarrow> 
  (case tp of MTValue val \<Rightarrow> accessTypeStore destl v''' = Some tp
      | MTArray x' t' \<Rightarrow> (\<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
                          (case t'' of MTArray parent_len parent_arr \<Rightarrow> 
                              \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                           | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
                        )))"
proof(induction tp arbitrary:destl a v''' )
  case (MTArray x1 t)
  show ?case
  proof intros 
    fix destl'
    assume **:"minitRec destl (MTArray x1 t) a = v'''"
      and ***:"TypedMemSubPref destl' destl (MTArray x1 t)"
    have a5:"(let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a 
                      in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1) = v'''" 
      using **  minitRec.simps(1)[of destl x1 t ] by simp
    then obtain m where mdef:"updateTypedStore destl (MPointer destl) (MTArray x1 t) a = m" by auto

    then have v''def:"v''' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" 
      using a5 mdef by metis 
    have "\<exists>t''. CompMemType v''' x1 t t'' destl destl' \<and>
               (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))" 
      using ***
    proof(induction rule: iter_ind[OF _ _ v''def[symmetric]]) 
      case (1)
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
          and a20:"(TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
            (\<exists>t''. CompMemType v' x t t'' destl destl' \<and>
                   (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
                    | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval))))"
          and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
      then show ?case 
      proof(cases "destl' = destl")
        case True
        then show ?thesis using 2 
          by (metis accessStore_updateStore hash_inequality minitSelfPointers minitSingleChange2)
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
            using minitRec_SubPrefixes2_typed[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] a30 
            by (meson ShowLNatDot f1 hash_injective)
          obtain t'' where i2:"(CompMemType v' x t t'' destl destl' \<and>
             (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval)))"
            using True a20 by blast

          have i5:"\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
            using a30 minitRec_SubPrefixes by blast
          moreover have i6:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
            by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
                nat_neq_iff typedPrefix_imp_SubPref)
          ultimately have i7:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" by auto
          have i8:"\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l" 
            using minitSelfPointers[OF a10] by blast

          show ?thesis
          proof(cases t'')
            case (MTArray x11 x12)
            then have cc0:"CompMemType v' x t (MTArray x11 x12) destl destl' \<and> (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some x12)" 
              using i2 by simp
            then have "CompMemType v'' x t (MTArray x11 x12) destl destl' \<and> (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12)"
              using CompMemType_preservation_induction[OF i5 i6 i7 cc0 i8] 
              by (smt (verit, ccfv_threshold) LSubPrefL2_def True TypedMemSubPref.simps(2) a30 hash_flatten_right hashesInts i6 minitRec_SubPrefixes_typed
                  typedPrefix_imp_SubPref)
            then show ?thesis  using CompMemType_extend2 by force
          next
            case (MTValue x2)
            then have cc0:"accessTypeStore destl' v' = Some (MTValue x2) \<and> CompMemType v' x t (MTValue x2) destl destl'" using i2 by simp
            then have "CompMemType v'' x t (MTValue x2) destl destl' \<and> accessTypeStore destl' v'' = Some (MTValue x2)"
              using CompMemTypeValue_preservation_induction[OF i5 i6 i7 cc0 i8] 
              using True a30 i6 minitRec_SubPrefixes_typed by blast
            then show ?thesis using CompMemType_extend by fastforce
          qed 

        next
          case False
          then have b5:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
            using 2 TypedMemSubPref.simps(2)[of destl' destl "(Suc x)" t] f1 
            using less_Suc_eq 
            by (metis TypedMemSubPref.simps(2))
          then have "accessTypeStore destl' m = accessTypeStore destl' v'" 
            using False a10 minitSingleChange2_typed by blast
          then have "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" using a30 by simp
          then have IH1:"(TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
          (case t of
           MTArray x' t' \<Rightarrow>
             \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
                   (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
                    | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
           | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t))" 
            using MTArray.IH[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] by simp

          have "\<exists>t''. CompMemType v'' (Suc x) t t'' destl destl' \<and>
            (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))" 
	          proof(cases "t")
	            case (MTArray x11 x12)
	            have step_arr:
	              "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12) v' = v''"
	              using a30 MTArray by simp
	            have v''Def:
	              "v'' = iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12)
	                (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))
	                  (MTArray x11 x12) v') x11"
	              using step_arr unfolding Let_def minitRec.simps(1) by blast
	            have root_bundle:
	              "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 x12)
	                \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	              using minitRec_array_root_both[OF step_arr] by simp
	            then show ?thesis 
	            proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	              case True
	              then have "CompMemType v'' (Suc x) t t destl destl'" 
	                using MTArray root_bundle by auto
	              moreover have "\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12" 
	                using minit_TypeCompChangeIndexs[OF v''Def[symmetric]] True by auto
	              ultimately show ?thesis using MTArray by force
	            next
	              case False
              then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using b5 by auto
	              then have "\<exists>t''. CompMemType v'' x11 x12 t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
	               (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
	                | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))" 
	                using IH1 MTArray by simp
	              then show ?thesis using MTArray root_bundle by auto
	            qed
	          next
            case (MTValue x2)
            then show ?thesis 
              using IH1 b5 by auto
          qed

          then show ?thesis by blast         
        qed
      qed
    qed
    then show "case MTArray x1 t of
       MTArray x' t' \<Rightarrow>
         \<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
               (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
       | MTValue val \<Rightarrow> accessTypeStore destl v''' = Some (MTArray x1 t)" by auto
  qed
next
  case (MTValue x)
  show ?case 
  proof intros
    fix destl'
    assume **:" minitRec destl (MTValue x) a = v'''"
    assume ***:"TypedMemSubPref destl' destl (MTValue x)"
    then have mdef:"v''' = updateTypedStore destl (MValue (ival x)) (MTValue x) a" 
      using ** minitRec.simps(2)[of destl x] by simp
    then have "accessTypeStore destl v''' = Some (MTValue x)" 
      unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then show "case MTValue x of
       MTArray x' t' \<Rightarrow>
         \<exists>t''. CompMemType v''' x' t' t'' destl destl' \<and>
               (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''' = Some parent_arr
                | MTValue pval \<Rightarrow> accessTypeStore destl' v''' = Some (MTValue pval))
       | MTValue val \<Rightarrow> accessTypeStore destl v''' = Some (MTValue x)" by simp
  qed
qed

lemma minit_TypeCompChange:
  assumes "iter (\<lambda>i m''. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x1 = v'"
  shows "(\<forall>destl'. TypedMemSubPref destl' destl (MTArray x1 t) \<longrightarrow> 
          (\<exists>st. CompMemType v' x1 t st destl destl' \<and>
            (case st of MTArray parent_len parent_arr \<Rightarrow> 
              \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval))))"
proof(induction  rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20: "(\<forall>destl'.
             TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
             (\<exists>st. CompMemType v' x t st destl destl' \<and>
                   (case st of
                    MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
                    | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval))))"
      and a30: "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast

  show ?case 
  proof intros
    fix destl' 
    assume a1:"TypedMemSubPref destl' destl (MTArray (Suc x) t)" 
    show "\<exists>st. CompMemType v'' (Suc x) t st destl destl' \<and>
            (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))"
    proof(cases "TypedMemSubPref destl' destl (MTArray x t)")
      case True
      then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"  using True
        by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
      moreover have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using True 
        by (smt (verit, ccfv_threshold) LSubPrefL2_def ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesInts nat_neq_iff
            neg_MemLSubPrefL2_imps_TypedMemSubPref)
      ultimately have i1:"\<forall>destl'. destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> \<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        accessTypeStore destl' v' = accessTypeStore destl' v''" 
        using minitRec_SubPrefixes2_typed[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] a30 by simp
      obtain st where i2:"(CompMemType v' x t st destl destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> 
                \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' v' = Some (MTValue pval)))" using True a20 by blast

      have self_pointers: "\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
        using minitSelfPointers[OF a10] by blast



      have store_preserved: "\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
        using a30 minitRec_SubPrefixes by blast
      moreover have no_prefix_conflict: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
        by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
            nat_neq_iff typedPrefix_imp_SubPref)
      ultimately have store_consistency: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" by auto
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
      then have a2:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
        using a1 unfolding TypedMemSubPref.simps 
        using less_SucE by blast
	      then show ?thesis 
	      proof(cases t)
	        case (MTArray x11 x12)
	        have step_arr:
	          "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12) v' = v''"
	          using a30 MTArray by simp
	        have v''Def:
	          "v'' = iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12)
	            (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))
	              (MTArray x11 x12) v') x11"
	          using step_arr unfolding Let_def  minitRec.simps(1) by blast
	        have root_bundle:
	          "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 x12)
	            \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	          using minitRec_array_root_both[OF step_arr] by simp
	        then show ?thesis
	        proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	          case True
	          then have "\<forall>i<x11. TypedMemSubPref (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12)" by auto
	          then have "\<forall>i<x11. accessTypeStore (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12"
	            using minit_TypeCompChangeIndexs[OF v''Def[symmetric]] by blast
	          moreover have "CompMemType v'' (Suc x) (MTArray x11 x12) (MTArray x11 x12) destl destl'"
	            using MTArray True root_bundle unfolding CompMemType.simps by blast
	          ultimately show ?thesis
	            using MTArray True root_bundle by force
	        next
	          case False
	          then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using a2 by blast
          then have "(case t of
         MTArray x' t' \<Rightarrow>
           \<exists>t''. CompMemType v'' x' t' t'' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) destl' \<and>
                 (case t'' of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some parent_arr
	                  | MTValue pval \<Rightarrow> accessTypeStore destl' v'' = Some (MTValue pval))
	         | MTValue val \<Rightarrow> accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some t)" 
	            using minitRec_TypeCompChange[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] a30 by simp
	          then show ?thesis using MTArray root_bundle by auto
	        qed
	      next
	        case (MTValue x2)
        then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using a2 by simp
        then have "updateTypedStore destl' (MValue (ival x2)) (MTValue x2) v' = v''"
          using a30 minitRec.simps(2)[of destl' x2] MTValue by simp
        then show ?thesis unfolding updateTypeStore_def updateTypedStore_def accessTypeStore_def updateStore_def using MTValue  
          using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> accessTypeStore_def by auto
      qed
    qed
  qed
qed

lemma minitRec_somesome:
  "minitRec destl tp a = v''' \<longrightarrow>
  (\<forall>destl'. TypedMemSubPref destl' destl tp \<longrightarrow> ((\<exists>t. accessStore destl' v''' = Some t) 
      \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v''' = Some tt)))"
proof(induction tp arbitrary:destl a v''' )
  case (MTArray x1 t)
  show ?case
  proof intros 
    fix destl'
    assume **:"minitRec destl (MTArray x1 t) a = v'''"
      and ***:"TypedMemSubPref destl' destl (MTArray x1 t)"
    have a5:"(let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a 
                      in iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1) = v'''" 
      using **  minitRec.simps(1)[of destl x1 t ] by simp
    then obtain m where mdef:"updateTypedStore destl (MPointer destl) (MTArray x1 t) a = m" by auto

    then have v''def:"v''' = iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x1" 
      using a5 mdef by metis 
    have "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)" 
      using ***
    proof(induction rule: iter_ind[OF _ _ v''def[symmetric]]) 
      case (1)
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
          and a20:"(TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
           (\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt))"
          and a30:"minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast
      then show ?case 
      proof(cases "destl' = destl")
        case True
        then show ?thesis using 2 
          by (metis accessStore_updateStore hash_inequality minitSelfPointers minitSingleChange2)
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
            using minitRec_SubPrefixes2_typed[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] a30 
            by (meson ShowLNatDot f1 hash_injective)
          have i2:"(\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt)"
            using True a20 by blast

          have i5:"\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
            using a30 minitRec_SubPrefixes by blast
          moreover have i6:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" 
            by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
                nat_neq_iff typedPrefix_imp_SubPref)
          ultimately have i7:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" by auto
          have i8:"\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l" 
            using minitSelfPointers[OF a10] by blast

          show ?thesis using i2 
            using True a30 i6 i7 minitRec_SubPrefixes_typed by auto
        next
          case False
          then have b5:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
            using 2 TypedMemSubPref.simps(2)[of destl' destl "(Suc x)" t] f1 
            using less_Suc_eq 
            by (metis TypedMemSubPref.simps(2))
          then have "accessTypeStore destl' m = accessTypeStore destl' v'" 
            using False a10 minitSingleChange2_typed by blast
          then have "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" using a30 by simp
          then have IH1:"(\<forall>destl'.
        TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        (\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt))" 
            using MTArray.IH[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] by simp

          have "(\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt)" 
	          proof(cases "t")
	            case (MTArray x11 x12)
	            have step_arr:
	              "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12) v' = v''"
	              using a30 MTArray by simp
	            have v''Def:
	              "v'' = iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12)
	                (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))
	                  (MTArray x11 x12) v') x11"
	              using step_arr unfolding Let_def minitRec.simps(1) by blast
	            have root_bundle:
	              "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 x12)
	                \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	              using minitRec_array_root_both[OF step_arr] by simp
	            then show ?thesis 
	            proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	              case True
	              then have "CompMemType v'' (Suc x) t t destl destl'" 
	                using MTArray root_bundle by auto
	              moreover have "\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12" 
	                using minit_TypeCompChangeIndexs[OF v''Def[symmetric]] True by auto
	              ultimately show ?thesis
	                using MTArray True root_bundle by auto
	            next
	              case False
	              then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using b5 by auto
	              then have "(\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt)" 
	                using IH1 MTArray by simp
	              then show ?thesis using MTArray root_bundle by auto
	            qed
	          next
	            case (MTValue x2)
            then show ?thesis 
              using IH1 b5 by auto
          qed

          then show ?thesis by blast         
        qed
      qed
    qed
    then show "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)" by auto
  qed
next
  case (MTValue x)
  show ?case 
  proof intros
    fix destl'
    assume **:" minitRec destl (MTValue x) a = v'''"
    assume ***:"TypedMemSubPref destl' destl (MTValue x)"
    then have mdef:"v''' = updateTypedStore destl (MValue (ival x)) (MTValue x) a" 
      using ** minitRec.simps(2)[of destl x] by simp
    then have "accessTypeStore destl v''' = Some (MTValue x)" 
      unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    then show "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)" 
      by (metis "***" MConAccessSame.simps(1) SameMCon_imps_MConAccessSame TypedMemSubPref.simps(1) arraysGreaterZero.simps(1) mdef
          minitRec.simps(2) minitRecMCon)
  qed
qed

lemma minit_TypeCompChange_somesome:
  assumes "iter (\<lambda>i m''. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t m'') m x1 = v'"
  shows "(\<forall>destl'. TypedMemSubPref destl' destl (MTArray x1 t) \<longrightarrow> 
          ((\<exists>t. accessStore destl' v' = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v' = Some tt)))"
proof(induction  rule: iter_ind[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter (\<lambda>i. minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x = v'"
      and a20: "(\<forall>destl'. TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
             ((\<exists>t. accessStore destl' v' = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v' = Some tt)))"
      and a30: "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t v' = v''" by blast

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
      ultimately have i1:"\<forall>destl'. destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> \<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        accessTypeStore destl' v' = accessTypeStore destl' v''" 
        using minitRec_SubPrefixes2_typed[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] a30 by simp
      have i2:"(\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt)" 
        using True a20 by blast

      have store_preserved: "\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
        using a30 minitRec_SubPrefixes by blast
      moreover have no_prefix_conflict: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
        by (smt (verit, best) LSubPrefL2_def TypedMemSubPref.simps(2) hash_suffixes_associative hashesInts
            nat_neq_iff typedPrefix_imp_SubPref)
      ultimately have store_consistency: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" 
        by auto

      show ?thesis using i2 
        using True \<open>\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t\<close> \<open>destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> i1 store_consistency by force

    next
      case False
      then have a2:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" 
        using a1 unfolding TypedMemSubPref.simps 
        using less_SucE by blast
	      then show ?thesis  
	      proof(cases t)
	        case (MTArray x11 x12)
	        have step_arr:
	          "minitRec (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12) v' = v''"
	          using a30 MTArray by simp
	        have v''Def:
	          "v'' = iter (\<lambda>i. minitRec (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12)
	            (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))
	              (MTArray x11 x12) v') x11"
	          using step_arr unfolding Let_def minitRec.simps(1) by blast
	        have root_bundle:
	          "accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MTArray x11 x12)
	            \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
	          using minitRec_array_root_both[OF step_arr] by simp
	        then show ?thesis
	        proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
	          case True
	          then have "\<forall>i<x11. TypedMemSubPref (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12)" by auto
	          then have "\<forall>i<x11. accessTypeStore (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12"
	            using minit_TypeCompChangeIndexs[OF v''Def[symmetric]] by blast
	          moreover have "CompMemType v'' (Suc x) (MTArray x11 x12) (MTArray x11 x12) destl destl'"
	            using MTArray True root_bundle unfolding CompMemType.simps by blast
	          ultimately show ?thesis
	            using MTArray True root_bundle by simp
	        next
	          case False
	          then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using a2 by blast
	          then have "(\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt)" 
	            using minitRec_somesome[of "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] a30 by simp
	          then show ?thesis using MTArray root_bundle by auto
	        qed
	      next
        case (MTValue x2)
        then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using a2 by simp
        then have "updateTypedStore destl' (MValue (ival x2)) (MTValue x2) v' = v''"
          using a30 minitRec.simps(2)[of destl' x2] MTValue by simp
        then show ?thesis unfolding updateTypeStore_def updateTypedStore_def accessTypeStore_def updateStore_def using MTValue  
          using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> accessTypeStore_def 
          by (metis TypedMemSubPref.simps(1) a30 minitRec_somesome)
      qed
    qed
  qed
qed



end
