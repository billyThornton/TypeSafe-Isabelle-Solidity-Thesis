theory TypeSafe_Support
   imports Solidity_Main

begin
(*iter' should be moved to the iter' definition file.*)
lemma iter'_induct:
  assumes "\<And>v'. iter' f v 0 = Some v' \<Longrightarrow> P 0 v'"
    "\<And>x v''. (\<exists>v'. iter' f v x = Some v' \<and> P x v' \<and> f x v' = Some v'') \<Longrightarrow> iter' f v (Suc x) = Some v'' \<Longrightarrow> P (Suc x) v''"
  shows "iter' f v x = Some v' \<Longrightarrow> P x v'"
  apply (induction x arbitrary: v') using assms apply blast
proof -
  fix x v'
  assume xx:"\<And>v'. iter' f v x = Some v' \<Longrightarrow> P x v'" and
    *: "iter' f v (Suc x) = Some v'"

  from * obtain v'' where "f (Suc x - 1) v'' = Some v'" and "iter' f v x = Some v''"
    using iter'.simps[of f v "Suc x"] by (auto split: option.split_asm)
  then have "f x v'' = Some v'" and "iter' f v x = Some v''" by simp+
  then show "P (Suc x) v'" using assms(2)[OF _ *] xx by simp
qed

lemma iter'_invariant:
  assumes run: "iter' f v x = Some v'"
    and init: "I v"
    and step: "\<And>i v1 v2. I v1 \<Longrightarrow> f i v1 = Some v2 \<Longrightarrow> I v2"
  shows "I v'"
proof -
  have "\<And>v''. iter' f v x = Some v'' \<Longrightarrow> I v''"
  proof (rule iter'_induct[where P = "\<lambda>_ v''. I v''"])
    fix v''
    assume "iter' f v 0 = Some v''"
    then have "v'' = v" by simp
    with init show "I v''" by simp
  next
    fix i v''
    assume "\<exists>v'. iter' f v i = Some v' \<and> I v' \<and> f i v' = Some v''"
    then obtain v1 where "I v1" and "f i v1 = Some v''" by blast
    then show "iter' f v (Suc i) = Some v'' \<Longrightarrow> I v''" using step by blast
  qed
  with run show ?thesis by simp
qed

lemma iter'_indexed_invariant:
  assumes run: "iter' f v x = Some v'"
    and init: "P 0 v"
    and step: "\<And>i v1 v2. P i v1 \<Longrightarrow> f i v1 = Some v2 \<Longrightarrow> P (Suc i) v2"
  shows "P x v'"
proof -
  have "\<And>v''. iter' f v x = Some v'' \<Longrightarrow> P x v''"
  proof (rule iter'_induct[where P = P])
    fix v''
    assume "iter' f v 0 = Some v''"
    then have "v'' = v" by simp
    with init show "P 0 v''" by simp
  next
    fix i v''
    assume "\<exists>v'. iter' f v i = Some v' \<and> P i v' \<and> f i v' = Some v''"
    then obtain v1 where "P i v1" and "f i v1 = Some v''" by blast
    then show "iter' f v (Suc i) = Some v'' \<Longrightarrow> P (Suc i) v''" using step by blast
  qed
  with run show ?thesis by simp
qed

lemma iter'_indexed_type_writes:
  fixes loc :: "nat \<Rightarrow> String.literal"
  assumes run: "iter' f v x = Some v'"
    and old: "\<And>i j v1 v2. j < i \<Longrightarrow> f i v1 = Some v2
      \<Longrightarrow> accessTypeStore (loc j) v2 = accessTypeStore (loc j) v1"
    and new: "\<And>i v1 v2. f i v1 = Some v2 \<Longrightarrow> accessTypeStore (loc i) v2 = Some tp"
  shows "\<forall>j<x. accessTypeStore (loc j) v' = Some tp"
proof (rule iter'_indexed_invariant[OF run, where P = "\<lambda>i m. \<forall>j<i. accessTypeStore (loc j) m = Some tp"])
  show "\<forall>j<0. accessTypeStore (loc j) v = Some tp" by simp
next
  fix i v1 v2
  assume IH: "\<forall>j<i. accessTypeStore (loc j) v1 = Some tp"
    and step: "f i v1 = Some v2"
  show "\<forall>j<Suc i. accessTypeStore (loc j) v2 = Some tp"
  proof (intro allI impI)
    fix j
    assume j_lt: "j < Suc i"
    show "accessTypeStore (loc j) v2 = Some tp"
    proof (cases "j < i")
      case True
      then have "accessTypeStore (loc j) v1 = Some tp"
        using IH by blast
      moreover have "accessTypeStore (loc j) v2 = accessTypeStore (loc j) v1"
        using old[OF True step] by simp
      ultimately show ?thesis
        by simp
    next
      case False
      then have "j = i"
        using j_lt by auto
      then show ?thesis
        using new[OF step] by simp
    qed
  qed
qed

lemma iter_ind:              
  assumes "iter f v 0 = v \<Longrightarrow> P 0 v"
    "\<And>x v''. (\<exists>v'. iter f v x = v' \<and> P x v' \<and> f x v' = v'') \<Longrightarrow> iter f v (Suc x) = v'' \<Longrightarrow> P (Suc x) v''"
  shows "iter f v x = v' \<Longrightarrow> P x v'" 
  apply (induction x arbitrary: v') using assms apply fastforce
proof -
  fix x v'
  assume xx:"\<And>v'. iter f v x = v' \<Longrightarrow> P x v'" and
    *: "iter f v (Suc x) = v'"

  from * obtain v'' where "f (Suc x-1) v'' = v'" and "iter f v x = v''" using iter.simps[of f v "Suc x"] by (auto split: option.split_asm)
  then have yy:"f x v'' = v'" and "iter f v x = v''" by simp+
  then show  "P (Suc x) v'" using assms(2)[OF _ *]  xx by blast
qed

lemma iter_indexed_type_writes:
  fixes loc :: "nat \<Rightarrow> String.literal"
  assumes run: "iter f v x = v'"
    and old: "\<And>i j v1 v2. j < i \<Longrightarrow> f i v1 = v2
      \<Longrightarrow> accessTypeStore (loc j) v2 = accessTypeStore (loc j) v1"
    and new: "\<And>i v1 v2. f i v1 = v2 \<Longrightarrow> accessTypeStore (loc i) v2 = Some tp"
  shows "\<forall>j<x. accessTypeStore (loc j) v' = Some tp"
proof (rule iter_ind[OF _ _ run])
  show "iter f v 0 = v \<Longrightarrow> \<forall>j<0. accessTypeStore (loc j) v = Some tp"
    by simp
next
  fix i v2
  assume "\<exists>v1. iter f v i = v1 \<and> (\<forall>j<i. accessTypeStore (loc j) v1 = Some tp) \<and> f i v1 = v2"
  then obtain v1 where IH: "\<forall>j<i. accessTypeStore (loc j) v1 = Some tp"
    and step: "f i v1 = v2" by blast
  show "iter f v (Suc i) = v2 \<Longrightarrow> \<forall>j<Suc i. accessTypeStore (loc j) v2 = Some tp"
  proof (intro allI impI)
    fix j
    assume j_lt: "j < Suc i"
    show "accessTypeStore (loc j) v2 = Some tp"
    proof (cases "j < i")
      case True
      then have "accessTypeStore (loc j) v1 = Some tp"
        using IH by blast
      moreover have "accessTypeStore (loc j) v2 = accessTypeStore (loc j) v1"
        using old[OF True step] by simp
      ultimately show ?thesis
        by simp
    next
      case False
      then have "j = i"
        using j_lt by auto
      then show ?thesis
        using new[OF step] by simp
    qed
  qed
qed

lemma updateTypedStore_root_type[simp]:
  "accessTypeStore loc (updateTypedStore loc v tp m) = Some tp"
  unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def
  by simp

end
