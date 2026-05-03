section\<open>Defining the properties of typesafe environments in Isabelle-Solidity\<close>
theory TypeSafe_Def
  imports TypeSafe_Memory TypeSafe_Storage

begin

subsection \<open>Ensuring unique locations\<close>
  (*
Checks a finite map (specifically denvalue) to ensure that the locations are all unique.
The number of unique store locations must equal the number of unique variable names.
*)
definition unique_locations :: "(String.literal, type \<times> denvalue) fmap \<Rightarrow> bool" where
  "unique_locations denval = (\<forall>x y. x |\<in>| fmran denval \<and> y |\<in>| fmran denval \<and> snd x = snd y \<longrightarrow> x = y)"


text \<open>Shows that if an enironement has unique locations and two elements are chosen from the denvalue
of which their locations are the same then they must be the same element.
This ensure that no duplicate variables with the same location can exist.\<close>
lemma uniqueLocs:
  assumes "unique_locations (Denvalue ev)"
    and "x |\<in>| fmran (Denvalue ev)"
    and "y |\<in>| fmran (Denvalue ev)"
    and "snd x = snd y"
  shows "x = y" using assms unique_locations_def by blast



subsubsection \<open>Pushing to the stack maintains stackLocations\<close>

lemma stackPushToplocSafe:
  assumes "lessThanTopLocs k"
    and "k' = push p k"
  shows "lessThanTopLocs k'" unfolding lessThanTopLocs_def
proof(intros)
  fix tloc loc
  assume **:"Toploc k' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  have a120:"Toploc k<Toploc k'" using assms by (simp add:push_def allocate_def updateStore_def accessStore_def)
  have a125:"tloc \<noteq> Toploc k" using "**" a120 by auto
  then have a126:"(ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))" 
    by (metis Read_Show_nat'_id)
  have a130:"\<forall>tloc loc. Toploc k \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc k = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp
  have a140:"k' = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) p k in snd (allocate s))" unfolding push_def assms(2) by auto
  then have acces:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) \<longrightarrow> accessStore locs k' = accessStore locs k" unfolding accessStore_def updateStore_def 
    by (simp add:push_def allocate_def updateStore_def accessStore_def split:if_split_asm)
  have a150:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) k = None" using a130 a120 ** 
    by (metis LSubPrefL2_def dual_order.strict_trans1 nless_le)
  then show "accessStore loc k' = None" 
  proof(cases "loc = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)")
    case True
    then show ?thesis using acces a150 a126 by simp
  next
    case False
    then show ?thesis using acces a150 a126  ShowLNatDot
      by (metis "**" LSubPrefL2_def a120 a130 hash_inequality hash_int_prefix hash_suffixes_associative nat_less_le order_less_le_trans)
  qed
next 
  fix loc y 
  assume *:"accessStore loc k' = Some y"
  have a140:"k' = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) p k in snd (allocate s))" unfolding push_def assms(2) by auto
  then have acces:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) \<longrightarrow> accessStore locs k' = accessStore locs k" unfolding accessStore_def updateStore_def 
    by (simp add:push_def allocate_def updateStore_def accessStore_def split:if_split_asm)
  have " \<exists>tloc<Toploc k'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  proof(cases "loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))")
    case True
    have a10:"Toploc k < Toploc k'" using a140 unfolding allocate_def updateStore_def by simp
    have "LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))" using True LSubPrefL2_def by simp
    have "\<forall>l. l\<noteq>(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) \<longrightarrow>  \<not>(LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) l)" using ShowLNatDot unfolding LSubPrefL2_def hash_def 
      using subPrefCannotBeInt by auto
    then show ?thesis using True a10 assms 
      using LSubPrefL2_def by auto
  next
    case False
    have "((\<forall>tloc loc. Toploc k \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc k = None) 
          \<and> (\<forall>loc y. accessStore loc k = Some y \<longrightarrow> (\<exists>tloc<Toploc k. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))" 
      using assms lessThanTopLocs_def[of k]  by blast
    then obtain tloc where  tlocdef:"tloc < Toploc k \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using False * acces by metis
    moreover have "Toploc k < Toploc k'" using a140 unfolding allocate_def updateStore_def by simp
    ultimately show ?thesis using assms lessThanTopLocs_def[of k] * tlocdef 
      using order.strict_trans by auto
  qed
  then show "\<exists>tloc<Toploc k'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" by simp
qed

lemma lessThanSome_imps_Locs:
  assumes "lessThanTopLocs mem"
    and "accessStore p' mem = Some y"
    and "LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  shows "x < Toploc mem"
proof(cases "p' = (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
  case True
  have a10:"\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp

  have a20:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t x) mem = Some y" using assms(2) True by simp
  have "ReadL\<^sub>n\<^sub>a\<^sub>t(ShowL\<^sub>n\<^sub>a\<^sub>t x) = x" using Read_Show_nat'_id by auto
  have "x < Toploc mem" using a10 a20 
    by (metis LSubPrefL2_def linorder_le_less_linear option.discI)
  then have "LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t x) (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> x < Toploc mem" unfolding LSubPrefL2_def by simp
  then show ?thesis using True by simp
next
  case False
  have a10:"\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp
  then obtain i where a20:"(p' = hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i)" using assms(3) False unfolding LSubPrefL2_def by blast
  then have a20:"accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i) mem = Some y" using assms(2) by simp
  have "x < Toploc mem" using a10 a20 
    by (metis LSubPrefL2_def linorder_le_less_linear option.discI)
  then show ?thesis by blast
qed

lemma lessThanSome_imps_Locs2:
  assumes "lessThanTopLocs mem"
    and " accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some y"
    and "LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  shows "x < Toploc mem"
proof(cases "p' = (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
  case True
  have a10:"\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp

  have a20:"accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some y" using assms(2) True by simp
  have "ReadL\<^sub>n\<^sub>a\<^sub>t(ShowL\<^sub>n\<^sub>a\<^sub>t x) = x" using Read_Show_nat'_id by auto
  have "x < Toploc mem" using a10 a20 
    by (metis LSubPrefL2_def True assms(1) lessThanSome_imps_Locs)
  then have "LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t x) (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> x < Toploc mem" unfolding LSubPrefL2_def by simp
  then show ?thesis using True by simp
next
  case False
  have a10:"\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None" 
    using assms(1) unfolding lessThanTopLocs_def by simp
  then obtain i' where a20:"(p' = hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i')" using assms(3) False unfolding LSubPrefL2_def by blast
  then have a20:"accessStore (hash (hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some y" using assms(2) by simp
  have "x < Toploc mem" using a10 a20 
    by (metis LSubPrefL2_def assms(1) hash_suffixes_associative lessThanSome_imps_Locs)
  then show ?thesis by blast
qed

lemma TS_imps_InDenLessStack2:
  assumes "MCon tp1 mem stl1"
    and "LSubPrefL2 stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
    and "(\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None)"
    and "(\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<longrightarrow> accessStore locs mem' = accessStore locs mem"
    and "\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<and> accessStore l mem' = Some (MPointer l') \<longrightarrow> l' = l"
    and "MCon tp2 mem' stl2"
  shows "\<not> TypedMemSubPrefPtrs mem' x11 x12 stl2 stl1" 
proof(cases x12)
  case (MTArray x11' x12')
  have "\<not> TypedMemSubPrefPtrs mem' x11 (MTArray x11' x12') stl2 stl1" unfolding TypedMemSubPrefPtrs.simps
  proof
    assume *:"\<exists>i<x11. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem' x11' x12' l stl1)"
    then obtain i l where idef:"i<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem' x11' x12' l stl1)" by blast
    then have lneq:"l \<noteq> stl1" using assms(1,2,4,5,6) 
      by (metis (no_types, opaque_lifting) LSubPrefL2_def MCon_imps_Some Option.option.simps(3) assms(3) Not_Sub_More_Specific verit_comp_simplify1(2))
    then have ldef:"l = (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using assms idef 
      by (metis LSubPrefL2_def hash_suffixes_associative)
    then have lsubloc:"LSubPrefL2  l  (ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem))" using assms
      using LSubPrefL2_def hash_suffixes_associative 
      by metis
    have lneq2:"\<forall>i<x11'. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" 
      by (metis (no_types, opaque_lifting) AllPtrsNotTop2 LSubPrefL2_def assms(1,3,4) Not_Sub_More_Specific le_refl lessThanTopLocs_def lsubloc)
    then have "TypedMemSubPrefPtrs mem' x11' x12' l stl1" using idef lneq by blast
    then show False using lneq2 lsubloc
    proof(induction x12' arbitrary:x11' l)
      case (MTArray x1 x12')
      have "\<exists>i'<x11'. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and>
         (l' = stl1 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' stl1)" 
        using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
      then obtain i' l' where i'def:"i'<x11' \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and> (l' = stl1 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' stl1)" by blast
      have "LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using MTArray.prems(3) 
        using LSubPrefL2_def hash_suffixes_associative by auto
      then have l'def:"l' = (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i'))" using i'def assms by blast
      then have l'neq:"l' \<noteq> stl1" using MTArray.prems(2) i'def by blast
      then have "TypedMemSubPrefPtrs mem' x1 x12' l' stl1" using i'def by simp
      moreover have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" using l'def l'neq 
        by (metis (no_types, opaque_lifting) LSubPrefL2_def MCon_imps_Some MTArray.prems(3) assms(1,3) Not_Sub_More_Specific less_not_refl option.distinct(1)
            verit_comp_simplify1(3))
      ultimately show ?case using MTArray.IH[of x1 l'] 
        by (simp add: \<open>LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))\<close> l'def)
    next
      case (MTValue x)
      then show ?case unfolding TypedMemSubPrefPtrs.simps by blast
    qed
  qed
  then show ?thesis using MTArray by simp
next
  case (MTValue x2)
  then show ?thesis 
    using AllPtrsNotTop2 SubPtrs_top assms(1,2,3,4,6) lessThanTopLocs_def by blast
qed

lemma TS_imps_InDenLessStack3:
  assumes "MCon (MTArray x11' x12') mem stl1"
    and "LSubPrefL2 stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
    and "(\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None)"
    and "(\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<longrightarrow> accessStore locs mem' = accessStore locs mem"
    and "\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<and> accessStore l mem' = Some (MPointer l') \<longrightarrow> l' = l"
    and "MCon tp2 mem' stl2"
  shows "\<not> TypedMemSubPrefPtrs mem' x11' x12' stl1 stl2" 
proof(cases x12')
  case (MTArray x11 x12)
  have "\<not> TypedMemSubPrefPtrs mem' x11' (MTArray x11 x12) stl1 stl2" unfolding TypedMemSubPrefPtrs.simps 
  proof
    assume *:"\<exists>i<x11'. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l) \<and> (l = stl2 \<or> TypedMemSubPrefPtrs mem' x11 x12 l stl2)"
    then obtain i l where idef:"i<x11' \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l) \<and> (l = stl2 \<or> TypedMemSubPrefPtrs mem' x11 x12 l stl2)" by blast
    have "\<not> LSubPrefL2 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using assms(1,2,3,4,5,6) LSubPrefL2_def 
      by (metis MConArrayPointers MTArray gr_zeroI idef le_refl less_nat_zero_code option.discI)
    then have mconl:"MCon (MTArray x11 x12) mem l" using assms(1,5) MTArray idef 
      by (metis MCon_imps_sub_Mcon)
    then have lneq:"l \<noteq> stl2" 
      using AllPtrsNotTop2 assms(2,3,4) lessThanTopLocs_def by blast
    then have lsubloc:"\<not> LSubPrefL2  l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using assms LSubPrefL2_def hash_suffixes_associative mconl idef 
      by (metis (no_types, lifting) MCon_imps_Some le_refl option.discI)
    have lneq2:"\<forall>i<x11. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl2" 

      using MemLSubPrefL2_specific_imps_general assms(2) lsubloc by blast
    then have "TypedMemSubPrefPtrs mem' x11 x12 l stl2" using idef lneq by blast
    then show False using lneq2 lsubloc mconl
    proof(induction x12 arbitrary:x11 l)
      case (MTArray x1 x12')
      have "\<exists>i'<x11. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and> (l' = stl2 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' stl2)" 
        using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
      then obtain i' l' where i'def:"i'<x11 \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and> (l' = stl2 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' stl2)" by blast
      then have mconl':"MCon (MTArray x1 x12')  mem l'" using assms(5) MTArray(5) 
        by (metis MCon_imps_sub_Mcon MTArray.prems(3) MemLSubPrefL2_specific_imps_general)
      then have l'neq:"l' \<noteq> stl2" 
        using AllPtrsNotTop2 assms(2,3,4) lessThanTopLocs_def by blast
      then have "TypedMemSubPrefPtrs mem' x1 x12' l' stl2" using i'def by simp
      then have l'subloc:"\<not> LSubPrefL2  l'  (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
        using AllPtrsNotTop2 assms(3,4) lessThanTopLocs_def mconl' by blast
      moreover have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl2" using l'subloc assms(2) 
        by (meson MemLSubPrefL2_specific_imps_general)
      ultimately show ?case using MTArray.IH[of x1 l'] i'def 
        using l'neq mconl' by blast
    next
      case (MTValue x)
      then show ?case unfolding TypedMemSubPrefPtrs.simps by blast
    qed
  qed
  then show ?thesis using MTArray by simp
next
  case (MTValue x2)
  then show ?thesis using assms(1) assms(2) assms(3) by fastforce
qed

lemma subPtrs_nonTop:
  assumes "MCon (MTArray x11' x12') mem stl1"
    and "(\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None)"
    and "(\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<longrightarrow> accessStore locs mem' = accessStore locs mem"
    and "TypedMemSubPrefPtrs mem' x11' x12' stl1 dloc1"
  shows "\<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" 
proof(cases x12')
  case (MTArray x11 x12)
  then obtain i l where idef:"i<x11' \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs mem' x11 x12 l dloc1)" 
    using assms by auto
  have "\<not> LSubPrefL2 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem))" using assms(1,2) LSubPrefL2_def 
    by (metis MConArrayPointers MTArray gr_zeroI idef le_refl less_nat_zero_code option.discI)
  then have mconl:"MCon (MTArray x11 x12) mem l" using assms(1,4) MTArray idef 
    by (metis MCon_imps_sub_Mcon)
  then have lsubloc:"\<not> LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using assms(2) LSubPrefL2_def hash_suffixes_associative mconl idef 
    by (metis (no_types, lifting) MCon_imps_Some le_refl option.discI)
  show ?thesis 
  proof
    assume *:"LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
    show False
    proof(cases "l = dloc1")
      case True
      then show ?thesis using "*" lsubloc by blast
    next
      case False
      then have lneq2:"\<forall>i<x11. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> dloc1" using mconl lsubloc idef assms(3,4)  
        using "*" MemLSubPrefL2_specific_imps_general by blast
      then have "TypedMemSubPrefPtrs mem' x11 x12 l dloc1" using idef False by blast
      then show ?thesis using lneq2 lsubloc mconl
      proof(induction x12 arbitrary:x11 l)
        case (MTArray x1 x12')
        have "\<exists>i'<x11. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' dloc1)" 
          using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
        then obtain i' l' where i'def:"i'<x11 \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' dloc1)" by blast
        then have mconl':"MCon (MTArray x1 x12')  mem l'" using assms(4) MTArray(5) 
          by (metis MCon_imps_sub_Mcon MTArray.prems(3) MemLSubPrefL2_specific_imps_general)
        have l'neq:"l' \<noteq> dloc1" 
          using "*" AllPtrsNotTop2 assms(2,3) lessThanTopLocs_def mconl' by blast
        then have "TypedMemSubPrefPtrs mem' x1 x12' l' dloc1" using i'def by simp
        then have l'subloc:"\<not> LSubPrefL2  l'  (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using l'neq assms i'def mconl' 
          using AllPtrsNotTop2 lessThanTopLocs_def by blast
        moreover have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> dloc1" using l'subloc 
          using "*" MemLSubPrefL2_specific_imps_general by blast
        ultimately show ?case using MTArray.IH[of x1 l'] i'def 
          using l'neq mconl' by blast
      next
        case (MTValue x)
        then show ?case by auto
      qed 
    qed
  qed
next
  case (MTValue x2)
  then show ?thesis using assms(1,2,5) by fastforce
qed

lemma PreExistMconNotChangeByToploc:
  assumes "(\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "(\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None)"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem)) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem)) \<longrightarrow> accessStore locs mem = accessStore locs m"
    and "MCon tp1 mem stl1"
  shows "MCon tp1 m stl1" using assms(4)
proof(induction tp1 arbitrary: stl1)
  case (MTArray x1 struct)
  then have accessSome:"\<forall>i'<x1. \<exists>y. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = Some y" 
    by (metis bot_nat_0.not_eq_extremum less_nat_zero_code mcon_accessStore)
  moreover have accessSame:"\<forall>i'<x1. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m" using calculation
    by (metis Read_Show_nat'_id antisym_conv1 assms(2,3) option.distinct(1) readLintNotEqual)

  have "\<forall>i<x1.
(case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False 
  | Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct m (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
  | Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct m loc2 | MTValue Types \<Rightarrow> False))"
  proof intros
    fix i' assume asm3:"i'<x1"
    show "case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m of None \<Rightarrow> False 
        | Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct m (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')))
        | Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct m loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases "accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m")
      case None
      then show ?thesis using accessSome accessSame asm3 by auto
    next
      case (Some a)
      then show ?thesis 
      proof(cases a)
        case (MValue x1')
        then show ?thesis using accessSome accessSame Some asm3 MTArray by (cases struct; auto)
      next
        case (MPointer x2)
        then have "MCon struct mem x2" using accessSome accessSame Some asm3 MTArray 
          by (metis MconSameTypeSameAccessWithTyping)
        then have "MCon struct m x2" using MTArray by simp
        then show ?thesis using accessSome accessSame Some asm3 MTArray MPointer by (cases struct; auto)
      qed
    qed
  qed
  moreover have "x1>0" using MTArray(2) unfolding MCon.simps by presburger
  moreover have "(\<exists>p. accessStore stl1 m = Some (MPointer p)) \<or> accessStore stl1 m = None" using calculation(3) MTArray unfolding MCon.simps 
    by (metis accessSome lessThanSome_imps_Locs2 lessThanTopLocs_def assms(1,2,3) nat_less_le )
  ultimately show ?case using MCon.simps(2)[of x1 struct m ] by simp
next
  case (MTValue x')
  then show ?case 
    by (metis MCon.simps(1) assms(2,3) case_optionE le_refl option.discI)
qed

subsection \<open>Balances and Svalues conform\<close>
definition balanceTypes :: "accounts \<Rightarrow> bool" where
  "balanceTypes acc = (\<forall>adv. typeCon (TUInt b256) (Bal (acc adv)))"

definition addressFormat::"address \<Rightarrow> bool"
  where "addressFormat cur = (typeCon TAddr cur)"

abbreviation envAddressesWellFormed :: "environment \<Rightarrow> bool" where
  "envAddressesWellFormed ev \<equiv> addressFormat (Address ev) \<and> addressFormat (Sender ev)"

definition svalueTypes :: "valuetype \<Rightarrow> bool" where
  "svalueTypes sval = typeCon (TUInt b256) sval"

subsection \<open>Compatiable pointers. \<close>



(*type of the parent, location of the parent, type of the subprefix, location of the subprefix*)
primrec Subpref :: "stypes \<Rightarrow> location \<Rightarrow> stypes \<Rightarrow> location \<Rightarrow> bool"
  where
    "Subpref (STValue typ) Modulatedparent typ2 subloc = ((Modulatedparent = subloc) \<and> typ2 = (STValue typ))"
  |"Subpref (STArray len arr) Modulatedparent typ2 subloc = (((STArray len arr) = typ2 \<and> Modulatedparent = subloc)
                                                        \<or> ( \<exists>i::nat. i < len \<and> Subpref arr (hash Modulatedparent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) typ2 subloc))"
  |"Subpref (STMap fromTyp toTyp) Modulatedparent typ2 subloc = (((STMap fromTyp toTyp) = typ2 \<and> Modulatedparent = subloc) 
                                                            \<or>(\<exists>i::String.literal. (typeCon fromTyp i) \<and> Subpref toTyp (hash Modulatedparent i) typ2 subloc))"


lemma  "\<not>Subpref  (STArray 3 (STValue TBool)) (STR ''1.5'') (STValue TBool) (STR ''4.1.5'')" using Subpref.simps hash_def by simp? eval
lemma  "Subpref  (STArray 5 (STValue TBool)) (STR ''1.5'') (STValue TBool) (STR ''1.1.5'')" using Subpref.simps hash_def by simp? eval
lemma  "Subpref (STArray 5 (STArray 4 (STArray 3 (STValue TBool)))) (STR ''1.5'') ((STValue TBool)) (STR ''1.1.1.1.5'') " using Subpref.simps hash_def by simp? eval
lemma  "Subpref (STArray 5 (STArray 4 (STArray 3 (STValue TBool)))) (STR ''1.5'') ((STArray 3 (STValue TBool))) (STR ''1.1.1.5'') " using Subpref.simps hash_def by simp? eval

lemma Subpref_strict_imps_hash_reachable:
  assumes "Subpref tp1 stl1 tp2 stl2"
    and "stl1 \<noteq> stl2"
  shows "\<exists>i. hash stl1 i = stl2"
  using assms
proof(induction tp1 arbitrary:stl1)
  case (STArray x1 tp1)
  then obtain i where idef:"(i < x1 \<and> Subpref tp1 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tp2 stl2)" by auto
  then show ?case
  proof(cases "(hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = stl2")
    case True
    then show ?thesis using idef by auto
  next
    case False
    then show ?thesis using STArray(1)[of "(hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] idef hash_suffixes_associative by auto
  qed
next
  case (STMap x1 tp1)
  then obtain i where idef:"typeCon x1 i \<and> Subpref tp1 (hash stl1 i) tp2 stl2" by auto
  then show ?case 
  proof(cases "(hash stl1 i) = stl2")
    case True
    then show ?thesis by auto
  next
    case False
    then show ?thesis using STMap(1)[of "(hash stl1 i)"] idef 
                            hash_suffixes_associative by auto
  qed
next
  case (STValue x)
  then show ?case using Subpref.simps(1) by simp
qed

definition typeCompat::"(String.literal, type \<times> denvalue) fmap   \<Rightarrow> stack \<Rightarrow> memoryT \<Rightarrow> storageT \<Rightarrow> calldataT \<Rightarrow> bool"
  where "typeCompat den sckO mem sto cd = (\<forall>t l. (t, l) |\<in>| fmran (den)
            \<longrightarrow> (case l of (Stackloc loc) \<Rightarrow>
                  (case (accessStore loc sckO) of
                   Some(KValue val) \<Rightarrow> 
                      (case t of (Value typ) \<Rightarrow> typeCon typ val
                       | _ \<Rightarrow> False )
                   | Some(KMemptr stloc) \<Rightarrow>
                      (case t of (type.Memory struct) \<Rightarrow> MCon struct mem stloc 
                        | _ \<Rightarrow> False
                      )
                   | Some(KCDptr stloc) \<Rightarrow> 
                      (case t of (type.Calldata struct) \<Rightarrow> MCon struct cd stloc
                        | _ \<Rightarrow> False
                      )
                   | Some(KStoptr stloc) \<Rightarrow>
                        (case t of (type.Storage struct) \<Rightarrow> SCon struct stloc sto
                          | _ \<Rightarrow> False)
                      
                   | _ \<Rightarrow> False)
                | (Storeloc loc) \<Rightarrow> 
                      (case t of (type.Storage typ) \<Rightarrow> SCon typ loc sto
                        | _ \<Rightarrow> False)
                )
          )"

subsection \<open>Shorthand - Suplementary lemmas\<close>
text \<open>Collection of lemmas which shorten common proof obligations\<close>

text \<open>Support functions to simplify the typeCon expressions definition \<close>
fun extractValueType :: "stackvalue \<Rightarrow> valuetype" where
  "extractValueType (KValue v) = v"
| "extractValueType (KCDptr v) = v"
| "extractValueType (KMemptr v) = v"
| "extractValueType (KStoptr v) = v"







locale typesafe_base = statement_with_gas +
  assumes methodVarsNoPref: "\<forall>c ct dud i1 i2 t1 t2. i1 \<noteq> i2 \<and> ep $$ c = Some(ct,dud) \<and> ct $$ i1 = Some (Var t1) \<and> ct $$ i2 = Some (Var t2)
                              \<longrightarrow> (\<not>TypedStoSubpref i1 i2 t2) \<and> (\<not>TypedStoSubpref i2 i1 t1)"

context typesafe_base
begin

text \<open>Checks that a given environment and state are considered fully initialised this meaning that the contract has an initialised account
                and all the contract variables have been initialised in the denvalue. 
                These two processes are the first things that would need to be done when creating a new environment (check statement NEW)\<close>

definition fullyInitialised::"environment \<Rightarrow> accounts \<Rightarrow> stack \<Rightarrow> bool"
  where "fullyInitialised env acc sk = (
(\<exists>c ct dud.
          Type (acc (Address env)) = Some (atype.Contract c) \<and>
          Contract env = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. ct $$ id = Some (Var v) \<longleftrightarrow>
                  Denvalue env $$ id = Some (type.Storage v, Storeloc id)) \<and>
          (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>

          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
              accessStore l sk = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and>
                       CompStoType t' t l' p)))


)"

lemma test_not_vacuous:
  fixes my_contract :: "String.literal" 
  fixes n :: "stypes"
  (* ASSUME THE BLUEPRINT IS EXACTLY 1 VARIABLE, NOTHING ELSE *)
  assumes blueprint_def: "my_blueprint = fmupd (STR ''balance'') (Var n) fmempty"
  assumes ep_def: "ep $$ my_contract = Some (my_blueprint, dud)" 

  shows "\<exists>env acc sk. fullyInitialised env acc sk \<and> 
                      Denvalue env $$ (STR ''balance'') = Some (type.Storage n, Storeloc (STR ''balance''))"
proof -
  let ?addr = "STR ''A''"
  let ?den  = "fmupd (STR ''balance'') (type.Storage n, Storeloc (STR ''balance'')) fmempty"
  let ?env  = "(emptyEnv ?addr my_contract (STR '''') (STR ''''))\<lparr>Denvalue := ?den\<rparr>"
  let ?acc  = "emptyAccount(?addr := emptyAcc\<lparr>Type := Some (atype.Contract my_contract)\<rparr>)"

  have map_eq: "\<And>i v. my_blueprint $$ i = Some (Var v) \<longleftrightarrow>
                    Denvalue ?env $$ i = Some (type.Storage v, Storeloc i)"
    using blueprint_def by simp

  have loc_eq: "\<And>id v loc.
      Denvalue ?env $$ id = Some (type.Storage v, Storeloc loc) \<Longrightarrow> id = loc"
    using fmlookup by (simp split:if_splits)

  have ptr_vacuous: "\<And>t l p.
      (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue ?env) \<and>
      accessStore l emptyStore = Some (KStoptr p)
      \<Longrightarrow> (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue ?env) \<and> CompStoType t' t l' p)"
    by (simp add: accessStore_def emptyStore_def)

  have fi: "fullyInitialised ?env ?acc emptyStore"
    unfolding fullyInitialised_def
    using ep_def map_eq loc_eq ptr_vacuous
    by (intro exI[of _ my_contract] exI[of _ my_blueprint] exI[of _ dud]) simp

  moreover have "Denvalue ?env $$ (STR ''balance'') =
      Some (type.Storage n, Storeloc (STR ''balance''))"
    by simp
  ultimately show ?thesis
    by blast
qed


definition AddressTypes :: "accounts \<Rightarrow> bool" where
    "AddressTypes ac =
      (\<forall>adv. case Type (ac adv) of
               Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep
             | _ \<Rightarrow> True)"

lemma AddressTypes_ep_lookup:
  assumes "AddressTypes ac"
    and "Type (ac adv) = Some (atype.Contract c)"
  shows "\<exists>ct dud. ep $$ c = Some (ct, dud)"
proof -
  from assms(1) have "case Type (ac adv) of
    Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep | _ \<Rightarrow> True"
    unfolding AddressTypes_def by blast
  then have "c |\<in>| fmdom ep" using assms(2) by simp
  then obtain v where "ep $$ c = Some v" using fmlookup_dom_iff 
    by fast
  then show ?thesis by (cases v) auto
qed

abbreviation accountsWellTyped :: "accounts \<Rightarrow> bool" where
  "accountsWellTyped acc \<equiv> balanceTypes acc \<and> AddressTypes acc"


definition safeContract :: "accounts \<Rightarrow> (address \<Rightarrow> storageT) \<Rightarrow> bool" where
  "safeContract acc sto =
    (\<forall>e ct dud i tp.
      Type (acc (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
      ep $$ Contract e = Some (ct, dud) \<and>
      fmlookup ct i = Some (Var tp)
      \<longrightarrow> SCon tp i (sto (Address (e::environment))))"


subsection \<open>type consistency between typed_mapping and denvalue for reachable locations\<close>

text \<open>This property ensures that the types stored in the typed_mapping
of memory are consistent with the types derivable from the denvalue for locations
that are reachable from variables in the environment.\<close>

definition denvalueTypeCorrectness :: "environment \<Rightarrow> stack \<Rightarrow> memoryT \<Rightarrow> bool"
  where
    "denvalueTypeCorrectness env sck mem =
    (\<forall>t l ptr_loc. (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
        accessStore l sck = Some (KMemptr ptr_loc) \<longrightarrow>
        (case t of MTArray len arr \<Rightarrow> 
                (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr) 
          | MTValue val \<Rightarrow> accessTypeStore ptr_loc mem = Some (MTValue val))
      )"

definition subPrefixStructuralConsistency :: "memoryT \<Rightarrow> bool"
  where
    "subPrefixStructuralConsistency mem = 
      (\<forall>locs tp. accessTypeStore locs mem = Some tp \<longrightarrow>
          (case accessStore locs mem of Some (MPointer p) \<Rightarrow>
               (\<exists>len arr. MCon tp mem p \<and> tp = MTArray len arr 
                  \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr)
                )
           | Some (MValue v) \<Rightarrow>
               (\<exists>val. MCon tp mem locs \<and> tp = MTValue val \<and>accessTypeStore locs mem = Some tp)
           | None \<Rightarrow> False))"

definition SomeValSomeTyp:: "memoryT \<Rightarrow> bool"
  where 
    "SomeValSomeTyp mem = (\<forall>locs. (\<exists>t. accessStore locs mem = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore locs mem = Some tt))"

subsection \<open>Typesafe environments\<close>
text \<open>The TypeSafe defition ensures that a given env, stack, memory, accounts, storage and calldata
      are Typesafe.
In this instance typesafety is defined over two sets of properties. An instance of enironment must satisfy
certain operation characteristics. 
And 2 all types and locations defined in the denvalue of the env must ensure that the String representation
of the value must conform to the respective type.\<close>
definition TypeSafe :: "environment \<Rightarrow> accounts \<Rightarrow> stack \<Rightarrow> memoryT \<Rightarrow> (address \<Rightarrow> storageT) \<Rightarrow> calldataT \<Rightarrow> bool"
  where "TypeSafe ev acc sck mem sto cd= (
          typeCompat (Denvalue ev) sck mem (sto (Address ev)) cd \<and>
          (unique_locations (Denvalue ev)) \<and>
          (compPointers sck (Denvalue ev)) \<and>
          (lessThanTopLocs sck) \<and> (lessThanTopLocs mem) \<and> (lessThanTopLocs cd) \<and>
          envAddressesWellFormed ev \<and>
          accountsWellTyped acc \<and>
          (safeContract acc sto) \<and>
          (svalueTypes (Svalue ev)) \<and>
          denvalueTypeCorrectness ev sck mem \<and>
          subPrefixStructuralConsistency mem \<and>
          SomeValSomeTyp mem)"


subsection \<open>All stack locations in the devalue must have a valid value in the stack\<close>
lemma typeSafeAllStacklocsExist: 
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(t, l2) |\<in>| fmran (Denvalue ev)"
    and "l2 = Stackloc l"
  shows "\<exists>v. accessStore l sck = Some v"
proof -
  have "\<forall>t l. (t, l) |\<in>| fmran (Denvalue ev) \<longrightarrow> 
        (case l of (Stackloc loc) \<Rightarrow> 
          (case (accessStore loc sck) of
            Some(KValue val) \<Rightarrow> (case t of (Value typ) \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
          | Some(KMemptr stloc) \<Rightarrow> (case t of (type.Memory struct) \<Rightarrow> MCon struct mem stloc | _ \<Rightarrow> False)
          | Some(KCDptr stloc) \<Rightarrow> (case t of (Calldata struct) \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
          | Some(KStoptr stloc) \<Rightarrow> (case t of (type.Storage struct) \<Rightarrow> SCon struct stloc (sto (Address ev)) | _ \<Rightarrow> False)
          | _ \<Rightarrow> False)
        | (Storeloc loc) \<Rightarrow> (case t of (type.Storage typ) \<Rightarrow> SCon typ loc (sto (Address ev)) | _ \<Rightarrow> False))"
    using assms(1) unfolding TypeSafe_def typeCompat_def by simp
  then have "case l2 of (Stackloc loc) \<Rightarrow> \<exists>v. accessStore loc sck = Some v"
    using assms(2) assms(3)  denvalue.simps(5) case_optionE by fastforce
  then show ?thesis using assms(3) by simp
qed



subsection \<open>astack does not impact unique locations\<close>
lemma updateEnvUniqueLocs:
  assumes "TypeSafe ev' (Accounts st) sck' mem' (Storage st) cd'"
    and "(k',e) = astack ip (v) (p) (sck', ev')"
  shows "unique_locations (Denvalue e)" unfolding unique_locations_def
proof(intros)
  have a10:"e = (updateEnv ip (v) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev')" using assms(2) by simp
  then have a15:"Denvalue e = Denvalue(ev' \<lparr> Denvalue := fmupd ip ((v),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev') \<rparr>)" by simp
  then have a17:"(Denvalue e) $$ ip = Some  ((v),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp
  have a20:"unique_locations (Denvalue ev')" using  assms(1) TypeSafe_def by simp
  have a30:"lessThanTopLocs sck'" using assms(1) TypeSafe_def by simp
  fix x' y
  assume aULoc:"x' |\<in>| fmran (Denvalue e) \<and> y |\<in>| fmran (Denvalue e) \<and> snd x' = snd y"
  then have a40:" (\<forall>tloc loc. Toploc sck' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc sck' = None)" using lessThanTopLocs_def Read_Show_nat'_id a30 by auto
  then have "\<forall>x y. \<not>((Denvalue ev') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" using TypeSafe_def assms typeSafeAllStacklocsExist fmranI a40  
    by (metis LSubPrefL2_def nle_le option.distinct(1) prod.exhaust_sel)
  then have a50:"\<forall>x' y. ((Denvalue e) $$ x'  = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> x' = ip \<and> (fst y) = (v)" using a30 a15 fmranI  by auto
  show "x' = y"
  proof(cases "snd x' = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))")
    case True
    then obtain x'' where "(Denvalue e) $$ x'' = Some x'" using fmranI aULoc by auto
    then have "x'' = ip" using a50 True by blast
    then show ?thesis using a50 aULoc True by (metis fmlookup_ran_iff prod_eq_iff) 
  next
    case False  
    then obtain x'' where a140:"(Denvalue e) $$ x'' = Some x'" using fmranI aULoc by auto
    then have a150:"x'' \<noteq> ip" using a50 False a17 by (metis option.inject snd_conv)
    have a160:"\<forall>x y. x \<noteq> ip \<and> (Denvalue e) $$ x = Some y \<longrightarrow> (Denvalue ev') $$ x = Some y" using a15 by simp
    then have "(Denvalue ev') $$ x'' = Some x'" using a140 a150 by blast 
    then show ?thesis  using aULoc a20 unique_locations_def False a160 a17 by (metis fmranE fmranI option.inject snd_conv) 
  qed
qed

lemma sameSckTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((Value typ), (Stackloc loc)) |\<in>| fmran (Denvalue ev) \<and> accessStore loc sck = Some (KValue val) \<longrightarrow> typeCon typ val" 
  using assms unfolding TypeSafe_def typeCompat_def by fastforce 

lemma sameMemTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((type.Memory struct), (Stackloc loc)) |\<in>| fmran (Denvalue ev) \<and> accessStore loc sck = Some (KMemptr stloc) \<longrightarrow> MCon struct mem stloc" 
  using assms unfolding TypeSafe_def typeCompat_def by fastforce

lemma sameCdTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((Calldata struct), (Stackloc loc)) |\<in>| fmran (Denvalue ev) \<and> accessStore loc sck = Some (KCDptr stloc) \<longrightarrow> MCon struct cd stloc" 
  using assms unfolding TypeSafe_def typeCompat_def by fastforce

lemma sameStoTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((type.Storage struct), (Stackloc loc)) |\<in>| fmran (Denvalue ev) \<and> accessStore loc sck = Some (KStoptr stloc) \<longrightarrow>  SCon struct stloc (sto (Address ev))" 
  using assms unfolding TypeSafe_def typeCompat_def by fastforce

lemma sameStoLocTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((type.Storage struct), (Storeloc loc)) |\<in>| fmran (Denvalue ev) \<longrightarrow>  SCon struct loc (sto (Address ev))" using assms 
  unfolding TypeSafe_def typeCompat_def by fastforce

lemma typeSafeUnique:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "unique_locations (Denvalue ev)" using assms unfolding TypeSafe_def by simp 

lemma typeSafeAccounts:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "balanceTypes acc" using assms unfolding TypeSafe_def by simp

lemma typeSafeAddressTypes:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "AddressTypes acc" using assms unfolding TypeSafe_def by simp

lemma typeSafeAccountsWellTyped:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "accountsWellTyped acc" using assms unfolding TypeSafe_def by simp

lemma typeSafeEnvAddresses:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "envAddressesWellFormed ev" using assms unfolding TypeSafe_def by simp

lemma typeSafeSvalue:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "svalueTypes (Svalue ev)" using assms unfolding TypeSafe_def by simp 

lemma typeSafeCompPointers:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "compPointers sck (Denvalue ev)" using assms unfolding TypeSafe_def by simp 

lemma lexp_stackloc_imps_id:
  assumes "lexp lv env cd st g = Normal ((LStackloc l2, t'), g')"
  shows "\<exists>i. lv = Id i"
proof (cases lv)
  case (Id i)
  then show ?thesis by auto
next
  case (Ref i r)
  then have "lexp (Ref i r) env cd st g =
    (case Denvalue env $$ i of None \<Rightarrow> throw Err
     | Some (tp, Stackloc l) \<Rightarrow>
         (case accessStore l (Stack st) of None \<Rightarrow> throw Err
         | Some (KMemptr l') \<Rightarrow> (case tp of type.Memory x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind> (\<lambda>t. local.msel True t l' r env cd (st) \<bind> (\<lambda>(l'', t'). return (LMemloc l'', type.Memory t')))
         | Some (KStoptr l') \<Rightarrow> (case tp of type.Storage x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind> (\<lambda>t. local.ssel t l' r env cd (st) \<bind> (\<lambda>(l'', t'). return (LStoreloc l'', type.Storage t'))) 
         | Some _ \<Rightarrow> throw Err)
     | Some (tp, Storeloc l) \<Rightarrow> (case tp of type.Storage x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind> (\<lambda>t. local.ssel t l r env cd (st) \<bind> (\<lambda>(l', t'). return (LStoreloc l', type.Storage t'))))
     g" using lexp.simps(2)[of i r env cd st g] Ref by simp
  then have "\<not>(\<exists>l tp. lexp (Ref i r) env cd (st) g = Normal ((LStackloc l, tp), g'))"
    by (auto split: option.splits prod.splits denvalue.split_asm type.splits stackvalue.splits result.splits)
  then have False using assms Ref by simp
  then show ?thesis by simp
qed

lemma lexpDenStor:
  assumes "lexp lv env cd (st) g = Normal ((LStoreloc l2, t'), g')"
    and "lv = Id x1"
  shows "(t', Storeloc l2) |\<in>| fmran (Denvalue env)" using assms
proof -
  have "(Denvalue env) $$ x1 = Some (t', Storeloc l2)" 
    using assms lexp.simps(1) by (simp split: option.split_asm prod.split_asm denvalue.split_asm)
  then show ?thesis using Finite_Map.fmranI[of "(Denvalue env)" x1 "(t', Storeloc l2)"] by simp
qed

lemma lexpDen:
  assumes "lexp lv env cd (st) g = Normal ((LStackloc l2, t'), g')"
    and "lv = Id i"
  shows "(t', Stackloc l2) |\<in>| fmran (Denvalue env)"
proof - 
  have "(case (Denvalue env) $$ i of
      Some (tp, (Stackloc l)) \<Rightarrow> return (LStackloc l, tp)
    | Some (tp, (Storeloc l)) \<Rightarrow> return (LStoreloc l, tp)
    | _ \<Rightarrow> throw Err) g = Normal ((LStackloc l2, t'), g')" using lexp.simps(1) assms by auto
  then have "(Denvalue env) $$ i = Some (t', Stackloc l2)" by (simp split: option.split_asm prod.split_asm denvalue.split_asm)
  then show ?thesis using Finite_Map.fmranI[of "(Denvalue env)" i "(t', Stackloc l2)"] by simp
qed

lemma lexpStackloc_imps_inDen:
  assumes "lexp lv env cd (st) g = Normal ((LStackloc l2, t'), g')"
  shows "(t', Stackloc l2) |\<in>| fmran (Denvalue env)" using assms lexpDen lexp_stackloc_imps_id by metis

lemma stackLocs_imp_NotDen:
  assumes "lessThanTopLocs sck'"
    and "TypeSafe ev' (Accounts st) sck' mem' (Storage st) cd'"
  shows "\<forall>x y. (Denvalue ev') $$ x = Some y \<longrightarrow> snd y \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))" 
proof - 
  have " accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' = None" using lessThanTopLocs_def Read_Show_nat'_id assms(1) using LSubPrefL2_def by auto
  then show ?thesis using assms(2) unfolding TypeSafe_def typeCompat_def using fmranI by fastforce
qed

lemma TS_imps_InDenLessStack:
  assumes "TypeSafe env acc sck mem sto cd"
    and "((type.Memory (MTArray x11 x12)), (Stackloc loc)) |\<in>| fmran (Denvalue env)"
    and "(accessStore loc sck') = Some (KMemptr stl2)"
    and "tloc = (Toploc mem) \<and> LSubPrefL2 stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
    and "MCon (MTArray x11 x12) mem stl2"
  shows "\<not>TypedMemSubPrefPtrs mem x11 x12 stl2 stl1" 
proof(cases x12)
  case (MTArray x11' x12')
  then have  Mcon:"MCon (MTArray x11 x12) mem stl2" using assms(1) unfolding TypeSafe_def using assms(2,3,4,5) 
    by fastforce
  have t:"((\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None) \<and>
   (\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
    using assms(1) unfolding TypeSafe_def lessThanTopLocs_def by auto

  have "\<not> TypedMemSubPrefPtrs mem x11 (MTArray x11' x12') stl2 stl1" unfolding TypedMemSubPrefPtrs.simps 
  proof
    assume *:"\<exists>i<x11. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x11' x12' l stl1)"
    then obtain i l where idef:"i<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x11' x12' l stl1)" by blast
    then have neq:"l \<noteq> stl1" using Mcon 
      by (metis MCon_imps_Some MCon_imps_sub_Mcon LSubPrefL2_def assms(4) eq_imp_le Not_Sub_More_Specific not_Some_eq t)
    then have neqSub:"\<forall>i<x11'. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" using t assms(4) idef Mcon 
      by (metis (mono_tags, opaque_lifting) MCon_imps_Some MCon_imps_sub_Mcon LSubPrefL2_def MemLSubPrefL2_specific_imps_general Not_Sub_More_Specific le_refl not_None_eq)
    have mconl: "MCon (MTArray x11' x12') mem l" using idef Mcon 
      using MCon_imps_sub_Mcon MTArray by blast
    then have "TypedMemSubPrefPtrs mem x11' x12' l stl1" using idef neq by simp
    then show False using neqSub mconl
    proof(induction x12' arbitrary: x11' l)
      case (MTArray x1 x12')
      then have "\<exists>i'<x11'. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = Some (MPointer l') \<and> (l' = stl1 \<or> TypedMemSubPrefPtrs mem x1 x12' l' stl1)"  
        unfolding TypedMemSubPrefPtrs.simps by simp
      then obtain i' l' where i'def:"i'<x11' \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = Some (MPointer l') \<and> (l' = stl1 \<or> TypedMemSubPrefPtrs mem x1 x12' l' stl1)" by blast
      then have l'neq:"l' \<noteq> stl1" using MTArray.prems 
        by (metis MCon_imps_Some LSubPrefL2_def assms(4) eq_imp_le Not_Sub_More_Specific mcon_typedptrs_ims_existance not_Some_eq t)
      then have "TypedMemSubPrefPtrs mem x1 x12' l' stl1" using i'def by simp
      have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> stl1" using i'def l'neq MTArray.prems 
        by (metis MCon_imps_Some LSubPrefL2_def assms(4) eq_imp_le Not_Sub_More_Specific mcon_typedptrs_ims_existance not_Some_eq t)
      then show ?case using MTArray.IH[of x1 l'] l'neq MTArray.prems(3) i'def by fastforce
    next
      case (MTValue x)
      then show ?case unfolding TypedMemSubPrefPtrs.simps by blast
    qed
  qed

  then show ?thesis using MTArray by auto

next
  case (MTValue x2)
  have Mcon:"MCon (MTArray x11 x12) mem stl2" using assms(1) unfolding TypeSafe_def using assms(2,3,4,5) 
    by fastforce
  have t:"((\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None) \<and>
   (\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
    using assms(1) unfolding TypeSafe_def lessThanTopLocs_def by auto
  have " \<not>TypedMemSubPrefPtrs mem x11 (MTValue x2) stl2 stl1" unfolding TypedMemSubPrefPtrs.simps 
  proof
    assume *:" \<exists>i<x11. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1"
    then show False using Mcon assms t 
      by (metis MCon_imps_Some LSubPrefL2_def MemLSubPrefL2_specific_imps_general Not_Sub_More_Specific le_refl not_Some_eq)
  qed
  then show ?thesis using MTValue by simp
qed


lemma typeSafe_noDenElementOverToploc_mem:
  assumes " TypeSafe env (Accounts st) (Stack st) mem (Storage st) cd"
    and "((type.Memory struct), (Stackloc loc)) |\<in>| fmran (Denvalue env)"
    and "(accessStore loc (Stack st)) =  Some(KMemptr stloc)"
  shows "\<not>LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
proof
  assume *:"LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
  have h1:"((\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)) \<longrightarrow> accessStore loc mem = None) \<and>
   (\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))" 
    using assms(1) unfolding TypeSafe_def lessThanTopLocs_def  by blast
  have h2:"MCon struct mem stloc" using assms unfolding TypeSafe_def typeCompat_def by fastforce
  then show False 
    using * h1 MCon_imps_Some lessThanSome_imps_Locs lessThanSome_imps_Locs2 lessThanTopLocs_def by fast
qed

lemma typeSafeAllPtrsNotTop:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue ev)"
    and "accessStore l sck = Some (KMemptr ptr)"
  shows "ptr \<noteq> ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem) \<and> 
        (\<forall>len2 arr2. \<not>TypedMemSubPrefPtrs mem len2 arr2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) ptr)\<and>
        (\<forall>len2 arr2. t = (MTArray len2 arr2) \<longrightarrow> \<not>TypedMemSubPrefPtrs mem len2 arr2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))) \<and>
        (\<forall>len2 arr2 len1 arr1 locs. t = (MTArray len2 arr2) \<longrightarrow> (\<nexists>dloc. TypedMemSubPrefPtrs mem len2 arr2 ptr dloc
                                                                        \<and> TypedMemSubPrefPtrs mem len1 arr1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) dloc))"
proof intros
  have ptrMCon:"MCon t mem ptr" using assms(1,2,3) unfolding TypeSafe_def typeCompat_def by force
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x" 
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) mem = None 
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def 
    using LSubPrefL2_def by blast
  show notTop:"ptr \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using ptrMCon toplocs unfolding lessThanTopLocs_def 
    by (metis MCon_imps_Some LSubPrefL2_def dual_order.refl option.distinct(1))
  fix len2 arr2
  show notSub:"\<not> TypedMemSubPrefPtrs mem len2 arr2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) ptr" 
  proof
    assume *:"TypedMemSubPrefPtrs mem len2 arr2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) ptr"
    show False
    proof(cases arr2)
      case (MTArray x11 x12)
      then have "(\<exists>i<len2. \<exists>l. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
          \<and> (l = ptr \<or> TypedMemSubPrefPtrs mem x11 x12 l ptr))" 
        using * TypedMemSubPrefPtrs.simps(2)[of mem len2 x11 x12 "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" ptr]
        by blast
      then show ?thesis using SomeA noneA by auto
    next
      case (MTValue x2)
      then show ?thesis using SomeA noneA * 
          TypedMemSubPrefPtrs.simps(1)[of mem len2 x2 "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" ptr] 
        using hash_suffixes_associative by force
    qed
  qed
  assume tDef:"t = MTArray len2 arr2"
  show "\<not> TypedMemSubPrefPtrs mem len2 arr2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
    using SomeA noneA 
    by (metis MCon_imps_Some mcon_typedptrs_ims_existance option.distinct(1) ptrMCon tDef)

  fix len1 arr1 locs
  show "\<nexists>dloc. TypedMemSubPrefPtrs mem len2 arr2 ptr dloc 
        \<and> TypedMemSubPrefPtrs mem len1 arr1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) dloc "
  proof
    assume **:"\<exists>dloc. TypedMemSubPrefPtrs mem len2 arr2 ptr dloc 
                \<and> TypedMemSubPrefPtrs mem len1 arr1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) dloc"
    then obtain dloc where dlocDef:"TypedMemSubPrefPtrs mem len2 arr2 ptr dloc 
                \<and> TypedMemSubPrefPtrs mem len1 arr1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) dloc" by blast
    then consider (ArrArr) l1 a1 l2 a2 where "arr1 = MTArray l1 a1 \<and> arr2 = MTArray l2 a2 "
      | (ArrVal) l1 a1 v where "arr1 = MTArray l1 a1 \<and> arr2 = MTValue v"
      | (ValArr) l2 a2 v where "arr2 = MTArray l2 a2 \<and> arr1 = MTValue v"
      | (ValVal) v1 v2 where "arr1 = MTValue v1 \<and> arr2 = MTValue v2" 
      by (meson mtypes.exhaust)
      
    then show "False"
    proof(cases)
      case ArrArr
      then show ?thesis using dlocDef 
        by (simp add: noneA)
    next
      case ArrVal
      then show ?thesis using dlocDef 
        by (simp add: noneA)
    next
      case ValArr
      then show ?thesis using dlocDef 
        by (metis MCon_imps_Some hash_suffixes_associative mcon_typedptrs_ims_existance noneA option.distinct(1) ptrMCon
            TypedMemSubPrefPtrs.simps(1) tDef)
    next
      case ValVal
      then have "(\<exists>i<len2. hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i) = dloc) \<and> (\<exists>i<len1. hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) (ShowL\<^sub>n\<^sub>a\<^sub>t i) = dloc)" 
        using dlocDef TypedMemSubPrefPtrs.simps(1) by simp
      then show ?thesis using ShowLNatDot hash_injective notTop by blast
    qed
  qed

qed


lemma typeSafeAllPtrsNotTop2:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue ev)"
    and "accessStore l sck = Some (KMemptr ptr)"
  shows "\<forall>tl. tl \<ge> Toploc mem \<longrightarrow>
        (\<not>LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t tl))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) ptr)"
proof intros
  fix tl 
  assume *:" Toploc mem \<le> tl"
  have ptrMCon:"MCon t mem ptr" using assms(1,2,3) unfolding TypeSafe_def typeCompat_def by force
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x" 
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) mem = None 
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def 
    using LSubPrefL2_def by blast
  show "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t tl)" 
    using LSubPrefL2_def SomeA hash_suffixes_associative noneA * 
    by (metis lessThanTopLocs_def option.discI toplocs)
  show "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) ptr" using LSubPrefL2_def MemLSubPrefL2_specific_imps_general * 
    using MemLSubPrefTransitive \<open>\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t tl)\<close> by blast

qed

lemma typeSafeAllMemPtrsCantTop:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(type.Memory tp, Stackloc l) |\<in>| fmran (Denvalue ev)"
    and "accessStore l sck = Some (KMemptr ptr)"
  shows "\<forall>len arr loc tl. tl \<ge> Toploc mem \<and> tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem len arr ptr loc \<longrightarrow> 
        (\<not>LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tl))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) loc)"
proof intros
  fix len arr loc tl
  assume *:"Toploc mem \<le> tl \<and> tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem len arr ptr loc"
  then have ptrMCon:"MCon (MTArray len arr) mem ptr" using assms(1,2,3) unfolding TypeSafe_def typeCompat_def by fastforce
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x" 
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) mem = None 
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def 
    using LSubPrefL2_def by blast
  show "\<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tl)" using * noneA SomeA 
    using assms(1,2,3) ptrMCon 
    by (metis LSubPrefL2_def MCon_imps_Some hash_flatten_right lessThanTopLocs_def
        mcon_typedptrs_ims_existance option.discI toplocs)
  then show "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (tl)) loc" using * noneA SomeA LSubPrefL2_def MemLSubPrefL2_specific_imps_general
    by metis
qed

lemma AccessedMemPtrsCantTop:
  assumes "lessThanTopLocs mem"
  shows "\<forall>len arr loc tl. tl \<ge> Toploc mem \<and> tp = MTArray len arr \<and> 
        MCon (MTArray len arr) mem ptr \<and> TypedMemSubPrefPtrs mem len arr ptr loc \<longrightarrow> 
        (\<not>LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tl))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) loc)"
proof intros
  fix len arr loc tl
  assume *:"Toploc mem \<le> tl \<and> tp = MTArray len arr  \<and> MCon (MTArray len arr) mem ptr \<and> TypedMemSubPrefPtrs mem len arr ptr loc"
  then have ptrMCon:"MCon (MTArray len arr) mem ptr" by fastforce
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x" 
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) mem = None 
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def 
    using LSubPrefL2_def by blast
  show "\<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tl)" using * noneA SomeA 
    using assms(1) ptrMCon 
    by (metis LSubPrefL2_def MCon_imps_Some hash_flatten_right lessThanTopLocs_def
        mcon_typedptrs_ims_existance option.discI toplocs)
  then show "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (tl)) loc" using * noneA SomeA LSubPrefL2_def MemLSubPrefL2_specific_imps_general
    by metis
qed

lemma CompMemTypeSubIndexes:
  assumes "CompMemType mem len arr (MTArray x t) pParentPtr p"
    and "subPrefixStructuralConsistency mem"
    and "MCon (MTArray len arr) mem pParentPtr"
    and "\<forall>i<len. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr"
  shows "\<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some t" using assms
proof(induction arr arbitrary:len pParentPtr)
  case (MTArray x1 arr)
  obtain i l where idef:"i<len \<and> accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) 
              \<and> (l = p \<and> MTArray x1 arr = MTArray x t \<or> CompMemType mem x1 arr (MTArray x t) l p)" 
    using MTArray.prems(1) unfolding CompMemType.simps by blast
  then have mc:"MCon (MTArray x1 arr) mem l"  using MTArray.prems(3) by auto
  then show ?case 
  proof(cases "l = p")
    case True
    then have tps:"MTArray x1 arr = MTArray x t" using idef MTArray.prems 
      by (metis existingLocation_imps_allLocs_same)
    have "\<forall>i<len.\<exists>p'. accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p')"
      using MTArray.prems(3) 
      by (metis MConArrayPointers bot_nat_0.not_eq_extremum less_nat_zero_code)
    then have "\<forall>i<len.\<exists>p'. accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p') \<and>
          (\<exists>len arr'. MCon (MTArray x1 arr) mem p' \<and> (MTArray x1 arr) = MTArray len arr' 
                      \<and> (\<forall>i<len. accessTypeStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr'))" 
      using MTArray.prems(2,4) unfolding subPrefixStructuralConsistency_def by fastforce
    then show ?thesis using idef True tps by auto
  next
    case False
    then have cmp:"CompMemType mem x1 arr (MTArray x t) l p" using idef by simp
    have "\<forall>i<x1. accessTypeStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr" 
      using idef MTArray.prems(2,4) unfolding subPrefixStructuralConsistency_def by fastforce
    then have "\<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some t" 
      using MTArray.IH[OF cmp MTArray.prems(2) mc _] by blast
    then show ?thesis by blast
  qed
next
  case (MTValue x)
  then show ?case by simp
qed


lemma subPrefixStructCon_imps_compmemtype:
  assumes "TypedMemSubPrefPtrs mem' x11 x12 stl2 stl1"
    and "\<forall>i<x11. accessTypeStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some x12"
    and "MCon (MTValue x2) mem stl1"
    and subPref:"subPrefixStructuralConsistency mem'"
    and acc1SameLoaded:"accessStore stl1 mem = accessStore stl1 m\<^sub>l" 
    and IH1:"\<forall>v. accessStore stl1 m\<^sub>l = Some (MValue v) \<longrightarrow> (\<exists>v'. accessStore stl1 mem' = Some (MValue v'))"
    and acT1:"accessTypeStore stl1 mem'  = Some (MTValue x2)"
  shows "CompMemType mem' x11 x12 (MTValue x2) stl2 stl1" using assms(1,2,3)
proof(induction x12 arbitrary:x11 stl2)
  case (MTArray x1 x12)
  obtain ii ll where iidef: "ii<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' = Some (MPointer ll) 
         \<and> (ll = stl1 \<or> TypedMemSubPrefPtrs mem' x1 x12 ll stl1)" 
    using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
  then show ?case 
  proof(cases "ll = stl1")
    case True
    then have ll:" MCon (MTArray x1 x12) mem' ll 
              \<and> (\<forall>i<x1. accessTypeStore (hash ll (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some x12)" 
      using subPref iidef MTArray.prems(2) 
      unfolding subPrefixStructuralConsistency_def by fastforce
    obtain v where "accessStore stl1 mem = Some (MValue v)" 
      using MTArray.prems(3) unfolding MCon.simps by (auto split:option.splits memoryvalue.splits)
    then have "accessStore stl1 m\<^sub>l = Some (MValue v)" using acc1SameLoaded by simp
    then obtain v' where "accessStore stl1 mem' = Some (MValue v')" using IH1 by auto
    then have "MCon (MTValue x2) mem' stl1" 
      using subPref acT1 unfolding subPrefixStructuralConsistency_def 
      using True ll by force
    then show ?thesis unfolding CompMemType.simps using iidef True ll by auto
  next
    case False
    have ll:" MCon (MTArray x1 x12) mem' ll 
              \<and> (\<forall>i<x1. accessTypeStore (hash ll (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some x12)" 
      using subPref iidef MTArray.prems(2)  
      unfolding subPrefixStructuralConsistency_def by fastforce
    then have tmp:"TypedMemSubPrefPtrs mem' x1 x12 ll stl1" using iidef False by simp
    then have "CompMemType mem' x1 x12 (MTValue x2) ll stl1" 
      using MTArray.IH[OF tmp _ MTArray.prems(3)] ll by simp
    then show ?thesis using iidef by auto
  qed
next
  case (MTValue x)                  
  then have idef:"\<exists>i<x11. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1" 
    using MTValue unfolding TypedMemSubPrefPtrs.simps by simp
  then obtain i where "i<x11 \<and> hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1" by blast
  then have "x = x2" using MTValue acT1 
    by auto
  then show ?case unfolding CompMemType.simps using idef by blast
qed


end

text \<open>Sanity check: the locale assumptions are dischargeable.\<close>
global_interpretation typesafe_vacuous: typesafe_base costs_ex fmempty costs_min
  by unfold_locales auto

text \<open>Non-vacuous sanity check: a concrete non-empty procedure environment.\<close>
definition nv_ct :: "(Identifier, member) fmap"
  where "nv_ct =
    fmap_of_list
      [(STR ''x'', Var (STValue TBool)),
       (STR ''y'', Var (STValue (TUInt b8)))]"

definition nv_ctor :: "(Identifier \<times> type) list \<times> s"
  where "nv_ctor = ([], SKIP)"

definition nv_contract :: contract
  where "nv_contract = (nv_ct, nv_ctor, SKIP)"

definition ep_nonvacuous :: environment\<^sub>p
  where "ep_nonvacuous = fmap_of_list [(STR ''C'', nv_contract)]"

lemma ep_nonvacuous_has_two_vars:
  "\<exists>ct dud t1 t2.
     ep_nonvacuous $$ (STR ''C'') = Some (ct, dud) \<and>
     ct $$ (STR ''x'') = Some (Var t1) \<and>
     ct $$ (STR ''y'') = Some (Var t2) \<and>
     (STR ''x'') \<noteq> (STR ''y'')"
  unfolding ep_nonvacuous_def nv_contract_def nv_ct_def nv_ctor_def
  by simp

global_interpretation typesafe_nonvacuous: typesafe_base costs_ex ep_nonvacuous costs_min
  by (unfold_locales; auto simp: ep_nonvacuous_def nv_contract_def nv_ct_def nv_ctor_def)

end
