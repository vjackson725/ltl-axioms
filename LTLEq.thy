theory LTLEq
  imports Main "HOL-Library.Lattice_Syntax"
begin

section \<open> Helper Lemmas \<close>

lemma All_add_Suc2:
  fixes n :: nat
  shows \<open>(\<forall>x. P (n + x)) \<longleftrightarrow> P n \<and> (\<forall>x. P (Suc (n + x)))\<close>
  by (metis Suc_funpow add.commute add_eq_if funpow_swap1)

lemma Ex_Suc2:
  fixes n :: nat
  shows \<open>(\<exists>i. P i) = (P 0 \<or> (\<exists>i. P (Suc i)))\<close>
  using zero_induct by blast

subsection \<open> Helpful Boolean Algebra Lemmas \<close>

context boolean_algebra 
begin

(* A bit of notational trickery *)

abbreviation (input) bool_proves :: \<open>['a,'a] \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 50) where
  \<open>p \<turnstile> q \<equiv> p \<le> q\<close>

abbreviation (input) bool_impl :: \<open>['a,'a] \<Rightarrow> 'a\<close> (infixr \<open>\<rightarrow>\<close> 60) where
  \<open>p \<rightarrow> q \<equiv> -p \<squnion> q\<close>

abbreviation (input) bool_iff :: \<open>['a,'a] \<Rightarrow> 'a\<close> (infixr \<open>\<leftrightarrow>\<close> 60) where
  \<open>p \<leftrightarrow> q \<equiv> (p \<rightarrow> q) \<sqinter> (q \<rightarrow> p)\<close>


lemma impl_top_as_inf: \<open>p \<rightarrow> q = \<top> \<longleftrightarrow> p \<sqinter> q = p\<close>
  by (metis compl_inf inf_compl_bot inf_compl_bot_left1 inf_le2 inf_sup_distrib1
      inf_top.right_neutral sup.absorb2 sup_cancel_left2)

lemma impl_top_as_sup: \<open>p \<rightarrow> q = \<top> \<longleftrightarrow> p \<squnion> q = q\<close>
  by (metis impl_top_as_inf inf.orderI le_iff_sup sup_compl_top_left1)

lemma internalise_le: \<open>p \<turnstile> q \<longleftrightarrow> p \<rightarrow> q = top\<close>
  by (simp add: impl_top_as_sup le_iff_sup)

lemma bool_impl_galois: \<open>a \<turnstile> b \<rightarrow> c \<longleftrightarrow> a \<sqinter> b \<turnstile> c\<close>
  by (simp add: internalise_le sup.assoc)

lemma bool_impl_galois_deduct: \<open>top \<turnstile> b \<rightarrow> c \<longleftrightarrow> b \<turnstile> c\<close>
  by (simp add: internalise_le sup.assoc)

lemma bool_iff_eq_eq: \<open>top \<turnstile> p \<leftrightarrow> q \<longleftrightarrow> (p = q)\<close>
  by (metis impl_top_as_inf inf_absorb2 inf_le2 inf_top.right_neutral)

end


section \<open> LTL \<close>

text \<open>
  The main LTL operations, without any definitions.
  I include all of them, instead of defining some of them, because the axiomatisations disagree
  about which ones are primary.
\<close>

class ltl_ops = boolean_algebra +
  fixes ltl_next :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<circle>_\<close> [75] 75)
  fixes ltl_until :: \<open>['a,'a] \<Rightarrow> 'a\<close> (infix \<open>\<U>\<close> 73)
  fixes ltl_weakuntil :: \<open>['a,'a] \<Rightarrow> 'a\<close> (infix \<open>\<W>\<close> 73)
  fixes ltl_globally :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<box>_\<close> [75] 75)
  fixes ltl_finally  :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<diamond>_\<close> [75] 75)
begin

definition ltl_modalimpl :: \<open>['a,'a] \<Rightarrow> 'a\<close> (infix \<open>\<Rightarrow>\<close> 63) where
  \<open>p \<Rightarrow> q \<equiv> \<box>(p \<rightarrow> q)\<close>
  
definition ltl_modaliff :: \<open>['a,'a] \<Rightarrow> 'a\<close> (infix \<open>\<Leftrightarrow>\<close> 63) where
  \<open>p \<Leftrightarrow> q \<equiv> \<box>(p \<leftrightarrow> q)\<close>

lemma modalimpl_refl[simp]: \<open>\<top> \<turnstile> \<box>\<top> \<Longrightarrow> \<top> \<turnstile> p \<Rightarrow> p\<close>
  by (simp add: ltl_modalimpl_def)

lemma modaliff_refl[simp]: \<open>\<top> \<turnstile> \<box>\<top> \<Longrightarrow> \<top> \<turnstile> p \<Leftrightarrow> p\<close>
  by (simp add: ltl_modaliff_def)

end

subsection \<open> Axiomatisation 1: Equational \<close>

text \<open>
  This axiomatisation is modified from Manna and Pnueli's axiomatisation from
    The Temporal Logic of Reactive and Concurrent Systems (1991)
  which is replicated in von Karger's
    An Algebraic Approach to Temporal Logic (1995).
  (See also Axiomatisation 2).
\<close>

class ltl_algebra_eq = ltl_ops +
  assumes ltl_globally_def: \<open>\<box> p = p \<W> \<bottom>\<close>
  assumes ltl_finally_def: \<open>\<diamond> p = -(\<box>(-p))\<close>
  assumes ltl_until_def: \<open>p \<U> q = p \<W> q \<sqinter> \<diamond>q\<close>

  assumes fx0_globally_implies: \<open>\<box>p \<sqinter> p = \<box>p\<close>
  assumes fx1_next_selfdual: \<open>-(\<circle>p) = \<circle>(-p)\<close>
  assumes fx2_next_disj_distrib: \<open>\<circle>(p \<squnion> q) = \<circle>p \<squnion> \<circle>q\<close>
  assumes fx3_generalisation: \<open>\<box>(\<box>(p \<rightarrow> q) \<rightarrow> (\<box>p \<rightarrow> \<box>q)) = top\<close>
  assumes fx4_globally_next: \<open>\<box>p \<sqinter> \<box>(\<circle>p) = \<box>p\<close>
  assumes fx5_globally_impl_next_impl_globally: \<open>\<box>(p \<rightarrow> \<circle>p) \<sqinter> \<box>(p \<rightarrow> \<box>p) = \<box>(p \<rightarrow> \<circle>p)\<close>
  assumes fx6_weakuntil_unfolding: \<open>p \<W> q = q \<squnion> (p \<sqinter> \<circle>(p \<W> q))\<close>
  assumes fx7_globally_implies_weak: \<open>\<box>p \<sqinter> (p \<W> q) = \<box>p\<close>
begin

lemma generalisation: \<open>p = \<top> \<Longrightarrow> \<box>p = \<top>\<close>
  by (metis fx3_generalisation sup_top_right)

lemma fx3_equivalence0:
  \<open>(\<forall>p q. \<box>(\<diamond>(p \<sqinter> -q) \<squnion> (\<diamond>(-p) \<squnion> \<box>q)) = top)
    \<longleftrightarrow>
    (\<forall>p q. \<box>(\<box>(p \<rightarrow> q) \<rightarrow> (\<box>p \<rightarrow> \<box>q)) = top)\<close>
  by (simp add: ltl_finally_def)

lemma fx3_equivalence1:
  \<open>(\<forall>p q. \<box>(\<diamond>(p \<sqinter> -q) \<squnion> (\<diamond>(-p) \<squnion> \<box>q)) = top)
    \<longleftrightarrow>
    (\<forall>p q. \<box>(\<diamond>(-p \<sqinter> -q) \<squnion> (\<diamond>p \<squnion> \<box>q)) = top)\<close>
  by (metis double_compl)


lemma global_theorem_eq_theorem: \<open>top \<turnstile> \<box>p \<longleftrightarrow> top \<turnstile> p\<close>
  by (metis fx0_globally_implies fx3_generalisation inf.commute inf_top.right_neutral top_le)

lemma deduce_finally: \<open>p \<turnstile> \<diamond>p\<close>
  by (simp add: compl_le_swap1 fx0_globally_implies inf.orderI ltl_finally_def)

lemma globally_impl_le_distrib: \<open>\<box>(p \<rightarrow> q) \<turnstile> \<box>p \<rightarrow> \<box>q\<close>
  using global_theorem_eq_theorem bool_impl_galois_deduct fx3_generalisation
  by fastforce

lemma next_imlp_distrib[simp]: \<open>\<circle>(p \<rightarrow> q) = \<circle>p \<rightarrow> \<circle>q\<close>
  by (simp add: fx1_next_selfdual fx2_next_disj_distrib)

lemma next_conj_distrib[simp]: \<open>\<circle>(p \<sqinter> q) = \<circle>p \<sqinter> \<circle>q\<close>
  by (metis compl_inf double_compl fx1_next_selfdual next_imlp_distrib)


lemma globally_unfolding: \<open>\<box>p = p \<sqinter> \<circle>(\<box>p)\<close>
  using fx6_weakuntil_unfolding
  by (metis ltl_globally_def sup_bot_left)

lemma finally_unfolding: \<open>\<diamond>p = p \<squnion> \<circle>(\<diamond>p)\<close>
  by (metis globally_unfolding compl_sup double_compl fx1_next_selfdual ltl_finally_def)

lemma until_unfolding: \<open>p \<U> q = q \<squnion> (p \<sqinter> \<circle>(p \<U> q))\<close>
  apply (simp only: ltl_until_def)
  apply (subst fx6_weakuntil_unfolding)
  apply (simp add: inf.assoc sup_inf_distrib1 finally_unfolding[symmetric])
  done


lemma globally_top[simp]: \<open>\<box>\<top> = \<top>\<close>
  by (simp add: global_theorem_eq_theorem top_le)

lemma globally_bot[simp]: \<open>\<box>\<bottom> = \<bottom>\<close>
  by (metis globally_unfolding inf_bot_left)

lemma finally_top[simp]: \<open>\<diamond>\<top> = \<top>\<close>
  by (simp add: ltl_finally_def)

lemma finally_bot[simp]: \<open>\<diamond>\<bottom> = \<bottom>\<close>
  by (simp add: ltl_finally_def)


lemma globally_monotone:
  \<open>p \<turnstile> q \<Longrightarrow> \<box>p \<turnstile> \<box>q\<close>
  by (metis global_theorem_eq_theorem globally_top bool_impl_galois_deduct fx3_generalisation
      internalise_le)

lemma finally_monotone:
  \<open>p \<turnstile> q \<Longrightarrow> \<diamond>p \<turnstile> \<diamond>q\<close>
  by (simp add: globally_monotone ltl_finally_def)


lemma globally_conj_distrib: \<open>\<box>(p \<sqinter> q) = \<box>p \<sqinter> \<box>q\<close>
  oops

lemma globally_disj_left: \<open>\<box>p \<turnstile> \<box>(p \<squnion> q)\<close>
  by (simp add: globally_monotone)

lemma globally_disj_right: \<open>\<box>q \<turnstile> \<box>(p \<squnion> q)\<close>
  by (simp add: globally_monotone)

lemma finally_disj_distrib: \<open>\<diamond>(p \<squnion> q) = \<diamond>p \<squnion> \<diamond>q\<close>
  oops

lemma finally_conj_left: \<open>\<diamond>(p \<sqinter> q) \<turnstile> \<diamond>p\<close>
  by (simp add: finally_monotone)

lemma finally_conj_right: \<open>\<diamond>(p \<sqinter> q) \<turnstile> \<diamond>q\<close>
  by (simp add: finally_monotone)


lemma globally_idem: \<open>\<box>\<box>p = \<box>p\<close>
  by (metis deduce_finally finally_top global_theorem_eq_theorem globally_unfolding
      bool_impl_galois_deduct fx0_globally_implies fx5_globally_impl_next_impl_globally
      impl_top_as_inf inf.right_idem inf_absorb2)

lemma finally_idem: \<open>\<diamond>\<diamond>p = \<diamond>p\<close>
  by (simp add: globally_idem ltl_finally_def)


lemma globally_finally_eq_globally_until: \<open>\<box>p \<sqinter> \<diamond>q = \<box>p \<sqinter> p \<U> q\<close>
  by (metis fx7_globally_implies_weak inf.assoc ltl_until_def)

lemma negweakuntil_unfolding: \<open>-(q \<W> r) = -r \<sqinter> (-q \<squnion> \<circle>-(q \<W> r))\<close>
  by (metis compl_inf compl_sup fx1_next_selfdual fx6_weakuntil_unfolding)


lemma globally_induction: \<open>p \<turnstile> q \<Longrightarrow> p \<turnstile> \<circle>p \<Longrightarrow> p \<turnstile> \<box>q\<close>
  by (metis global_theorem_eq_theorem globally_disj_right globally_top bool_impl_galois_deduct
      fx5_globally_impl_next_impl_globally inf_top_left internalise_le sup.absorb1 transp_le
      transpD)

lemma weakuntil_induction:
  assumes ih: \<open>p \<turnstile> r \<squnion> (q \<sqinter> \<circle>p)\<close>
  shows \<open>p \<turnstile> q \<W> r\<close>
proof -
  have \<open>p \<sqinter> -(q \<W> r) \<turnstile> \<box>q\<close>
  proof (rule globally_induction)
    have l0: \<open>-(q \<W> r) \<turnstile> -r \<sqinter> (-q \<squnion> \<circle>-(q \<W> r))\<close>
      using negweakuntil_unfolding by auto
    then show g0: \<open>p \<sqinter> -(q \<W> r) \<turnstile> q\<close>
      using ih
      by (metis bool_impl_galois compl_le_swap1 inf.absorb2 inf.cobounded1
          inf.coboundedI1 sup_mono)

    have \<open>-(q \<W> r) \<turnstile> -q \<squnion> \<circle>-(q \<W> r)\<close>
      by (metis inf_le2 negweakuntil_unfolding)
    then have l1: \<open>p \<sqinter> -(q \<W> r) \<turnstile> -q \<squnion> \<circle>-(q \<W> r)\<close>
      using inf.coboundedI2 by blast

    have \<open>p \<sqinter> -(q \<W> r) \<turnstile> \<circle>-(q \<W> r)\<close>
      using g0 l1
      and bool_impl_galois inf.absorb_iff2 inf_commute
      by auto
    moreover have \<open>p \<sqinter> -(q \<W> r) \<turnstile> \<circle>p\<close>
      using inf.mono[OF ih l0] inf_sup_distrib2 by auto
    ultimately show \<open>p \<sqinter> -(q \<W> r) \<turnstile> \<circle>(p \<sqinter> -(q \<W> r))\<close>
      by simp
  qed
  moreover have \<open>\<box>q \<turnstile> q \<W> r\<close>
    by (simp add: fx7_globally_implies_weak inf.orderI)
  ultimately have \<open>p \<sqinter> -(q \<W> r) \<turnstile> q \<W> r\<close>
    using order_trans by blast
  then show ?thesis
    using le_iff_sup sup_inf_distrib2 by auto
qed



lemma gleft_wuntil_eq_sup: \<open>\<box>p \<W> q = \<box>p \<squnion> q\<close>
  by (metis globally_idem globally_unfolding fx6_weakuntil_unfolding fx7_globally_implies_weak
      inf.assoc sup.commute next_conj_distrib)

lemma weakuntil_absorb_globally: \<open>p \<W> q \<squnion> \<box>p = p \<W> q\<close>
  by (simp add: fx7_globally_implies_weak inf.orderI sup_absorb1)

lemma weakuntil_left_conj_distrib: \<open>(p \<sqinter> q) \<W> r = (p \<W> r) \<sqinter> (q \<W> r)\<close>
proof (intro order.antisym inf.boundedI)
  show \<open>(p \<sqinter> q) \<W> r \<turnstile> p \<W> r\<close>
    apply (rule weakuntil_induction)
    apply (subst fx6_weakuntil_unfolding)
    apply (metis inf_sup_distrib2 le_sup_iff sup.coboundedI2 sup_ge1 sup_inf_absorb)
    done
next
  show \<open>(p \<sqinter> q) \<W> r \<turnstile> q \<W> r\<close>
    apply (rule weakuntil_induction)
    apply (subst fx6_weakuntil_unfolding)
    apply (metis eq_iff inf_le2 sup_mono inf.assoc)
    done
next
  show \<open>p \<W> r \<sqinter> q \<W> r \<turnstile> (p \<sqinter> q) \<W> r\<close>
    apply (rule weakuntil_induction)
    apply clarsimp
    apply (subst fx6_weakuntil_unfolding)
    apply (simp add: sup_inf_distrib1)
    apply (intro conjI)
    apply (simp add: inf.assoc)
      apply (metis dual_order.trans fx6_weakuntil_unfolding inf.assoc inf.left_commute inf_commute
        inf_le1 sup_commute sup_inf_distrib1)
     apply (simp add: inf.assoc inf.coboundedI2)
    apply (metis dual_order.trans fx6_weakuntil_unfolding inf.assoc inf.left_commute inf_commute
        inf_le2 sup_inf_distrib1)
    done
qed

lemma weakuntil_right_disj_distrib: \<open>p \<W> (q \<squnion> r) = (p \<W> q) \<sqinter> (p \<W> r)\<close>
  oops

lemma until_pseudotransitive: \<open>(p \<U> q) \<sqinter> (-q \<U> r) \<turnstile> p \<U> r\<close>
  oops


lemma globally_next_comm[simp]: \<open>\<circle>\<box>p = \<box>\<circle>p\<close>
  oops

lemma finally_next_comm[simp]: \<open>\<circle>\<diamond>p = \<diamond>\<circle>p\<close>
  oops

lemma next_weakuntil_distrib[simp]: \<open>\<circle>(p \<W> q) = \<circle>p \<W> \<circle>q\<close>
  oops


lemma weakuntil_left_idem: \<open>p \<W> (p \<W> q) = p \<W> q\<close>
  oops

lemma weakuntil_right_idem: \<open>(p \<W> q) \<W> q = p \<W> q\<close>
  oops

lemma until_left_idem: \<open>p \<U> (p \<U> q) = p \<U> q\<close>
  oops

lemma until_right_idem: \<open>(p \<U> q) \<U> q = p \<U> q\<close>
  oops


lemma possibly_reccurence_eq_recurrence: \<open>\<diamond>\<box>\<diamond>p = \<box>\<diamond>p\<close>
  oops

lemma globally_persistence_eq_persistence: \<open>\<box>\<diamond>\<box>p = \<diamond>\<box>p\<close>
  oops


text \<open>Things I can't yet prove\<close>

lemma \<open>p \<W> q \<turnstile> \<box>p \<squnion> (\<diamond>-p \<sqinter> \<diamond>q)\<close>
  oops

lemma finally_globally_eq_finally_weakuntil: \<open>\<diamond>q \<squnion> \<box>p = \<diamond>q \<squnion> p \<W> q\<close>
  apply (intro order.antisym sup.boundedI)
     apply simp
    apply (simp add: sup.assoc sup.orderI weakuntil_absorb_globally)
   apply simp
  oops

lemma until_eq_weakuntil_and_poss: \<open>p \<W> q = p \<U> q \<squnion> \<box>p\<close>
  oops
(*
proof -
  have \<open>p \<U> q \<squnion> \<box>p = p \<W> q \<sqinter> \<diamond>q \<squnion> \<box>p\<close>
    by (simp add: ltl_until_def)
  also have \<open>... = p \<W> q \<sqinter> (\<diamond>q \<squnion> \<box>p)\<close>
    by (simp add: sup_inf_distrib2 weakuntil_absorb_globally)
  also have \<open>... = p \<W> q\<close>
    by (metis finally_globally_eq_finally_weakuntil inf.orderE sup_ge2)
  finally show ?thesis
    by (simp add: ltl_until_def)
qed
*)

end

subsection \<open> Axiomatisation 2 \<close>

text \<open>
  This axiomatisation is modified from Manna and Pnueli's axiomatisation from
    The Temporal Logic of Reactive and Concurrent Systems (1991)
  which is replicated in von Karger's
    An Algebraic Approach to Temporal Logic (1995).
\<close>
class ltl_algebra_manna_pnueli = ltl_ops +
  assumes ltl_globally_def: \<open>\<box> p = p \<W> \<bottom>\<close>
  assumes ltl_finally_def:  \<open>\<diamond> p = -(\<box>(-p))\<close>
  assumes ltl_until_def:    \<open>p \<U> q = p \<W> q \<sqinter> \<diamond>q\<close>

  assumes fx0_globally_implies:     \<open>\<top> \<turnstile> \<box>p \<rightarrow> p\<close>
  assumes fx1_next_selfdual:        \<open>\<top> \<turnstile> -(\<circle>p) \<Leftrightarrow> \<circle>(-p)\<close>
  assumes fx2_next_imlp_distrib:    \<open>\<top> \<turnstile> \<circle>(p \<rightarrow> q) \<Leftrightarrow> (\<circle>p \<rightarrow> \<circle>q)\<close>
  assumes fx3_generalisation: \<open>\<top> \<turnstile> \<box>(p \<rightarrow> q) \<Rightarrow> (\<box>p \<rightarrow> \<box>q)\<close>
  assumes fx4_globally_next:        \<open>\<top> \<turnstile> \<box>p \<rightarrow> \<box>(\<circle>p)\<close>
  assumes fx5_globally_induction:   \<open>\<top> \<turnstile> (p \<Rightarrow> \<circle>p) \<rightarrow> (p \<Rightarrow> \<box>p)\<close>
  assumes fx6_weakuntil_unfolding:  \<open>\<top> \<turnstile> p \<W> q \<Leftrightarrow> q \<squnion> (p \<sqinter> \<circle>(p \<W> q))\<close>
  assumes fx7_globally_impl_wuntil: \<open>\<top> \<turnstile> \<box>p \<Rightarrow> p \<W> q\<close>
begin

lemma globally_deduct: \<open>\<box>p \<turnstile> p\<close>
  using bool_impl_galois_deduct fx0_globally_implies by auto

lemma global_theorem_eq_theorem: \<open>\<top> \<turnstile> \<box>p \<longleftrightarrow> \<top> \<turnstile> p\<close>
  by (metis fx0_globally_implies fx3_generalisation internalise_le ltl_modalimpl_def
      top.ordering_top_axioms ordering_top.extremum_unique)

lemma p_modaliff_q_then_eq: \<open>top \<turnstile> p \<Leftrightarrow> q \<Longrightarrow> (p = q)\<close>
  using fx0_globally_implies
  by (metis antisym impl_top_as_inf inf_le2 inf_top.right_neutral ltl_modaliff_def)

lemma modaliff_eq_eq: \<open>top \<turnstile> p \<Leftrightarrow> q \<longleftrightarrow> (p = q)\<close>
  by (simp add: bool_impl_galois_deduct eq_iff global_theorem_eq_theorem ltl_modaliff_def)

lemma \<open>top \<turnstile> p \<Leftrightarrow> q \<longleftrightarrow> top \<turnstile> p \<leftrightarrow> q\<close>
  by (simp add: global_theorem_eq_theorem ltl_modaliff_def)


lemma modal_theorem_galois: \<open>p \<turnstile> q \<longleftrightarrow> top \<turnstile> p \<Rightarrow> q\<close>
  by (simp add: bool_impl_galois_deduct global_theorem_eq_theorem ltl_modalimpl_def)

lemma global_global_impl_distrib:
  \<open>\<top> \<turnstile> \<box>(\<box>(p \<rightarrow> q) \<rightarrow> \<box>p \<rightarrow> \<box>q)\<close>
  using fx3_generalisation ltl_modalimpl_def by auto

lemma global_global_next_deduce:
  \<open>\<box>p \<turnstile> \<box>\<circle>p\<close>
  using bool_impl_galois_deduct fx4_globally_next by blast

lemma self_impl_next_deduce_self_impl_globally:
  \<open>\<box>(p \<rightarrow> \<circle>p) \<turnstile> \<box>(p \<rightarrow> \<box>p)\<close>
  using bool_impl_galois_deduct fx5_globally_induction ltl_modalimpl_def by auto

lemma globally_deduce_weakuntil:
  \<open>\<box>p \<turnstile> p \<W> q\<close>
  using fx7_globally_impl_wuntil modal_theorem_galois by auto

lemma next_disj_distrib: \<open>\<circle>(p \<squnion> q) = \<circle>p \<squnion> \<circle>q\<close>
  by (metis double_compl fx1_next_selfdual fx2_next_imlp_distrib p_modaliff_q_then_eq)

text \<open>
  This equivalence is straightforward, as my equational rules
   are just rewritten versions of the Manna-Pnueli axioms.
\<close>
interpretation manna_pnueli_is_an_ltl_algebra: ltl_algebra_eq
  apply (unfold_locales)
            apply (simp add: ltl_globally_def)
           apply (simp add: ltl_finally_def)
          apply (simp add: ltl_until_def)
         apply (simp add: globally_deduct inf.absorb1)
        apply (simp add: fx1_next_selfdual p_modaliff_q_then_eq)
       apply (simp add: next_disj_distrib)
      apply (simp add: global_global_impl_distrib antisym)
     apply (simp add: global_global_next_deduce inf.absorb1)
    apply (simp add: self_impl_next_deduce_self_impl_globally inf.absorb1)
   apply (simp add: fx6_weakuntil_unfolding p_modaliff_q_then_eq inf.absorb1)
  apply (simp add: globally_deduce_weakuntil inf.absorb1)
  done

end

context ltl_algebra_eq
begin

interpretation ltl_algebra_proves_manna_pnueli_axioms: ltl_algebra_manna_pnueli
  apply (unfold_locales)
            apply (simp add: ltl_globally_def)
           apply (simp add: ltl_finally_def)
          apply (simp add: ltl_until_def)
         apply (simp add: fx0_globally_implies impl_top_as_inf internalise_le)
        apply (metis compl_sup_top eq_refl fx1_next_selfdual globally_top inf.semilattice_axioms
      ltl_modaliff_def semilattice.idem)
       apply (metis compl_sup_top eq_iff fx0_globally_implies generalisation ltl_modaliff_def
      next_imlp_distrib)
      apply (simp add: fx3_generalisation ltl_modalimpl_def)
     apply (metis fx4_globally_next inf_le2 internalise_le top_greatest)
    apply (simp add: fx5_globally_impl_next_impl_globally impl_top_as_inf internalise_le
      ltl_modalimpl_def)
   apply (metis eq_refl fx6_weakuntil_unfolding globally_top inf.semilattice_axioms
      internalise_le ltl_modaliff_def semilattice.idem)
  apply (metis fx7_globally_implies_weak globally_top impl_top_as_inf ltl_modalimpl_def
      top_greatest)
  done

end


subsection \<open> Axiomatisation 3 \<close>

text \<open>
  This axiomatisation from Gabbay, Pnueli, Shelah, and Stavi's
    Temporal Analysis of Fairness
  and is the second axiomatisation they present
\<close>

class ltl_algebra_gpss2 = ltl_ops +
  assumes ltl_finally_def: \<open>\<diamond> p = -(\<box>(-p))\<close>
  assumes ltl_until_def: \<open>p \<U> q = p \<W> q \<sqinter> \<diamond>q\<close>

  assumes kripke_g: \<open>\<top> \<turnstile> \<box>(p \<rightarrow> q) \<rightarrow> \<box>p \<rightarrow> \<box>q\<close>
  assumes x_selfdual: \<open>\<top> \<turnstile> -(\<circle>p) \<leftrightarrow> \<circle>(-p)\<close>
  assumes kripke_x: \<open>\<top> \<turnstile> \<circle>(p \<rightarrow> q) \<rightarrow> \<circle>p \<rightarrow> \<circle>q\<close>
  assumes g_unfolding: \<open>\<top> \<turnstile> \<box>p \<leftrightarrow> p \<sqinter> \<circle>\<box>p\<close>
  assumes selfnext_is_selfg: \<open>\<top> \<turnstile> \<box>(p \<rightarrow> \<circle>p) \<rightarrow> \<box>(p \<rightarrow> \<box>p)\<close>
  assumes wuntil_finally: \<open>\<top> \<turnstile> \<box>p \<rightarrow> p \<W> q\<close>
  assumes wuntil_unfolding: \<open>\<top> \<turnstile> p \<W> q \<leftrightarrow> q \<squnion> (p \<sqinter> \<circle>(p \<W> q))\<close>
  assumes generalisation: \<open>\<top> \<turnstile> p \<Longrightarrow> \<top> \<turnstile> \<box>p\<close>
begin

text \<open> Make the axioms nicer to work with\<close>

lemma kripke_g_deduct: \<open>\<box>(p \<rightarrow> q) \<turnstile> \<box>p \<rightarrow> \<box>q\<close>
  using bool_impl_galois_deduct kripke_g top_boolI by blast

lemma x_selfdual_eq: \<open>-(\<circle>p) = \<circle>(-p)\<close>
  using bool_iff_eq_eq x_selfdual by blast
 
lemma kripke_x_deduct: \<open>\<circle>(p \<rightarrow> q) \<turnstile> \<circle>p \<rightarrow> \<circle>q\<close>
  using bool_impl_galois_deduct kripke_x by blast

lemma g_unfolding_eq: \<open>\<box>p = p \<sqinter> \<circle>\<box>p\<close>
  using bool_iff_eq_eq g_unfolding by blast

lemma selfnext_is_selfg_deduct: \<open>\<box>(p \<rightarrow> \<circle>p) \<turnstile> \<box>(p \<rightarrow> \<box>p)\<close>
  using internalise_le selfnext_is_selfg by auto

lemma wuntil_finally_deduct_deduct: \<open>\<box>p \<turnstile> p \<W> q\<close>
  using internalise_le wuntil_finally by auto

lemma wuntil_unfolding_eq: \<open>p \<W> q = q \<squnion> (p \<sqinter> \<circle>(p \<W> q))\<close>
  using bool_iff_eq_eq wuntil_unfolding by blast

subsubsection \<open> Derived Lemmas \<close>

lemma necessitation: \<open>\<top> \<turnstile> \<box>p \<Longrightarrow> \<top> \<turnstile> p\<close>
  by (metis bool_iff_eq_eq g_unfolding inf_eq_top_iff top_le)

lemma global_theorem_iff_theorem: \<open>\<top> \<turnstile> \<box>p \<longleftrightarrow> \<top> \<turnstile> p\<close>
  by (metis generalisation necessitation top_le)


lemma globally_induction: \<open>a \<turnstile> b \<Longrightarrow> a \<turnstile> \<circle>a \<Longrightarrow> a \<turnstile> \<box>b\<close>
  by (metis g_unfolding_eq global_theorem_iff_theorem kripke_g_deduct bool_impl_galois_deduct
      impl_top_as_inf inf.left_idem internalise_le selfnext_is_selfg_deduct)

lemma finally_induction: \<open>a \<turnstile> b \<Longrightarrow> \<circle>b \<turnstile> b \<Longrightarrow> \<diamond>a \<turnstile> b\<close>
  by (metis compl_mono double_compl globally_induction ltl_finally_def x_selfdual_eq)

paragraph \<open> Idempotence \<close>

lemma globally_idem: \<open>\<box>\<box>p = \<box>p\<close>
proof (rule antisym)
  show \<open>\<box>\<box>p \<turnstile> \<box>p\<close>
    by (metis g_unfolding_eq inf.cobounded1)
next
  have \<open>\<box>p \<turnstile> \<circle>\<box>p\<close>
    by (metis g_unfolding_eq inf_le2)
  then show \<open>\<box>p \<turnstile> \<box>\<box>p\<close>
    by (simp add: globally_induction)
qed

lemma finally_idem: \<open>\<diamond>\<diamond>p = \<diamond>p\<close>
  by (simp add: globally_idem ltl_finally_def)

paragraph \<open> Next \<close>


lemma next_true[simp]: \<open>\<circle>\<top> = \<top>\<close>
  by (metis g_unfolding_eq global_theorem_iff_theorem inf_top.left_neutral top_unique)

lemma next_false[simp]: \<open>\<circle>\<bottom> = \<bottom>\<close>
  by (metis compl_top_eq next_true x_selfdual_eq)

lemma globally_next_push_in: \<open>\<circle>\<box>p \<turnstile> \<box>\<circle>p\<close>
proof (rule globally_induction)
  show \<open>\<circle>\<box>p \<le> \<circle>p\<close>
    by (metis g_unfolding_eq kripke_x_deduct bool_impl_galois_deduct inf.cobounded1 internalise_le
        next_true)
next
  show \<open>\<circle>\<box>p \<le> \<circle>\<circle>\<box>p\<close>
    by (metis g_unfolding_eq kripke_x_deduct bool_impl_galois_deduct inf_le2 internalise_le
        next_true)
qed

lemma globally_next_push_out: \<open>\<box>\<circle>p \<turnstile> \<circle>\<box>p\<close>
  oops

lemma globally_next_commute: \<open>\<box>\<circle>p = \<circle>\<box>p\<close>
  oops


lemma finally_next_commute: \<open>\<diamond>\<circle>p = \<diamond>\<box>p\<close>
  oops


paragraph \<open> Globally Distribution \<close>

lemma globally_proves_next_globally: \<open>\<box>p \<turnstile> \<circle>\<box>p\<close>
  by (metis g_unfolding_eq globally_idem inf.orderI)

lemma globally_true[simp]: \<open>\<box>\<top> = \<top>\<close>
  by (simp add: global_theorem_iff_theorem top_le)

lemma globally_false[simp]: \<open>\<box>\<bottom> = \<bottom>\<close>
  by (metis g_unfolding_eq inf_bot_left)

subparagraph \<open> Conjunction \<close>

lemma globally_conj_split_left: \<open>\<box>(p \<sqinter> q) \<turnstile> \<box>p\<close>
  by (metis g_unfolding_eq globally_proves_next_globally globally_induction inf_le1 le_infI1)

lemma globally_conj_split_right: \<open>\<box>(p \<sqinter> q) \<turnstile> \<box>q\<close>
  by (metis g_unfolding_eq globally_proves_next_globally globally_induction inf_le2 le_infI1)

lemma globally_distrib_conj_split: \<open>\<box>(p \<sqinter> q) \<turnstile> \<box>p \<sqinter> \<box>q\<close>
  using globally_conj_split_left globally_conj_split_right
  by simp

lemma globally_distrib_conj_combine: \<open>\<box>p \<sqinter> \<box>q \<turnstile> \<box>(p \<sqinter> q)\<close>
  oops

lemma globally_distrib_conj: \<open>\<box>(p \<sqinter> q) = \<box>p \<sqinter> \<box>q\<close>
  oops

subparagraph \<open> Disjunction \<close>

lemma globally_distrib_disj_combine_left: \<open>\<box>p \<turnstile> \<box>(p \<squnion> q)\<close>
  by (metis g_unfolding_eq globally_proves_next_globally globally_induction le_infI1 sup_ge1)

lemma globally_distrib_disj_combine_right: \<open>\<box>q \<turnstile> \<box>(p \<squnion> q)\<close>
  by (metis g_unfolding_eq globally_proves_next_globally globally_induction le_infI1 sup_ge2)

lemma globally_distrib_disj_combine: \<open>\<box>p \<squnion> \<box>q \<turnstile> \<box>(p \<squnion> q)\<close>
  using globally_distrib_disj_combine_left globally_distrib_disj_combine_right
  by simp

paragraph \<open> Finally Distribution \<close>

lemma finally_false[simp]: \<open>\<diamond>\<bottom> = \<bottom>\<close>
  by (simp add: ltl_finally_def)

lemma finally_true[simp]: \<open>\<diamond>\<top> = \<top>\<close>
  by (simp add: ltl_finally_def)

subparagraph \<open> Disjunction \<close>

lemma finally_distrib_disj_split: \<open>\<diamond>(p \<squnion> q) \<turnstile> \<diamond>p \<squnion> \<diamond>q\<close>
  oops

lemma finally_distrib_disj_combine: \<open>\<diamond>p \<squnion> \<diamond>q \<turnstile> \<diamond>(p \<squnion> q)\<close>
  using globally_distrib_conj_split ltl_finally_def by auto

subparagraph \<open> Conjunction \<close>

lemma finally_conj_split_left: \<open>\<diamond>(p \<sqinter> q) \<turnstile> \<diamond>p\<close>
sledgehammer
  by (metis g_unfolding_eq globally_proves_next_globally compl_mono globally_induction
      inf.cobounded1 inf.coboundedI1 ltl_finally_def)

lemma finally_conj_split_right: \<open>\<diamond>(p \<sqinter> q) \<turnstile> \<diamond>q\<close>
  by (metis g_unfolding_eq globally_proves_next_globally compl_mono globally_induction
      inf.cobounded2 inf.coboundedI1 ltl_finally_def)

lemma finally_distrib_conj_split: \<open>\<diamond>(p \<sqinter> q) \<turnstile> \<diamond>p \<sqinter> \<diamond>q\<close>
  by (simp add: finally_conj_split_left finally_conj_split_right)

paragraph \<open> Next Distribution \<close>

subparagraph \<open> Disjunction \<close>

lemma next_disj_distrib_split: \<open>\<circle>(p \<squnion> q) \<turnstile> \<circle>p \<squnion> \<circle>q\<close>
    by (metis kripke_x_deduct double_compl x_selfdual_eq)

lemma next_disj_distrib_combine: \<open>\<circle>p \<squnion> \<circle>q \<turnstile> \<circle>(p \<squnion> q)\<close>
  oops

subparagraph \<open> Conjunction \<close>

lemma next_conj_distrib_split: \<open>\<circle>(p \<sqinter> q) \<turnstile> \<circle>p \<sqinter> \<circle>q\<close>
  oops

lemma next_conj_distrib_combine: \<open>\<circle>p \<sqinter> \<circle>q \<turnstile> \<circle>(p \<sqinter> q)\<close>
  using kripke_x_deduct compl_le_compl_iff x_selfdual_eq by fastforce

paragraph \<open> Weak Until \<close>

lemma globally_as_wuntil: \<open>\<box>p = p \<W> \<bottom>\<close>
proof (rule antisym)
  show \<open>\<box>p \<turnstile> p \<W> \<bottom>\<close>
    by (simp add: wuntil_finally_deduct_deduct)
next
  have \<open>p \<W> \<bottom> \<turnstile> p\<close>
    by (metis inf.cobounded1 sup_bot_left wuntil_unfolding_eq)
  moreover have \<open>p \<W> \<bottom> \<turnstile> \<circle>(p \<W> \<bottom>)\<close>
    by (metis inf_le2 sup_bot.left_neutral wuntil_unfolding_eq)
  ultimately show \<open>p \<W> \<bottom> \<turnstile> \<box>p\<close>
    by (force intro: globally_induction)
qed

lemma glob_weakuntil_fin_eq_disj: \<open>\<box>p \<W> q = \<box>p \<squnion> q\<close>
proof -
  have \<open>\<box>p \<W> q = (\<box>p \<W> q) \<squnion> \<box>p\<close>
    by (metis sup.order_iff wuntil_finally_deduct_deduct globally_idem)
  also have \<open>... =  q \<squnion> (\<box>p \<sqinter> \<circle>(\<box>p \<W> q)) \<squnion> \<box>p\<close>
    by (metis wuntil_unfolding_eq)
  also have \<open>... =  (\<box>p \<squnion> (\<box>p \<sqinter> \<circle>(\<box>p \<W> q))) \<squnion> q\<close>
    using sup.assoc sup.commute by auto
  also have \<open>... =  \<box>p \<squnion> q\<close>
    by (metis sup_inf_absorb)
  finally show ?thesis .
qed

lemma weakuntil_fin_eq_disj: \<open>p \<W> \<diamond>q = \<box>p \<squnion> \<diamond>q\<close>
  oops

lemma weakuntil_induction: \<open>p \<turnstile> r \<squnion> (q \<sqinter> \<circle>p) \<Longrightarrow> p \<turnstile> q \<W> r\<close>
  oops


paragraph \<open> Globally + Finally \<close>

lemma globally_conj_finally_eq_globally: \<open>\<box>p \<sqinter> \<diamond>p = \<box>p\<close>
  by (metis g_unfolding_eq compl_inf impl_top_as_inf inf_cancel_left1 ltl_finally_def sup_compl_top)

lemma globally_disj_finally_eq_finally: \<open>\<box>p \<squnion> \<diamond>p = \<diamond>p\<close>
  by (simp add: globally_conj_finally_eq_globally inf.orderI sup.absorb2)


paragraph \<open> Manna-Pnueli Axioms \<close>

lemma fx0_globally_implies: \<open>\<top> \<turnstile> \<box>p \<rightarrow> p\<close>
  by (metis g_unfolding_eq bool_impl_galois_deduct inf.cobounded1)

lemma fx1_next_selfdual: \<open>\<top> \<turnstile> -(\<circle>p) \<Leftrightarrow> \<circle>(-p)\<close>
  by (simp add: x_selfdual_eq)

lemma fx2_next_imlp_distrib: \<open>\<top> \<turnstile> \<circle>(p \<rightarrow> q) \<Leftrightarrow> (\<circle>p \<rightarrow> \<circle>q)\<close>
  sorry 

lemma fx3_generalisation: \<open>\<top> \<turnstile> \<box>(p \<rightarrow> q) \<Rightarrow> (\<box>p \<rightarrow> \<box>q)\<close>
  by (simp add: generalisation kripke_g ltl_modalimpl_def)

lemma fx4_globally_next: \<open>\<top> \<turnstile> \<box>p \<rightarrow> \<box>(\<circle>p)\<close>
  by (metis g_unfolding_eq globally_next_push_in bool_impl_galois_deduct le_infI2)

lemma fx5_globally_induction: \<open>\<top> \<turnstile> (p \<Rightarrow> \<circle>p) \<rightarrow> (p \<Rightarrow> \<box>p)\<close>
  by (simp add: ltl_modalimpl_def selfnext_is_selfg)

lemma fx6_weakuntil_unfolding: \<open>\<top> \<turnstile> p \<W> q \<Leftrightarrow> q \<squnion> (p \<sqinter> \<circle>(p \<W> q))\<close>
  using wuntil_unfolding_eq by fastforce

lemma fx7_globally_impl_wuntil: \<open>\<top> \<turnstile> \<box>p \<Rightarrow> p \<W> q\<close>
  by (simp add: generalisation ltl_modalimpl_def wuntil_finally)

interpretation gpss2_proves_manna_pnueli_axioms: ltl_algebra_manna_pnueli
 apply (unfold_locales)
            apply (simp add: globally_as_wuntil)
           apply (simp add: ltl_finally_def)
          apply (simp add: ltl_until_def)
         apply (simp add: fx0_globally_implies)
        apply (simp add: fx1_next_selfdual)
       apply (simp add: fx2_next_imlp_distrib)
      apply (simp add: fx3_generalisation)
     apply (simp add: fx4_globally_next)
    apply (simp add: fx5_globally_induction)
   apply (simp add: fx6_weakuntil_unfolding)
  apply (simp add: fx7_globally_impl_wuntil)
  done

end

context  ltl_algebra_manna_pnueli
begin

lemma globally_unfolding: \<open>\<box>p = p \<sqinter> \<circle>\<box>p\<close>
  by (metis fx6_weakuntil_unfolding ltl_globally_def p_modaliff_q_then_eq sup_bot.left_neutral)

interpretation manna_pnueli_proves_gpss2_axioms: ltl_algebra_gpss2
  apply (unfold_locales)
  apply (simp add: ltl_finally_def)
          apply (simp add: ltl_until_def)
         apply (metis global_global_impl_distrib global_theorem_eq_theorem)
        apply (metis bool_iff_eq_eq fx1_next_selfdual modaliff_eq_eq)
       apply (metis compl_sup_top eq_iff fx2_next_imlp_distrib modaliff_eq_eq)
      apply (subst bool_iff_eq_eq, metis globally_unfolding)
     apply (simp add: bool_impl_galois_deduct self_impl_next_deduce_self_impl_globally)
    apply (simp add: bool_impl_galois_deduct globally_deduce_weakuntil)
   apply (simp only: bool_iff_eq_eq fx6_weakuntil_unfolding p_modaliff_q_then_eq)
  apply (simp add: global_theorem_eq_theorem)
  done

end

(* TODO
subsection \<open> Axiomatisation 4 \<close>

text \<open>
  This axiomatisation from Gabbay, Pnueli, Shelah, and Stavi's
    Temporal Analysis of Fairness
  and is the first axiomatisation they present
\<close>

class ltl_algebra_gpss1 = ltl_ops +
  fixes ltl_xuntil :: \<open>['a,'a] \<Rightarrow> 'a\<close> (infix \<open>\<U>\<^sup>+\<close> 73)
  fixes ltl_xglobally :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<box>\<^sup>+_\<close> [75] 75)
  fixes ltl_xfinally :: \<open>'a \<Rightarrow> 'a\<close> (\<open>\<diamond>\<^sup>+_\<close> [75] 75)

  assumes xfinally_def: \<open>\<diamond>\<^sup>+ p = -(\<box>\<^sup>+-p)\<close>

  assumes kripke_g: \<open>\<top> \<turnstile> \<box>(p \<rightarrow> q) \<rightarrow> \<box>p \<rightarrow> \<box>q = \<top>\<close>
  assumes x_selfdual: \<open>-(\<circle>p) = \<circle>(-p)\<close>
  assumes kripke_x: \<open>\<circle>(p \<rightarrow> q) \<rightarrow> \<circle>p \<rightarrow> \<circle>q = \<top>\<close>
  assumes g_unfolding: \<open>\<box>p = p \<sqinter> \<circle>\<box>p\<close>
  assumes selfnext_is_selfg: \<open>\<box>(p \<rightarrow> \<circle>p) \<rightarrow> \<box>(p \<rightarrow> \<box>p) = \<top>\<close>
  assumes until_finally: \<open>p \<U> q \<rightarrow> \<diamond>q = \<top>\<close>
  assumes until_unfolding: \<open>p \<U> q = q \<squnion> (p \<sqinter> \<circle>(p \<U> q))\<close>
  assumes generalisation: \<open>p = \<top> \<Longrightarrow> \<box>p = \<top>\<close>
begin
end

*)

subsection \<open> Axiomatisation 5 \<close>

text \<open>
  Kröger and Merz's axiomatisation from
\<close>


(* Kröger-Merz *)
class km_ltl_algebra = ltl_ops +
  assumes ltl_finally_def: \<open>\<diamond> p = -(\<box>(-p))\<close>
  assumes x_selfdual: \<open>-(\<circle>p) = \<circle>(-p)\<close>

  assumes kripke_x: \<open>\<top> \<turnstile> \<circle>(p \<rightarrow> q) \<rightarrow> \<circle>p \<rightarrow> \<circle>q\<close>
  assumes g_unfolding: \<open>\<top> \<turnstile> \<box>p \<rightarrow> p \<sqinter> \<circle>\<box>p\<close>

  assumes next_derive: \<open>\<top> \<turnstile> p \<Longrightarrow> \<top> \<turnstile> \<circle>p\<close>
  assumes globally_induction: \<open>\<And>a b. a \<turnstile> b \<Longrightarrow> a \<turnstile> \<circle>a \<Longrightarrow> a \<turnstile> \<box>b\<close>

  assumes weakuntil_finally: \<open>\<top> \<turnstile> \<box>p \<rightarrow> p \<W> q\<close>
  assumes weakuntil_unfolding: \<open>p \<W> q = q \<squnion> (p \<sqinter> \<circle>(p \<W> q))\<close>
begin

lemma next_distrib_backwards: \<open>\<top> \<turnstile> (\<circle>p \<rightarrow> \<circle>q) \<rightarrow> \<circle>(p \<rightarrow> q)\<close>
proof -
  have A0: \<open>\<top> \<turnstile> \<circle>(-(p \<rightarrow> q) \<rightarrow> p)\<close>
    by (simp add: next_derive sup.assoc sup.left_commute)
  
  have \<open>\<top> \<turnstile> -(\<circle>(p \<rightarrow> q)) \<rightarrow> \<circle>p\<close>
    by (metis A0 internalise_le kripke_x top_le x_selfdual)
  moreover have \<open>\<top> \<turnstile> -(\<circle>(p \<rightarrow> q)) \<rightarrow> -(\<circle>q)\<close>
    by (metis A0 abel_semigroup.commute compl_top_eq double_compl internalise_le kripke_x
        sup.abel_semigroup_axioms sup_bot.left_neutral sup_ge2)
  ultimately show ?thesis
    by (metis bool_impl_galois compl_le_compl_iff compl_le_swap2 inf_top_left
        sup_least)
qed

lemma weakuntil_induction: \<open>p \<turnstile> r \<squnion> (q \<sqinter> \<circle>p) \<Longrightarrow> p \<turnstile> q \<W> r\<close>
  oops

end



subsection \<open> Model Soundness \<close>

lemma add_one_step_induction:
  fixes n :: nat
  shows \<open>\<forall>i. P (n + i) \<longrightarrow> P (Suc (n + i)) \<Longrightarrow> P (n + i) \<Longrightarrow> P (n + i + j)\<close>
  by (induct j) (simp add: add.assoc)+

lemma model_helper_weakuntil_unfolding:
  fixes n :: nat
  shows \<open>((\<exists>j. Q (n + j) \<and> (\<forall>i<j. P (n + i))) \<or> (\<forall>i. P (n + i))) =
          (Q n \<or> P n \<and> ((\<exists>j. Q (Suc (n + j)) \<and> (\<forall>i<j. P (Suc (n + i)))) \<or> (\<forall>i. P (Suc (n + i)))))\<close>
proof -
  have \<open>((\<exists>j. Q (n + j) \<and> (\<forall>i<j. P (n + i))) \<or> (\<forall>i. P (n + i)))
        = ((\<exists>j. Q (n + j) \<and> (\<forall>i<j. P (n + i))) \<or> P n \<and> (\<forall>i. P (Suc (n + i))))\<close>
    by (metis All_add_Suc2)
  also have \<open>... = (Q n \<or> (\<exists>i. Q (Suc (n + i)) \<and> P n \<and> (\<forall>ia<i. P (Suc (n + ia)))) \<or> P n \<and> (\<forall>i. P (Suc (n + i))))\<close>
    by (subst Ex_Suc2, simp add: All_less_Suc2)
  finally show ?thesis
    by blast
qed

interpretation ltl_algebra_eq
  \<open>\<lambda>p q :: 'a \<Rightarrow> nat \<Rightarrow> bool. \<lambda>s n. p s n - q s n\<close>
  \<open>\<lambda>p. \<lambda>s n. - p s n\<close>
  \<open>\<lambda>p q. \<lambda>s n. p s n \<and> q s n\<close>
  \<open>\<lambda>p q. \<forall>s n. p s n \<turnstile> q s n\<close>
  \<open>\<lambda>x y. ((\<forall>s n. x s n \<turnstile> y s n) \<and> \<not> (\<forall>s n. y s n \<turnstile> x s n))\<close>
  \<open>\<lambda>p q. \<lambda>s n. p s n \<or> q s n\<close>
  \<open>\<lambda>s n. False\<close>
  \<open>\<lambda>s n. True\<close>
  \<open>\<lambda>p. \<lambda>s n. p s (n+1)\<close>
  \<open>\<lambda>p q. \<lambda>s n. (\<exists>j. q s (n+j) \<and> (\<forall>i<j. p s (n+i)))\<close>
  \<open>\<lambda>p q. \<lambda>s n. (\<exists>j. q s (n+j) \<and> (\<forall>i<j. p s (n+i))) \<or> (\<forall>i. p s (n+i))\<close>
  \<open>\<lambda>p. \<lambda>s n. \<forall>i. p s (n+i)\<close>
  \<open>\<lambda>p. \<lambda>s n. \<exists>i. p s (n+i)\<close>
  apply (unfold_locales)
                      apply force+
         apply (metis add.right_neutral)
        apply force
       apply force
      apply force
     apply (metis Suc_eq_plus1 add_Suc_right)
    apply (force simp add: add_one_step_induction)
   apply (simp add: model_helper_weakuntil_unfolding)
  apply force
  done

end
