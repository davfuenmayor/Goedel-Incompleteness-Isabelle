(*<*)
theory second_incompleteness_class
  imports embedding
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3]
(*>*)

section \<open>Second Incompleteness Theorem\<close>

(* If F is consistent, then (assuming IV) F \<turnstile> G\<^sub>F \<^bold>\<leftrightarrow> Cons *)
lemma G_eq_Cons: fixes G
                 assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>]" (* axiom 4 (logic is K4) *)
                 and   "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]"
                 shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]"
proof -
  have "[\<^bold>\<turnstile> \<^bold>\<bottom> \<^bold>\<rightarrow> G]" by simp     (* since \<^bold>\<bottom> implies everything (including G) *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<bottom> \<^bold>\<rightarrow> G)]" by simp                         (* by Necessitation *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<box>G]" by simp                         (* by modal axiom K *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<sim>G]" using assms(2) by blast    (* using diagonalization *)
  hence LtoR: "[\<^bold>\<turnstile> G \<^bold>\<rightarrow> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]" by blast (* contraposition *)

  have RtoL: "[\<^bold>\<turnstile> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> G]" using assms(1) assms(2) (* 4 + diagonalization *)
                               by smt            (* employing an SMT solver *)
  thus "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]" using LtoR RtoL by blast
qed

(* If F is consistent, then (assuming GL) F \<turnstile>/ Cons *)
lemma nonProv_Cons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]" (* axiom GL *)
                    shows "\<sim>[\<^bold>\<turnstile> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]"
proof
  assume provCons: "[\<^bold>\<turnstile> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]"          (* assume Cons (\<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>) were provable *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>]" by simp       
  hence 1: "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>)]" by simp   (* by Necessitation *)
  have  2: "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<bottom>]" using assms(1) by (rule allE)
  from 1 2 have provIncons: "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]" by simp
  from provCons provIncons have "[\<^bold>\<turnstile> \<^bold>\<bottom>]" by simp    (* by plain consistency *)
  thus False by simp
qed


(************************  Other variants **********************************)

abbreviation "GL \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"        (* (GL) *)
abbreviation "S_consistency \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi>] \<longrightarrow> [\<^bold>\<turnstile> \<phi>]"  (* (3) *)
abbreviation "S_consistency_var \<equiv> [\<^bold>\<turnstile>  \<^bold>\<forall>\<phi>. \<^bold>\<box>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"  (* (3.var) *)

(* Both formalizations are incomparable/independent*)
lemma "S_consistency \<Longrightarrow> S_consistency_var" nitpick oops (*countermodel found*)
lemma "S_consistency_var \<Longrightarrow> S_consistency" nitpick oops (*countermodel found*)

lemma nonProv_Cons_var: assumes GL shows "\<sim>S_consistency_var" nitpick oops (*countermodel found*)

(*<*)
end
(*>*)