(*<*)
theory second_incompleteness_par
  imports embedding
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3]
(*>*)

section \<open>Second Incompleteness Theorem\<close>

abbreviation neg :: "wo\<Rightarrow>wo" ("\<^bold>\<not>_" [54] 55) where "\<^bold>\<not>\<phi> \<equiv> \<^bold>\<not>\<^sup>p\<phi>" (* negation is paraconsistent *)
abbreviation circ :: "wo\<Rightarrow>wo" ("\<^bold>\<circ>_" [54] 55) where "\<^bold>\<circ>\<phi> \<equiv> \<^bold>\<circ>\<^sup>m\<^sup>b\<^sup>c\<phi>"

(* If F is consistent, then (assuming IV) F \<turnstile> G\<^sub>F \<^bold>\<leftrightarrow> Cons *)
lemma G_eq_Cons: fixes G 
                 assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>]"  (* axiom 4 (logic is K4) *) 
                 and "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]" 
                 and "[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>G]"                        (* \<^bold>\<box>G is \<^bold>\<circ>-consistent *)
                 and "[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom>]"                       (* \<^bold>\<box>\<^bold>\<bottom> is \<^bold>\<circ>-consistent *)
                 shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]"
proof -
  have "[\<^bold>\<turnstile> \<^bold>\<bottom> \<^bold>\<rightarrow> G]" by simp     (* since \<^bold>\<bottom> implies everything (including G) *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<bottom> \<^bold>\<rightarrow> G)]" by simp                         (* by Necessitation *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<box>G]" by simp                         (* by modal axiom K *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<not>G]" using assms(2) assms(3) by blast   (* by diag + \<^bold>\<circ>\<^bold>\<box>G *)
  have LtoR: "[\<^bold>\<turnstile> G \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]" using assms(2) assms(3) by blast

  have RtoL: "[\<^bold>\<turnstile>  \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> G]" using assms    (* using all assumptions above *)
                               by smt        (* and employing an SMT solver *)
  thus "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]" using LtoR RtoL by blast
qed

(* If F is consistent, then (assuming GL) F \<turnstile>/ Cons *)
lemma nonProv_Cons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"        (* axiom GL *) 
                    and "[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom>]"                  (* \<^bold>\<box>\<^bold>\<bottom> is \<^bold>\<circ>-consistent *)
                    shows "\<sim>[\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]"
proof
  assume provCons: "[\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]"          (* assume Cons (\<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>) were provable *)
  hence neg:"[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>]" using assms(2) by blast           (* since \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom> *)
  hence 1: "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>)]" by simp                   (* by Necessitation *)
  have  2: "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<bottom>]" using assms(1) by (rule allE)
  from 1 2 have provIncons: "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]" by simp
  from neg provCons provIncons have "[\<^bold>\<turnstile> \<^bold>\<bottom>]" by simp        
  thus False by simp
qed

(********************************************************************)
abbreviation "incons \<equiv>  \<^bold>\<box>\<^bold>\<bottom>"             (* (4.b-par) *)
abbreviation "cons_par \<equiv>  \<^bold>\<not>incons"             (* (4.b-par) *)
abbreviation "consistency_par \<equiv> \<forall>\<phi>. \<sim>[\<^bold>\<turnstile>  \<^bold>\<not>\<phi> \<^bold>\<and> \<phi>]"        (* (1-par) *)
abbreviation "star_consistency_par \<equiv> \<forall>\<phi>. \<sim>[\<^bold>\<turnstile> \<^bold>\<not>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>]"   (* (2-par) *)
abbreviation "P_consistency_a \<equiv>  \<sim>[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]"            (* (4.a) *)
abbreviation "P_consistency_b_par \<equiv>  [\<^bold>\<turnstile> cons_par]"             (* (4.b-par) *)
abbreviation "circ_consistency \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<circ>\<phi>]"               (* (5) *)

(* If F is consistent, then (assuming GL) F \<turnstile>/ Cons *)
lemma nonProv_Cons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"        (* axiom GL *) 
                    and "[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom>]"                  (* \<^bold>\<box>\<^bold>\<bottom> is \<^bold>\<circ>-consistent *)
                    shows "circ_consistency" nitpick

(*<*)
end
(*>*)