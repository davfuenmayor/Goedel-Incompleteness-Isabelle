(*<*)
theory first_incompleteness_par
  imports embedding
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3]
(*>*)

section \<open>First Incompleteness Theorem (paraconsistent scenario)\<close>

abbreviation neg :: "wo\<Rightarrow>wo" ("\<^bold>\<not>_" [54] 55) where "\<^bold>\<not>\<phi> \<equiv> \<^bold>\<not>\<^sup>p\<phi>" (* negation is paraconsistent*)
abbreviation circ :: "wo\<Rightarrow>wo" ("\<^bold>\<circ>_" [54] 55) where "\<^bold>\<circ>\<phi> \<equiv> \<^bold>\<circ>\<^sup>m\<^sup>b\<^sup>c\<phi>"

lemma "\<forall>P. [\<^bold>\<turnstile> P] \<or> [\<^bold>\<turnstile> \<^bold>\<not>P]" nitpick[card w=2] oops (* countermodel found *)
lemma "\<exists>P. \<sim>[\<^bold>\<turnstile> P] \<and> \<sim>[\<^bold>\<turnstile> \<^bold>\<not>P]" nitpick[card w=1] oops (* countermodel found *)

(* If F is consistent, then F \<turnstile>/ G\<^sub>F *)
lemma non_provable: fixes G 
                    assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]" 
                    and     "[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>G]" (* assumes \<^bold>\<circ>-consistency of \<^bold>\<box>G*)
                    shows   "\<sim>[\<^bold>\<turnstile> G]"
proof
  assume Gprov: "[\<^bold>\<turnstile> G]"                    (* assume G were provable *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>G]" by simp                   (* by necessitation *)
  hence negGprov: "[\<^bold>\<turnstile> \<^bold>\<not>G]" using assms(1) assms(2) by blast
  from Gprov negGprov have "[\<^bold>\<turnstile> \<^bold>\<bottom>]"          (* by plain consistency *)
    using assms(2) by presburger           (* + \<^bold>\<circ>-consistency of \<^bold>\<box>G *)
  thus False by simp
qed

(* If F is \<^bold>*-consistent, then F \<turnstile>/ \<^bold>\<not>G\<^sub>F *)
lemma non_refutable_v1: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]" 
                        and     "\<forall>\<phi>. \<sim>[\<^bold>\<turnstile> \<^bold>\<not>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>]" (* \<^bold>*-consistency *)
                        and     "[\<^bold>\<turnstile> \<^bold>\<circ>G]" (* assumes \<^bold>\<circ>-consistency of G*)
                        shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<not>G]"
proof
  assume negGprov: "[\<^bold>\<turnstile> \<^bold>\<not>G]"               (* assume G were refutable *)
  hence provGprov: "[\<^bold>\<turnstile> \<^bold>\<box>G]" using assms(1) assms(3) by blast
  have Gcons: "\<sim>[\<^bold>\<turnstile> \<^bold>\<not>G \<^bold>\<and> \<^bold>\<box>G]" using assms(2) by (rule allE)
  from negGprov provGprov have "[\<^bold>\<turnstile> \<^bold>\<not>G \<^bold>\<and> \<^bold>\<box>G]" by simp
  hence "[\<^bold>\<turnstile> \<^bold>\<bottom>]" using Gcons by simp      (* using \<^bold>*-consistency of G *)
  thus False by simp
qed

(* If F is consistent, then (under an additional assumption) F \<turnstile>/ \<^bold>\<not>G\<^sub>F *)
lemma non_refutable_v2: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]" 
                        and     "\<forall>\<phi>.[\<^bold>\<turnstile> \<^bold>\<box>\<phi>]\<longrightarrow>[\<^bold>\<turnstile> \<phi>]" (* S-consistency*) 
                        and     "[\<^bold>\<turnstile> \<^bold>\<circ>G]"  (* assumes \<^bold>\<circ>-consistency of G*)
                        shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<not>G]" 
proof
  assume negGprov: "[\<^bold>\<turnstile> \<^bold>\<not>G]"                (* assume G were refutable *)
  hence provGprov: "[\<^bold>\<turnstile> \<^bold>\<box>G]" using assms(1) assms(3) by blast
  have  "[\<^bold>\<turnstile> \<^bold>\<box>G] \<longrightarrow> [\<^bold>\<turnstile> G]" using assms(2) by (rule allE)
  hence "[\<^bold>\<turnstile> G]" using provGprov by (rule mp)
  hence "[\<^bold>\<turnstile> \<^bold>\<bottom>]" using negGprov assms(3) by simp   (* consistency + \<^bold>\<circ>G *)
  thus False by simp
qed


(************************  Other variants **********************************)

abbreviation "P_consistency_a \<equiv>  \<sim>[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]"                 (* (4.a) *)
abbreviation "P_consistency_b_par \<equiv>  [\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]"             (* (4.b-par) *)
abbreviation "circ_consistency \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<circ>\<phi>]"               (* (5) *)


(* If F is P-consistent-a, then F \<turnstile>/ \<^bold>\<not>G\<^sub>F *)
lemma non_refutable_v3: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]" 
                        and     P_consistency_a
                        and     "[\<^bold>\<turnstile> \<^bold>\<circ>G]" (* assumes \<^bold>\<circ>-consistency of G*)
                      shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<not>G]" using assms by meson

(* If F is P-consistent-b, then F \<turnstile>/ \<^bold>\<not>G\<^sub>F *)
lemma non_refutable_v4: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]" 
                        and     P_consistency_b_par
                        and     "[\<^bold>\<turnstile> \<^bold>\<circ>G]" (* assumes \<^bold>\<circ>-consistency of G*)
                      shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<not>G]" oops (* TODO: cannot be proven nor disproven*)

(* If F is \<^bold>\<circ>-consistent, then F \<turnstile>/ \<^bold>\<not>G\<^sub>F *)
lemma non_refutable_v5: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]" 
                        and     circ_consistency
                        and     "[\<^bold>\<turnstile> \<^bold>\<circ>G]" (* assumes \<^bold>\<circ>-consistency of G*)
                        shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<not>G]" oops (* TODO: cannot be proven nor disproven*)

(*<*)
end
(*>*)