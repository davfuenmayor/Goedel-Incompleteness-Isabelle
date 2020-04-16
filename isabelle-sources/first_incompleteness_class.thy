(*<*)
theory first_incompleteness_class
  imports embedding
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3]
(*>*)

section \<open>First Incompleteness Theorem (classical scenario)\<close>

lemma "\<forall>P. [\<^bold>\<turnstile> P] \<or> [\<^bold>\<turnstile> \<^bold>\<sim>P]" nitpick[card w=2] oops (* countermodel found *)
lemma "\<exists>P. \<sim>[\<^bold>\<turnstile> P] \<and> \<sim>[\<^bold>\<turnstile> \<^bold>\<sim>P]" nitpick[card w=1] oops (* countermodel found *)

(* If F is consistent, then F \<^bold>\<turnstile>/ G\<^sub>F *)
lemma non_provable: fixes G 
                    assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]"
                    shows   "\<sim>[\<^bold>\<turnstile> G]" 
proof
  assume Gprov: "[\<^bold>\<turnstile> G]"                    (* assume G were provable *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>G]" by simp                   (* by necessitation *)
  hence negGprov: "[\<^bold>\<turnstile> \<^bold>\<sim>G]" using assms(1) by blast
  from Gprov negGprov have "[\<^bold>\<turnstile> \<^bold>\<bottom>]" by simp (* by plain consistency *)
  thus False by simp
qed

(* If F is \<^bold>*-consistent, then F \<^bold>\<turnstile>/ \<^bold>\<sim>G\<^sub>F *)
lemma non_refutable_v1: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]" 
                        and     "\<forall>\<phi>. \<sim>[\<^bold>\<turnstile> \<^bold>\<sim>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>]" (* \<^bold>*-consistency *)
                        shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<sim>G]"
proof
  assume negGprov: "[\<^bold>\<turnstile> \<^bold>\<sim>G]"               (* assume G were refutable *)
  hence provGprov: "[\<^bold>\<turnstile> \<^bold>\<box>G]" using assms(1) by blast
  have Gcons: "\<sim>[\<^bold>\<turnstile> \<^bold>\<sim>G \<^bold>\<and> \<^bold>\<box>G]" using assms(2) by (rule allE)
  from negGprov provGprov have "[\<^bold>\<turnstile> \<^bold>\<sim>G \<^bold>\<and> \<^bold>\<box>G]" by simp
  hence "[\<^bold>\<turnstile> \<^bold>\<bottom>]" using Gcons by simp      (* using \<^bold>*-consistency of G *)
  thus False by simp
qed

(* If F is consistent, then (under an additional assumption) F \<^bold>\<turnstile>/ \<^bold>\<sim>G\<^sub>F *)
lemma non_refutable_v2: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]" 
                        and     "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi>]\<longrightarrow>[\<^bold>\<turnstile> \<phi>]" (* S-consistency*)
                        shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<sim>G]" 
proof
  assume negGprov: "[\<^bold>\<turnstile> \<^bold>\<sim>G]"                 (* assume G were refutable *)
  hence provGprov: "[\<^bold>\<turnstile> \<^bold>\<box>G]" using assms(1) by blast
  have  "[\<^bold>\<turnstile> \<^bold>\<box>G] \<longrightarrow> [\<^bold>\<turnstile> G]" using assms(2) by (rule allE)
  hence "[\<^bold>\<turnstile> G]" using provGprov by (rule mp)
  hence "[\<^bold>\<turnstile> \<^bold>\<bottom>]" using negGprov by simp
  thus False by simp
qed


(************************  Other variants **********************************)

abbreviation "P_consistency_a \<equiv>  \<sim>[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]"            (* (4.a) *)
abbreviation "P_consistency_b \<equiv>  [\<^bold>\<turnstile> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]"            (* (4.b) *)

(* If F is P-consistent(a), then F \<^bold>\<turnstile>/ \<^bold>\<sim>G\<^sub>F *)
lemma non_refutable_v3: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]" 
                        and     P_consistency_a
                        shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<sim>G]" 
  using assms(1) assms(2) by blast

(* If F is P-consistent(b), then F \<^bold>\<turnstile>/ \<^bold>\<sim>G\<^sub>F *)
lemma non_refutable_v4: fixes G 
                        assumes "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]" 
                        and     P_consistency_b
                        shows   "\<sim>[\<^bold>\<turnstile> \<^bold>\<sim>G]" 
  using assms(1) assms(2) by blast

(*<*)
end
(*>*)