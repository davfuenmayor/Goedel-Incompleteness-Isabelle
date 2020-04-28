theory second_incompleteness_class
  imports embedding
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3]

section \<open>Second Incompleteness Theorem (classical scenario)\<close>

(* Gödel's second incompleteness theorem: 

Assume F is a consistent formal system which contains arithmetic.
Let Cons\<^sub>F be a formula of F representing the consistency of the system, then: 
                       F \<^bold>\<turnstile>/ Cons\<^sub>F 

Below we reconstruct two variants. The conclusion follows from the first one
together with the first incompleteness theorem as a straightforward corollary.
In second variant the conclusion is derived employing a stronger logic (GL).
*)

(* If F is consistent, then F \<^bold>\<turnstile> G\<^sub>(\<^sub>F\<^sub>) \<^bold>\<leftrightarrow> Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma G_eq_Cons: fixes G
                 assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>]"                 (* axiom 4 *)
                 and   "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]"                 (* G's fixed-point *)
                 shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]"      (* equivalence of G and Cons *)
proof -
  have "[\<^bold>\<turnstile> \<^bold>\<bottom> \<^bold>\<rightarrow> G]" by simp                (* since \<^bold>\<bottom> implies everything *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<bottom> \<^bold>\<rightarrow> G)]" by simp                      (* by necessitation *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<box>G]" by simp                       (* by modal axiom K *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<sim>G]" using assms(2) by blast  (* using G's fixed-point *)
  hence LtoR: "[\<^bold>\<turnstile> G \<^bold>\<rightarrow> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]" by blast               (* by contraposition *)

  have RtoL: "[\<^bold>\<turnstile> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> G]" using assms(1) assms(2) (*use 4 + fixed-point*)
                                   by smt      (* employing an SMT solver *)
  thus "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]" using LtoR RtoL by blast
qed

(* If F is consistent, then (assuming Löb's theorem) F \<^bold>\<turnstile>/ Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma nonProv_Cons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"        (* axiom L *)
                    shows "\<sim>[\<^bold>\<turnstile> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]"           (* Cons is non-provable *)
proof
  assume provCons: "[\<^bold>\<turnstile> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]"               (* assume Cons were provable *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>]" by simp           (* by the properties of negation*)
  hence 1: "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<^bold>\<bottom>\<^bold>\<rightarrow>\<^bold>\<bottom>)]" by simp                   (* by necessitation *)
  have  2: "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<^bold>\<bottom>\<^bold>\<rightarrow>\<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<bottom>]" using assms(1) by (rule allE) (*inst. L*)
  from 1 2 have provIncons: "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]" by simp         (* by modus ponens *)
  from provCons provIncons have "[\<^bold>\<turnstile> \<^bold>\<bottom>]" by simp  (* by plain consistency *)
  thus False by simp
qed

section \<open>Experiments with other variants\<close>

abbreviation "S_consistency \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi>] \<longrightarrow> [\<^bold>\<turnstile> \<phi>]"  
abbreviation S_consistency_obj::"wo" ("S-Cons") where "S-Cons \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>"

abbreviation "star_consistency \<equiv> \<forall>\<phi>. \<sim>[\<^bold>\<turnstile> \<^bold>\<sim>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>]"
abbreviation star_consistency_obj::"wo" ("*-Cons") where "*-Cons \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<sim>\<^bold>\<box>(\<^bold>\<sim>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>)"

abbreviation "P_consistency_a \<equiv> \<sim>[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]" 
abbreviation P_consistency_a_obj::"wo" ("P-Cons-a") where "P-Cons-a \<equiv> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<box>\<^bold>\<bottom>"


(*********** Variant 1 ************)

(* If F is S-consistent, then F \<^bold>\<turnstile> G\<^sub>(\<^sub>F\<^sub>) \<^bold>\<leftrightarrow> S-Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma G_eq_SCons: fixes G
                  assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>]"                 (* axiom 4 *)
                  and   "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]"                 (* G's fixed-point *)
                  and   S_consistency    
                  shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> S-Cons]"  (* equivalence of G and S-Cons *)
  nitpick oops (* countermodel found *)

(* If F is *-consistent, then F \<^bold>\<turnstile> G\<^sub>(\<^sub>F\<^sub>) \<^bold>\<leftrightarrow> *-Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma G_eq_starCons: fixes G
                     assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>]"                 (* axiom 4 *)
                     and   "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]"                 (* G's fixed-point *)
                     and   star_consistency
                     shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> *-Cons]"   (* equivalence of G and *-Cons *)
  nitpick oops (* countermodel found *)

(* If F is P-consistent-a, then F \<^bold>\<turnstile> G\<^sub>(\<^sub>F\<^sub>) \<^bold>\<leftrightarrow> P-Cons-a\<^sub>(\<^sub>F\<^sub>) *)
lemma G_eq_PCons_a:  fixes G
                     assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>]"                 (* axiom 4 *)
                     and   "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<sim>\<^bold>\<box>G]"                 (* G's fixed-point *)
                     and   P_consistency_a
                     shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> P-Cons-a]" (* equivalence of G and P-Cons-a *)
  nitpick oops (* countermodel found *)


(*********** Variant 2 **************)

(* If F is S-consistent, then (assuming Löb's theorem) F \<^bold>\<turnstile>/ S-Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma nonProv_SCons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"           (* axiom L *)
                  (* and   S_consistency     (* strengthening the assumptions *) *)
                     shows "\<sim>[\<^bold>\<turnstile> S-Cons]"           (* S-Cons is non-provable *)
  nitpick oops (* countermodel found *) 
  (* TODO: prove or refute if strengthening the assumptions with S_consistency*)
  

(* If F is *-consistent, then (assuming Löb's theorem) F \<^bold>\<turnstile>/ *-Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma nonProv_starCons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"           (* axiom L *)
                        and   star_consistency     (* strengthening the assumptions *)
                        shows "\<sim>[\<^bold>\<turnstile> *-Cons]"           (* *-Cons is non-provable *)
  oops (* by (metis IV_char2 assms(1) mod nonProv_Cons)*)
 (* TODO: seems to be provable from first assumption. Verify *)

(* If F is P-consistent-a, then (assuming Löb's theorem) F \<^bold>\<turnstile>/ P-Cons-a\<^sub>(\<^sub>F\<^sub>) *)
lemma nonProv_PCons_a: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"           (* axiom L *)
                       and   P_consistency_a     (* strengthening the assumptions *)
                       shows "\<sim>[\<^bold>\<turnstile> P-Cons-a]"          (* P-Cons-a is non-provable *)
  using assms(1) nonProv_Cons by blast

end