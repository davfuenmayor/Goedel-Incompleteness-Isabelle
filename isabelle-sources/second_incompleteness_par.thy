theory second_incompleteness_par
  imports embedding
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3]

section \<open>Second Incompleteness Theorem (paraconsistent scenario)\<close>

(* Here we reconstruct the proofs of Gödel's second theorem (file "second_incompleteness_class.thy")
but this time employing the paraconsistent logic (R)mbC (featuring a paraconsistent negation). *)

abbreviation neg :: "wo\<Rightarrow>wo" ("\<^bold>\<not>_" [54] 55) where "\<^bold>\<not>\<phi> \<equiv> \<^bold>\<not>\<^sup>p\<phi>" (* negation is paraconsistent *)
abbreviation circ :: "wo\<Rightarrow>wo" ("\<^bold>\<circ>_" [54] 55) where "\<^bold>\<circ>\<phi> \<equiv> \<^bold>\<circ>\<^sup>m\<^sup>b\<^sup>c\<phi>" (* logic is (R)mbC *)

(* If F is consistent, then F \<^bold>\<turnstile> G\<^sub>(\<^sub>F\<^sub>) \<^bold>\<leftrightarrow> Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma G_eq_Cons: fixes G 
                 assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>]"                (* axiom 4 *) 
                 and "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]"                   (* G's fixed-point *)
                 and "[\<^bold>\<turnstile> \<^bold>\<circ>G]"                     (* \<^bold>\<box>G is \<^bold>\<circ>-consistent *)
                 and "[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>G]"                     (* \<^bold>\<box>G is \<^bold>\<circ>-consistent *)
                 and "[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom>]"                    (* \<^bold>\<box>\<^bold>\<bottom> is \<^bold>\<circ>-consistent *)
                 shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]" (*using assms by smt*)
proof -
  have "[\<^bold>\<turnstile> \<^bold>\<bottom> \<^bold>\<rightarrow> G]" by simp                 (* since \<^bold>\<bottom> implies everything *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<bottom> \<^bold>\<rightarrow> G)]" by simp                       (* by necessitation *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<box>G]" by simp                        (* by modal axiom K *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<not>G]" using assms(2) assms(4) (* use fixed-point + \<^bold>\<circ>\<^bold>\<box>G \<dots>*)
                          by blast      (*\<dots> by contraposition + chain rule*)  
  hence LtoR: "[\<^bold>\<turnstile> G \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]" using  assms(3) by blast (*by contrap.*)

  have "[\<^bold>\<turnstile> G \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<box>G]" using assms(2) by blast
  hence "[\<^bold>\<turnstile> \<^bold>\<box>G \<^bold>\<rightarrow> \<^bold>\<not>G]" using assms(4) by blast
  hence "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<box>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>G]" by simp (* necessitation followed by K*)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>G \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<not>G]"  using assms(1) by blast (* by chain rule *)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>G \<^bold>\<rightarrow> (\<^bold>\<box>G \<^bold>\<and> \<^bold>\<box>\<^bold>\<not>G)]" by simp (* trivial*)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>G \<^bold>\<rightarrow> \<^bold>\<box>(G \<^bold>\<and> \<^bold>\<not>G)]" by simp (* property of normal modal logics*)
  hence "[\<^bold>\<turnstile> \<^bold>\<box>G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<bottom>]" using assms(3) by blast (*definition of \<^bold>\<bottom>*)
  hence "[\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<box>G]" using assms(5) by blast (*contraposition*)
  hence RtoL: "[\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> G]" using assms(2) by blast (*fixd-point*)

  thus "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]" using LtoR RtoL by blast 
qed

(* lemma  "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G] \<Longrightarrow>[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom>] \<Longrightarrow>[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>G] \<Longrightarrow> [\<^bold>\<turnstile> \<^bold>\<circ>G]" nitpick *)
(*
(* If F is consistent, then (assuming Löb's theorem) F \<^bold>\<turnstile>/ Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma nonProv_Cons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"         (* axiom L *) 
                    and "[\<^bold>\<turnstile> \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom>]"                 (* \<^bold>\<box>\<^bold>\<bottom> is \<^bold>\<circ>-consistent *)
                    shows "\<sim>[\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]"
proof
  assume provCons: "[\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]"                 (* assume Cons were provable *)
  hence neg:"[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>]" using assms(2) by blast (*prop. negation + \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom> *)
  hence 1: "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>)]" by simp                  (* by necessitation *)
  have  2: "[\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<^bold>\<bottom> \<^bold>\<rightarrow> \<^bold>\<bottom>) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<bottom>]" using assms(1) by (rule allE) (*inst. L*)
  from 1 2 have provIncons: "[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]" by simp           (* by modus ponens *)
  from provCons provIncons have "[\<^bold>\<turnstile> \<^bold>\<bottom>]" using assms(2)    (* using  \<^bold>\<circ>\<^bold>\<box>\<^bold>\<bottom> \<dots>*)
                              by simp          (*\<dots> by LFI definition of \<^bold>\<bottom> *)       
  thus False by simp
qed

section \<open>Experiments with other variants\<close>

abbreviation "star_consistency \<equiv> \<forall>\<phi>. \<sim>[\<^bold>\<turnstile> \<^bold>\<not>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>]"
abbreviation star_consistency_obj::"wo" ("*-Cons") where "*-Cons \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>)"

abbreviation "P_consistency_a  \<equiv>  \<sim>[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]" 
abbreviation P_consistency_a_obj::"wo" ("P-Cons-a") where "P-Cons-a \<equiv> \<^bold>\<not>\<^bold>\<box>\<^bold>\<box>\<^bold>\<bottom>"

abbreviation "circ_consistency \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<circ>\<phi>]"  
abbreviation circ_consistency_obj::"wo" ("\<^bold>\<circ>-Cons") where "\<^bold>\<circ>-Cons \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<circ>\<phi>"


(*********** Variant 1 ************)

(* If F is *-consistent, then F \<^bold>\<turnstile> G\<^sub>(\<^sub>F\<^sub>) \<^bold>\<leftrightarrow> *-Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma G_eq_starCons: fixes G
                     assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>]"                 (* axiom 4 *)
                     and   "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]"                 (* G's fixed-point *)
                     and   star_consistency
                     shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> *-Cons]"   (* equivalence of G and *-Cons *)
  nitpick oops (* countermodel found *)

(* If F is P-consistent-a, then F \<^bold>\<turnstile> G\<^sub>(\<^sub>F\<^sub>) \<^bold>\<leftrightarrow> P-Cons-a\<^sub>(\<^sub>F\<^sub>) *)
lemma G_eq_PCons_a:  fixes G
                     assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>]"                 (* axiom 4 *)
                     and   "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]"                 (* G's fixed-point *)
                     and   P_consistency_a
                     shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> P-Cons-a]" (* equivalence of G and P-Cons-a *)
  nitpick oops (* countermodel found *)

(* If F is \<^bold>\<circ>-consistent, then F \<^bold>\<turnstile> G\<^sub>(\<^sub>F\<^sub>) \<^bold>\<leftrightarrow> S-Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma G_eq_circCons: fixes G
                     assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi>]"                 (* axiom 4 *)
                     and   "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<box>G]"                 (* G's fixed-point *)
                     and   circ_consistency    
                     shows "[\<^bold>\<turnstile> G \<^bold>\<leftrightarrow> \<^bold>\<circ>-Cons]"   (* equivalence of G and \<circ>-Cons *)
  nitpick oops (* countermodel found *)

(*********** Variant 2 **************)

(* If F is *-consistent, then (assuming Löb's theorem) F \<^bold>\<turnstile>/ *-Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma nonProv_starCons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"           (* axiom L *)
                        (* and   star_consistency     (* strengthening the assumptions *)  *)
                        shows "\<sim>[\<^bold>\<turnstile> *-Cons]"           (* *-Cons is non-provable *)
  nitpick oops (* countermodel found *) 
  (* TODO: prove or refute if strengthening the assumptions with star_consistency*)

(* If F is P-consistent-a, then (assuming Löb's theorem) F \<^bold>\<turnstile>/ P-Cons-a\<^sub>(\<^sub>F\<^sub>) *)
lemma nonProv_PCons_a: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"           (* axiom L *)
                       and   P_consistency_a     (* strengthening the assumptions *)
                       shows "\<sim>[\<^bold>\<turnstile> P-Cons-a]"         (* P-Cons-a is non-provable *)
  nitpick oops (* countermodel found *)

(* If F is circ-consistent, then (assuming Löb's theorem) F \<^bold>\<turnstile>/ \<^bold>\<circ>-Cons\<^sub>(\<^sub>F\<^sub>) *)
lemma nonProv_circCons: assumes "\<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"           (* axiom L *)
                        and   circ_consistency     (* strengthening the assumptions *) 
                        shows "\<sim>[\<^bold>\<turnstile> \<^bold>\<circ>-Cons]"           (* \<^bold>\<circ>-Cons is non-provable *)
  nitpick oops (* countermodel found *) 
*)
end