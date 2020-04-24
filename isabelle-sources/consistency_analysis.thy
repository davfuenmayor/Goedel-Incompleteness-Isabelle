theory consistency_analysis
  imports embedding
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3]

section \<open>Consistency Analysis\<close>

subsection \<open>Consistency Analysis (classical)\<close>

abbreviation "consistency \<equiv> \<forall>\<phi>. \<sim>[\<^bold>\<turnstile>  \<^bold>\<sim>\<phi> \<^bold>\<and> \<phi>]"        (* (1) *)
abbreviation "star_consistency \<equiv> \<forall>\<phi>. \<sim>[\<^bold>\<turnstile> \<^bold>\<sim>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>]"  (* (2) *)
abbreviation "S_consistency \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi>] \<longrightarrow> [\<^bold>\<turnstile> \<phi>]"  (* (3) *)
abbreviation "P_consistency_a \<equiv>  \<sim>[\<^bold>\<turnstile> \<^bold>\<box>\<^bold>\<bottom>]"            (* (4.a) *)
abbreviation "P_consistency_b \<equiv>  [\<^bold>\<turnstile> \<^bold>\<sim>\<^bold>\<box>\<^bold>\<bottom>]"            (* (4.b) *)

(* (i) *)
(* (1) is a tautology *)
lemma consistency by simp

(* (ii) *)
(* (2) and (4.a) are equivalent *)
lemma "star_consistency \<longleftrightarrow> P_consistency_a" by blast

(* (iii) *)
(* (3) implies (2) *)
lemma "S_consistency \<longrightarrow> star_consistency" by blast
lemma "star_consistency \<longrightarrow> S_consistency" nitpick oops (*countermodel found*)
(* (3) implies (4.a) *)
lemma "S_consistency \<longrightarrow> P_consistency_a" by blast
lemma "P_consistency_a \<longrightarrow> S_consistency" nitpick oops (*countermodel found*)

(* (iv) *)
(* (4.b) implies (4.a) *)
lemma "P_consistency_b \<longrightarrow> P_consistency_a" by simp
lemma "P_consistency_a \<longrightarrow> P_consistency_b" nitpick oops (*countermodel found*)
(* (4.b) implies (2) *)
lemma "P_consistency_b \<longrightarrow> star_consistency" by blast
lemma "star_consistency \<longrightarrow> P_consistency_b" nitpick oops (*countermodel found*)

(* (v) *)
(* (3) and (4.b) are incomparable *)
lemma "S_consistency \<longrightarrow> P_consistency_b" nitpick oops (*countermodel found*)
lemma "P_consistency_b \<longrightarrow> S_consistency" nitpick oops (*countermodel found*)

subsection \<open>Consistency Analysis (paraconsistent)\<close>

abbreviation neg :: "wo\<Rightarrow>wo" ("\<^bold>\<not>_" [54] 55) where "\<^bold>\<not>\<phi> \<equiv> \<^bold>\<not>\<^sup>p\<phi>" (* negation is paraconsistent *)
abbreviation circ :: "wo\<Rightarrow>wo" ("\<^bold>\<circ>_" [54] 55) where "\<^bold>\<circ>\<phi> \<equiv> \<^bold>\<circ>\<^sup>m\<^sup>b\<^sup>c\<phi>" (* logic is mbC *)

abbreviation "consistency_par \<equiv> \<forall>\<phi>. \<sim>[\<^bold>\<turnstile>  \<^bold>\<not>\<phi> \<^bold>\<and> \<phi>]"        (* (1) *)
abbreviation "star_consistency_par \<equiv> \<forall>\<phi>. \<sim>[\<^bold>\<turnstile> \<^bold>\<not>\<phi> \<^bold>\<and> \<^bold>\<box>\<phi>]"   (* (2) *)
abbreviation "P_consistency_b_par \<equiv>  [\<^bold>\<turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<bottom>]"             (* (4.b) *)
abbreviation "circ_consistency \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<circ>\<phi>]"               (* (5) *)

(* (i) *)
(* (1) is not a tautology *)
lemma consistency_par nitpick oops (*countermodel found*)

(* (ii) *)
(* (2) implies (1) *)
lemma "star_consistency_par \<longrightarrow> consistency_par" by blast
lemma "consistency_par \<longrightarrow> star_consistency_par" nitpick oops (*countermodel found*)

(* (iii) *)
(* (5) implies (1) *)
lemma "circ_consistency \<longrightarrow> consistency_par" by simp
lemma "consistency_par \<longrightarrow> circ_consistency" nitpick oops (*countermodel found*)

(* (iv) *)
(* (2) implies (4.a) *)
lemma "star_consistency_par \<longrightarrow> P_consistency_a" by blast
lemma "P_consistency_a \<longrightarrow> star_consistency_par" nitpick oops (*countermodel found*)

(* (v) *)
(* (3) implies (4.a) *)
lemma "S_consistency \<longrightarrow> P_consistency_a" by blast
lemma "P_consistency_a \<longrightarrow> S_consistency" nitpick oops (*countermodel found*)

(* (vi) *)
(* (2) and (3) are incomparable *)
lemma "star_consistency_par \<longrightarrow> S_consistency" nitpick oops (*countermodel found*)
lemma "S_consistency \<longrightarrow> star_consistency_par" nitpick oops (*countermodel found*)
(* (3) and (1) are incomparable *)
lemma "S_consistency \<longrightarrow> consistency_par" nitpick oops (*countermodel found*)
lemma "consistency_par \<longrightarrow> S_consistency" nitpick oops (*countermodel found*)
(* (4.a) and (1) are incomparable *)
lemma "P_consistency_a \<longrightarrow> consistency_par" nitpick oops (*countermodel found*)
lemma "consistency_par \<longrightarrow> P_consistency_a" nitpick oops (*countermodel found*)

(* (vii) *)
(* (4.b) and (1) are incomparable *)
lemma "P_consistency_b_par \<longrightarrow> consistency_par" nitpick oops (*countermodel found*)
lemma "consistency_par \<longrightarrow> P_consistency_b_par" nitpick oops (*countermodel found*)
(* (4.b) and (2) are incomparable *)
lemma "P_consistency_b_par \<longrightarrow> star_consistency_par" nitpick oops (*countermodel found*)
lemma "star_consistency_par \<longrightarrow> P_consistency_b_par" nitpick oops (*countermodel found*)
(* (4.b) and (3) are incomparable *)
lemma "P_consistency_b_par \<longrightarrow> S_consistency" nitpick oops (*countermodel found*)
lemma "S_consistency \<longrightarrow> P_consistency_b_par" nitpick oops (*countermodel found*)
(* (4.b) and (4.a) are incomparable *)
lemma "P_consistency_b_par \<longrightarrow> P_consistency_a" nitpick oops (*countermodel found*)
lemma "P_consistency_a \<longrightarrow> P_consistency_b_par" nitpick oops (*countermodel found*)

(* (viii) *)
(* (5) and (2) are incomparable *)
lemma "circ_consistency \<longrightarrow> star_consistency_par" nitpick oops (*countermodel found*)
lemma "star_consistency_par \<longrightarrow> circ_consistency" nitpick oops (*countermodel found*)
(* (5) and (3) are incomparable *)
lemma "circ_consistency \<longrightarrow> S_consistency" nitpick oops (*countermodel found*)
lemma "S_consistency \<longrightarrow> circ_consistency" nitpick oops (*countermodel found*)
(* (5) and (4.a) are incomparable *)
lemma "circ_consistency \<longrightarrow> P_consistency_a" nitpick oops (*countermodel found*)
lemma "P_consistency_a \<longrightarrow> circ_consistency" nitpick oops (*countermodel found*)
(* (5) and (4.b) are incomparable *)
lemma "circ_consistency \<longrightarrow> P_consistency_b_par" nitpick oops (*countermodel found*)
lemma "P_consistency_b_par \<longrightarrow> circ_consistency" nitpick oops (*countermodel found*)

end