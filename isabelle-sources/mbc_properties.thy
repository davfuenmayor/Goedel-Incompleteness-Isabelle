(*<*)
theory mbc_properties
  imports embedding
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3]
(*>*)

section \<open>mbC Properties\<close>

abbreviation neg :: "wo\<Rightarrow>wo" ("\<^bold>\<not>_" [54] 55) where "\<^bold>\<not>\<phi> \<equiv> \<^bold>\<not>\<^sup>p\<phi>" (* negation is paraconsistent*)
abbreviation circ :: "wo\<Rightarrow>wo" ("\<^bold>\<circ>_" [54] 55) where "\<^bold>\<circ>\<phi> \<equiv> \<^bold>\<circ>\<^sup>m\<^sup>b\<^sup>c\<phi>" (* logic is (R)mbC *)

(* (1) *)
lemma "[a \<^bold>\<and> \<^bold>\<not>a \<^bold>\<turnstile>\<^sub>l \<^bold>\<not>\<^bold>\<circ>a]" by simp
lemma "[\<^bold>\<not>\<^bold>\<circ>a \<^bold>\<turnstile>\<^sub>l a \<^bold>\<and> \<^bold>\<not>a]" nitpick oops (* countermodel found *) 

(* (2) *)
lemma "[\<^bold>\<circ>a \<^bold>\<turnstile>\<^sub>l \<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a)]" by simp 
lemma "[\<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a) \<^bold>\<turnstile>\<^sub>l \<^bold>\<circ>a]" nitpick oops (* countermodel found *) 

(* (3) *)
lemma "[\<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile>\<^sub>l a \<^bold>\<or> b]" by blast
lemma "[a \<^bold>\<or> b \<^bold>\<turnstile>\<^sub>l \<^bold>\<not>a \<^bold>\<rightarrow> b]" nitpick oops (* countermodel found *)

(* (4) *)
lemma "[\<^bold>\<circ>a, a \<^bold>\<or> b  \<^bold>\<turnstile>\<^sub>l \<^bold>\<not>a \<^bold>\<rightarrow> b]" by simp

(* (5) *)
lemma "[a \<^bold>\<rightarrow> b \<^bold>\<turnstile>\<^sub>l \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops (* countermodel found *)
lemma "[\<^bold>\<circ>b, a \<^bold>\<rightarrow> b \<^bold>\<turnstile>\<^sub>l \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" by blast

(* (6) *)
lemma "[a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile>\<^sub>l b \<^bold>\<rightarrow> \<^bold>\<not>a]" nitpick oops (* countermodel found *)
lemma "[\<^bold>\<circ>b, a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile>\<^sub>l b \<^bold>\<rightarrow> \<^bold>\<not>a]" by blast

(* (7) *)
lemma "[\<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile>\<^sub>l \<^bold>\<not>b \<^bold>\<rightarrow> a]" nitpick oops (* countermodel found *)
lemma "[\<^bold>\<circ>b, \<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile>\<^sub>l \<^bold>\<not>b \<^bold>\<rightarrow> a]" by blast

(* (8) *)
lemma "[\<^bold>\<not>a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile>\<^sub>l b \<^bold>\<rightarrow> a]" nitpick oops (* countermodel found *)
lemma "[\<^bold>\<circ>b, \<^bold>\<not>a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile>\<^sub>l b \<^bold>\<rightarrow> a]" by blast

(*<*)
end
(*>*)