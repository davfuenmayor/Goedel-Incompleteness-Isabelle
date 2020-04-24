theory embedding
  imports Main
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format = 3] (*default settings*)

section \<open>Shallow Semantical Embedding SSE of paraconsistent modal logic\<close>

(** Remarks on notation:

Isabelle/HOL operators are: @{text "\<forall>, \<exists>, \<and>, \<or>, \<longrightarrow>, \<longleftrightarrow>, \<not>"}.
The symbol @{text "\<Longrightarrow>"} is the metalogical (Isabelle/HOL) turnstile.
Object-logical operators are written in bold symbols (e.g. @{text "\<^bold>\<forall>, \<^bold>\<and>, \<^bold>\<rightarrow>, \<^bold>\<not>,"})

Important: we redefine below Isabelle's symbol for classical negation @{text "\<not>"} to avoid
confusions with the notation employed in the literature on paraconsistent logic.*)
abbreviation not::"bool\<Rightarrow>bool" ("\<sim>_" [52]53) where "\<sim>\<phi> \<equiv> \<not>\<phi>" 


subsection \<open>Embedding operators as definitions/abbreviations\<close>

typedecl w                  (**type for possible worlds*)
type_synonym wo = "w\<Rightarrow>bool" (**type for propositions (i.e. characteristic functions of truth-sets)*)

(** Algebraic operations on truth-sets:*)
abbreviation top::"wo" ("\<^bold>\<top>")    where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation bottom::"wo" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation meet::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<inter>" 51) where "\<phi> \<^bold>\<inter> \<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"
abbreviation join::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<union>" 50) where "\<phi> \<^bold>\<union> \<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
abbreviation subs::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<Rightarrow>" 49) where "\<phi> \<^bold>\<Rightarrow> \<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)"
abbreviation sequ::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<approx>" 48) where "\<phi> \<^bold>\<approx> \<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"
abbreviation compl::"wo\<Rightarrow>wo" ("_\<^sup>C" [54]55)      where    "\<phi>\<^sup>C  \<equiv> \<lambda>w. \<sim>(\<phi> w)"
consts S1::"wo\<Rightarrow>wo" ("S\<^sub>\<not>")   (** introduces additional (unconstrained) constant *)
consts S2::"wo\<Rightarrow>wo" ("S\<^sub>\<circ>")   (** introduces additional (unconstrained) constant *)

(** Type-lifted ('intensionalized') boolean connectives:*)
abbreviation cand::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<and>" 51)  where "\<phi> \<^bold>\<and> \<psi>  \<equiv> \<phi> \<^bold>\<inter> \<psi> "
abbreviation cor:: "wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<or>" 50)  where "\<phi> \<^bold>\<or> \<psi>  \<equiv> \<phi> \<^bold>\<union> \<psi>"
abbreviation cimp::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<rightarrow>" 49) where  "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<^bold>\<Rightarrow> \<psi>"
abbreviation cequ::"wo\<Rightarrow>wo\<Rightarrow>wo" (infix  "\<^bold>\<leftrightarrow>" 48) where  "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> \<phi> \<^bold>\<approx> \<psi>"
abbreviation cneg::"wo\<Rightarrow>wo"      ("\<^bold>\<sim>_" [54]55)   where   "\<^bold>\<sim>\<phi>   \<equiv> \<phi>\<^sup>C"

(** Paraconsistent LFI operators:*)
abbreviation pneg::"wo\<Rightarrow>wo"      ("\<^bold>\<not>\<^sup>p_" [54]55)   where   "\<^bold>\<not>\<^sup>p\<phi>  \<equiv> \<phi>\<^sup>C \<^bold>\<union> (S\<^sub>\<not> \<phi>)" (* i.e. \<phi> \<^bold>\<rightarrow> (S\<^sub>\<not> \<phi>) *)
abbreviation pcon_dC :: "wo\<Rightarrow>wo" ("\<^bold>\<circ>\<^sup>d\<^sup>c_" [54] 55) where "   \<^bold>\<circ>\<^sup>d\<^sup>c\<phi> \<equiv> \<^bold>\<not>\<^sup>p(\<phi> \<^bold>\<and> \<^bold>\<not>\<^sup>p\<phi>)"  (* for mbC-cl*)
abbreviation pcon_ciw :: "wo\<Rightarrow>wo" ("\<^bold>\<circ>\<^sup>c\<^sup>i\<^sup>w_" [54] 55) where "\<^bold>\<circ>\<^sup>c\<^sup>i\<^sup>w\<phi>  \<equiv> \<^bold>\<sim>(\<phi> \<^bold>\<and> \<^bold>\<not>\<^sup>p\<phi>)"  (* for mbC-ciw*)
abbreviation pcon_mbC::"wo\<Rightarrow>wo"  ("\<^bold>\<circ>\<^sup>m\<^sup>b\<^sup>c_" [54]55) where   "\<^bold>\<circ>\<^sup>m\<^sup>b\<^sup>c\<phi>  \<equiv> \<^bold>\<circ>\<^sup>c\<^sup>i\<^sup>w\<phi> \<^bold>\<and> (S\<^sub>\<circ> \<phi>)"

(** Accessibility relation and modal operators:*)
consts aRel::"w\<Rightarrow>w\<Rightarrow>bool" (infix "r" 70)
abbreviation mbox :: "wo\<Rightarrow>wo" ("\<^bold>\<box>_"[54]55) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v) \<longrightarrow> (\<phi> v)"
abbreviation mdia :: "wo\<Rightarrow>wo" ("\<^bold>\<diamond>_"[54]55) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v) \<and> (\<phi> v)" (*i.e. \<sim>\<box>\<sim>\<phi> *)

subsection \<open>Meta-logical predicates for validity and consequence\<close>

abbreviation valid::"wo\<Rightarrow>bool"       ("[\<^bold>\<turnstile> _]") where  "[\<^bold>\<turnstile>  \<phi>]  \<equiv> \<forall>w. \<phi> w"  (**i.e. truth in all worlds*)
abbreviation satisfiable::"wo\<Rightarrow>bool" ("[\<^bold>\<turnstile>\<^sup>s\<^sup>a\<^sup>t_]") where "[\<^bold>\<turnstile>\<^sup>s\<^sup>a\<^sup>t \<phi>] \<equiv> \<exists>w. \<phi> w"  (**i.e. truth in some world*)
abbreviation invalid::"wo\<Rightarrow>bool"     ("[\<^bold>\<turnstile>\<^sup>i\<^sup>n\<^sup>v_]") where "[\<^bold>\<turnstile>\<^sup>i\<^sup>n\<^sup>v \<phi>] \<equiv> \<forall>w. \<sim>\<phi> w" (**i.e. falsity in all worlds*)

abbreviation conseq_global::"wo\<Rightarrow>wo\<Rightarrow>bool" ("[_ \<^bold>\<turnstile>\<^sub>g _]") where 
    "[\<phi> \<^bold>\<turnstile>\<^sub>g \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi>] \<longrightarrow> [\<^bold>\<turnstile> \<psi>]"
abbreviation conseq_local::"wo\<Rightarrow>wo\<Rightarrow>bool" ("[_ \<^bold>\<turnstile>\<^sub>l _]") where 
    "[\<phi> \<^bold>\<turnstile>\<^sub>l \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi> \<^bold>\<rightarrow> \<psi>]"
abbreviation equ_global::"wo\<Rightarrow>wo\<Rightarrow>bool" ("[_ \<cong>\<^sub>g _]") where 
    "[\<phi> \<cong>\<^sub>g \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi>] \<longleftrightarrow> [\<^bold>\<turnstile> \<psi>]"
abbreviation equ_local::"wo\<Rightarrow>wo\<Rightarrow>bool" ("[_ \<cong>\<^sub>l _]") where 
    "[\<phi> \<cong>\<^sub>l \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi> \<^bold>\<leftrightarrow> \<psi>]"
abbreviation conseq_global2::"wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile>\<^sub>g _]") where 
    "[\<phi>, \<gamma> \<^bold>\<turnstile>\<^sub>g \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi>] \<longrightarrow> ([\<^bold>\<turnstile> \<gamma>] \<longrightarrow> [\<^bold>\<turnstile> \<psi>])"
abbreviation conseq_local2::"wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile>\<^sub>l _]") where 
    "[\<phi>, \<gamma> \<^bold>\<turnstile>\<^sub>l \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi> \<^bold>\<rightarrow> (\<gamma> \<^bold>\<rightarrow> \<psi>)]"
abbreviation conseq_global3::"wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>bool" ("[_,_,_ \<^bold>\<turnstile>\<^sub>g _]") where 
    "[\<phi>, \<gamma>, \<eta> \<^bold>\<turnstile>\<^sub>g \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi>] \<longrightarrow> ([\<^bold>\<turnstile> \<gamma>] \<longrightarrow> [\<^bold>\<turnstile> \<eta>] \<longrightarrow> [\<^bold>\<turnstile> \<psi>])"
abbreviation conseq_local3::"wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>wo\<Rightarrow>bool" ("[_,_,_ \<^bold>\<turnstile>\<^sub>l _]") where 
    "[\<phi>, \<gamma>, \<eta> \<^bold>\<turnstile>\<^sub>l \<psi>] \<equiv> [\<^bold>\<turnstile> \<phi> \<^bold>\<rightarrow> \<gamma> \<^bold>\<rightarrow> \<eta> \<^bold>\<rightarrow> \<psi>]"

subsection \<open>Verifying some meta-logical properties\<close>

lemma mod: "[\<^bold>\<box>a \<cong>\<^sub>l \<^bold>\<sim>\<^bold>\<diamond>\<^bold>\<sim>a]" by simp
theorem K: "[\<^bold>\<box>(p \<^bold>\<rightarrow> q) \<^bold>\<turnstile>\<^sub>l \<^bold>\<box>p \<^bold>\<rightarrow> \<^bold>\<box>q]" by simp
theorem Nec: "[a \<^bold>\<turnstile>\<^sub>g \<^bold>\<box>a]" by simp
theorem local_implies_global_conseq: "[a \<^bold>\<turnstile>\<^sub>l b] \<longrightarrow> [a \<^bold>\<turnstile>\<^sub>g b]" by simp

(** Note that we use the Isabelle's keywork 'nitpick' to indicate that we invoke a model finder,
called Nitpick, to find a countermodel (default behaviour) or to find a satisfying model
(in which case it will be indicated explicitly by providing the option 'satisfy').
Below we invoke Nitpick to find a counterexample and it succeeds: *)
theorem global_doesnt_imply_local_conseq: "[a \<^bold>\<turnstile>\<^sub>g b] \<longrightarrow> [a \<^bold>\<turnstile>\<^sub>l b]" nitpick[card w=2] oops (* counterexample found*)

subsection \<open>Extensions\<close>

(** We introduce unrestricted quantification for objects of arbitrary type: *)  
abbreviation mforall ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
abbreviation mexists ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"   
abbreviation mforallB (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation mexistsB (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"

(** We introduce some useful abbreviations (for future use as axioms): *)
abbreviation "T_ax   \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>]" (** aka. M *)
abbreviation "B_ax   \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<diamond>\<phi>]"
abbreviation "D_ax   \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>]"
abbreviation "IV_ax  \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>]"
abbreviation "V_ax   \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>]"
abbreviation "D_sem  \<equiv> \<forall>x. \<exists>y. x r y" (** i.e. frame seriality*)
abbreviation "T_sem  \<equiv> \<forall>x. x r x" (** i.e. frame reflexivity*)
abbreviation "IV_sem \<equiv> \<forall>x y z. x r y \<and> y r z \<longrightarrow> x r z" (** i.e. frame transitivity*)

(** We verify some Sahlqvist correspondences: *)
lemma D_char1: "D_sem \<longrightarrow> D_ax" by auto
lemma D_char2: "D_ax \<longrightarrow> D_sem" by auto
lemma T_char1: "T_sem \<longrightarrow> T_ax" by simp
lemma T_char2: "T_ax \<longrightarrow> T_sem" by blast
lemma IV_char1: "IV_sem \<longrightarrow> IV_ax" by blast
lemma IV_char2: "IV_ax \<longrightarrow> IV_sem" by blast

abbreviation "L_ax    \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>(\<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>]"
abbreviation "LR_rule  \<equiv> \<forall>\<phi>. [\<^bold>\<turnstile> \<^bold>\<box>\<phi>\<^bold>\<rightarrow>\<phi>] \<longrightarrow>  [\<^bold>\<turnstile> \<phi>]"

(** Axiom L is strictly stronger than rule LR *)
lemma "L_ax \<longrightarrow> LR_rule" by blast
lemma "LR_rule \<longrightarrow> L_ax" nitpick oops (*countermodel found*)

(** axioms L and T are inconsistent *)
lemma "\<lbrakk>L_ax; T_ax\<rbrakk> \<Longrightarrow> False" by blast
(** rule LR and axiom T are inconsistent *)
lemma "\<lbrakk>LR_rule; T_ax\<rbrakk> \<Longrightarrow> False" by blast

(** axioms L and D are also inconsistent *)
lemma "\<lbrakk>L_ax; D_ax\<rbrakk> \<Longrightarrow> False" by (metis bot2E)
(** rule LR and axiom D are also inconsistent *)
lemma "\<lbrakk>LR_rule; D_ax\<rbrakk> \<Longrightarrow> False" by (metis bot2E)

end