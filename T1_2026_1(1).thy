theory T1_2026_1
  imports Main
begin

(* Coloque aqui o nome dos integrantes do grupo *)

primrec pot :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
poteq1: "pot x 0 = 1" |
poteq2: "pot x (Suc y) = x * pot x y"

lemma t1: "\<forall>x m::nat. pot x (m + n) = pot x m * pot x n"
  sorry

theorem t2: "\<forall>x m::nat. pot x (m * n) = pot (pot x m) n"
  sorry

primrec cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
cateq1: "cat [] ys = ys" |
cateq2: "cat (x#xs) ys = x#cat xs ys"

primrec reverso :: "'a list \<Rightarrow> 'a list" where
reveq1: "reverso [] = []" |
reveq2: "reverso (x#xs) = cat (reverso xs) [x]"

primrec somatorio :: "nat list \<Rightarrow> nat" where
somaeq1: "somatorio [] = 0" |
somaeq2: "somatorio (x#xs) = x + somatorio xs"

lemma t3: "\<forall>ys::nat list. somatorio (cat xs ys) = somatorio xs + somatorio ys"
  sorry

theorem t4: "somatorio (reverso xs) = somatorio xs"
  sorry

end