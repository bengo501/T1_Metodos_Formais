theory T1_2026_1
  imports Main
begin

(* Coloque aqui o nome dos integrantes do grupo *)

primrec pot :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
poteq1: "pot x 0 = 1" |
poteq2: "pot x (Suc y) = x * pot x y"

lemma t1: "\<forall>x m::nat. pot x (m + n) = pot x m * pot x n"
proof
  fix x m :: nat
  show "pot x (m + n) = pot x m * pot x n"
  proof (induction m)
    case 0
    calc
      pot x (0 + n) = pot x n
        by simp
      also have "... = 1 * pot x n"
        by (simp only: one_mult[symmetric])
      also have "... = pot x 0 * pot x n"
        by (simp only: poteq1)
      finally show ?case .
  next
    case (Suc m)
    have ih: "pot x (m + n) = pot x m * pot x n"
      using Suc.IH .
    calc
      pot x (Suc m + n) = pot x (Suc (m + n))
        by simp
      also have "... = x * pot x (m + n)"
        by (simp only: poteq2)
      also have "... = x * (pot x m * pot x n)"
        by (simp only: ih)
      also have "... = (x * pot x m) * pot x n"
        by (simp only: mult_assoc)
      also have "... = pot x (Suc m) * pot x n"
        by (simp only: poteq2)
      finally show ?case .
  qed
qed

theorem t2: "\<forall>x m::nat. pot x (m * n) = pot (pot x m) n"
proof
  fix x m :: nat
  show "pot x (m * n) = pot (pot x m) n"
  proof (induction n)
    case 0
    calc
      pot x (m * 0) = pot x 0
        by simp
      also have "... = 1"
        by (simp only: poteq1)
      also have "... = pot (pot x m) 0"
        by (simp only: poteq1)
      finally show ?case .
  next
    case (Suc n)
    have ih: "pot x (m * n) = pot (pot x m) n"
      using Suc.IH .
    have h1: "pot x (m * n + m) = pot x (m * n) * pot x m"
      using t1[rule_format, of x "m * n", where n=m] .
    calc
      pot x (m * Suc n) = pot x (m * n + m)
        by simp
      also have "... = pot x (m * n) * pot x m"
        by (rule h1)
      also have "... = pot (pot x m) n * pot x m"
        by (simp only: ih)
      also have "... = pot x m * pot (pot x m) n"
        by (simp only: mult_comm)
      also have "... = pot (pot x m) (Suc n)"
        by (simp only: poteq2)
      finally show ?case .
  qed
qed

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
proof (induction xs)
  case Nil
  show "\<forall>ys::nat list. somatorio (cat [] ys) = somatorio [] + somatorio ys"
  proof
    fix ys :: "nat list"
    calc
      somatorio (cat [] ys) = somatorio ys
        by (simp only: cateq1)
      also have "... = 0 + somatorio ys"
        by (simp only: add_0_left)
      also have "... = somatorio [] + somatorio ys"
        by (simp only: somaeq1)
      finally show "somatorio (cat [] ys) = somatorio [] + somatorio ys" .
  qed
next
  case (Cons x xs)
  have ih: "\<forall>ys::nat list. somatorio (cat xs ys) = somatorio xs + somatorio ys"
    using Cons.IH .
  show "\<forall>ys::nat list. somatorio (cat (x # xs) ys) = somatorio (x # xs) + somatorio ys"
  proof
    fix ys :: "nat list"
    calc
      somatorio (cat (x # xs) ys) = somatorio (x # cat xs ys)
        by (simp only: cateq2)
      also have "... = x + somatorio (cat xs ys)"
        by (simp only: somaeq2)
      also have "... = x + (somatorio xs + somatorio ys)"
        by (simp only: ih)
      also have "... = (x + somatorio xs) + somatorio ys"
        by (simp only: add_assoc)
      also have "... = somatorio (x # xs) + somatorio ys"
        by (simp only: somaeq2)
      finally show "somatorio (cat (x # xs) ys) = somatorio (x # xs) + somatorio ys" .
  qed
qed

theorem t4: "somatorio (reverso xs) = somatorio xs"
proof (induction xs)
  case Nil
  show ?case
    by (simp only: reveq1 somaeq1)
next
  case (Cons x xs)
  have ih: "somatorio (reverso xs) = somatorio xs"
    using Cons.IH .
  have hcat: "somatorio (cat (reverso xs) [x]) = somatorio (reverso xs) + somatorio [x]"
    using t3[rule_format, where xs="reverso xs", of "[x]"] .
  have hsingle: "somatorio [x] = x"
  proof -
    calc
      somatorio [x] = somatorio (x # [])
        by simp
      also have "... = x + somatorio []"
        by (simp only: somaeq2)
      also have "... = x + 0"
        by (simp only: somaeq1)
      also have "... = x"
        by (simp only: add_0_right)
      finally show ?thesis .
  qed
  calc
    somatorio (reverso (x # xs)) = somatorio (cat (reverso xs) [x])
      by (simp only: reveq2)
    also have "... = somatorio (reverso xs) + somatorio [x]"
      by (rule hcat)
    also have "... = somatorio xs + somatorio [x]"
      by (simp only: ih)
    also have "... = somatorio xs + x"
      by (simp only: hsingle)
    also have "... = x + somatorio xs"
      by (simp only: add_comm)
    also have "... = somatorio (x # xs)"
      by (simp only: somaeq2)
    finally show ?case .
qed

end