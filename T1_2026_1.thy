theory T1_2026_1
  imports Main
begin

(* Coloque aqui o nome dos integrantes do grupo *)

primrec pot :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
poteq1: "pot x 0 = 1" |
poteq2: "pot x (Suc y) = x * pot x y"

lemma t1: "\<forall>x m::nat. pot x (m + n) = pot x m * pot x n"
proof (intro allI)
  fix x m :: nat
  show "pot x (m + n) = pot x m * pot x n"
  proof (induction m)
    case 0
    show ?case
    proof -
      have add0: "0 + n = n"
        by (simp only: add_0_left)
      have "pot x (0 + n) = pot x n"
        by (rule arg_cong [of _ _ "pot x"]) (rule add0)
      also have "pot x n = 1 * pot x n"
        by (simp only: mult_1_left[symmetric])
      also have "1 * pot x n = pot x 0 * pot x n"
        by (simp only: poteq1)
      finally show ?thesis .
    qed
  next
    case (Suc m)
    have ih: "pot x (m + n) = pot x m * pot x n"
      using Suc.IH .
    show ?case
    proof -
      have addSuc: "Suc m + n = Suc (m + n)"
        by (simp only: add_Suc)
      have "pot x (Suc m + n) = pot x (Suc (m + n))"
        by (rule arg_cong [of _ _ "pot x"]) (rule addSuc)
      also have "pot x (Suc (m + n)) = x * pot x (m + n)"
        by (simp only: poteq2)
      also have "x * pot x (m + n) = x * (pot x m * pot x n)"
        by (simp only: ih)
      also have "x * (pot x m * pot x n) = (x * pot x m) * pot x n"
        by (simp only: mult.assoc)
      also have "(x * pot x m) * pot x n = pot x (Suc m) * pot x n"
        by (simp only: poteq2)
      finally show ?thesis .
    qed
  qed
qed

theorem t2: "\<forall>x m::nat. pot x (m * n) = pot (pot x m) n"
proof (intro allI)
  fix x m :: nat
  show "pot x (m * n) = pot (pot x m) n"
  proof (induction n)
    case 0
    (* indução em n: recursão de * no segundo argumento; caso n = 0 *)
    show ?case
    proof -
      have mul0: "m * 0 = 0"
        by (simp only: mult_0_right)
      have "pot x (m * 0) = pot x 0"
        by (rule arg_cong [of _ _ "pot x"]) (rule mul0)
      also have "pot x 0 = 1"
        by (simp only: poteq1)
      also have "1 = pot (pot x m) 0"
        by (simp only: poteq1[symmetric])
      finally show ?thesis .
    qed
  next
    case (Suc n)
    have ih: "pot x (m * n) = pot (pot x m) n"
      using Suc.IH .
    (* instanciar t1: expoente (m * n) + m, segundo expoente em t1 é o parâmetro livre n := m *)
    have h_t1: "pot x (m * n + m) = pot x (m * n) * pot x m"
      using t1[rule_format, of x "m * n", where n=m] .
    show ?case
    proof -
      (* definir multiplicação no sucessor: m * Suc n = m * n + m *)
      have mulSuc: "m * Suc n = m * n + m"
        by (simp only: mult_Suc_right)
      have "pot x (m * Suc n) = pot x (m * n + m)"
        by (rule arg_cong [of _ _ "pot x"]) (rule mulSuc)
      also have "pot x (m * n + m) = pot x (m * n) * pot x m"
        by (rule h_t1)
      also have "pot x (m * n) * pot x m = pot (pot x m) n * pot x m"
        by (simp only: ih)
      also have "pot (pot x m) n * pot x m = pot x m * pot (pot x m) n"
        by (simp only: mult.commute)
      also have "pot x m * pot (pot x m) n = pot (pot x m) (Suc n)"
        by (simp only: poteq2)
      finally show ?thesis .
    qed
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
    (* caso xs = []: cat e somatorio da lista vazia; ys arbitrário fixo *)
    have "somatorio (cat [] ys) = somatorio ys"
      by (simp only: cateq1)
    also have "somatorio ys = 0 + somatorio ys"
      by (simp only: add_0_left[symmetric])
    also have "0 + somatorio ys = somatorio [] + somatorio ys"
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
    (* passo: HI universal em ys; depois associatividade da soma *)
    have "somatorio (cat (x # xs) ys) = somatorio (x # cat xs ys)"
      by (simp only: cateq2)
    also have "somatorio (x # cat xs ys) = x + somatorio (cat xs ys)"
      by (simp only: somaeq2)
    also have "x + somatorio (cat xs ys) = x + (somatorio xs + somatorio ys)"
      by (simp only: ih)
    also have "x + (somatorio xs + somatorio ys) = (x + somatorio xs) + somatorio ys"
      by (simp only: add.assoc)
    also have "(x + somatorio xs) + somatorio ys = somatorio (x # xs) + somatorio ys"
      by (simp only: somaeq2)
    finally show "somatorio (cat (x # xs) ys) = somatorio (x # xs) + somatorio ys" .
  qed
qed

theorem t4: "somatorio (reverso xs) = somatorio xs"
proof (induction xs)
  case Nil
  (* caso base: reverso [] = []; mesmo somatório *)
  show ?case
    by (simp only: reveq1)
next
  case (Cons x xs)
  have ih: "somatorio (reverso xs) = somatorio xs"
    using Cons.IH .
  (* t3 com xs := reverso xs e ys := [x] *)
  have hcat: "somatorio (cat (reverso xs) [x]) = somatorio (reverso xs) + somatorio [x]"
    using t3[rule_format, where xs="reverso xs", of "[x]"] .
  have hsingle: "somatorio [x] = x"
  proof -
    (* notação [x] coincide com x # []; depois somaeq2, somaeq1, neutro à direita *)
    have "somatorio [x] = x + somatorio []"
      by (simp only: somaeq2)
    also have "\<dots> = x + 0"
      by (simp only: somaeq1)
    also have "\<dots> = x"
      by (simp only: add_0_right)
    finally show ?thesis .
  qed
  show ?case
  proof -
    have "somatorio (reverso (x # xs)) = somatorio (cat (reverso xs) [x])"
      by (simp only: reveq2)
    also have "\<dots> = somatorio (reverso xs) + somatorio [x]"
      by (rule hcat)
    also have "\<dots> = somatorio xs + somatorio [x]"
      by (simp only: ih)
    also have "\<dots> = somatorio xs + x"
      by (simp only: hsingle)
    also have "\<dots> = x + somatorio xs"
      by (simp only: add.commute)
    also have "\<dots> = somatorio (x # xs)"
      by (simp only: somaeq2)
    finally show ?thesis .
  qed
qed

end