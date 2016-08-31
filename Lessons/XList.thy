theory XList
imports Main
begin

declare [[names_short]]

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

lemma app_nil [simp] : "app xs Nil = xs"
apply(induction xs)
apply simp
apply simp
done

lemma app_assoc [simp] : "app (app xs ys) zs = app xs (app ys zs)"
apply(induction xs arbitrary: ys zs)
apply simp
apply simp
done

lemma rev_app [simp] : "rev (app xs ys) = app (rev ys) (rev xs)"
apply(induction xs arbitrary: ys)
apply simp
apply simp
done

theorem rev_rev: "rev (rev xs) = xs"
apply(induction xs)
apply(simp)
apply(simp)
done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev Nil ys = ys" |
"itrev (Cons x xs) ys = itrev xs (Cons x ys)"

lemma itrev_rev0 [simp] : "itrev xs ys = app (rev xs) ys"
apply (induction xs arbitrary: ys)
apply simp
apply simp
done

theorem itrev_rev : "itrev xs Nil = rev xs"
apply simp
done

end