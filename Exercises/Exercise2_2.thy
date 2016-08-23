theory Exercise2_2
imports Main
begin
fun add::"nat\<Rightarrow>nat\<Rightarrow>nat" where
"add 0 n = n"|
"add (Suc m) n = Suc(add m n)"

lemma add_02: "add m 0 = m"
apply(induction m)
apply(auto)
done

thm add_02

lemma add_assoc: "add (add x y) z = add x (add y z)"
apply(induction x)
apply(auto)
done

lemma add_cum: "add x y = add y x"
apply(induction x)
apply auto




end