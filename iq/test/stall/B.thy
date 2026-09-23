theory B
  imports A
begin

text \<open>Innocent middle theory: green whether or not \<open>foo_loop\<close> is enabled in A.\<close>

lemma b_foo_zero: "foo 7 = 0"
  unfolding foo_def by (rule refl)

lemma b_arith: "(2::nat) + 2 = 4"
  by simp

end
