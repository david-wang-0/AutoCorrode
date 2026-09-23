theory C
  imports B
begin

text \<open>Innocent theory between B and D: green whether or not \<open>foo_loop\<close> is enabled in A.
  (Put a \<open>simp\<close> on a \<open>foo\<close> term here instead of in D to see the limitation: PIDE forks
  terminal proofs, so a spin here would not block D, and a wait on D would not notice it.)\<close>

lemma c_foo_zero: "foo 5 = 0"
  unfolding foo_def by (rule refl)

lemma c_arith: "(3::nat) + 3 = 6"
  by simp

end
