theory D
  imports C
begin

text \<open>End of the chain, and the first \<open>simp\<close> on a \<open>foo\<close> term. Green while \<open>foo_loop\<close>
  in A is commented out; once it is a simp rule, \<open>d_ok\<close> sits in PIDE \<open>running\<close> forever.\<close>

lemma d_ok: "foo 3 + 0 = foo 3"
  by simp

lemma d_after: "(4::nat) + 4 = 8"
  by simp

end
