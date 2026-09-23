theory A
  imports Main
begin

text \<open>
  Root of the fixture chain A \<rightarrow> B \<rightarrow> C \<rightarrow> D used to demonstrate I/Q stall detection.

  \<open>foo\<close> and \<open>bar\<close> are both constantly 0. The commented-out lemma below is true, but as
  simp rules its two equations rewrite \<open>foo n \<rightarrow> bar n \<rightarrow> foo n \<rightarrow> \<dots>\<close> forever, with
  constant term size, so the simplifier neither terminates nor runs out of memory.
  (A single rule \<open>foo n = foo (Suc n)\<close> would not do: the simplifier reorients a rule
  whose right-hand side is an instance of its left-hand side.) A, B and C stay
  green either way; the first \<open>simp\<close> on a \<open>foo\<close> term is in D, at the end of the chain,
  so that is where the proof spins. This is the "upstream change breaks something
  further down the chain" situation.
\<close>

definition foo :: "nat \<Rightarrow> nat" where
  "foo n = 0"

definition bar :: "nat \<Rightarrow> nat" where
  "bar n = 0"

lemma foo_const: "foo n = foo m"
  by (simp add: foo_def)

\<comment> \<open>Uncomment to make C diverge (demo_stall.py toggles this line):\<close>
(* lemma foo_loop [simp]: "foo n = bar n" "bar n = foo n" by (simp_all add: foo_def bar_def) *)

end
