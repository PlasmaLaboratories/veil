import Veil

/-!
Regression for `Next.tr_abstract` generation when an action has several
parameters and its transition carries generated `Decidable` arguments.

The per-action weakening theorem and the transition stored in the assembled
`Next` relation can elaborate with propositionally equal, but not
definitionally identical, `Decidable` instances. The generated proof must
neutralize those instances without changing the abstract states being compared.
-/

veil module NextTransitionAbstractParameterizedAction

type node
type seq_t

instantiate seq : TotalOrderWithMinimum seq_t

relation pending : node → node → seq_t → Bool
function latest : node → node → seq_t

#gen_state

after_init {
  pending N M R := false;
  latest N M := seq.zero
}

action receive (n : node) (m : node) (r : seq_t) {
  require pending n m r;
  latest n m := if seq.le r (latest n m) then latest n m else r
}

safety [latestRefl] latest N M = latest N M

#gen_spec

end NextTransitionAbstractParameterizedAction
