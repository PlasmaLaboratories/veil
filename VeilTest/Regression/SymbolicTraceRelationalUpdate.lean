import Veil

/-!
Regression for symbolic traces over a point update whose value reads the
pre-state relation. This is the shape used to extend block ancestry in VFHS.
-/

veil module SymbolicTraceRelationalUpdate

type block

immutable individual genesis : block

relation proposed (B : block)
relation parentOf (B : block) (P : block)
relation ancestor (B : block) (A : block)

#gen_state

after_init {
  proposed B := decide $ B = genesis
  parentOf B P := false
  ancestor B A := false
}

action extend_ancestry (b : block) (p : block) {
  require ¬ proposed b
  require b ≠ genesis
  require proposed p
  proposed b := true
  parentOf b p := true
  ancestor b A := decide $ A = p ∨ ancestor p A
}

invariant true

#gen_spec

sat trace [extend_ancestry_reachable] {
  extend_ancestry
  assert (∃ b, b ≠ genesis ∧ proposed b ∧ ancestor b genesis)
}

end SymbolicTraceRelationalUpdate

-- Keep the Bool representation shape exercised directly: if `smtSimp` leaves
-- the nested `decide` in place, lean-smt sees its `Decidable` argument as a
-- first-class sort and reports `cannot translate Type`.
set_option warningAsError true in
example (α : Type) [DecidableEq α] (b p : α)
    (ancestor next : α → α → Bool)
    (h :
      ∀ x y,
        (if b = x then decide (y = p ∨ ancestor p y = true) else ancestor x y) =
          next x y) :
    next b p = true := by
  veil_simp only [smtSimp] at h
  veil_smt
