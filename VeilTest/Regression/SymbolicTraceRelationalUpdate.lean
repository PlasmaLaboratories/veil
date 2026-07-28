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

-- Mirrored equation orientation: the updated function on the right-hand side.
set_option warningAsError true in
example (α : Type) [DecidableEq α] (b p : α)
    (ancestor next : α → α → Bool)
    (h :
      ∀ x y,
        next x y =
          (if b = x then decide (y = p ∨ ancestor p y = true) else ancestor x y)) :
    next b p = true := by
  veil_simp only [smtSimp] at h
  veil_smt

-- Conditional `decide` in the else branch.
set_option warningAsError true in
example (α : Type) [DecidableEq α] (b q p : α) (hq : b ≠ q)
    (ancestor next : α → α → Bool)
    (h :
      ∀ x y,
        (if b = x then ancestor x y else decide (y = p ∨ ancestor p y = true)) =
          next x y) :
    next q p = true := by
  veil_simp only [smtSimp] at h
  veil_smt

-- Else-branch `decide` with the mirrored equation orientation.
set_option warningAsError true in
example (α : Type) [DecidableEq α] (b q p : α) (hq : b ≠ q)
    (ancestor next : α → α → Bool)
    (h :
      ∀ x y,
        next x y =
          (if b = x then ancestor x y else decide (y = p ∨ ancestor p y = true))) :
    next q p = true := by
  veil_simp only [smtSimp] at h
  veil_smt
