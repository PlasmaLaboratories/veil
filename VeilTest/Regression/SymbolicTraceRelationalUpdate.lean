import Veil

/-!
Regression for symbolic traces over a point update whose value reads the
pre-state relation. This is the shape used to extend block ancestry in VFHS.
-/

veil module SymbolicTraceRelationalUpdate

type replica
type block
type view
type quorum

instantiate tot : TotalOrder view

immutable individual genesis : block
immutable individual genesisView : view
immutable relation member (R : replica) (Q : quorum)
immutable relation byz (R : replica)
immutable relation succ (V1 : view) (V2 : view)

relation proposed (B : block)
relation blockView (B : block) (V : view)
relation parentOf (B : block) (P : block)
relation justView (B : block) (V : view)
relation directJust (B : block)
relation ancestor (B : block) (A : block)
relation voted (R : replica) (V : view) (B : block)
relation qcOn (B : block) (V : view)
relation knowsQC (R : replica) (B : block) (V : view)
relation sentNewView (R : replica) (TV : view) (B : block) (HV : view)
relation vcTimedView (B : block) (TV : view)
relation vcQuorum (B : block) (Q : quorum)
relation finalized (B : block)

#gen_state

after_init {
  proposed B := decide $ B = genesis
  blockView B V := decide $ B = genesis ∧ V = genesisView
  parentOf B P := false
  justView B V := false
  directJust B := false
  ancestor B A := false
  voted R V B := false
  qcOn B V := decide $ B = genesis ∧ V = genesisView
  knowsQC R B V := decide $ B = genesis ∧ V = genesisView
  sentNewView R TV B HV := false
  vcTimedView B TV := false
  vcQuorum B Q := false
  finalized B := false
}

assumption [quorum_intersection]
  ∀ (Q1 : quorum) (Q2 : quorum), ∃ (N : replica), member N Q1 ∧ member N Q2 ∧ ¬ byz N
assumption [succ_lt]
  ∀ (V1 : view) (V2 : view), succ V1 V2 → tot.le V1 V2 ∧ V1 ≠ V2
assumption [succ_functional]
  ∀ (V : view) (V1 : view) (V2 : view), succ V V1 ∧ succ V V2 → V1 = V2
assumption [succ_no_between]
  ∀ (V1 : view) (V2 : view) (W : view),
    succ V1 V2 → ¬ (tot.le V1 W ∧ V1 ≠ W ∧ tot.le W V2 ∧ W ≠ V2)

action propose_direct (b : block) (p : block) (v : view) (pv : view) {
  require ¬ proposed b
  require b ≠ genesis
  require proposed p
  require blockView p pv
  require qcOn p pv
  require succ pv v
  proposed b := true
  blockView b v := true
  parentOf b p := true
  justView b pv := true
  directJust b := true
  ancestor b A := decide $ A = p ∨ ancestor p A
}

invariant true

#gen_spec

sat trace [propose_direct_reachable] {
  propose_direct
  assert (∃ b, b ≠ genesis ∧ proposed b)
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
