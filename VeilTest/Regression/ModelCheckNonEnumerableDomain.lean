import Veil

/-!
# Regression: explicit-state model checking rejects unsafe hybrid fields

For a relation/function over a non-enumerable domain, the default concrete
representation is hybrid. A quantified update can turn it into a canonical
function whose placeholder hash collapses distinct states. Explicit-state
model checking must reject that query rather than report a false SAFE result.
-/

veil module ModelCheckNonEnumerableDomain

relation r : Nat → Bool

#gen_state

after_init { r N := false }

action set5 { r 5 := true }

invariant [no5] ¬ r 5

#gen_spec

/--
error: Explicit-state model checking cannot soundly fingerprint field 'r': its non-enumerable domain can be represented canonically after an unrestricted update. Use a finite instantiation or SMT verification instead.
-/
#guard_msgs in
#model_check interpreted {} {}

end ModelCheckNonEnumerableDomain

-- Finite domains have an `Enumeration`, so quantified updates stay in the
-- concrete representation and explicit-state model checking remains enabled.
veil module ModelCheckEnumerableDomain

relation r : Fin 6 → Bool

#gen_state

after_init { r N := false }

action keep5False { r 5 := false }

invariant [no5] ¬ r 5

#gen_spec

/-- info: ✅ No violation (explored 1 states) -/
#guard_msgs(info) in
#model_check interpreted {} {}

end ModelCheckEnumerableDomain
