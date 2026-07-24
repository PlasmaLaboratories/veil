import Veil

/-!
# Regression: failed declarations block specification finalization

Lean can recover from a command elaboration error, and `#guard_msgs` deliberately
does so in batch tests. A failed Veil declaration must remain visible to
`#gen_spec`; otherwise finalization silently assembles and verifies a weaker
specification with the failed declaration omitted.
-/

set_option linter.unusedVariables false

veil module FailedDeclarationFinalization

individual flag : Bool

/-- error: unable to extract type from binder failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation) -/
#guard_msgs in
relation omitted {badBinder : Bool}

#gen_state

after_init { flag := false }

action keep { flag := false }

invariant [valid] flag = false

/-- error: Unbound uncapitalized variable: nonexistent_pred -/
#guard_msgs in
invariant [broken] nonexistent_pred flag

/-- error: Cannot finalize Veil module FailedDeclarationFinalization: 2 Veil declarations failed to elaborate. -/
#guard_msgs in
#gen_spec

end FailedDeclarationFinalization
