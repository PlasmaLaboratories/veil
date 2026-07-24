import Veil

set_option veil.__modelCheckCompileMode true

veil module CompileModeReportsSkippedVerification

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag {
  flag := true
}

invariant flag = false

#gen_spec

/--
warning: Skipping #check_invariants because `veil.__modelCheckCompileMode` is true. This option is reserved for generated model-checker sources and must not be set in user code.
-/
#guard_msgs in
#check_invariants

/--
warning: Skipping #check_action because `veil.__modelCheckCompileMode` is true. This option is reserved for generated model-checker sources and must not be set in user code.
-/
#guard_msgs in
#check_action set_flag

/--
warning: Skipping trace verification because `veil.__modelCheckCompileMode` is true. This option is reserved for generated model-checker sources and must not be set in user code.
-/
#guard_msgs in
sat trace { }

/--
warning: Skipping #gen_theorems because `veil.__modelCheckCompileMode` is true. This option is reserved for generated model-checker sources and must not be set in user code.
-/
#guard_msgs in
#gen_theorems

end CompileModeReportsSkippedVerification
