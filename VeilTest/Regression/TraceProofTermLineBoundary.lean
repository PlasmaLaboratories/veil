import Veil

veil module TraceProofTermLineBoundary

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action stay {
  flag := flag
}

invariant flag = false

#gen_spec

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    flag = false
-/
#guard_msgs in
sat trace { }

set_option maxRecDepth 1000 in
#check Nat

end TraceProofTermLineBoundary
