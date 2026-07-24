import Veil

/-!
# Regression: procedure parameters cannot shadow state or theory components

Veil inserts local binders for all components inside every action body. A
parameter with the same name would therefore be dead, and references in the
written body would resolve to the component instead.
-/

veil module ProcedureParameterComponentCollision

individual flag : Bool
immutable individual enabled : Bool

#gen_state

/--
error: Parameter 'flag' of 'badMutable' conflicts with a Veil state or theory component of the same name. Component binders are introduced inside procedure bodies and would shadow this parameter.
-/
#guard_msgs in
action badMutable (flag : Bool) {
  require flag
}

/--
error: Parameter 'enabled' of 'badImmutable' conflicts with a Veil state or theory component of the same name. Component binders are introduced inside procedure bodies and would shadow this parameter.
-/
#guard_msgs in
procedure badImmutable (enabled : Bool) {
  require enabled
}

/--
error: Parameter 'flag' of 'badTransition' conflicts with a Veil state or theory component of the same name. Component binders are introduced inside procedure bodies and would shadow this parameter.
-/
#guard_msgs in
transition badTransition (flag : Bool) {
  flag' = flag
}

-- A distinct parameter remains available normally.
action good (value : Bool) {
  require value = enabled
  flag := value
}

end ProcedureParameterComponentCollision
