# Control-flow integration evidence

Run after building `Miri.Interpreter.ControlFlow`:

```
python3 tests/control_flow/test_source_transitions.py
```

The test verifies source-lock SHA256 values, extracts the actual pinned Rust
bodies of `go_to_block`, `return_to_block`, `unwind_to_block`, and
`return_from_current_stack_frame`, and compiles them with fixture dependencies.
Only the Rust visibility and result type signatures are adapted. Logging macros
are inert; UB macros return a fixture error; return-place reading, copying,
cleanup, and machine termination are explicit fixture implementations.

Ten expected traces cover normal read→pop→copy→cleanup→goto ordering,
NoJump, root NoCleanup, root-unwind UB, unwind skipping copy, mutation retained
after a copy error, Continue, Unreachable, termination callbacks changing the
location, and impossible normal return. `Transitions.lean` checks counterpart
outcomes using kernel-checked `rfl`/`decide`; it also checks first-match switch
comparison order, failure while reading an ignored Assert condition, and the
optional-overflow operator distinction. A concrete Step/ControlFlow binding
runs Goto→Nop→Return and checks that the next driver iteration returns false.

These are component integration tests with supplied interpreter callbacks.
They do not execute full official Miri or establish Rust program safety, the
callback implementations' correctness, or semantic equivalence for all states.
