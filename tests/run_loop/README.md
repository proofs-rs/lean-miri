# Scheduler callback integration evidence

After building `Miri.Interpreter.RunLoop`, run:

```
python3 tests/run_loop/test_source_run_loop.py
```

The test checks the pinned scheduler.rs SHA256 against upstream/source-lock.json before
extracting its actual `run_on_stack_empty` and `step_current_thread` bodies.
It also extracts `run_threads`, changes its infinite loop to one block, changes
the result type to unit, and adds a successful unit result after the block.
All other method bodies retain source ordering. Interpreter, machine, callback,
clock, and host polling dependencies are explicit fixtures. No actual host
sleep occurs. The machine-stop macro returns a fixture error.

Eight compiled Rust traces check Pending versus Ready, nonempty core execution,
core failure preventing callback execution, callback failure preventing
restoration, interrupt handling before scheduling, host polling when
communication is enabled, and isolated sleeping. Callback execution asserts
that its callback slot was taken, and the output observes callback restoration
and diagnostic origin reset. Counterpart Lean examples use kernel-checked
`decide`; they additionally test take failure, restoration before termination,
the isolated infinite-sleep error, and termination UB classification.

A false core step with Pending leaves the thread running. An empty MIR stack
therefore does not imply program exit. The Lean tests distinguish successful
scheduler continuation from an exit produced by the termination hook.

These tests validate orchestration with supplied operations. They do not
validate TLS destruction, full thread termination, host I/O, scheduling policy,
or the complete official Miri semantics, and do not establish Rust safety.
