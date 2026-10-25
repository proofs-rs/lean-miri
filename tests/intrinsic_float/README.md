# Portable float intrinsic comparison

`python3 tests/intrinsic_float/source_compare.py` checks 29,240 outputs of the
actual IntrinsicFloat helpers against the pinned rustc_apfloat dependency.
It verifies locked APFloat and rustc intrinsics source hashes before execution.
The corpus covers four IEEE widths, signed zeros, subnormals, normal boundaries,
infinities, signaling/quiet NaNs, exact product cancellation, five integral
rounding modes, four min/max operations and both equal-number choices.

NaNs use preferred-NaN adjustment. This is finite helper comparison, not all
NaN policies, the full typed Intrinsics dispatcher, architecture intrinsics,
or a Rust safety proof. The oracle executes APFloat rather than host floats.
