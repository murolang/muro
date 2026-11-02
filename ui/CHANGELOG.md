# Changelog

## 0.1.0

`mix muro.ui path.muro` opens one checked book. The page draws one node for each spec, evidence, and run, one edge for each use, and a session as a compound node. Each meeting on that session is drawn with the configurations and transitions the checker recorded. A backend switch redraws the OTP, FSM, C, Rust, or Zig outline — its names, signatures, layouts, and clauses — without checking the book again. A click shows the source file, line, and column. An edge also shows the out-of-order refusal, and a use that is not a step says there is no refusal. A meeting that fails to check is that error, with no configurations.

The package depends on `muro ~> 0.20.5`. It does not emit code and it does not change the wall.
