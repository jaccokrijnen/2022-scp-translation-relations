Run `make` to build.
Tested with Coq 8.13.2.

Properties mentioned in the paper
===

* BoundIn: [BoundVars.v](src/Language/PlutusIR/Analysis/BoundVars.v)
* Globally Unique Variables: [UniqueBinders.v](src/Language/PlutusIR/Analysis/UniqueBinders.v)
* Well-scoped Expressions: [WellScoped.v](src/Language/PlutusIR/Analysis/WellScoped.v)
* Pure Bindings: [Purity.v](src/Language/PlutusIR/Analysis/Purity.v)


Translation relations mentioned in the paper
===

* Variable Renaming: [Rename.v](src/Language/PlutusIR/Transform/Rename.v)
* Inlining: [Inline.v](src/Language/PlutusIR/Transform/Inline.v)
* Beta redexes: [Beta.v](src/Language/PlutusIR/Transform/Beta.v)
* Splitting recursive let groups: [SplitRec.v](src/Language/PlutusIR/Transform/SplitRec.v)
* Unwrap-wrap elimination: [Unwrap.v](src/Language/PlutusIR/Transform/Unwrap.v)
* Dead-code elimination: [DeadCode.v](src/Language/PlutusIR/Transform/DeadCode.v)
* Let-floating: [FloatLet.v](src/Language/PlutusIR/Transform/FloatLet.v)
* Encoding of non-strict bindings: [LetNonStrict.v](src/Language/PlutusIR/Transform/LetNonStrict.v)
* Thunking of recursive bindings: [ThunkRecursions.v](src/Language/PlutusIR/Transform/ThunkRecursions.v)
* Encoding of non-recursive bindings: [LetNonRec.v](src/Language/PlutusIR/Transform/LetNonRec.v)
* Compatibility: [Compat.v](src/Language/PlutusIR/Transform/Compat.v)
