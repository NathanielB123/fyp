# Various Bits and Pieces Relating to my Final Year (Masters) Project at Imperial: Local Rewriting in Dependent Type Theory

## Guide:

- [Report](./Report): LaTeX/literate Agda source for the interim and final report documents.
- [Check](./check): A bidirectional NbE typechecker for "SCBool", a minimal dependently typed language featuring Boolean "smart case".
- [Untyped](./Untyped/BoolRw.agda): A proof that for untyped lambda calculus with Booleans, well-foundedness of "non-deterministic reduction" (as defined in the report) implies well-foundedness of `β`-reduction + arbitrary rewrites to closed Booleans.
- [STLC](./STLC): A proof that STLC is strongly normalising w.r.t. "spontaneous reduction", based on András Kovács' [StrongNorm.agda](https://github.com/AndrasKovacs/misc-stuff/blob/master/agda/STLCStrongNorm/StrongNorm.agda) (which itself is based on Girard's SN proof for STLC in "Proofs and Types"). In the report, instead of proving SN of spontaneous reduction directly (which gets a bit convoluted), we prove SN w.r.t. "non-deterministic" reduction, which comes out more cleanly.
- [Dependent](./Dependent): Agda mechanisations of a minimal dependent type theory with Booleans, and the extended languages "SCBool" and "SCDef", as defined in the report.
- [Completion.hs](./Completion.hs): Implementations of ground completion and E-Graphs for first order terms, just to learn the concepts.

## Note:

Some of the Agda mechanisations (specifically the "strictified" syntaxes in the [Dependent](./Dependent/) folder, and any files that depend on them) require my fork of Agda to typecheck ([specifically, the `mutual-rewrite` branch pushed here](https://github.com/NathanielB123/agda/tree/mutual-rewrite)).
