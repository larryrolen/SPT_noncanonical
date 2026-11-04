# Conditional classification of smallest-parts congruences

This package states conditional versions of Theorem 1.1 and Corollary 1.2 of
Larry Rolen's [paper](https://arxiv.org/abs/2611.04178v1). Under the displayed
inputs, a prime-modulus spt congruence with prime at least five must have the
canonical residue. With the additional canonical inputs, the only pairs for
any prime are (5,4), (7,5), and (13,6).

The original manuscript-facing declarations are not complete unconditional Lean
proofs. The main library contains 62 admitted literature statements, with one
additional duplicate admission in the contained `SPT_noncanonical` directory.
The original conditional exports also depend on two admitted facts:
`normalizedEisenstein_minus_reduces` and `normalizedEisenstein_plus_reduces`.
These express E_(p-1) congruent to 1 and E_(p+1) congruent to E_2 coefficientwise
modulo p, in the paper's discussion around equation (2.2).

`Solution.lean` adds `SptClassification.Palomar.EisensteinCongruenceInputs` and
two endpoints in that namespace. Their other premises are unchanged:
`CharacterIntervalInput`, `ConstantTermInputs`, `ProgressionInputs`,
`CharacterObstructionInputFamily`, and (for the full classification)
`CanonicalInputs`. All project-specific definitions and premises are stated in
`Challenge.lean`, which imports only Mathlib.

The Solution's proof-producing tactic expands precisely the original proof
fragments depending on those two admissions and substitutes the corresponding
explicit hypotheses. It leaves checked fragments intact, rejects an additional
unhandled axiom, and submits the resulting term to Lean's ordinary kernel.
It does not disable kernel checks or permit `sorryAx`. The local axiom audit
of both new endpoints and every supporting target contains only `propext`,
`Classical.choice`, and `Quot.sound` (or a subset).

The package upgrades Lean and Mathlib to 4.35.0-rc2 and exposes definition bodies
needed by the standalone statement. Two elementary lower bounds on the
Eisenstein weights are named lemmas to avoid unstable generated proof names.
The original mathematical premises and conclusions are retained. The interval certificate modules have two chains of ordinary build-order
imports, so at most two of these large modules compile at once. No certificate
statement or proof is changed. This bounds memory use after the first full
preflight exceeded the 16 GB worker capacity during the Solution build.

Challenge proof holes are deliberate and all are selected in `comparator.json`;
the Solution provides their checked proofs. Its cache-reset commands preserve
original auxiliary-lemma names when definitions from different source modules
are collected in one file; they affect elaboration only.

The upgraded Solution and Challenge build, and the local statement and
reachable-definition comparison passes against the actual Solution.

The full Palomar workflow for the exact submitted commit must pass, including
independent NanoDa proof checking. Local builds and audits do not replace it.
No human alignment review or unconditional classification is claimed.
