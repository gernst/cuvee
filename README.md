# Cuvée

Cuvée is a tool for specification and proof engineering.
It works on an intermediate language that is very close to [SMT-LIB](smtlib.cs.uiowa.edu/),
but accepts a subset of the [Boogie language](https://github.com/boogie-org), too.

Setup:

    git submodule init

Running:

    ./Cuvee.sh -help
    ./Cuvee.sh examples/boogie/list.bpl

Please see examples in

    `examples/boogie`

*Disclaimer*: The tool is currently in active development and therefore some functionality might be broken
and some inference could be unsound or return unexpected results.

Please do not hesitate to open an issue for bugs and feature requests.

Current use cases are elaborated below. Note that not all are fully implemented yet, it is more of a wishlist of features.

## Human-readable SMT-LIB engineering via Boogie Syntax

A major obstacle to working with SMT-LIB files is that the S-expression based syntax
is not so much readable for everybody. Therefore Cuvée offers two 
a seamless translation between SMT-LIB and Boogie for the intersection between the two languages.
There are parsers for both languages and pretty printers (the Boogie one is prototypical),
such that SMT-LIB scripts can be debugged in a more conventional syntax
The SMT-LIB pretty printer formats the S-expressions in such a way that they become easy to read,
exposing their respective structure.

Proof goals (i.e. negated `assert`ions in SMT-LIB) can be presented in a normalized way
such that all unnecessary nesting in the formula is flattened and trivial parts are simplified (see also below).
This helps to untangle the assumptions from the conclusions resp. different proof goals of a large formula.

## SMT-LIB script debugging and simplification

During the development of verification tools,
a problem that one may run into is the need to understand why a particular script is not
producing the results that are expected.
There are many sources for this, including bad encoding of background theories,
bad translation of verification conditions, missing side-conditions and invariants,
or simply a misunderstanding of the correctness of a particular verification task.

It is then helpful to take apart proof obligations with respect to provable parts
and redundant assumptions. While SMT solvers offer tactics (such as boolean simplification)
to support this kind of debugging, these may not be integrated into the workflow of a verification pipeline
(i.e. they have to be added manually to scripts) and they are not necessarily as powerful as desired.

For example, SMT solvers typically instantiate axioms which define recursive functions
by triggering and then merging the respective equations into their congruence data structure.
Interactive theorem provers like Isabelle, however, instead rewrite goals
with those equations that make good simplification rules.
For some cases such rewrites are *always* desirable (cf. recursive list functions),
and Cuvée can detect and apply definitions automaticaly.

A similar situation occurs with the question of unfolding non-recursive definitions,
such as containment of an element in an array range:

    contains(x, a, l, r) <==> exists k. l <= k < r && a[k] == x

Consider for example the folllwing two lemmas

    contains(x, a, l1, r1) ==> contains(x, a, l2, r2)
    contains(x, a1, l, r)  ==> contains(x, a2, l, r)

which schematically reflect typical conditions from the correctnes of array algorithms
(e.g. index computations resp. array modifications).
If such a proof fails to verify one is interested in automatically pinpointing why.
Here, the first condition fails for those k from the definition of `contains`
which are not in the overlap of the two ranges.
The second condition fails if `a1` and `a2` differ in an index that is in the range `l..r`.
Note that the concrete models produced by the SMT solver reflect this high-level
intuition only to a very limited degree. Cuvée will be able to automatically produce these
via an abductive inverence, backed by SMT reasoning and heuristics
while at the same time keeping the general structure of the proof goal intact.

Note, this is work in progress.

## Program Verification

Cuvée implements a simple imperative language with procedures very similar to that of Boogie,
but it supports no `goto`, only structured control flow.
The translations to verificaion conditions is done by weakest-precondition like operators,
which are reflected in the logic. There are three modalities, weakest precondition,
weakest liberal precondition, and weakest possible precondition (i.e. existence of a run),
where the latter two coincide with box and diamond from Dynamic Logic (on branch `wp`).

For `while` loops, Cuvée offers not just invariants but also summaries
(cf. Ernst, VMCAI 2022), which allow one to sometimes express certain correctness conditions more naturally,
and which may lead to novel approaches to automatically prove the correctness of loopy programs.

To that end, there are two flags, `-infer:summary` and `-infer:frame`, implemented on branch `infer`,
which represent first steps in this direction.


## Further Research Directions

The tool is intended as an experimental platform to quickly prototype ideas.
Some ongoing efforts for example focus on the following topics.
Note, not all of these are developed in this public repository.

- abstract interpretation for Boogie programs
- proof scripts that interleave with a high-degree of automation
- experiments Horn-clause encodings
- inference of loop specifications (contracts with invariants and summaries)
- automatic induction wiht generalization and lemma inference