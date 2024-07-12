# Grove Formalism

This repository contains the full Agda mechanization of the core Grove data structures and theorems stated in the paper along with the mechanization of the marking framework for total error localization and recovery.

---

## Mechanization

All semantics and metatheorems are mechanizaed in the Agda proof assistant. To check the proofs, an installation of [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download) is required. The proofs are known to load cleanly under Agda `2.6.4`.

Once Agda is installed, running `agda Grove.agda` in the top-level directory will cause Agda to check all the proofs.

---

## File Organization

Here is where to find each definition:

- [prelude.agda](./Grove/Prelude.agda) contains definitions and utilities not specific to the marked
    lambda calculus.

- [grove/core/](./Grove/core) contains definitions related to the core Grove mechanization:
  - [typ.agda](./core/typ.agda) contains the syntax definition for types, the base, consistency,
        matched arrow and product types, and meet judgments, alongside useful lemmas about types.
  - [uexp.agda](./core/uexp.agda) contains the syntax definition and bidirectional typing
        judgments for unmarked expressions.
  - [mexp.agda](./core/mexp.agda) contains the syntax definition and bidirectional typing
        judgments for marked expressions.
  - [erasure.agda](./core/erasure.agda) contains the definition of mark erasure.
  - [lemmas.agda](./core/lemmas.agda) contains some lemmas about unmarked and marked
        expressions.

- [marking/](./Grove/Marking) contains definitions and [theorems](#where-to-find-each-theorem) related
    to marking:
  - [marking.agda](./Grove/Marking/Marking.agda) contains the bidirectional marking judgment.
  - [totality.agda](./Grove/Marking/Properties/Totality.agda), [unicity.agda](./Grove/Marking/Properties/Unicity.agda), and
        [wellformed.agda](./Grove/Marking/Properties/WellFormed.agda) contain theorems about marking (see the [next
    section](#where-to-find-each-theorem)).

### Where to Find Each Theorem

Every theorem is proven in the mechanization. Here is where to find each theorem:

- Theorem B.1, *Marking Totality*, is in [properties/totality.agda](./Grove/Marking/Properties/Totality.agda), given
    by `↬⇒-totality` and `↬⇐-totality`.

- Theorem B.2, *Marking Well-Formedness*, is in
    [properties/wellformed.agda](./Grove/Marking/Properties/WellFormed.agda), given by `↬⇒□` and `↬⇐□`.

- Theorem B.3, *Marking of Well-Typed/Ill-Typed Expressions*, is in
    [properties/wellformed.agda](./Grove/Marking/Properties/WellFormed.agda), whose first part is given by `⇒τ→markless`
    and `⇐τ→markless`, and second part is given by `¬⇒τ→¬markless` and `¬⇐τ→¬markless`.

- Theorem B.4, *Marking Unicity*, is in [properties/unicity.agda](./Grove/Marking/Properties/Unicity.agda), given by
    `↬⇒-unicity` and `↬⇐-unicity`.

### Assumptions and Representation Decisions


- The consistency rules are slightly different from those in the formalism and paper to facilitate
    a simpler unicity proof for marking. Type inconsistency is defined as the negation of
    consistency, that is, `τ₁ ~̸ τ₂ = ¬ (τ₁ ~ τ₂) = (τ₁ ~ τ₂) → ⊥`. This formulation is equivalent to
    a judgmental definition.

- Since we are only concerned with well-typed marked expressions, they are encoded as
    intrinsically typed terms. Variables, while otherwise extraneous, are preserved in the syntax
    for the sake of mark erasure. As a result, judgments on marked expressions, such as `subsumable`
    and `markless`, are formulated bidirectionally.

- Conjunctions in the antecedents of theorems have been converted into sequences of implications,
    which has no effect other than to simplify the proof text.

- The formalism and paper do not state exactly what the `num` type is; for simplicity, we use
    unary natural numbers, as defined in [prelude.agda](./Grove/Prelude.agda).