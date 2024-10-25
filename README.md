# Grove Formalism

This repository contains the full Agda mechanization of the core Grove data structures and theorems stated in the paper along with the mechanization of the marking framework for total error localization and recovery, with the exception that for some functions and proofs we provide written justification of termination at the end of this file, and allow the mechanization to retain some termination-related holes. 

---

## Marking Mechanization

All semantics and metatheorems are mechanizaed in the Agda proof assistant. To check the proofs, an installation of [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download) is required. The proofs are known to load cleanly under Agda `2.6.4` and stdlib `2.1.1`.

Once, installed `grove.agda` in the top-level directory will cause Agda to check all the proofs.

---

## File Organization

Here is where to find each definition:

- [Grove/Prelude.agda](./Grove/Prelude.agda) contains general definitions and utilities, mainly definitions related to the list representation of finite sets. 

- [Grove/Core](./Grove/Core) contains the definitions of graphs and groves, and the proofs of patch commutativity, correct classification of vertices, and recomposability.

<!-- - [Grove/Core](./Grove/Core) contains definitions related to the core Grove mechanization:
  - [typ.agda](./core/typ.agda) contains the syntax definition for types, the base, consistency,
        matched arrow and product types, and meet judgments, alongside useful lemmas about types.
  - [uexp.agda](./core/uexp.agda) contains the syntax definition and bidirectional typing
        judgments for unmarked expressions.
  - [mexp.agda](./core/mexp.agda) contains the syntax definition and bidirectional typing
        judgments for marked expressions.
  - [erasure.agda](./core/erasure.agda) contains the definition of mark erasure.
  - [lemmas.agda](./core/lemmas.agda) contains some lemmas about unmarked and marked
        expressions. -->

- [Grove/Marking](./Grove/Marking) contains definitions and theorems related
    to marking:
  - [Grove/Marking/Marking.agda](./Grove/Marking/Marking.agda) contains the bidirectional marking judgment.
  - [Grove/Marking/Properties/Totality.agda](./Grove/Marking/Properties/Totality.agda), [Grove/Marking/Properties/Unicity.agda](./Grove/Marking/Properties/Unicity.agda), and [Grove/Marking/Properties/WellFormed.agda](./Grove/Marking/Properties/WellFormed.agda) contain theorems about marking (see the [next section](#where-to-find-each-theorem)).

### Where to Find Each Theorem

Every theorem is proven in the mechanization. Here is where to find each theorem:

- Theorem 3.2, *Action Commutativity*, is in [Grove/Core/Properties/ActionCommutative.agda](./Grove/Core/Properties/ActionCommutative.agda), given by `ActionRel-comm`.

- Theorem 3.18, *Recomposability*, is in [Grove/Core/Properties/Recomposability.agda](./Grove/Core/Properties/Recomposability.agda), given by `recomposability`.

- Theorem B.1, *Marking Totality*, is in [Grove/Marking/Properties/Totality.agda](./Grove/Marking/Properties/Totality.agda), given by `↬⇒-totality` and `↬⇐-totality`.

- Theorem B.2, *Marking Well-Formedness*, is in [Grove/Marking/Properties/WellFormed.agda](./Grove/Marking/Properties/WellFormed.agda), given by `↬⇒□` and `↬⇐□`.

- Theorem B.3, *Marking of Well-Typed/Ill-Typed Expressions*, is in [Grove/Marking/Properties/WellFormed.agda](./Grove/Marking/Properties/WellFormed.agda), whose first part is given by `⇒τ→markless` and `⇐τ→markless`, and second part is given by `¬⇒τ→¬markless` and `¬⇐τ→¬markless`.

- Theorem B.4, *Marking Unicity*, is in [Grove/Marking/Properties/Unicity.agda](./Grove/Marking/Properties/Unicity.agda), given by `↬⇒-unicity` and `↬⇐-unicity`.

### Assumptions and Representation Decisions

- Termination is not proven for some functions and proofs related to vertex classification and live subgraph decomposition. See the [section on termination](#termination-and-fuel).

- Finite sets are represented using lists, with an inductive membership predicate and equivalence defined as a biimplication of membership. This definition of equivalence is given by `elem-equiv` in [Grove/Prelude.agda](./Grove/Prelude.agda).

- In the marking formalism, we are only concerned with well-typed marked expressions, so they are encoded as intrinsically typed terms. Variables, while otherwise extraneous, are preserved in the syntax for the sake of mark erasure. As a result, judgments on marked expressions, such as `subsumable` and `markless`, are formulated bidirectionally.

<!-- - The consistency rules are slightly different from those in the formalism and paper to facilitate
    a simpler unicity proof for marking. Type inconsistency is defined as the negation of
    consistency, that is, `τ₁ ~̸ τ₂ = ¬ (τ₁ ~ τ₂) = (τ₁ ~ τ₂) → ⊥`. This formulation is equivalent to
    a judgmental definition. -->

<!-- - Conjunctions in the antecedents of theorems have been converted into sequences of implications,
    which has no effect other than to simplify the proof text.

- The formalism and paper do not state exactly what the `num` type is; for simplicity, we use
    unary natural numbers, as defined in [prelude.agda](./Grove/Prelude.agda). -->

### Termination and Fuel

In the definition of `recomp`, the termination checker is disabled. In `Classify.agda`, `ClassifyCorrect.agda`, `Decomp.agda`, and `Recomposability.agda`, a natural number fuel is used to bypass the termination checker. We were unable to simply use the `TERMINATING` pragma in these latter cases, because doing so led to odd issues with Agda's coverage checking. The use of this fuel means there are several holes in these files, and the `allow-unsolved-metas` option is enabled. Most of these holes correspond to a function or proof case in which `fuel = zero`, which cannot be sensibly completed. The remaining three holes are where we "convert" a hypothesis of the form `P fuel` into the hypothesis `P (suc fuel)`. This is valid since the fuel is an arbitrary argument that does not change the value of a function or the meaning of a proposition.

In the case of `recomp`, the Agda was unable to infer termination because we used a `map` over a vector of subterms. Termination is clear, and we decided not to rewrite the definition of `recomp` in a way that Agda recognizes as terminating because it would cost us in clarity of definition and directness of proof. 

In the case of the other four files, termination was infeasible to prove mechanically due to the traversal of a possibly cyclic graph by the relevant functions and proofs. We opted to use fuel in the mechanization and prove termination manually. Termination is justified here. 

#### Classify 

The function `classify` traverses the input graph, tracking a list `ws` of vertices `w` paired with the minimal ID encountered between `w` and the current vertex. When the current vertex appears in `ws` paired with its own ID, `classify` terminates. Since the input graph is finite, then if `classify` has recursed enough times, `ws` must contain a duplicate vertex. Since `classify` proceeds deterministically from vertex to vertex, it will continue to recurse along the cycle from this repeated vertex back to itself. Since the IDs are unique among the vertices of the graph, and totally ordered, some vertex along this cycle must have a minimal ID. When `classify` reaches this vertex the second time, the termination condition will be met.  

This argument extends to both functions in the ClassifyCorrect module, `classify-correct` and `classify-complete`, because these proofs have the same recurrence and termination structure as `classify`.

#### Decomp

Decomp traverses the graph by recursing on all children of each vertex it encounters, terminating on vertices that are classified as `Top MP` or `Top U`. A vertex is classified as `Top MP` if it has multiple parents, and `Top U` if it is the vertex with minimal ID on a cycle in which each vertex in the cycle has only one parent. `classify-correct` and `classify-complete` guarantee the correctness and completeness of this classification. 

`decomp` will never recurse onto a vertex it has already seen. Assume for contradiction that this were to happen, with one call to `decomp` resulting in two recursive calls `decomp(v)`. Then two paths lead from the initial vertex `v`.  Either these two paths branch and reconverge, in which case the vertex at which they reconverge would have multiple parents and therefore would not be recursed on, or the one of the paths is included in the other, in which case the entirety of a finite cycle from `v` to `v` will have been traversed. If any vertex in this cycle has multiple parents, then recursion would stop there. Each vertex must have a parent, in order for the cycle to form. Therefore, each vertex has a unique parent. One vertex in this cycle has a minimal ID, and therefore is classified as `Top U`, so `decomp` would not have recursed on it. This is a contradiction. Therefore the recursion of `decomp` is bounded by the finite size of the graph, and it terminates in all cases.

#### Recomposability

Finally, each hole in `Recomposability.agda` is simply the result of referring to applications of `classify`, `classify-correct`, `classify-complete`, or `decomp` that require (nonzero) fuel in order to reduce. With termination of these functions and proof assured, fuel can be ignored, and these holes can be removed from consideration.  

