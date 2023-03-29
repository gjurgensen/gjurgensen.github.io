---
title: "Coq Equality I"
date: 2021-08-03 00:00:01
math: true
draft: false
---

When one first begins to learn Coq, it is easy to glide right over the topic of equality. The property is so primitive in ordinary mathematics, you'd be forgiven for assuming its presence in Coq to be trivial. In fact, it is anything but. Equality plays a very prominent role in Coq, and in dependent type theory in general. This post constitutes the first in a mini-series dedicated to understanding the fundamentals and intricacies of equality in Coq.

## Introduction

Many introductions to Coq will point users to the appropriate tactics without necessarily imparting the underlying mechanics, or at least not initially. When one is first learning, this is likely the most efficient path forward. However, it does not provide the deepest of foundations from which to build one's understanding.

When I first encountered equality in Coq, I only learned that "simple" equalities could be resolved with the `reflexivity` tactic. It was not, at the time, clear to me what qualified as "simple" and what didn't.

For instance, we can easily prove that `0` is the left identity of addition on naturals:

```Coq
Theorem plus_0_l : forall n: nat,
  0 + n = n.
Proof.
  intros *.
  reflexivity.
Qed.
```

However, we cannot use the same approach to prove `0` to be the right identity:

```Coq
Theorem plus_0_r : forall n: nat,
  n + 0 = n.
Proof.
  intros *.
  Fail reflexivity.
(* The command has indeed failed with message:
   In environment
   n : nat
   Unable to unify "n" with "n + 0".
 *)
Abort.
```

In order to explain why these cases are different, we are going to have to back up a few steps, all the way to the fundamentals.

## A Tale of Two Equalities

Before we proceed, we must distinguish between two separate notions of equality. The first notion is called *definitional* equality (or sometimes *convertibility*), and the second is called *propositional* equality. These equalities differ in the level at which they are stated. Propositional equality is the equality we have dealt with so far, represented using the `=` symbol. Notably, it is a proposition *within* Coq. That is, assertions of propositional equality are regular types, and proofs of propositional equality are regular proof terms. In contrast, definitional equality refers to a judgement within the meta-theory of Coq. We use the symbol $≡$ to denote definitional equality. Note that we will often simply refer to "equality" when the context makes its clear which equality we refer to.

It is necessary to understand definitional equality before we can truly understand propositional equality. Thankfully, definitional equality is not especially complicated. Two terms in Coq are definitionally equal if and only if they reduce to the same value under the usual reduction/conversion. For instance, we have the definitional equality `1 + 1` $\equiv$ `2`, which follows from reducing the left-hand side.

For a more rigorous definition of definitional equality in Coq, see [here](https://coq.inria.fr/refman/language/core/conversion.html#term-convertible).

How is definitional equality, a meta-theoretic judgment, relevant to us end-users of Coq? It is relevant insofar as it affects Coq's typing rules.

$$
\cfrac{\Gamma \vdash t : A \qquad \Gamma \vdash A \equiv B}{\Gamma \vdash t : B}\ [\text{Convertibility}]
$$

This rule may be read "within context $\Gamma$, if $t$ has type $A$, and $A$ is definitionally equal to $B$, then $t$ also has type $B$". In other words, definitionally equal terms are interchangeable in types.

For instance, let's say we have a vector of two elements on type `A`. We might represent that with the type `vec A 2`, but it could just as easily take the type `vec A (1 + 1)`, since the two types are definitionally equal.

In a sense, we exploit this interchangeability of definitionally equal terms in our definition of propositional equality, reproduced here:

```coq
Inductive eq (A: Type) (x: A) : A -> Prop :=
  eq_refl : eq A x x.

(* Make arguments implicit *)
Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Notation "x = y" := (eq x y) : type_scope.
```

As we can see, the equality type family, named `eq`, is simply an inductively-defined proposition. It's singular constructor produces a proof of reflexive equalities. E.g., `eq_refl 2 : 2 = 2`. At first glance, it may appear that this constructor can *only* represent such syntactically reflexive equalities. However, if we apply our understanding of definitional equality, we see this is not so. For instance, the same proof term may take on a definitionally equal proposition: `eq_refl 2: 1 + 1 = 2`. Of course, it doesn't stop there. We could concoct any number of suitable types: `2 * 1 = 1 * 2`, `784 / 392 = 2 + (0 * 42)`, etc.

Hopefully it is evident that definitional equality implies propositional equality. If $\Gamma \vdash$ `x` $\equiv$ `y`, then $\Gamma \vdash$ `eq_refl x` : `x = y`. What about the converse? Does propositional equality imply definitional equality? In Coq, the answer is a resounding "no!", but that is not so in all type theories.

Some type theories force definitional equality to follow propositional equality by adding the following rule:

$$
\cfrac{\Gamma \vdash h : x = y}{\Gamma \vdash x \equiv y}[\text{Extensionality}]
$$

Type theories with an equality reflection rule such as the one above are referred to as *extensional* type theories. Those which do not are called *intentional*. Coq lacks such a rule, and is therefore *intentional*.

Extensional type theories are appealing in that we may take advantage of the type convertibility rule even with propositional equalities. However, it comes at a major cost. Up to now, definitional equality has been decidable. With the introduction of the extensionality rule, definitional equality is no longer decidable, since propositional equality is not decidable. By extension, our entire typing procedure becomes undecidable.

## The Reflexivity Tactic

With this background, the `reflexivity` tactic is quite easy to explain. To a first approximation, the tactic does little more than applying the `eq_refl` constructor. Let's repeat our previous proof:

```Coq
Theorem plus_0_l : forall n: nat,
  0 + n = n.
Proof.
  intros *.
  (* reflexivity. *)
  exact eq_refl.
Qed.
```

This will also shed light on the earlier failed proof.

```Coq
Theorem plus_0_r : forall n: nat,
  n + 0 = n.
Proof.
  intros *.
  Fail exact eq_refl.
(* The command has indeed failed with message:
   In environment
   n : nat
   The term "eq_refl" has type "n + 0 = n + 0" while it is expected to have type
   "n + 0 = n" (cannot unify "n + 0" and "n").
 *)
Abort.
```

Why is `eq_refl` a sufficient proof in the first theorem, but not the second? Given our new insight, we should expect it has something to do with definitional equality, and indeed that hunch is correct. Recall the definition of addition:

```Coq
Fixpoint add (n m: nat) : nat :=
  match n with
  | 0    => m
  | S n' => S (add n' m)
  end.

Notation "n + m" := (add n m) : nat_scope.
```

As we see, the definition is recursive on the left argument. Therefore, the expression `0 + n` is definitionally equal to `n`, even in the context where `n` is unknown. In contrast, the expression `n + 0` cannot be meaningfully reduced. We may apply β-reduction, but then we are left with a match construct we cannot simplify.

The solution, as you probably know, is to continue the proof by induction on `n`. It is clear that we must consider the concrete values of `n`, and simple case analysis is insufficient.

```Coq
Theorem plus_0_r : forall n: nat,
  n + 0 = n.
Proof.
  intro n.
  induction n as [|n IH].
  - exact eq_refl.
  - cbn.
    rewrite IH.
    exact eq_refl.
Qed.
```

This proof demonstrates how propositional equality is stronger than definitional equality. The induction principle allows us to take a step of reasoning which is unavailable to definitional equality judgments.

Note that the proof uses the `rewrite` tactic. We will eventually demystify this tactic, just as we did `reflexivity`. However, that would be skipping ahead a bit too far.

First, we should probably talk about [*in*equality](/posts/coq-inequality).
