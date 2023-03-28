---
title: "A Fistful of Axioms"
date: 2021-11-18 00:00:01
draft: false
tag: Coq
---

![A Fistful of Dollars](/images/a_fistful_of_dollars.png)

As we all know, one should only introduce axioms into a proof environment with the utmost care. Introducing a contradictable axiom would be disastrous. Our logic would lose all meaning once all objects are provable.

However, I think some Coq users are *too* fearful of axioms, and end up avoiding them entirely. In doing so, they make their lives much more difficult than they need to be.

I'd argue that there are several axioms which are perfectly reasonable, and even prudent to accept. In this post, I'll discuss some of the most common axioms, roughly ordered in what I consider most to least easily accepted.

For readability, I take a number of notational liberties, including using `∀`, `∃`, `≠`, and `λ` for `forall`, `exists`, `<>`, and `fun` respectively.

# 1. UIP

UIP stands for "uniqueness (unicity) of identity proofs". Recall that the "identity" type is another name for the equality type. Formally, UIP makes the following claim:

```Coq
uip : ∀ A (x y: A) (p q: x = y), p = q
```

This might be hard to digest at first due to the sort of self-referential nature of asserting an equality over equalities. The statement is in fact perfectly reasonable. An equality proof is a term like any other, and so naturally we can assert an equality over two such proof terms. Recall the definition of the equality type:

```Coq
Inductive eq (A : Type) (x : A) : A -> Prop :=
  | eq_refl : eq A x x.
```

In the above definition, I have stripped away the common notation for clarity. The type `eq A x x` would typically be written `x = x`, where the type `A` is left implicit (similarly, we allow the constructor `eq_refl x` to implicitly mean `@eq_refl A x`).

So what does UIP claim in plain english, and why should we accept it? UIP claims that there is just one proof (up to propositional equality) of any particular equality. This is in fact incredibly intuitive. There is only one constructor, and no choices with respect to its arguments. Sure, we could prove `1+1 = 2` by either `eq_refl (1+1)` or `eq_refl 2`, but both of these are definitionally equal! We still only have "one" proof.

UIP is perfectly consistent at a metatheoretic level. We simply consider all possible concrete proof terms, and observe their definitional equivalence. I would argue that UIP is perfectly innocuous and that there is no reason not to accept it, since it is immensely helpful in reasoning about inversions over dependent terms.

It is perhaps surprising that this fact is unprovable. We will explain why it is unprovable shortly. First, I'd like to enumerate some equivalent statements to UIP which are often axiomatized in its place:

```Coq
uip_refl : ∀ A (x: A) (h: x = x), h = eq_refl x

axiom_K : ∀ A (x: A) (P: x = x -> Prop), P (eq_refl x) -> ∀ h, P h

eq_rect_eq : ∀ A (x: A) (P: A -> Type) (y: P x) (h: x = x),
    y = eq_rect x P y x h

JMeq_eq : ∀ A (x y: A), JMeq x y -> x = y
```

`uip_refl` is a specialization of UIP to reflexive equalities. It is perhaps a nicer property to axiomatize, because it more directly states what we are unable to prove within Coq. As we will see shortly, we specifically struggle to retain the information that the equality is reflexive while eliminating said equality.

`axiom_K` is a special eliminator, similar to `eq_ind` and `eq_rect`, which is again specialized to the reflexive case.

`eq_rect_eq` is much more difficult to immediately digest. Unfortunately, this is actually the variant of UIP you'll most likely use if you import from the standard library. Recall that `eq_rect` is the generic eliminator of equalities, generated automatically as any inductive definition will generate a `_rect` function.
It is sufficient to note that the equality declared here would hold for `h := eq_refl x`, the singular canonical proof of type `x = x`.

Lastly, we have `JMeq_eq`. This one is a bit out of place, and will take us on a small digression. You may skip this paragraph if you wish. Recall that `JMeq`, sometimes called heterogeneous equality, is a generalization of the typical equality. `JMeq`, like `eq`, only admits propositionally equal terms. It is more relaxed than `eq`, however, in that you may state questionably typed equalities. This allows one to state silly equalities like `JMeq 0 false`, but of course this is not provable. Where it is useful is in stating equalities over two terms whose types are propositionally equal, but not definitionally equal. For instance, consider a vector concatenation operator `vconcat : ∀ A m n, vector A m -> vector A n -> vector A (m + n)`. Vectors are like fixed-length lists. As we can see by the type, the length of the resulting vector will naturally be the sum of the length of the two operands. It would be quite natural for us to assert that this operation is associative. Our first attempt at a proposition might look like `∀ A m n o (v1: vector A m) (v2: vector A n) (v3: vector A o), vconcat v1 (vconcat v2 v3) = vconcat (vconcat v1 v2) v3`. This looks perfectly reasonable, but it is in fact ill-typed! The left-hand-side of the equality has type `vector A (n + (m + o))`, while the right-hand-side has type `vector A ((n + m) + o)`. Of course, we know these are propositionally equal due to the associativity of addition, but Coq expects them to be definitionally equal, which they are not. We can proceed by replacing our normal equality with the `JMeq` variant.

That `JMeq_eq` is equivalent to UIP is perhaps surprising. The key intuition is that both statements are in some sense "obvious" if we extend beyond the limitations of our `match` construct and consider at a metatheoretic level the full space of concrete instantiations of our proof terms.

I went out of my way to list all of these equivalent definitions to UIP because, unfortunately, all of these are often discussed and axiomatized independently. Unfortunately, there is no common consensus on *which* statement should be axiomatized, even though they are commonly known to be equivalent. In fact, we often see some redundant axioms: the Coq standard library currently axiomatizes `eq_rect_eq` in `Coq.Logic.Eqdep` and `JMeq_eq` in `Coq.Logic.JMeq`, even though one could derive one from the other.

I also listed these equivalent statements because I think some of the variants are more useful in demonstrating why UIP is unprovable without axioms. Take for instance `uip_refl`, which narrows the problem to reflexive equalities. This simplifies the statement, because we can directly compare the abstract proof term to the concrete `eq_refl` constructor. Consider the following term:

```Coq
λ A (x: A) (h: x = x),
  match h return (h = eq_refl x) with
  | eq_refl _ => eq_refl (eq_refl x)
  end
```

We would hope this term to be a proof of `uip_refl`. In actuality, it fails to type check. The problem is that Coq cannot satisfy the type we attempt to assert with the `return` clause of the `match`. Coq will give us the error message:

```Coq
In environment
A : Type
x : A
h : x = x
a : A
h0 : x = a
The term "eq_refl x" has type "x = x" while it is expected to have type "x = a".
```

What are these `a` and `h0` terms?! We didn't introduce them! They are in fact introduced implicitly by the `match` construct. We could introduce them explicitly if we'd like:

```Coq
λ A (x: A) (h: x = x),
  match h as h0 in (_ = a) return (h0 = eq_refl x) with
  | eq_refl _ => eq_refl (eq_refl x)
  end
```

We finally see the crux of the issue. To type the `match` term, Coq identifies `h` with a new variable `h0`, and gives it the type `x = a`. We therefore lose the vital fact that `h` is reflexive, and the return type `h0 = eq_refl x` is ill-typed! `h0` has type `x = a`, while `eq_refl x` has type `x = x`. The reflexive case `?x = ?x` may be seen as a sub-family of the larger type family `?x = ?y`, and the match construct is in fact fatally unable to narrow its consideration to a refined sub-family.

This begs the question: *why* can't the `match` construct handle precise elimination over type sub-families? This is where I have to admit that my knowledge is lacking. Perhaps this would greatly complicate our type judgments? Perhaps type-checking would become undecidable or intractable?

Whatever the reason is, I can confidently say that asserting UIP axiomatically is very safe, and the only reasons I can imagine why we wouldn't want to do so is if the statement is provable by a more powerful axiom, or if it it conflicts with another axiom (for instance, UIP is incompatible with the univalence axiom of homotopic type theory).

# 2. Functional Extensionality

It turns out, quite a few common axioms revolve around equality. Functional extensionality, as the name implies, specifically expands our notion of equality on functions.

```Coq
func_ext : ∀ A B (f g: A -> B), (∀ a, f a = g a) -> f = g
```

This statement concludes that functions `f` and `g` are equal, assuming they are *pointwise* equal. That is, the two functions must be equal on every input.

Of course, the statement above is formulated over non-dependent functions. The generalized statement that we would axiomatize would be:

```Coq
dep_func_ext : ∀ (A: Type) (B: A -> Type) (f g: ∀ a, B a),
  (∀ a, f a = b a) -> f = g
```

This notion of function equality is certainly intuitive. Basically, we are treating function as black-boxes, identifying them completely with their external behavior, and ignoring their internal structure.

How would Coq normally treat function equality? Just like with any other type of object, two functions must be *definitionally equal* to be considered equal. This might sound sufficient, but it is actually surprising limited.

Consider the functions `id_nat := λ n: nat, n` and `plus0 := λ n: nat, n + 0`. It is quite natural to consider these functions equal, since `n + 0` will reduce to `n` for any `n`. However, `n + 0` is not *definitionally* equal to `n` when `n` is abstract/opaque. Recall that definitional equality follows from reduction rules, and the addition operator is recursive on the left operand. While `0 + n` is definitionally equal to `n` for an abstract `n` value, `n + 0` is *not*.

This is why functional extensionality is so useful. Using the extensionality axiom, we can introduce `n` into our environment, and then prove `n + 0 = n` by induction on `n`, from which the equality of our functions follow.

The axiom is intuitive, but is it consistent? It is, since the only functions which we can prove to be unequal are exactly those which are extensionally unequal. You may be worried that we could leverage the differing internal structure of two functions like `id_nat` and `plus_0` to extract some difference between the two, but the only way to do that would be to use a `match` construct, which is unable to distinguish functions by syntax.

# 3. Proof Irrelevance

Now, we are slowly leaving the territory of "obvious" axioms. From here on out, the axioms we discuss will increasingly necessitate conscious dedication to a certain interpretation of objects or approach.

Proof irrelevance states that all proof terms of a particular `Prop` are equal.

```Coq
proof_irrelevance : ∀ (P: Prop) (p q: P), p = q
```

This may remind you of UIP. Indeed, some are quite happy to consider UIP a special case of proof irrelevance. However, I would stress that our motives for accepting UIP run much deeper than that of proof irrelevance. For UIP, we argued that this equality was "obvious" from a metatheoretic perspective. In contrast, one might say that general proof irrelevance seems obviously false from the same perspective!

For instance, let's consider the following silly `Prop`:

```Coq
Inductive foo : Prop :=
  | bar
  | baz.
```

`foo` has two constructors. Intuitively, wouldn't we expected `bar ≠ baz` to follow trivially from their differing structures?

In reality, we *cannot* prove `bar ≠ baz` in Coq. The details aren't important here, it suffices to know that we cannot prove *any* two terms of a share *Prop* type unequal, no matter how "obvious" it seems. Since we cannot prove them unequal, we are therefore free to assume them to be equal, as we do with the proof irrelevance axiom.

Why is this desirable? We have to remember the intended usage of the `Prop` universe, which is meant to represent logical propositions. Generally, we only care whether or not a specific `Prop` is inhabited or not. From this perspective, proof irrelevance is quite natural.
We are motivated less by the "positive" notion that proof terms over the same proposition should be equal, but rather by the "negative" notion that such proof terms aught not to be distinguished.

# 4. Propositional Extensionality

Here, we continue to extend our notion of equality, this time between propositions. Propositional extensionality states the following:

```Coq
prop_ext : ∀ (P Q: Prop), (P <-> Q) -> P = Q.
```

Again, we are softening our notion of literal equality, and replacing it with some notion of semantic (or observable) equality. What does it mean for two propositions to be equivalent? It is quite common to call two propositions connected by the biconditional "logically equivalent". Here, we admit exactly this sort of equality.

This axiom is possible due to our limited means of distinguishing between propositions. We cannot distinguish them syntactically, nor can we distinguish by specific inhabitants. We are only left with their "strength", as characterized by the ordering associated with implication. This "strength", the information carried by the proof, is how we identify propositions under propositional extensionality.

# 5. The Law of the Excluded Middle

At the core, each formal system is simply a set of unambiguous rules on uninterpreted symbols. We then choose to impose some interpretation on these symbols, with the range of valid interpretations being constrained by our rules.

We may comfortably use an existing and stable formal system without serious consideration of our interpretation, proceeding entirely on intuition. In contrast, when we extend a formal system, as we do to Coq when adding axioms, we are further constraining our possible interpretations over the system. Thus, it often requires considerable introspection to judge whether a potential axiom is consistent with our interpretation. If it is not, we have the choice of rejecting the axiom, or of adapting our interpretation.

Let `P: Prop` be a proposition within Coq. There then exists two obvious interpretations of the statement `P`. Following the spirit of classical logic, we could interpret this as the judgment that "`P` is true". The other interpretation, in the spirit of the curry-howard correspondence, or of intuitionistic logic, is "`P` is provable".

In a sense, the latter interpretation can be viewed as a strengthening of the former. If `P` is provable, then it is certainly true. In contrast, `P` may be true but not provable. Indeed, as Gödel demonstrated, every sufficiently powerful formal system will possess a proposition which is true but unprovable.

How then, do we interpret `p: P`. Of course, under the traditional curry-howard reading, we read it as "`p` is a proof of `P`". This is not satisfactory of the classical interpretation, since we may accept `p: P` for an unprovable `P`. Instead, we may read it as "`p` witnesses the truth of `P`", or "`p` is a judgment that `P` is true".

I would argue that the "provability" interpretation is more natural, due to our specific representation of propositions as families of proof objects. Furthermore, under this interpretation, Coq would be considered "complete", since by definition all provable propositions are realizable.

However, it is also perfectly natural to slide into the classical realm of interpretation when working within Coq, and to think in terms of "true" and "false" judgments, as opposed to "provable" and "provable contradiction". While the "provability" interpretation is more natural to Coq, the classical interpretation is arguably more natural to our intuitive logical reasoning.

One also can't deny that accepting a fully classical perspective is very convenient for our proofs.

I've waxed philosophical long enough, so let's consider the concrete axiom in question. Perhaps the most prominent and noteworthy axiom we consider, the so-called "law of the excluded middle" (LEM, or just EM) embodies the classical perspective:

```Coq
classic : ∀ P: Prop, P \/ ~P
```

Under the classical reading, this statement says "every proposition is either true or false", which is perfectly agreeable. Under the intuitionistic reading, it says "every proposition is either provable or provably contradictory", which as we have already mentioned, is absolutely not the case.

In the spirit of concretizing our ideas, consider the specific instantiation `P := (λ n: nat, n) = (λ n: nat, n + 0)`. From a meta-theoretic perspective, we understand `P \/ ~P` to be uninhabited (that is, unprovable) for this particular `P` (assuming we haven't added functional extensionality). Clearly our provability interpretation is inconsistent with the LEM axiom.

Given the overwhelming utility of LEM and its derivable classical relatives, I argue that it is worth adjusting our interpretation to accommodate it. This may seem to be a simple adjustment, but it isn't always so.

It is particularly challenging when we consider propositions indexed by non-propositional objects, i.e. constructive objects.
For instance, from LEM, we may prove the proposition `∀ P, inhabited ({P} + {~P})` (recall `inhabited` is essentially a degenerative case of `exists` which does not assert a predicate over the inhabitant). Since the term `{P} + {~P}` is a *`Type`*, not a `Prop`, it is extremely tempting to revert to our intuitionistic interpretation of this object as pertaining to either a proof of `P` or its negation. However, this interpretation would be problematic. The larger proposition would then be interpreted as a proof that every proposition has either a proof or a proof of its negation, which I have repeatedly reminded you is not the case.

Instead, we must interpret the above proposition as "there exists for each proposition a judgment that it is true or a judgment that it is false".

Beyond the stress this axiom places on our interpretation, there are several other reasons why one might not choose to accept LEM. Particularly, if one has chosen to embrace proof-relevance, the non-constructive, and therefore non-canonical nature of LEM is quite off-putting.

However, I would note that the `Prop` universe provides an extremely impoverished environment for proof-relevant logic. Unless one is interested in program extraction, one would be better off ignoring the `Prop` universe entirely, and conducting one's proofs entirely in the `Set`/`Type` universes, making one indifferent to the LEM axiom and the classical interpretation of the `Prop` universe. As a reminder, the `Prop` universe is quarantined from the `Set`/`Type` universes by elimination restrictions, meaning the LEM axiom does *not* lead to non-constructive objects in `Set`/`Type` in any meaningful sense.

Finally, before moving on, I should note that LEM implies some of the previously mentioned axioms: UIP and proof irrelevance. If you accept LEM, there is no reason to accept the other two axiomatically; you can derive them instead. It is always a good idea to minimize our collection of axioms when possible.

# 6. Choice

The axiom of choice has a long history in mainstream mathematics, with some philosophical objections to the concept. The choice of whether to axiomatize it in Coq is another matter entirely.

The axiom of choice can take many forms. Let's start with this formulation to establish our bearings:

```Coq
fun_choice : ∀ A B (R: A -> B -> Prop),
  (∀ a, ∃ b, R a b) ->
  ∃ f: A -> B, ∀ a, R a (f a)
```

Let's digest the statement. We have a relation `R`, which is known to be left-total. That is, each left element is associated with some right element. We then assert that we could reflect this relation into a function, where `R` relates the input of the function to the output.

It is certainly quite an interesting statement. Most interesting are the special cases where it would be derivable. For instance, if we replaces the `∃` with a `Type`-level sigma type, then the statement would be provable. This is because our proof that `R` is left-total would no longer rest on an opaque existential. Instead, it would transparently provide a witness upon which we could construct `f`. Such is the benefit of transparent constructivity. In fact, in early presentations of intuitionistic type theory before a separate `Prop` universe was considered, choice was completely derivable.

However, when we state choice in terms of the `Prop`-based `∃` quantifier, our problems re-emerge. Try to prove the above statement yourself, and you'll see where the problem occurs. We can only eliminate (i.e. pattern-match on) a proof term when we are construct a proof term. To construct `f: A -> B`, we assume `a: A`, but then we are unable to construct the non-proof term of type `B` without eliminating our existential.

The elimination restrictions on `Prop`s exist for very good reason. Are we sure it is a good idea to axiomatize choice? I'd argue that it is perfectly acceptable. The intention of `Prop` elimination restriction is to avoid leaking proof information out of the `Prop` universe. Since we break the elimination restriction only to end up eventually back in the `Prop` universe, information doesn't actually flow out of proof terms in any meaningful sense.

The formulation of choice above makes sense, but it isn't particularly attractive. Our primary intention with our axiom of choice is to relax our `Prop` elimination restriction. We don't care specifically about binary relations, so why do they play such a prominent role in our choice statement?

Indeed, the statement above is not directly axiomatized in Coq's standard library. Actually, it is derived by two other axioms, which are in fact *longer*, and generally leave a bad taste in my mouth. I much prefer an alternate statement, which is formulated in terms of the `inhabited` type family.

This type family is not very common in every day Coq, so I'll include the definition here:

```Coq
Inductive inhabited (A : Type) : Prop :=
  | inhabits : A -> inhabited A.

Notation "‖ A ‖" := (inhabited A)
  (at level 50, format "‖ A ‖").
```

This definition of `inhabited` is from the standard library, although the notation is not. The notation is borrowed from the homotopic type-theorists, who refer to `‖A‖` as a "(propositional) truncation of `A`". The `inhabited` type function simply reflect an arbitrary `Type` into a `Prop`. It is called a truncation because it "truncates" the space of `A` to a single witness of inhabitance (under the proof-irrelevance notion of singular proof terms up to propositional equality).

With these definitions, we have a much more appealing notion of choice:

```Coq
choice : ∀ (A: Type) (B: A -> Type), (∀ x, ‖B x‖) -> ‖∀ x, B x‖
```

This is the version which I prefer to axiomatize. At a glance, it immediately appear much more succinct and direct than the previous definition, even though they are logically equivalent.

To read this statement, it may be more intuitive to read `‖A‖` as "there exists some `a: A`", as opposed to the more direct reading "`A` is inhabited". Indeed, `inhabited` is very closely related to `exists`, by the theorem `∀ A, ‖A‖ <-> ∃ _: A, True`, which states that an assertion that `A` is inhabited is logically equivalent to the assertion that there exists some `a: A` such that `True` holds (as it always does).

Under this reading, the statement becomes "if from `x: A` we know there exists some element of `B x`, then there must exist a function of type `∀ x, B x`".

It may be difficult to see how this version of choice is equivalent to the previous formulation. To see how, first we note how this version can derive the previous. Given some `X`, `Y`, and `R: X -> Y -> Prop`, we simply instantiate this choice axiom with `A := X` and `B := λ x, {y | R x y}` to get a proof of `(∀ x, ‖{y | R x y}‖) -> ‖∀ x, {y | R x y}‖`. Then from `∀ U (P: U -> Prop), ‖{m | P m}‖ <-> ∃ m, P m`, it follows that `(∀ x, ∃ y, R x y) -> ∃ f: X -> Y, ∀ x, R x (f x)`.

In the opposite direction, we first note that our `fun_choice` axiom derives a parallel proposition over dependent functions/relations. The proof follows quickly after instantiating said theorem with the trivial relation `λ _ _, True`.

The various formulations of choice are generally quite safe to axiomatize. The only issue I am aware of arises when one combines choice and LEM with the `-impredicative-set` flag, which together are known to be inconsistent.

# 7. Description

All of the axioms up to this point I have chosen to accept myself in day-to-day use. That ends with *description*, which make very little sense under a traditional interpretation of the `Prop` and `Type` universes. Consider the definition of indefinite description:

```Coq
indef_descr : ∀ A (P: A -> Prop), (∃ x, P x) -> {x | P x}
```

Whereas choice represented a controlled relaxation of propositional elimination, indefinite description represents a complete abandonment of the restriction. In an unrestricted fashion, we are able to reflect any propositional existential into the `Type` universe.

If it isn't already clear that arbitrary propositions may be embedded into this existential, it may be helpful to consider this reformulation, using the same `inhabited` type as in the choice axiom:

```Coq
indef_descr' : ∀ A, ‖A‖ -> A.
```

It is difficult for me to imagine when one would want to accept this axiom. One is almost completely stripping away the important properties of the `Prop` universe, which leads me to wonder whether one wouldn't be better off at this point ignoring the `Prop` universe altogether, and doing all of your proofs and logic within `Type`?

Once the elimination restriction is gone, the only significant property of `Prop` is that it is impredicative. However, one could enable impredicativity for the `Set` universe if they so desired.