---
title: "A Proof of the Schröder-Bernstein Theorem in ACL2"
date: 2024-02-29 00:00:01
math: true
tag: ACL2
---

<!-- %s/`\([^`]\{-1,}\)`/{{<highlight acl2 "hl_inline=true">}}\1{{<\/highlight>}}/gc -->

Recently, Dr. Freek Wiedijk's [Formalizing 100 Theorems](https://cs.ru.nl/~freek/100/) list made the rounds within the ACL2 community.
One of the theorems on the list, which at that point had not been proved within ACL2, was the [Schröder-Bernstein](https://en.wikipedia.org/wiki/Schr%C3%B6der%E2%80%93Bernstein_theorem) Theorem. I had remembered trying to prove this theorem in Coq back in the day while fleshing out a theory of cardinality, before I realized it had already been proven elsewhere.
<!-- It turns out that there were several theorems on the list what folks had in fact proved, but had not been organized and brought to Dr. Wiedijk's attention. Still more were "almost" proved, or could be done straightforwardly. -->

The Schröder-Bernstein theorem states that, for sets $A$ and $B$, if there exists an injection from $A$ to $B$, and an injection from $B$ to $A$, then there must exist a bijection between the two sets. This is equivalent to saying that the ordering of cardinal numbers is antisymmetric. The statement seems rather simple, but I had no real intuition as to how one might construct such a bijection until reading existing proofs.

<!--
The statement of the Schröder-Bernstein theorem is quite intuitive --- at least, I think so. It says that, for sets $A$ and $B$, if there exists an injection from $A$ to $B$, and an injection from $B$ to $A$, then there must exist a bijection between the two sets. Perhaps this seems "obvious" to me because I already know that cardinal numbers are well-ordered. Schröder-Bernstein really just states that the ordering (of "there exists an injection") is antisymmetric. So the intuition I claim to have is "the existence of an injection is an ordinary sort of ordering". Is this intuition valid, and is it helpful?
-->

I found the proof described [here](https://www.cs.cornell.edu/courses/cs2800/2017fa/lectures/lec14-cantor.html) to be direct and easy to follow. Before constructing the bijection, we introduce a theory of "chains". Let's say that $f : A \rightarrow B$ and $g : B \rightarrow A$ are our two injections. A chain is a subset of $A \cup B$ whose elements are reachable to one another via repeated applications of $f$ and $g$, or their inverses. So the element $a \in A$ belongs to the chain: $\lbrace\ \dots\ ,\ f^{-1}(g^{-1}(a)),\ g^{-1}(a),\ a,\ f(a),\ g(f(a)),\ \dots\ \rbrace$. Similarly, $b \in B$ belongs to the chain: $\lbrace\ \dots\ ,\ g^{-1}(f^{-1}(b)),\ f^{-1}(b),\ b,\ g(b),\ f(g(b)),\ \dots\ \rbrace$. We may think of chains as a (potentially cyclical) sequence. Of course, $f^{-1}$ and $g^{-1}$ are not necessarily defined on all input, so sequences proceed rightward infinitely (possibly entering a cycle), but may have a "beginning" when traced leftward where the next inverse to be applied is undefined.

Note that the set of chains partitions $A \cup B$. That is, this notion of chains induces an equivalence class within $A \cup B$.

Among chains which have an initial element (an element for which $f^{-1}$ or $g^{-1}$ is undefined), we shall call chains which begin in $A$ "$A$-stoppers", and the others "$B$-stoppers". We then claim that for any given $a \in A$, $g^{-1} :~A \rightarrow B$ is a bijection on $a$'s chain if the chain is an $B$-stopper. Otherwise (regardless of whether the chain is an $A$-stopper or a non-stopper), $f$ is a bijection on the chain. It follows then that the function $h$, defined below, is a bijection from $A$ to $B$.

$$
h(a) = \begin{cases}
g^{-1}(a) &\text{if } stopper_B(a)\\\\
f(a)      &\text{otherwise}
\end{cases}
$$

To see the details, I'd encourage you to follow the earlier link to a full proof sketch, as the focus here is more on the ACL2 formalization.

## ACL2

As Dr. Matt Kaufmann will tell you, ACL2 was not primarily intended for this sort of proof. It is much more a system for efficient and pragmatic modeling and reasoning over software and hardware systems than it is, say, a compelling system for mathematical foundations. This is likely why we're not higher in Freek's list (at the time of writing, ACL2 and its predecessor nqthm have proved 45/100 theorem, while Isabelle leads with 89/100); most who are concerned primarily with pure mathematics will be drawn to other provers.

Whatever. Let's prove it anyway. It should be fun!

### Setup

Before we consider the proof, we must first determine how to even state the theorem in ACL2. Instead of using sets, we will use predicates, which are of course equivalent. Really, we just use functions. Recall that any non-{{<highlight acl2 "hl_inline=true">}}nil{{</highlight>}} value is considered "true" in ACL2, so we need not require that a function return a boolean to be considered a predicate. To remind us that a function is being thought of as a predicate, we'll use function names {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}q{{</highlight>}} (these will replace our sets $A$ and $B$).

Recall also that the ACL2 logic is untyped, and a function is defined for every value. So we cannot really define a function logically restricted to a particular domain. Instead, we define the function as we wish for the domain in question, and give it an arbitrary value outside of it. To say then that a function {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} has domain {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} and codomain {{<highlight acl2 "hl_inline=true">}}q{{</highlight>}}, it suffices to show {{<highlight acl2 "hl_inline=true">}}(implies (p x) (q (f x))){{</highlight>}} for all {{<highlight acl2 "hl_inline=true">}}x{{</highlight>}}.

<!-- The larger obstacle to encoding our theorem is that ACL2 does not have higher-order functions (although there has been some work toward pseudo-second-order functions [[1](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____APPLY_42), [2](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=SOFT____SOFT)]). It may therefore be unclear how we can even state this theorem. The trick is to avoid universal quantification by instead introducing a generic definition. For instance, instead of saying "for any injection $f : A \rightarrow B$", we will say "let $f : A \rightarrow B$ be an injection, and let's ignore its definition. In ACL2, we can do this with the [encapsulate](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____ENCAPSULATE) event. -->
The real obstacle to stating our theorem is that ACL2 does not have higher-order functions (although there has been some work toward pseudo-second-order functions [[1](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____APPLY_42), [2](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=SOFT____SOFT)]). Our solution will be to avoid universal quantification by instead introducing a generic definition. That is, instead of saying "for any function $f$", we will say "let us define some function $f$, and then throw away its definition". In ACL2, we can do this with an [{{<highlight acl2 "hl_inline=true">}}encapsulate{{</highlight>}}](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____ENCAPSULATE) event.

For example, say we wish to introduce an arbitrary function {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} with arbitrary domain and codomain {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}q{{</highlight>}}. We may do so with the following {{<highlight acl2 "hl_inline=true">}}encapsulate{{</highlight>}}.
```acl2
(encapsulate
  (((p *) => *)
   ((q *) => *)
   ((f *) => *))

  (local (define p (x) x))
  (local (define q (x) x))
  (local (define f (x) x))

  (defrule q-of-f-when-p
    (implies (p x)
             (q (f x)))))
```
Here we define each function to be the identity, but this is unimportant; they are declared to be [{{<highlight acl2 "hl_inline=true">}}local{{</highlight>}}](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____LOCAL) to the {{<highlight acl2 "hl_inline=true">}}encapsulate{{</highlight>}}, and therefore their definitions are limited to its scope. The theorem capturing the domain and codomain of {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}}, however, is non-local, and therefore will survive outside the {{<highlight acl2 "hl_inline=true">}}encapsulate{{</highlight>}}.

<!-- In this encapsulate, we define two functions: {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}}. We define both to be the identity function, but we mark the definitions as {{<highlight acl2 "hl_inline=true">}}local{{</highlight>}} so that they will be erased after the encapsulate is finished. Note that {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} will still be valid function symbols, it is just that logically their definitions are unconstrained. The only facts about {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}q{{</highlight>}} which are remember is our non-local theorem {{<highlight acl2 "hl_inline=true">}}p-of-f-when-p{{</highlight>}}, which states that {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} maps elements of {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} into elements of {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} (interpreting {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} as a predicate). We have therefore in effect defined an arbitrary {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} $:$ {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} $\rightarrow$ {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}}. -->

<!-- To set up the Schröder-Bernstein theorem, we state our premises in the following encapsulation: -->
To set up the Schröder-Bernstein theorem, we use an {{<highlight acl2 "hl_inline=true">}}encapsulate{{</highlight>}} similar to the example above, introducing not one but two functions, and also asserting their injectivity.
```acl2
(encapsulate
  (((f *) => *)
   ((g *) => *)
   ((p *) => *)
   ((q *) => *))

  (local (define p (x) (declare (ignore x)) :enabled t t))
  (local (define q (x) (declare (ignore x)) :enabled t t))

  (local (define f (x) :enabled t x))
  (local (define g (x) :enabled t x))

  (defrule q-of-f-when-p
    (implies (p x)
             (q (f x))))

  (defrule injectivity-of-f
    (implies (and (p x)
                  (p y)
                  (equal (f x) (f y)))
             (equal x y))
    :rule-classes nil)

  (defrule p-of-g-when-q
    (implies (q x)
             (p (g x))))

  (defrule injectivity-of-g
    (implies (and (q x)
                  (q y)
                  (equal (g x) (g y)))
             (equal x y))
    :rule-classes nil))
```

### Inverses

With the premises out of the way, we can start our actual proof.

First, we'll want to define inverses for {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}g{{</highlight>}}. For this, we'll use ACL2's [{{<highlight acl2 "hl_inline=true">}}defchoose{{</highlight>}}](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____DEFCHOOSE) event. {{<highlight acl2 "hl_inline=true">}}defchoose{{</highlight>}} permits you to define non-computational functions via a choice mechanism. Essentially, one provides {{<highlight acl2 "hl_inline=true">}}defchoose{{</highlight>}} with a predicate, and it defines a new function which is logically constrained to return a witness to the predicate, if one exists. This is how universally and existentially quantified statements are defined in ACL2.

<!-- Below, we define an inverse of {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} by first defining a predicate {{<highlight acl2 "hl_inline=true">}}is-f-inverse{{</highlight>}} stating that an element of the domain maps to the provided element in the codomain, and then using this predicate with {{<highlight acl2 "hl_inline=true">}}defchoose{{</highlight>}}. -->

An inverse function may be seen as providing a witness to the invertivilty of some element in the codomain. Therefore, we can use {{<highlight acl2 "hl_inline=true">}}defchoose{{</highlight>}} to define our inverse.
```acl2
(define is-f-inverse (inv x)
  (and (p inv)
       (q x)
       (equal (f inv) x)))

(defchoose f-inverse (inv) (x)
  (is-f-inverse inv x))

(define has-f-inverse (x)
  (is-f-inverse (f-inverse x) x))
```
The definition of {{<highlight acl2 "hl_inline=true">}}g-inverse{{</highlight>}} and its associates mirrors the above.

{{<highlight acl2 "hl_inline=true">}}defchoose{{</highlight>}} gives us a nice way to deal with inverses, but there is no getting around that many theorems will involve explicitly providing witnesses as proof [hints](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____HINTS). This isn't ideal; the prevailing ACL2 style is to do as much as possible with rewrite rules, and only provide a theorem with a couple [{{<highlight acl2 "hl_inline=true">}}enable{{</highlight>}}](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____ENABLE)/[{{<highlight acl2 "hl_inline=true">}}disable{{</highlight>}}](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____DISABLE) hints.

### Chains

After fleshing out a straightforward rewrite theory from our premises and inverse functions, we can start to define our notion of chains. First we note that our predicates {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}q{{</highlight>}} might not be disjoint. A chain segment therefore can not be just a list of values, since we wouldn't be able to discern which predicate the value was intended to satisfy. Our chains are going to be made up of values annotated with their "polarity", a boolean indicating membership in either {{<highlight acl2 "hl_inline=true">}}p{{</highlight>}} or {{<highlight acl2 "hl_inline=true">}}q{{</highlight>}}.

<!-- We avoid actually "constructing" chains, as they are, in general, infinite. All that is necessary is to define our equivalence relation with asserts two elements are in the same chain. This is easy enough. First we define a {{<highlight acl2 "hl_inline=true">}}chain<={{</highlight>}} operator, which says that some element is equal to or to the left of some other element on a chain. That is, there exists some finite number (perhaps 0) of alternating applications of {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}g{{</highlight>}} such that we start at the left element and end at the right element. The equivalence relation {{<highlight acl2 "hl_inline=true">}}chain={{</highlight>}} then is just defined such that {{<highlight acl2 "hl_inline=true">}}(chain= x y){{</highlight>}} iff {{<highlight acl2 "hl_inline=true">}}(or (chain<= x y) (chain<= y x)){{</highlight>}}. -->
<!-- Note that this entire notion of chains does not even use our inverse functions. Regardless, we will want to prove properties about our inverses and their relationships to chains nonetheless. -->

We avoid actually "constructing" chains, as they are, in general, infinite. All that is necessary is to define our equivalence relation with asserts two elements are in the same chain. This is easy enough. First we define a {{<highlight acl2 "hl_inline=true">}}chain<={{</highlight>}} operator, which says that some element is equal to or to the left of some other element on a chain. That is, there exists some finite number (perhaps 0) of alternating applications of {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} and {{<highlight acl2 "hl_inline=true">}}g{{</highlight>}} such that we start at the left element and end at the right element. Then {{<highlight acl2 "hl_inline=true">}}chain={{</highlight>}} following obviously from that.
```acl2
;; `(chain-steps x n)` proceeds `n` steps to the right of chain element `x`.
(define-sk chain<=
  ((x chain-elem-p)
   (y chain-elem-p))
  (exists n
    (equal (chain-steps x (nfix n)) y)))

(define chain=
  ((x chain-elem-p)
   (y chain-elem-p))
  (if (mbt (and (chain-elem-p x)
                (chain-elem-p y)))
      (or (chain<= x y)
          (chain<= y x))
    (equal x y)))

;; ...

(defequiv chain=)
```
Recall that [{{<highlight acl2 "hl_inline=true">}}mbt{{</highlight>}}](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____MBT) (= "must be true") is proved to always be true in [guard](https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2____GUARD)-verified execution. Logically, it is just the identity, but in execution it is replaced with the constant {{<highlight acl2 "hl_inline=true">}}t{{</highlight>}}. Its purpose here is to ensure that {{<highlight acl2 "hl_inline=true">}}chain={{</highlight>}} is an equivalence relation even on guard-violating inputs. ACL2 does not support conditional equivalence relations, and even if it did, it is good practice to use definitions which are well-behaved outside of the guard domain so as to avoid unnecessary hypotheses in one's rules.

We'll next need to capture our notion of "initial" elements of a chain.
```acl2
(define initial-p ((x chain-elem-p))
  (if (polarity x)
      (not (has-g-inverse (chain-elem x)))
    (not (has-f-inverse (chain-elem x)))))

(define initial-wrt (initial (x chain-elem-p))
  (and (chain-elem-p initial)
       (initial-p initial)
       (chain<= initial x)))

(defchoose get-initial (initial) (x)
  (initial-wrt initial x))

(define has-initial ((x chain-elem-p))
  (initial-wrt (get-initial x) x))
```
 <!-- We define an initial chain element to be one whose value does not have an {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} or {{<highlight acl2 "hl_inline=true">}}g{{</highlight>}} inverse (depending on the polarity). We could have just as well defined {{<highlight acl2 "hl_inline=true">}}initial-p{{</highlight>}} in terms of {{<highlight acl2 "hl_inline=true">}}chain<={{</highlight>}}. I.e. {{<highlight acl2 "hl_inline=true">}}(initial-p x){{</highlight>}} might have been defined as {{<highlight acl2 "hl_inline=true">}}(forall (y) (implies (chain<= y x) (equal x y))){{</highlight>}}. This definition involves a quantifier though, which we try to minimize in ACL2. Instead we prove this property as a consequence[^initial-p]. -->
 We define an initial chain element to be one whose value does not have an {{<highlight acl2 "hl_inline=true">}}f{{</highlight>}} or {{<highlight acl2 "hl_inline=true">}}g{{</highlight>}} inverse (depending on the polarity). We could have just as well defined {{<highlight acl2 "hl_inline=true">}}initial-p{{</highlight>}} in terms of {{<highlight acl2 "hl_inline=true">}}chain<={{</highlight>}}. I.e. {{<highlight acl2 "hl_inline=true">}}(initial-p x){{</highlight>}} might have been defined as {{< highlight acl2 "hl_inline=true" >}}(forall (y) (implies (chain<= y x) (equal x y))){{< /highlight >}}. This definition involves a quantifier though, which we try to minimize in ACL2. Instead we prove this property as a consequence[^initial-p].

[^initial-p]:
    Actually, the rule we prove is stronger, and a better rewrite rule: https://github.com/acl2/acl2/blob/master/books/projects/schroder-bernstein/chains.lisp#L429-L437

Again we see an appearance of {{<highlight acl2 "hl_inline=true">}}defchoose{{</highlight>}}, this time in the {{<highlight acl2 "hl_inline=true">}}get-initial{{</highlight>}} function. We have no choice[^choice] here, since we can't define the function computationally. We could walk backwards along the chain looking for an initial element or cycle, but we would have no way to tell if the chain proceeds backwards infinitely.

[^choice]: Pun intended.

Finally we can define {{<highlight acl2 "hl_inline=true">}}in-q-stopper{{</highlight>}}, mirroring $stopper_B$ from the informal sketch.

```acl2
(define in-q-stopper ((x chain-elem-p))
  (and (has-initial x)
       (not (polarity (get-initial x)))))
```
The first conjunct states that the chain is a stopper, and the second that the polarity of the initial element matches {{<highlight acl2 "hl_inline=true">}}q{{</highlight>}}.

### The Witness

Finally we have enough to define our bijective witness, {{<highlight acl2 "hl_inline=true">}}sb-witness{{</highlight>}}, mirroring $h$ from the initial sketch.

```acl2
;; `(make-chain-elem t x)` just makes `x` into a chain element, giving it
;; polariy `t` to indicate its membership in `p`.
(define sb-witness ((x p))
  (if (in-q-stopper (make-chain-elem t x))
      (g-inverse x)
    (f x)))
```
<!-- A whole lot of rewrite rules later, we eventually reach our conclusion, summarized by the following: -->
At this point, I will omit a whole lot of rewrite rules and intermediate theorems, as I really have been doing this whole time, to show you the conclusion, summarized below.
```acl2
(define-sk exists-sb-inverse (x)
  (exists inv
          (and (p inv)
               (equal (sb inv) x))))

(defrule q-of-sb-when-p
  (implies (p x)
           (q (sb x))))

(defrule injectivity-of-sb
  (implies (and (p x)
                (p y)
                (equal (sb x) (sb y)))
           (equal x y)))

(defrule surjectivity-of-sb
  (implies (q x)
           (exists-sb-inverse x)))
```
I have spared the reader from all of intermediate proofs because, truthfully, none of them are all that interesting in isolation. If you want to see the full proof, you'll have to check it out in the ACL2 [community books](https://github.com/acl2/acl2/tree/master/books/projects/schroder-bernstein)!

<!-- ### Conclusion -->

<!-- <!-1- I've omitted the actual meat of these proofs, focusing instead on representations within ACL2. The truth is, no individual intermediate rule is that interesting on its own. If you'd like to see the entire proof, check it out in the ACL2 [community books](https://github.com/acl2/acl2/tree/master/books/projects/schroder-bernstein)! -1-> -->
<!-- I have, of course, omitted the actual meat of the proof. The definitions presented here are quite few compared to all of the rules and intermediate theorems which were necessary to prove along the way. Truthfully, none of these intermediates are all that interesting on their own. They may be of interest in their entirety though. It is too much to be covered thoroughly in a blog post, so if you'd like to see the entire proof, check it out in the ACL2 [community books](https://github.com/acl2/acl2/tree/master/books/projects/schroder-bernstein)! -->

## Footnotes
