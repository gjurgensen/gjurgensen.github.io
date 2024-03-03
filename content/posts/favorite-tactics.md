---
title: "A Few of my Favorite Tactics"
date: 2021-11-13 00:00:01
draft: false
tag: Coq
---

![Sound of Music](/images/sound_of_music.jpg)

Having used Coq for a good while now, I've slowly begun to accumulate my own set of hand-written tactics. Writing your own tactics can be frustrating at first; Ltac is dynamic and stateful, the polar opposite of the Gallina we all love. But after some time, you're sure to start writing tactics that you're surprised you ever lived without.

In this post, I'll go through some of my personal favorite tactics I've written, with the hope that these examples show how Ltac can be used to make your proofs easier, and perhaps inspire you to write your own tactics. They are listed very roughly in accordance to their complexity and inter-dependencies.

A basic understanding of Ltac is assumed. If you are having trouble following along, I suggest you refer to the following documentation:
- [Tactic Index](https://coq.inria.fr/refman/coq-tacindex.html)
- [Tactic Notations](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#tactic-notations)

Documentation may be dry, but there's not better way to hone your understanding!

Let's jump in.

## 1. {{<highlight Coq "hl_inline=true">}}find{{</highlight>}}

{{<highlight Coq "hl_inline=true">}}find{{</highlight>}} is a higher-order tactic which takes a tactic as an argument. It then applies said tactic to the first hypothesis to make progress.

```Coq
Tactic Notation "find" tactic3(tac) :=
  match goal with
  | H : _ |- _ => progress tac H
  end.
```

This is useful shorthand when searching for a hypothesis, or when one would prefer not to use a hypothesis's name. For example, one could re-define the {{<highlight Coq "hl_inline=true">}}assumption{{</highlight>}} tactic as {{<highlight Coq "hl_inline=true">}}find (fun H => exact H){{</highlight>}}.

There are a myriad of reasons one might want to avoid explicitly using an identifier. It can be easier (as is the case with {{<highlight Coq "hl_inline=true">}}assumption{{</highlight>}}), but it can also be more maintainable. Identifiers within a proof are fragile, especially if introduced implicitly.

Before moving on, let's note a technical detail in the above definition. The {{<highlight Coq "hl_inline=true">}}tac{{</highlight>}} argument is given the nonterminal {{<highlight Coq "hl_inline=true">}}tactic3{{</highlight>}}. Tactic expressions have 6 precedence levels, with 0 representing maximal precedence, and 5 representing minimal precedence. Precedence is necessary to disambiguate tactic expressions such as {{<highlight Coq "hl_inline=true">}}a by b; c{{</highlight>}}. Should this be interpreted as {{<highlight Coq "hl_inline=true">}}a by (b; c){{</highlight>}}, or {{<highlight Coq "hl_inline=true">}}(a by b); c{{</highlight>}}? This depends on the precedence of the argument {{<highlight Coq "hl_inline=true">}}b{{</highlight>}} to {{<highlight Coq "hl_inline=true">}}a{{</highlight>}}. At tactic level 3, which we will use all throughout this post for consistency, it is parsed as {{<highlight Coq "hl_inline=true">}}(a by b); c{{</highlight>}}.

## 2. {{<highlight Coq "hl_inline=true">}}define{{</highlight>}}

By and large, tactics are used to construct *opaque* terms. With the exception of tactics like {{<highlight Coq "hl_inline=true">}}set{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}pose{{</highlight>}}, the definitions of most terms we add to our hypothesis list are completed forgotten; only their type is retained. Most often this is desirable, but occasionally we'd like to actually retain the definition of a term we build tactically.

We introduce a family of such functions called {{<highlight Coq "hl_inline=true">}}define{{</highlight>}}. The first version behaves much like assert.

<!-- When one invokes the {{<highlight Coq "hl_inline=true">}}assert{{</highlight>}} tactic, the proof is temporarily diverted to a separate goal, which once proved, becomes a hypothesis. Like nearly all tactics though, {{<highlight Coq "hl_inline=true">}}assert{{</highlight>}} will "forget" the actual value of the term it built, and only remembers the type. This is desirable most of the time, but sometimes one would prefer to remember the term we just built. The {{<highlight Coq "hl_inline=true">}}define{{</highlight>}} tactic does just that - it works like assert, but then remember the term that was built. -->

```Coq
Tactic Notation "define" uconstr(c) "as" ident(H) :=
  unshelve evar (H : c).

Tactic Notation "define" uconstr(c) "as" ident(H) "by" tactic3(tac) :=
  define c as H; [solve[tac]|].

Tactic Notation "define" uconstr(c) :=
  let H := fresh in
  define c as H.

Tactic Notation "define" uconstr(c) "by" tactic3(tac) :=
  define c; [solve[tac]|].
```

Here, {{<highlight Coq "hl_inline=true">}}evar{{</highlight>}} creates a unification variable of our desired type. Wrapping the tactic in {{<highlight Coq "hl_inline=true">}}unshelve{{</highlight>}} immediately focuses the newly created unification variable into the first subgoal. Once we clear that goal, the new hypothesis will be available, as in {{<highlight Coq "hl_inline=true">}}assert{{</highlight>}}, but this time, it will be fully visible, having just been built via unification.

You may notice from the above tactic definitions just how verbose and redundant it is to support the idiomatic optional clauses such as the {{<highlight Coq "hl_inline=true">}}as{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}by{{</highlight>}} clauses, since we have to give an instance for each combination of usage. Later in the post, we'll omit these obvious derivatives when they become to cumbersome.

<!-- This tactic is admittedly more niche than the rest. It isn't often we need to construct an intermediate, transparent term in proof mode. For anything of moderate complexity, it is likely better to define the term explicitly outside the context of the proof. But every once in a while, this tactic is genuinely handy, and I was enamored at how difficult this tactic was to write when I did want it, and yet how simple it ended up being once I found the appropriate definition. -->

A common scenario in which we'd like to retain a term's definition is when we are trying to prove an existential. Therefore, we create a version of define which works specifically on existentials.

```Coq
Tactic Notation "define" "exists" :=
  unshelve eexists.

Tactic Notation "define" "exists" "by" tactic3(tac) :=
  define exists; [solve[tac]|].
```

Again, we use the {{<highlight Coq "hl_inline=true">}}unshelve{{</highlight>}} trick, this time with {{<highlight Coq "hl_inline=true">}}eexists{{</highlight>}}.


## 3. {{<highlight Coq "hl_inline=true">}}forward{{</highlight>}}

Given a functional hypothesis {{<highlight Coq "hl_inline=true">}}H : forall a: A, B a{{</highlight>}}, or in the nondependent case,
{{<highlight Coq "hl_inline=true">}}H : A -> B{{</highlight>}}, {{<highlight Coq "hl_inline=true">}}forward H{{</highlight>}} focuses the new subgoal {{<highlight Coq "hl_inline=true">}}A{{</highlight>}}, which it then uses to specialize {{<highlight Coq "hl_inline=true">}}H{{</highlight>}}. The name therefore comes from the concept of "forward reasoning".

```Coq
Tactic Notation "forward" hyp(H):=
  match type of H with
  | forall i: ?x, _ =>
      let var := fresh i in
      define x as var;
      [|specialize (H var);
        unfold var in H;
        clear var
      ]
  end.

Tactic Notation "forward" hyp(H) "by" tactic3(tac) :=
  forward H; [solve [tac]|].
```

To accomplish our task, we use the previous {{<highlight Coq "hl_inline=true">}}define{{</highlight>}} tactic to build our term, which we then specialize our hypothesis {{<highlight Coq "hl_inline=true">}}H{{</highlight>}} with. We then remove the intermediate term from our hypotheses by unfolding its definition in the now specialized hypothesis {{<highlight Coq "hl_inline=true">}}H{{</highlight>}}, and clear it.

Why do we use {{<highlight Coq "hl_inline=true">}}define{{</highlight>}} here instead of one of a standard tactic? I.e., why do we want the specializing term to be transparent? In the nondependent case {{<highlight Coq "hl_inline=true">}}H : A -> B{{</highlight>}}, it won't make a difference. However, for the dependent case {{<highlight Coq "hl_inline=true">}}H : forall a: A, B a{{</highlight>}}, the particular term {{<highlight Coq "hl_inline=true">}}a: A{{</highlight>}} is generally significant, and therefore shouldn't be obscured.

## 4. {{<highlight Coq "hl_inline=true">}}(dependent) inv(c){{</highlight>}}

Inversion in Coq can get downright *ugly*. The proof state is often absolutely littered with new hypotheses. There are only so many times one can write {{<highlight Coq "hl_inline=true">}}inversion H; subst{{</highlight>}} before creating a shorthand. We introduce such a shorthand with the tactic {{<highlight Coq "hl_inline=true">}}inv{{</highlight>}}. Similarly, {{<highlight Coq "hl_inline=true">}}invc H{{</highlight>}} will perform {{<highlight Coq "hl_inline=true">}}inv H{{</highlight>}}, then {{<highlight Coq "hl_inline=true">}}clear H{{</highlight>}}, which I find is desirable more often than not.

(Note: I did not come up with the {{<highlight Coq "hl_inline=true">}}inv{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}invc{{</highlight>}} tactics myself. I found them originally in the [StructTact](https://github.com/uwplse/StructTact/blob/master/theories/StructTactics.v#L17https://github.com/uwplse/StructTact/blob/179bd5312e9d8b63fc3f4071c628cddfc496d741/theories/StructTactics.v#L17) library, and modified them to my liking).

```Coq
Tactic Notation "subst!" :=
  subst;
  repeat match goal with
  | H : ?x = ?x |- _ => clear H
  end.

Tactic Notation "inv" hyp(H) :=
  inversion H;
  subst!.

Tactic Notation "inv" hyp(H) "as" simple_intropattern(pat) :=
  inversion H as pat;
  subst!.

Tactic Notation "invc" hyp(H) :=
  (* Rename H first to free identifier *)
  let _temp := fresh "_temp" in
  rename H into _temp;
  inv _temp;
  try clear _temp.

Tactic Notation "invc" hyp(H) "as" simple_intropattern(pat) :=
  let _temp := fresh in
  rename H into _temp;
  inv _temp as pat;
  try clear _temp.
```

Beyond the behavior I described, you can see in these definitions some extra features. For instance, we strengthen {{<highlight Coq "hl_inline=true">}}subst{{</highlight>}} to clear syntactically reflexive equalities, and we rename to-be-cleared hypotheses to free up identifiers.

Note also in the {{<highlight Coq "hl_inline=true">}}invc{{</highlight>}} variants that we have to wrap our {{<highlight Coq "hl_inline=true">}}clear{{</highlight>}} with a {{<highlight Coq "hl_inline=true">}}try{{</highlight>}}. Some inversions will actually clear the hypothesis automatically (most notably inversions on equalities), and we don't want {{<highlight Coq "hl_inline=true">}}invc{{</highlight>}} to fail on such hypotheses.

We can continue making improvements on inversion. One very common issue arises when you invoke inversion on highly dependent terms. You will often end up with hypotheses of type {{<highlight Coq "hl_inline=true">}}existT P p x = existT P p y{{</highlight>}}. Intuitively, we would expect this to imply {{<highlight Coq "hl_inline=true">}}x = y{{</highlight>}}, but this is in fact not provable without an additional axiom, so regular inversion does not perform this task. If we were to accept the relevant axiom, we could vastly improve inversion for highly dependent terms.

The axiom we need is any one of the many variants of a class of axioms called "UIP" (Uniqueness of Identity Proofs). Here is one such axiom:

```Coq
Axiom uip_refl : forall A (a: A) (h : a = a), h = eq_refl a.
```

Hopefully this is quite intuitive. Given our inductive definition of {{<highlight Coq "hl_inline=true">}}eq{{</highlight>}}, it may even be surprising that we can't derive this proposition. {{<highlight Coq "hl_inline=true">}}eq_refl{{</highlight>}} is the only constructor of the equality type, so it stands to reason that any proof of {{<highlight Coq "hl_inline=true">}}a = a{{</highlight>}} must be convertible to {{<highlight Coq "hl_inline=true">}}eq_refl a{{</highlight>}}. As this post is not about axioms, I won't dive into *why* this proposition is unprovable. Suffice to say, it is perfectly innocuous (unless combined with more exotic axioms, such as univalence) and extremely helpful.

We can use Coq's variant of the UIP axiom by exporting {{<highlight Coq "hl_inline=true">}}Coq.Logic.EqDep{{</highlight>}} (their version of the axiom is called {{<highlight Coq "hl_inline=true">}}eq_rect_eq{{</highlight>}}. It looks quite different from {{<highlight Coq "hl_inline=true">}}uip_refl{{</highlight>}}, but the two are in fact logically equivalent).

We then introduce a variant of our inversion tactic called {{<highlight Coq "hl_inline=true">}}dependent inv{{</highlight>}} to leverage the extra power of this axiom:

```Coq
Require Import Coq.Logic.EqDep.

Ltac destr_sigma_eq :=
  repeat match goal with
  | H: existT _ _ _ = existT _ _ _ |- _ =>
      simple apply inj_pairT2 in H
  end.

Tactic Notation "dependent" "inv" hyp(H) :=
  inv H;
  destr_sigma_eq;
  subst!.

Tactic Notation "dependent" "inv" hyp(H) "as" simple_intropattern(pat) :=
  inv H as pat;
  destr_sigma_eq;
  subst!.

Tactic Notation "dependent" "invc" hyp(H) :=
  invc H;
  destr_sigma_eq;
  subst!.

Tactic Notation "dependent" "invc" hyp(H) "as" simple_intropattern(pat) :=
  invc H as pat;
  destr_sigma_eq;
  subst!.
```

## 5. {{<highlight Coq "hl_inline=true">}}gen / to{{</highlight>}}

Sometimes, one's hypothesis is just too specific, and needs to be weakened. In particular, this issue often arises as we prepare to induct on a hypothesis. The tactic {{<highlight Coq "hl_inline=true">}}gen x := y to P in H{{</highlight>}} will replace term {{<highlight Coq "hl_inline=true">}}y{{</highlight>}} in {{<highlight Coq "hl_inline=true">}}H{{</highlight>}} with the variable {{<highlight Coq "hl_inline=true">}}x{{</highlight>}}, where {{<highlight Coq "hl_inline=true">}}x{{</highlight>}} satisfies the predicate {{<highlight Coq "hl_inline=true">}}P{{</highlight>}}. The definition of {{<highlight Coq "hl_inline=true">}}x{{</highlight>}} is then discarded. It therefore "generalizes" {{<highlight Coq "hl_inline=true">}}y{{</highlight>}} up to the predicate.

```Coq
(* A version of cut where the assumption is the first subgoal *)
Ltac cut_flip p :=
  let H := fresh in
  assert (H: p);
    [|revert H].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P):=
  set (I := l);
  cut_flip (P I);
    [ unfold I; clear I
    | clearbody I
    ].

Tactic Notation "gen" ident(I) ":=" constr(l) "to" uconstr(P) "in" hyp(H) :=
  set (I := l) in H;
  cut_flip (P I);
    [ unfold I in H |- *; clear I
    | clearbody I
    ].

...
```
I define many more variants of {{<highlight Coq "hl_inline=true">}}gen / to{{</highlight>}}, for example with a {{<highlight Coq "hl_inline=true">}}by{{</highlight>}} clause, but the implementations are all obvious, following the general idioms followed by the standard tactics.

## 6. {{<highlight Coq "hl_inline=true">}}foreach{{</highlight>}}, {{<highlight Coq "hl_inline=true">}}forsome{{</highlight>}}, and other list-based tactics

It would be nice to have some tactics which operate over lists. Specifically, lists of
hypotheses. For instance, a {{<highlight Coq "hl_inline=true">}}foreach{{</highlight>}} combinator could apply some tactic to every hypothesis in a list (necessarily succeeding on each), and a {{<highlight Coq "hl_inline=true">}}forsome{{</highlight>}} tactic could do the same, but stop on the first success (and failing if none succeeded).

This immediate issue we run into is that hypotheses will generally have different types, whereas a Gallina list is necessarily homogenous in type. We could certainly overcome this issue with enough force. For instance, we could use a list of type-value pairs ({{<highlight Coq "hl_inline=true">}}list {x & x}{{</highlight>}}), but this quickly get's exhausting. We are forced to manually track types, and we must be careful to keep list elements in a canonical form which our Ltac can parse entirely syntactically. Far more convenient is to embrace Ltac's dynamic typing, and introduce a notion of heterogeneous lists.

Actually, we don't need to create very many new definitions. Instead, we re-purpose Gallina's tuples. Recall that the tuple {{<highlight Coq "hl_inline=true">}}(a, b, ..., y, z){{</highlight>}} actually de-sugars into the left-nested pairs {{<highlight Coq "hl_inline=true">}}((((a, b), ...), y), z){{</highlight>}}. We therefore interpret an arbitrary-length "flat" tuple as a non-empty heterogeneous list, where {{<highlight Coq "hl_inline=true">}}(t, h){{</highlight>}} represent the "cons" of {{<highlight Coq "hl_inline=true">}}h{{</highlight>}} to {{<highlight Coq "hl_inline=true">}}t{{</highlight>}}.

A non-pair {{<highlight Coq "hl_inline=true">}}x{{</highlight>}} is therefore interpreted as the single-element list. Of course, a heterogeneous list of pairs is therefore an ambiguous notion which ought to be avoided.

The only thing missing is a notion an empty heterogenous list. We might consider the unit value for this, but as we have enough ambiguity at the moment, we'll instead introduce a distinguished type and value for this purpose.

```Coq
Inductive Hnil : Set := hnil.
```

This creates some ambiguity of its own, as there are now two ways to represent singleton lists. Either as {{<highlight Coq "hl_inline=true">}}x{{</highlight>}} or {{<highlight Coq "hl_inline=true">}}(hnil, x){{</highlight>}}.

With our representation decided, we can define some list tactics!

```Coq
Ltac _foreach ls ftac :=
  lazymatch ls with
  | hnil => idtac
  | (?ls', ?H) =>
      first [ftac H| fail 0 ftac "failed on" H];
      _foreach ls' ftac
  | ?H => first [ftac H| fail 0 ftac "failed on" H]
  end.
Tactic Notation "foreach" constr(ls) tactic3(ftac) :=
  _foreach ls ftac.

Ltac _forsome ls ftac :=
  lazymatch ls with
  | hnil => fail 0 ftac "failed on every hypothesis"
  | (?ls', ?H) =>
      ftac H + _forsome ls' ftac
  | ?H => ftac H + fail 0 ftac "failed on every hypothesis"
  end.
Tactic Notation "forsome" constr(ls) tactic3(ftac) :=
  _forsome ls ftac.
```

There are a number of interesting aspects of these definitions. First, why do we define both {{<highlight Coq "hl_inline=true">}}_foreach{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}foreach{{</highlight>}}? Well, we'd prefer the tactic notation used in the {{<highlight Coq "hl_inline=true">}}foreach{{</highlight>}} definition, however tactic notations are un-recursive. Therefore, we must first define the recursive tactic {{<highlight Coq "hl_inline=true">}}_foreach{{</highlight>}}, and then wrap it in the notation defined by {{<highlight Coq "hl_inline=true">}}foreach{{</highlight>}}.

Second, notice we use {{<highlight Coq "hl_inline=true">}}lazymatch{{</highlight>}}. This is because there is ambiguity in our cases. Our third match case matches anything. By using {{<highlight Coq "hl_inline=true">}}lazymatch{{</highlight>}}, we commit to the first two cases if they match, and we only try the third if the first two fail to unify.

Why stop there, let's create some more list-based tactics!

```Coq
Ltac syn_eq H H' :=
  match H with
  | H' => true
  end.

Ltac in_list H ls := (forsome ls (syn_eq H)) + fail 0 H "not in list".
```

{{<highlight Coq "hl_inline=true">}}in_list{{</highlight>}} simply uses {{<highlight Coq "hl_inline=true">}}forsome{{</highlight>}} to check if an element occurs in a list (up to syntactic equality, not convertibility).

```Coq
Ltac _env ls cont :=
  match goal with
  | H : _ |- _ =>
      assert_fails (in_list H ls);
      _env (ls, H) cont
  end + (cont ls).
Tactic Notation "env" tactic3(cont) :=
  _env hnil cont.
```

{{<highlight Coq "hl_inline=true">}}env{{</highlight>}} will create a list of all of the hypotheses in our current environment (i.e. proof state). However, tactics can't easily "return" values, so we are instead forced into a continuation-passing paradigm in order to use the value built by {{<highlight Coq "hl_inline=true">}}env{{</highlight>}}. The second argument to {{<highlight Coq "hl_inline=true">}}env{{</highlight>}} is its continuation, which should be a tactic function expecting a list as an argument. For more information on this strategy, see section 14.3, "Functional Programming in Ltac", in Chlipala's [*Certified Programming with Dependent Types*](http://adam.chlipala.net/cpdt/cpdt.pdf#section.14.3).

```Coq
Ltac _list_minus ls1 ls2 keep cont :=
  lazymatch ls1 with
  | hnil => cont keep
  | (?t, ?h) =>
      tryif in_list h ls2 then
        _list_minus t ls2 keep cont
      else
        _list_minus t ls2 (keep, h) cont
  | ?h =>
      tryif in_list h ls2 then
        cont keep
      else
        cont (keep, h)
  end.
Tactic Notation "list_minus" constr(ls1) constr(ls2) tactic3(cont) :=
  _list_minus ls1 ls2 hnil cont.
```

Now we define {{<highlight Coq "hl_inline=true">}}list_minus{{</highlight>}} to take the difference of two lists. Again, this is necessarily done in a continuation-passing style.

Putting {{<highlight Coq "hl_inline=true">}}env{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}list_minus{{</highlight>}} together, we get {{<highlight Coq "hl_inline=true">}}env_delta{{</highlight>}}:

```Coq
Tactic Notation "env_delta" tactic3(tac) tactic3(cont) :=
  env (fun old =>
  tac;
  env (fun new =>
  list_minus new old cont
  )).
```

Here, we build a list only of the *new* hypotheses introduced into the environment by {{<highlight Coq "hl_inline=true">}}tac{{</highlight>}}. We do this by grabbing the environment before and after {{<highlight Coq "hl_inline=true">}}tac{{</highlight>}} is executed, and then calculating their difference.

## 7. {{<highlight Coq "hl_inline=true">}}(max) induct(!){{</highlight>}}

The standard {{<highlight Coq "hl_inline=true">}}induction{{</highlight>}} tactic can be surprisingly lacking in a couple of ways. First, it discards information when the arguments to the inductive term are not simple variables.

For instance, consider the proposition {{<highlight Coq "hl_inline=true">}}R^* 0 x{{</highlight>}}, where {{<highlight Coq "hl_inline=true">}}R^*{{</highlight>}} is the reflexive-transitive closure of {{<highlight Coq "hl_inline=true">}}R{{</highlight>}}. We would like to induct over the structure of the proof (a sequence of relation steps). However, if we were to invoke the regular {{<highlight Coq "hl_inline=true">}}induction{{</highlight>}} tactic, it would replace {{<highlight Coq "hl_inline=true">}}0{{</highlight>}} with an arbitrary variable, thereby losing that information. We can solve this issue by first replacing the {{<highlight Coq "hl_inline=true">}}0{{</highlight>}} with a variable ourselves, and creating a separate assumption equating the variable to the value it substitutes before its definition is erased by {{<highlight Coq "hl_inline=true">}}induction{{</highlight>}}.

To accomplish this task, we are going to need to introduce a number of helpful intermediate tactics.

```Coq
Ltac _repeat_count tac cont n :=
  tryif tac then
    _repeat_count tac cont (S n)
  else
    cont n.

Tactic Notation "repeat_count" tactic3(tac) tactic3(cont) :=
  _repeat_count tac cont 0.
```

Our first helper is a refinement of the standard {{<highlight Coq "hl_inline=true">}}repeat{{</highlight>}} tactic. Just like {{<highlight Coq "hl_inline=true">}}repeat{{</highlight>}}, it will apply a tactic 0 or more times, stopping at the first failure. {{<highlight Coq "hl_inline=true">}}repeat_count{{</highlight>}} expands on this functionality by counting the number of successful applications. We will see soon why this might be useful.

Note that this uses the continuation-passing style discussed in our introduction of the list-based tactics.

Knowing that some tactic has been applied {{<highlight Coq "hl_inline=true">}}n{{</highlight>}} times, we would perhaps like to perform another tactic {{<highlight Coq "hl_inline=true">}}n{{</highlight>}} times. This is precisely the role of the {{<highlight Coq "hl_inline=true">}}do{{</highlight>}} tactic. However, the {{<highlight Coq "hl_inline=true">}}do{{</highlight>}} tactic only accepts Ltac's internal notion of integers, which is distinct from the Gallina representation of natural numbers as used by the {{<highlight Coq "hl_inline=true">}}repeat_count{{</highlight>}} tactic. Therefore, we give an alternative definition of {{<highlight Coq "hl_inline=true">}}do{{</highlight>}}, called {{<highlight Coq "hl_inline=true">}}do_g{{</highlight>}} which uses Gallina's naturals.

```Coq
Ltac _do_g n tac :=
  match n with
  | S ?n' => tac; _do_g n' tac
  | 0 => idtac
  end.
Tactic Notation "do_g" constr(n) tactic3(tac) :=
  _do_g n tac.
```

Finally, we can define our improved induction tactic, called {{<highlight Coq "hl_inline=true">}}induct{{</highlight>}}.

```Coq
Ltac gen_eq_something H :=
  match type of H with
  | context[_ ?x] =>
      assert_fails (is_var x);
      gen ? := x to (eq x) in * by reflexivity
  end.

Ltac intro_try_rew :=
  intros [=<-] +
  intros [=->] +
  intros [=] +
  intro.

Ltac _induct_by H inductStep :=
  repeat_count (progress gen_eq_something H) (fun n =>
    inductStep H;
    do_g n intro_try_rew
  ).

Tactic Notation "induct" hyp(H) :=
  _induct_by H ltac:(fun hyp => induction hyp).

Tactic Notation "induct" hyp(H) "as" simple_intropattern(pat) :=
  _induct_by H ltac:(fun hyp => induction hyp as pat).

Tactic Notation "induct" hyp(H) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => induction hyp using c).

Tactic Notation "induct" hyp(H) "as" simple_intropattern(pat) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => induction hyp as pat using c).
```

The first definition, {{<highlight Coq "hl_inline=true">}}gen_eq_something{{</highlight>}}, simply looks for a non-variable argument in the hypothesis {{<highlight Coq "hl_inline=true">}}H{{</highlight>}} to generalize up to equality. The second tactic, {{<highlight Coq "hl_inline=true">}}intro_try_rew{{</highlight>}}, does {{<highlight Coq "hl_inline=true">}}intro{{</highlight>}}, but simultaneously tries fancier introductions which destructs/rewrites the equality. Finally, {{<highlight Coq "hl_inline=true">}}_induct_by{{</highlight>}} puts everything together. We {{<highlight Coq "hl_inline=true">}}gen_eq_something{{</highlight>}} our inductive term as much as possible. Note this will add equality assumptions to our goal. Now, we perform the induction given by {{<highlight Coq "hl_inline=true">}}inductStep{{</highlight>}}, and on each subgoal, we will introduce each of the equalities we added by {{<highlight Coq "hl_inline=true">}}gen_eq_something{{</highlight>}}.

If you have ever used {{<highlight Coq "hl_inline=true">}}dependent induction{{</highlight>}}, {{<highlight Coq "hl_inline=true">}}induct{{</highlight>}} is trying to do the same thing, sometimes called "inversion-induction", because it can be seen as simultaneously trying to invert and induct on the hypothesis. If {{<highlight Coq "hl_inline=true">}}dependent induction{{</highlight>}} does the same thing, why did we just re-create the functionality? Well, {{<highlight Coq "hl_inline=true">}}dependent induction{{</highlight>}} actually uses the heterogenous equality {{<highlight Coq "hl_inline=true">}}JMeq{{</highlight>}}, and uses the same UIP axiom we mentioned with {{<highlight Coq "hl_inline=true">}}dependent inv{{</highlight>}}. Therefore, {{<highlight Coq "hl_inline=true">}}induct{{</highlight>}} is something of a simpler variation of {{<highlight Coq "hl_inline=true">}}dependent induction{{</highlight>}}.

One annoying problem with our {{<highlight Coq "hl_inline=true">}}induct{{</highlight>}} tactic (and {{<highlight Coq "hl_inline=true">}}dependent induction{{</highlight>}}, for that matter) is that we often end up with inductive hypotheses of the form {{<highlight Coq "hl_inline=true">}}x = x -> y{{</highlight>}} (or {{<highlight Coq "hl_inline=true">}}forall x, x = y -> z{{</highlight>}}), which are trivial but annoying to simplify. To solve these, I include a tactic variant {{<highlight Coq "hl_inline=true">}}induct!{{</highlight>}}, which is more eager to clean up the hypothesis state.

```Coq
Tactic Notation "`" tactic3(tac) := tac.

(* Specialize hypothesis with a unification variable *)
Ltac especialize H :=
  match type of H with
  | forall x : ?T, _ =>
      let x' := fresh x in
      evar (x': T);
      specialize (H x');
      unfold x' in H;
      clear x'
  end.

Ltac ecut_eq_aux IH :=
  first
    [ match type of IH with
      | _ = _ -> _ =>
          try forward IH by exact eq_refl
      end
    | especialize IH;
      ecut_eq_aux IH].

Ltac ecut_eq IH :=
  match type of IH with
  | context[_ = _ -> _] => idtac
  end;
  ecut_eq_aux IH;
  let t := type of IH in
  assert_fails (`has_evar t).

Ltac _induct_excl_by H inductStep :=
  env_delta (_induct_by H inductStep) (fun ls =>
    foreach ls (fun H => repeat ecut_eq H)
  );
  subst!.

Tactic Notation "induct!" hyp(H) :=
  _induct_excl_by H ltac:(fun hyp => induction hyp).

Tactic Notation "induct!" hyp(H) "as" simple_intropattern(pat) :=
  _induct_excl_by H ltac:(fun hyp => induction hyp as pat).

Tactic Notation "induct!" hyp(H) "using" uconstr(c) :=
  _induct_excl_by H ltac:(fun hyp => induction hyp using c).

Tactic Notation "induct!" hyp(H) "as" simple_intropattern(pat) "using" constr(c) :=
  _induct_excl_by H ltac:(fun hyp => induction hyp as pat using c).
```

We create a tactic called {{<highlight Coq "hl_inline=true">}}ecut_eq{{</highlight>}} which will look for equality assumptions in a hypothesis, and attempt to resolve them automatically, potentially specializing the hypothesis with unification variables to do so, as long as no unification variables remain by the end.

The meat of {{<highlight Coq "hl_inline=true">}}induct!{{</highlight>}} is performed by the {{<highlight Coq "hl_inline=true">}}_induct_excl_by{{</highlight>}} tactic which uses {{<highlight Coq "hl_inline=true">}}env_delta{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}foreach{{</highlight>}} from our list tactics to apply {{<highlight Coq "hl_inline=true">}}ecut_eq{{</highlight>}} only to the hypotheses introduced during induction.

You may have noticed the odd-looking backtick tactic notation. Clearly this is just an identity combinator, right? What use is it here?

This bactick combinator highlights a very unfortunate corner of Ltac. Contrary to our expectations, the backtick combinator is *not* referentially transparent. That is, the tactic expression {{<highlight Coq "hl_inline=true">}}a{{</highlight>}} is *not* necessarily semantically equivalent to {{<highlight Coq "hl_inline=true">}}`a{{</highlight>}}.

Specifically, adding the backtick can affect when a tactic expression is executed. In the tactic expression {{<highlight Coq "hl_inline=true">}}a b{{</highlight>}}, where {{<highlight Coq "hl_inline=true">}}b{{</highlight>}} is a tactic expression being passed to the higher-order tactic combinator {{<highlight Coq "hl_inline=true">}}a{{</highlight>}}, it is unfortunately not always clear *when* {{<highlight Coq "hl_inline=true">}}b{{</highlight>}} will execute. Almost always, we'd prefer it to only execute at the point it is invoked by {{<highlight Coq "hl_inline=true">}}a{{</highlight>}}. For whatever reason, this is ensured in the expression {{<highlight Coq "hl_inline=true">}}a `b{{</highlight>}}, but not in {{<highlight Coq "hl_inline=true">}}a b{{</highlight>}}. Thus, the bactick can be interpreted as a way to properly delay execution of a tactic expression.

I wish I could explain when adding the backtick is necessary. The truth is, I don't know. The broader Coq community seems to be resigned to the fact that the execution semantics of Ltac are unclear, and place their hope in some eventual successor such as the mythical "Ltac2" to save us. (Much like Ltac's execution semantics, it is quite unclear *when* this will come to pass). Until then, we will have to simply live with this defect and insert a backtick now and again when our tactics are misbehaving.

Finally, we add one more feature to our custom induction. Often, we are tasked with manually reverting variables before inducting in order to maximally generalize our inductive hypothesis. Then, we have to re-{{<highlight Coq "hl_inline=true">}}intro{{</highlight>}}s them. Since there is no harm "over"-generalizing our inductive hypothesis in this way, we can automatically revert and re-{{<highlight Coq "hl_inline=true">}}intro{{</highlight>}}s all of our variables.

```Coq
Tactic Notation "do_generalized" constr(ls) tactic3(tac) :=
  repeat_count (
    find (fun H =>
      assert_fails (`in_list H ls);
      revert H
  )) (fun n =>
    tac;
    do_g n intro
  ).

Ltac _max_induction_by H inductStep :=
  do_generalized H (inductStep H).


Tactic Notation "max" "induction" hyp(H) :=
  _max_induction_by H ltac:(fun hyp => induction hyp).

Tactic Notation "max" "induction" hyp(H) "as" simple_intropattern(pat) :=
  _max_induction_by H ltac:(fun hyp => induction hyp as pat).

...

Tactic Notation "max" "induct!" hyp(H) :=
  _induct_excl_by H ltac:(fun hyp => max induction hyp).

Tactic Notation "max" "induct!" hyp(H) "as" simple_intropattern(pat) :=
  _induct_excl_by H ltac:(fun hyp => max induction hyp as pat).

...
```

## 8. {{<highlight Coq "hl_inline=true">}}tedious{{</highlight>}}/{{<highlight Coq "hl_inline=true">}}follows{{</highlight>}}

I'll end with a tactic which has been extremely useful to me, but I'd also consider to be quite experimental. I am quite a fan of the {{<highlight Coq "hl_inline=true">}}easy{{</highlight>}} tactic, and the related {{<highlight Coq "hl_inline=true">}}now{{</highlight>}} tactic, which automatically solves some simple goals. However, I got frustrated that it was unable to solve certain goals, such as those which would follow from one or two {{<highlight Coq "hl_inline=true">}}constructor{{</highlight>}} applications, or by {{<highlight Coq "hl_inline=true">}}eauto{{</highlight>}}.

I originally envisioned {{<highlight Coq "hl_inline=true">}}tedious{{</highlight>}}/{{<highlight Coq "hl_inline=true">}}follows{{</highlight>}} as slightly more powerful versions of {{<highlight Coq "hl_inline=true">}}easy{{</highlight>}}/{{<highlight Coq "hl_inline=true">}}now{{</highlight>}}, but I quickly found myself adding more and more functionality until these had become quite ambitious tactics. Still, I have tried to retain one important characteristic: that it be relatively quick to fail. Here they are in their current form:

```Coq
(* Induction failure occasionally produces odd warnings:
     https://github.com/coq/coq/issues/10766
   We silence these warnings with the following setting.
 *)
Global Set Warnings "-cannot-remove-as-expected".

Ltac _etedious n :=
  match n with
  | 0 => fail 1 "Ran out of gas"
  | S ?n' => intros; (
      (eauto; easy) +
      (constructor; _etedious n') +
      (econstructor; _etedious n') +
      ((find (fun H => injection H + induction H + destruct H)); _etedious n') +
      (fail 1 "Cannot solve goal")
    )
  end.

Ltac _tedious n :=
  match n with
  | 0 => fail 1 "Ran out of gas"
  | S ?n' => intros; (
      (auto; easy) +
      (constructor; _tedious n') +
      (econstructor; _etedious n') +
      ((find (fun H => injection H + induction H + destruct H)); _tedious n') +
      (fail 1 "Cannot solve goal")
    )
  end.

(* Slows exponentially with gas. Wouldn't suggest higher than 10. *)
Tactic Notation "tedious" constr(n) :=
  tryif
    match goal with
    | |- ?g => has_evar g
    end
  then
    _etedious n
  else
    _tedious n.

Tactic Notation "tedious" :=
  tedious 5.

Tactic Notation "follows" tactic3(tac) :=
  tac; tedious.

Tactic Notation "after" tactic3(tac) :=
  tac; try tedious.

Tactic Notation "tedious" "using" constr(lemmas) :=
  follows (foreach lemmas (fun H => epose proof H)).
```

As you can see, {{<highlight Coq "hl_inline=true">}}tedious{{</highlight>}} is a sort of brute force heuristic tactic to solve "straightforward" goals. It uses {{<highlight Coq "hl_inline=true">}}auto; easy{{</highlight>}} (or {{<highlight Coq "hl_inline=true">}}eauto; easy{{</highlight>}} if we expect there to be unificaiton variables) as its immediate solver. If the goal is not immediately solvable, it will try some step and recurse. Of course, we would have no reason to expect this to terminate by itself, so we start {{<highlight Coq "hl_inline=true">}}tedious{{</highlight>}} with some "gas". Each time it recurses, it loses gas, and when it gets to 0, it gives up. This "gas" is therefore the maximum search depth. By default, tedious starts with 5 gas. We note that increasing the gas will slow it down exponentially, since *each subgoal* {{<highlight Coq "hl_inline=true">}}tedious{{</highlight>}} encounters will have more gas, meaning it will be more likely to produce more subgoals/hypotheses.

In practice, I have found this tactic to exhibit suprising strength given its usual speed. However, there are certainly some times where the proof state is too complex and {{<highlight Coq "hl_inline=true">}}tedious{{</highlight>}} will take too long before giving up. Going forward, I'd like to experiment more with ways {{<highlight Coq "hl_inline=true">}}tedious{{</highlight>}} can inspect the proof state, either the number of subgoals or the number of hypotheses, and reduce its gas accordingly to get more consistent execution times.
