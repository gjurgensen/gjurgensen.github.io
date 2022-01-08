---
layout: post
title: "Coq Equality IV"
date: 2021-08-03 00:00:04
Tag: Coq
---

{% include mathjax.html %}

<!-- Click [here](/assets/coq/Inversion.v) for the corresponding Coq file. -->

## Inversion

 When I first learned about the `inversion` tactic, I was constantly getting it 
   mixed up with `destruct`. When plugging in a USB drive, one always finds themselves 
   trying the wrong side first. Similarly, I would always try the wrong tactic first
   before realizing my mistake.

   In fact, the two are quite similar in their goal. `destruct` is the classic means 
   of case analysis. When one invokes `destruct x`, the proof branches into $n$ proof 
   goals, for the $n$ constructors of the inductive type `x`.

   Let's take a look at what a proof using `destruct` looks like under the hood.
 
{% highlight Coq %}
Lemma andb_true: forall b: bool, andb b true = b.
Proof using.
  intros *.
  destruct b; exact eq_refl.
Defined.
Print andb_true.

(* andb_true = 
   fun b : bool =>
   if b as b0 return ((b0 && true)%bool = b0) then eq_refl else eq_refl
	    : forall b : bool, (b && true)%bool = b
 *)
{% endhighlight %}


 `destruct` structures our proof term as an if statement. More generally, it 
   generates a match statement on the inductive term's constructors.

   It is important to note here that the match statement does not take into account 
   any parameters to the inductive term which should in theory contradict certain 
   cases. Because `destruct` just generates a simple `match`, this information is 
   not taken into account, and is actually erased!

   Let's construct an example.
 

{% highlight Coq %}
Inductive even: nat -> Prop :=
  | is_even_0  : even 0
  | is_even_SS : forall n, even n -> even (S (S n)).

Lemma not_even_1 : ~ even 1.
Proof using.
  intro contra.
{% endhighlight %}


 We would like to perform case analysis on the `even 1` term to show both options
   are impossible.
 
{% highlight Coq %}
  destruct contra.
{% endhighlight %}


 But we lose the information that the term was parameterized over `1`! 
{% highlight Coq %}
  Undo.
{% endhighlight %}


 Even if we use the `eqn` variant, `destruct` will erase our parameter. 
{% highlight Coq %}
  destruct contra eqn:case.
  Undo.
{% endhighlight %}


 What we need here is inversion. `inversion` also considers the possible constructors 
   of the term. However, it actually looks at the values of the inductive term's 
   parameters to determine which cases are impossible.

   Conceptually, it is as if we are looking at the constructors, and reasoning about 
   them in reverse. What constructors could have produced this term? The name
   "inversion" is intentionally suggestive of this backward reasoning over constructors.

   In this case, `inversion` solves our goal instantly, since there are no possible 
   cases.
 
{% highlight Coq %}
  inversion contra.
{% endhighlight %}


 How would we go about replicating this behavior? Well, we know `destruct` erases 
   the value of our parameters, but what if we replaced our values with variables, 
   and specified the value of the variable in a separate hypothesis?
 
{% highlight Coq %}
  Undo.
  set (x := 1) in contra.
  destruct contra.
{% endhighlight %}


 The parameter is still being erased! The reason why is that the value of `x` is 
   overwritten by the case analysis. What we need to do is remember the value of x 
   in a separate hypothesis as an equality.
 
{% highlight Coq %}
  Undo.
  assert (x_eq: x = 1) by exact (eq_refl _).
{% endhighlight %}


 While not strictly neccessary, clearing the definition of x makes the context
   more readable.
 
{% highlight Coq %}
  clearbody x.
  destruct contra.
{% endhighlight %}


 There we go! We see the `x_eq` hypothesis was preserved, which we can discriminate 
   in both cases.
 
{% highlight Coq %}
  Undo.
  destruct contra; discriminate x_eq.
Qed.
{% endhighlight %}


 For fun, why don't we automate this with a tactic? The general process is:
   1. Replace values with variables
   2. Remember the equality between the new variable and its value.
   3. Clear the definition of the variable.
   4. Destruct the inductive term

   We can add more steps for convenience, such as substituting the equalities 
   back after the destruct step, and checking if any case is discriminable.
 

{% highlight Coq %}
Ltac gen_eq H x := 
  let i := fresh in 
  set (i := x) in H;
  let eq := fresh in 
  assert (eq: i = x) by exact eq_refl;
  clearbody i.

Goal ~ even 1.
  intro contra.
  gen_eq contra 1.
{% endhighlight %}


 These automatically generated names are ugly, but they should be largely erased 
   after substitution.

{% highlight Coq %}
Abort.

Ltac gen_eq_non_vars H := 
  repeat match type of H with 
  | context[_ ?x] =>
      assert_fails (is_var x);
      gen_eq H x
  end.

Goal ~ even 1.
  intro contra.
  gen_eq_non_vars contra.
Abort.

Ltac inv H :=
  gen_eq_non_vars H;
  destruct H;
  subst;
  try discriminate.

Goal ~ even 1.
  intro contra.
  inv contra.
{% endhighlight %}

 Success! 
{% highlight Coq %}
Qed.
{% endhighlight %}


 Let's try our hand at a more complicated example, where inversion doesn't trivially 
   solve our goal.
 
{% highlight Coq %}
Require Import Coq.Lists.List.
Import ListNotations.

Inductive in_list {A} (a: A): list A -> Prop :=
  | in_head : forall t,
      in_list a (a :: t)
  | in_tail : forall x t,
      in_list a t ->
      in_list a (x :: t).

Goal forall x, in_list x [1;2] -> x = 1 \/ x = 2.
  intros * H.
  inv H.
  - injection H1; repeat intros ->.
    auto.
  - injection H1; repeat intros ->.
    clear H1.
    inv H.
    + injection H1; repeat intros ->. 
      auto.
    + injection H1; repeat intros ->.
      clear H1.
      inv H.
Qed.
{% endhighlight %}


 Clearly, we can see our little `inv` tactic is really helpful for reasoning about 
   these dependent terms!

   To close things out, I should point out that our `inv` tactic actually diverges from 
   the `inversion` tactic in a couple important ways. First, the `inversion` tactic
   will actually preserve the original term. For instance, consider again the 
   `andb_true` proof.
 

{% highlight Coq %}
Lemma andb_true': forall b: bool, andb b true = b.
Proof using.
  intros *.
{% endhighlight %}


 Using `inversion` here on `b` won't actually destruct it, although it will fork
   our proof goal into two identical goals.
 
{% highlight Coq %}
  inversion b.
  Undo.
{% endhighlight %}


 This is because `inversion` actually makes a copy of the term, and destructs the 
   copy. The idea is that we only want inversion to perform case analysis on the facts 
   which produced the constructor, not on the constructor itself. We can replicate that
   behavior easily enough.
 
{% highlight Coq %}
Ltac inv H ::=
  let H' := fresh H in
  pose proof H as H';
  gen_eq_non_vars H';
  destruct H';
  subst;
  try discriminate.

  inv b.
Abort.
{% endhighlight %}


 The other thing `inversion` can do that `inv` can't is extract sub-equalities: 
{% highlight Coq %}
Goal forall a b, S a = S b -> a = b.
  intros * H.
  inversion H.
{% endhighlight %}


 However, this behavior is not in line with the goal of the rest of the tactic,
   so I'd argue is out of place being included in `inversion`.

   The more specialized `injectivity` accomplishes the same fundamental task:
 
{% highlight Coq %}
  Undo.
  injection H.
  auto.
Qed.

{% endhighlight %}

