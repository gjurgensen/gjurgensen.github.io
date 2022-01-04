---
layout: post
title: "Coq Equality II"
date: 2021-08-03 00:00:02
tag: Coq
---

<!-- Click [here](/assets/coq/Inequality.v) for the corresponding Coq file. -->

## Inequality

Last time we learned how to prove an equality without using `reflexivity`.
On the other side of the coin, how do we prove inequality without `discriminate`?

Let's start with a simple inequality: `1 <> 2`. What sort of proof term would `discriminate` generate?

{% highlight Coq %}
Lemma neq_1_2 : 1 <> 2.
Proof.
  discriminate.
Defined.
Print neq_1_2.

(* neq_1_2 = 
   fun H : 1 = 2 =>
   let H0 : False :=
     eq_ind 1
	   (fun e : nat =>
        match e with
        | 0 => False
        | S n => match n with
                 | 0 => True
                 | S _ => False
                 end
        end) I 2 H in
   False_ind False H0
        : 1 <> 2
 *)
{% endhighlight %}
    
Well, this wasn't as simple as we might have hoped. After trimming it down a bit, it starts to become a little more digestible:

{% highlight Coq %}
Check ((fun H: 1 = 2 =>
  eq_ind 1 (fun x =>
    match x with 
    | 1 => True
    | _ => False
    end
  ) I 2 H) : 1 <> 2
).
{% endhighlight %}

(We could in fact further reduce the term by η-reduction, but I'm not sure that enhances readability here).

   Recall that the type `1 <> 2` is equivalent to `1 = 2 -> False`. It should be no suprise
   then that our proof term is a function taking a proof term of `1 = 2`, and constructing
   a term of type `False`.

   The crux of our proof is the leading `eq_ind` function. This is the 
   induction principle generated for `eq`. Let's try to understand it by 
   checking its type.
 

{% highlight Coq %}
Check eq_ind.
(* eq_ind
	 : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y
 *)
{% endhighlight %}


 In english, this takes a dependent prop `P`, a proof of said proposition 
   for term `x`, and finally a proof that `x = y`, before producing a proof 
   of the proposition over `y`.

   <!-- This is certainly intuitive. If `x` and `y` are definitionally equal (as is 
   asserted by the `eq` type), then certainly they should be interchangeable. -->

   Hopefully this is intuitive. If `x` and `y` are equal, then they should be 
   interchangeable. Informally, what is true of `x` should be true of `y` by substitution.

  To prove then that `1` and `2` are unequal, we start with their assumed equality, 
  then use `eq_ind` to construct a contradiction.
  We choose the dependent proposition `P` supplied to `eq_ind` such that `P` obviously 
  holds for `1`, and obviously doesn't for `2`.
  With this goal in mind, we reach the following definition:
 
{% highlight Coq %}
Definition P := fun x =>
  match x with 
  | 1 => True
  | _ => False
  end.

Compute (P 1).
(* = True : Prop *)

Compute (P 2).
(* = False : Prop *)
{% endhighlight %}

 
 Now we just give `P` to `eq_ind`, and fill in the other necessary arguments: 

{% highlight Coq %}
Check ((fun H: 1 = 2 => eq_ind 1 P I 2 H) : 1 <> 2).
{% endhighlight %}


 This method we used here can be generalized to any structural inequality. To prove 
  `a <> b`, we would want to construct a similar `P` with a revised match statement

{% highlight Coq %}
Definition P := fun x =>
  match x with 
  | a => True 
  | _ => False
  end.
{% endhighlight %}
   
   So long as `a` and `b` are structurally unequal, the match statment will take one to 
   `True` and the other to `False`, setting the stage for our contradiction.

   And so, we have reached the heart of the discriminate tactic. `discriminate` will 
   construct such a dependent proposition, and use `eq_ind` to construct a contradiction
   Once it has proved `False`, it can prove any goal.
 

# Bonus: Proof (Ir)relevance
 
 That's it for the main topic, but for the interested reader, now is also a good time 
   for a digression on Props and (in)equality.

   While not directly derivable in Coq, many users decided to introduce the concept of proof 
   irrelevance axiomatically:
 
{% highlight Coq %}
Axiom proof_irrelevance: forall (P: Prop) (p1 p2: P), p1 = p2.
{% endhighlight %}


 <!-- That is, we are now permitting two terms of sort `Prop` to be considered equal,
   *even if they are not definitionally equal*. -->

  That is, we permit *any* two proofs terms of some proposition to be considered equal.

   Anytime you add an axiom to Coq, you must ensure that it is consistent. That is,
   that the axiom does not admit a proof of `False`.

   Proof irrelevance would be inconsistent if we could come up with some `p1` and `p2` 
   of a shared proposition which we could prove unequal, in direct contradiction with 
   the axiom.

   Thinking about what we just learned about inequalities, shouldn't such a proof be 
   rather trivial?

   Consider the following silly `Prop`:
 
{% highlight Coq %}
Inductive foo : Prop :=
  | bar : foo 
  | baz : foo.

Goal bar <> baz.
{% endhighlight %}

 Why reinvent the wheel? Let's just knock this out with `discriminate`:
 
{% highlight Coq %}
Fail discriminate.

(* The command has indeed failed with message:
   Not a discriminable equality.
 *)
{% endhighlight %}
   
   Uh oh. Perhaps we were overconfident. Unfortunately `discriminate` doesn't provide a very 
   informative error message, so let's just try building a manual proof like the one we did 
   earlier.

{% highlight Coq %}
Fail Definition P' := fun x =>
  match x with 
  | bar => True
  | baz => False
  end.
 
(* The command has indeed failed with message:
   Incorrect elimination of "x" in the inductive type "foo":
   the return type has sort "Type" while it should be "SProp" or "Prop".
   Elimination of an inductive object of sort Prop
   is not allowed on a predicate in sort Type
   because proofs can be eliminated only to build proofs.
 *)
{% endhighlight %}


 Failure again! At least this error message is more informative...

   Coq tells us that our elimination of `x` (our match term) is invalid, because a proof term
   (a term whose type has type `Prop`) cannot be eliminated to produce a term whose type 
   has type `Type`.
   
   What we have encountered is Coq's elimination restriction on proof terms. Proof terms are only
   allowed to be eliminated to construct further proof terms. Therefore, we prevent information 
   flow out of the `Prop` universe.

   There are many reasons for this restriction, and in fact we should be thankful for 
   it. Perhaps the most obvious is in terms of code extraction. Because the computational 
   components of a Coq spec (the `Set` and `Type` sorted terms) are independent of proof terms,
   we can completely erase them during extraction!

   The only information from `Prop`s that are allowed into `Type`s and `Set`s exist at the 
   type-level. So once we confirm that our spec type-checks within Coq, we are safe to erase 
   all proof terms in the extracted code.

   It also means that we can't prove an inequality on proof terms, even when it seems obvious by 
   structural differences.

Next up in our series, we deal with [rewriting](/coq equality/2021/08/02/rew).
