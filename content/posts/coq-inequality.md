---
title: "Coq Equality II"
date: 2021-08-03 00:00:02
draft: false
tag: Coq
---

## Inequality

Last time we learned how to prove an equality without using {{<highlight Coq "hl_inline=true">}}reflexivity{{</highlight>}}.
On the other side of the coin, how do we prove inequality without {{<highlight Coq "hl_inline=true">}}discriminate{{</highlight>}}?

Let's start with a simple inequality: {{<highlight Coq "hl_inline=true">}}1 <> 2{{</highlight>}}. What sort of proof term would {{<highlight Coq "hl_inline=true">}}discriminate{{</highlight>}} generate?

```Coq
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
```

Well, this wasn't as simple as we might have hoped. After trimming it down a bit, it starts to become a little more digestible:

```Coq
Check ((fun H: 1 = 2 =>
  eq_ind 1 (fun x =>
    match x with
    | 1 => True
    | _ => False
    end
  ) I 2 H) : 1 <> 2
).
```

(We could in fact further reduce the term by η-reduction, but I'm not sure that enhances readability here).

   Recall that the type {{<highlight Coq "hl_inline=true">}}1 <> 2{{</highlight>}} is equivalent to {{<highlight Coq "hl_inline=true">}}1 = 2 -> False{{</highlight>}}. It should be no suprise
   then that our proof term is a function taking a proof term of {{<highlight Coq "hl_inline=true">}}1 = 2{{</highlight>}}, and constructing
   a term of type {{<highlight Coq "hl_inline=true">}}False{{</highlight>}}.

   The crux of our proof is the leading {{<highlight Coq "hl_inline=true">}}eq_ind{{</highlight>}} function. This is the
   induction principle generated for {{<highlight Coq "hl_inline=true">}}eq{{</highlight>}}. Let's try to understand it by
   checking its type.


```Coq
Check eq_ind.
(* eq_ind
	 : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y
 *)
```


 In english, this takes a dependent prop {{<highlight Coq "hl_inline=true">}}P{{</highlight>}}, a proof of said proposition
   for term {{<highlight Coq "hl_inline=true">}}x{{</highlight>}}, and finally a proof that {{<highlight Coq "hl_inline=true">}}x = y{{</highlight>}}, before producing a proof
   of the proposition over {{<highlight Coq "hl_inline=true">}}y{{</highlight>}}.

   <!-- This is certainly intuitive. If {{<highlight Coq "hl_inline=true">}}x{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}y{{</highlight>}} are definitionally equal (as is
   asserted by the {{<highlight Coq "hl_inline=true">}}eq{{</highlight>}} type), then certainly they should be interchangeable. -->

   Hopefully this is intuitive. If {{<highlight Coq "hl_inline=true">}}x{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}y{{</highlight>}} are equal, then they should be
   interchangeable. Informally, what is true of {{<highlight Coq "hl_inline=true">}}x{{</highlight>}} should be true of {{<highlight Coq "hl_inline=true">}}y{{</highlight>}} by substitution.

  To prove then that {{<highlight Coq "hl_inline=true">}}1{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}2{{</highlight>}} are unequal, we start with their assumed equality,
  then use {{<highlight Coq "hl_inline=true">}}eq_ind{{</highlight>}} to construct a contradiction.
  We choose the dependent proposition {{<highlight Coq "hl_inline=true">}}P{{</highlight>}} supplied to {{<highlight Coq "hl_inline=true">}}eq_ind{{</highlight>}} such that {{<highlight Coq "hl_inline=true">}}P{{</highlight>}} obviously
  holds for {{<highlight Coq "hl_inline=true">}}1{{</highlight>}}, and obviously doesn't for {{<highlight Coq "hl_inline=true">}}2{{</highlight>}}.
  With this goal in mind, we reach the following definition:

```Coq
Definition P := fun x =>
  match x with
  | 1 => True
  | _ => False
  end.

Compute (P 1).
(* = True : Prop *)

Compute (P 2).
(* = False : Prop *)
```


 Now we just give {{<highlight Coq "hl_inline=true">}}P{{</highlight>}} to {{<highlight Coq "hl_inline=true">}}eq_ind{{</highlight>}}, and fill in the other necessary arguments:

```Coq
Check ((fun H: 1 = 2 => eq_ind 1 P I 2 H) : 1 <> 2).
```


 This method we used here can be generalized to any structural inequality. To prove
  {{<highlight Coq "hl_inline=true">}}a <> b{{</highlight>}}, we would want to construct a similar {{<highlight Coq "hl_inline=true">}}P{{</highlight>}} with a revised match statement

```Coq
Definition P := fun x =>
  match x with
  | a => True
  | _ => False
  end.
```

   So long as {{<highlight Coq "hl_inline=true">}}a{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}b{{</highlight>}} are structurally unequal, the match statment will take one to
   {{<highlight Coq "hl_inline=true">}}True{{</highlight>}} and the other to {{<highlight Coq "hl_inline=true">}}False{{</highlight>}}, setting the stage for our contradiction.

   And so, we have reached the heart of the discriminate tactic. {{<highlight Coq "hl_inline=true">}}discriminate{{</highlight>}} will
   construct such a dependent proposition, and use {{<highlight Coq "hl_inline=true">}}eq_ind{{</highlight>}} to construct a contradiction
   Once it has proved {{<highlight Coq "hl_inline=true">}}False{{</highlight>}}, it can prove any goal.


## Bonus: Proof (Ir)relevance

 That's it for the main topic, but for the interested reader, now is also a good time
   for a digression on Props and (in)equality.

   While not directly derivable in Coq, many users decided to introduce the concept of proof
   irrelevance axiomatically:

```Coq
Axiom proof_irrelevance: forall (P: Prop) (p1 p2: P), p1 = p2.
```


 <!-- That is, we are now permitting two terms of sort {{<highlight Coq "hl_inline=true">}}Prop{{</highlight>}} to be considered equal,
   *even if they are not definitionally equal*. -->

  That is, we permit *any* two proofs terms of some proposition to be considered equal.

   Anytime you add an axiom to Coq, you must ensure that it is consistent. That is,
   that the axiom does not admit a proof of {{<highlight Coq "hl_inline=true">}}False{{</highlight>}}.

   Proof irrelevance would be inconsistent if we could come up with some {{<highlight Coq "hl_inline=true">}}p1{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}p2{{</highlight>}}
   of a shared proposition which we could prove unequal, in direct contradiction with
   the axiom.

   Thinking about what we just learned about inequalities, shouldn't such a proof be
   rather trivial?

   Consider the following silly {{<highlight Coq "hl_inline=true">}}Prop{{</highlight>}}:

```Coq
Inductive foo : Prop :=
  | bar : foo
  | baz : foo.

Goal bar <> baz.
```

 Why reinvent the wheel? Let's just knock this out with {{<highlight Coq "hl_inline=true">}}discriminate{{</highlight>}}:

```Coq
Fail discriminate.

(* The command has indeed failed with message:
   Not a discriminable equality.
 *)
```

   Uh oh. Perhaps we were overconfident. Unfortunately {{<highlight Coq "hl_inline=true">}}discriminate{{</highlight>}} doesn't provide a very
   informative error message, so let's just try building a manual proof like the one we did
   earlier.

```Coq
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
```


 Failure again! At least this error message is more informative...

   Coq tells us that our elimination of {{<highlight Coq "hl_inline=true">}}x{{</highlight>}} (our match term) is invalid, because a proof term
   (a term whose type has type {{<highlight Coq "hl_inline=true">}}Prop{{</highlight>}}) cannot be eliminated to produce a term whose type
   has type {{<highlight Coq "hl_inline=true">}}Type{{</highlight>}}.

   What we have encountered is Coq's elimination restriction on proof terms. Proof terms are only
   allowed to be eliminated to construct further proof terms. Therefore, we prevent information
   flow out of the {{<highlight Coq "hl_inline=true">}}Prop{{</highlight>}} universe.

   There are many reasons for this restriction, and in fact we should be thankful for
   it. Perhaps the most obvious is in terms of code extraction. Because the computational
   components of a Coq spec (the {{<highlight Coq "hl_inline=true">}}Set{{</highlight>}} and {{<highlight Coq "hl_inline=true">}}Type{{</highlight>}} sorted terms) are independent of proof terms,
   we can completely erase them during extraction!

   The only information from {{<highlight Coq "hl_inline=true">}}Prop{{</highlight>}}s that are allowed into {{<highlight Coq "hl_inline=true">}}Type{{</highlight>}}s and {{<highlight Coq "hl_inline=true">}}Set{{</highlight>}}s exist at the
   type-level. So once we confirm that our spec type-checks within Coq, we are safe to erase
   all proof terms in the extracted code.

   It also means that we can't prove an inequality on proof terms, even when it seems obvious by
   structural differences.

Next up in our series, we deal with [rewriting](/posts/coq-rew).
