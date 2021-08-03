(** ** 2. Discriminate *)

(** Now we know how to manually prove an equality, without using `reflexivity`.
   On the other side of the coin, how do we prove inequality without `discriminate`?

   Let's start with a simple inequality, i.e. a structural inequality. This time,
   we'll skip right to the part where we cheat and print a generated proof term.
 *)

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
    
(** Well, this wasn't as simple as we might have hoped. Let me do the dirty work of cutting 
   it down to its leanest form:
 *)

Check ((fun H: 1 = 2 =>
  eq_ind 1 (fun x =>
    match x with 
    | 1 => True
    | _ => False
    end
  ) I 2 H) : 1 <> 2
).

(** We could in fact further reduce the term by eta reduction, but I think it is most digestable 
   in its current form.

   Recall that the type `1 <> 2` is equivalent to `1 = 2 -> False`. It should be no suprise
   then that our proof term is a function taking a proof term of `1 = 2`, and constructing
   a term of type `False`.

   The crux of our proof is the leading `eq_ind` function. This is in fact the 
   induction definition generated for the `eq` type. Let's check the type.
 *)

Check eq_ind.
(* eq_ind
	 : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y
 *)

(** In english, this takes a dependent prop P, a proof of said proposition 
   for term x, and finally a proof that `x = y`, before producing a proof 
   of the proposition over y.

   This is certainly intuitive. If x and y are definitionally equal (as is 
   asserted by the `eq` type), then certainly they should be interchangeable.

   Of course, in our example, x=1 and y=2 are definitionally *unequal*. We 
   therefore use eq_ind to construct our contradiction. To do so, we choose 
   our dependent proposition P such that it is obviously true for x=1, and 
   obviously wrong for y=2. With this goal in mind, we reach the following 
   definition:
 *)
Definition P := fun x =>
  match x with 
  | 1 => True
  | _ => False
  end.

Compute (P 1).
(* = True : Prop *)

Compute (P 2).
(* = False : Prop *)
 
(** Now we just give P to `eq_ind`, and fill in the other necessary arguments: *)

Check ((fun H: 1 = 2 => eq_ind 1 P I 2 H) : 1 <> 2).

(** This method we used here can be generalized to any structural inequality. To prove 
   a <> b, we would want to construct a similar P with a revised match statement

   ```
   match x with 
   | a => True 
   | _ => False
   end
   ```
   
   So long as `a` and `b` are structurally equal, the match statment will take one to 
   `True` and the other to `False`, setting the stage for our contradiction.

   And so, we have reached the heart of the discriminate tactic. `discriminate` will 
   construct such a dependent proposition, and use `eq_ind` to construct a contradiction
   Once it has proved `False`, it can prove any goal.
 *)

(** * Detour *)
 
(** That's it for the main topic, but for the interested reader, now is also a good time 
   for a digression on Props and (in)equality.

   While not provable in Coq, many users decided to introduce the concept of proof 
   irrelevance axiomatically. That is, they define such an axiom:
 *)
Axiom proof_irrelevance: forall (P: Prop) (p1 p2: P), p1 = p2.

(** That is, we are now permitting two terms of sort `Prop` to be considered equal,
   *even if they are not definitionally equal*.

   Anytime you add an axiom to Coq, you must ensure that it is consistent. That is,
   that the axiom does not admit a proof of `False`.

   Proof irrelevance would be inconsistent if we could come up with some `p1` and `p2` 
   of a shared Prop type which we could prove unequal, in direct contradiction with 
   the axiom.

   Think about what we just learned about inequalities, shouldn't such a proof be 
   rather trivial?

   Consider the following silly Prop:
 *)
Inductive foo : Prop :=
  | bar : foo 
  | baz : foo.

Goal bar <> baz.
(** Why reinvent the wheel? Let's just knock this out with `discriminate`:
 *)
Fail discriminate.

(* The command has indeed failed with message:
   Not a discriminable equality.
 *)
   
(** Uh oh. Perhaps we were overconfident. Unfortunately `discriminate` doesn't provide a very 
   informative error message, so let's just try building a manual proof like the one we did 
   earlier.
*)
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

(** Failure again! At least this error message is more informative...

   Coq tells us that our elimination of x (our match term) is invalid, because a Prop cannot
   be eliminated to produce a term of sort Type (the same applies producing a term of sort 
   Set). There are many reasons for this restriction, and in fact we should be thankful for 
   it. Perhaps the most obvious is in terms of code extraction. Because the computational 
   components of a Coq spec (the Set and Type sorted terms) are independent of Prop values,
   we can completely erase Props from the extraction!

   The only information from Props that are allowed into Types and Sets exist at the 
   type-level. So once we confirm that our spec type-checks within Coq, we are safe to erase 
   all Props in the extracted code.

   It also means that we can't prove an inequality of Props, even when it seems obvious by 
   structural differences.

   In this case, our match term in P' eliminates a term of sort Prop and produces a Prop.
   At first glance, this might appear consistent with the rules of Prop elimination. The
   problem is in the type of P', foo -> Prop.
 *)
Check (foo -> Prop).
   
(* foo -> Prop : Type *)

(** Thus, if P' were typable, it would be a Type, constructed by inspection of 
   a Prop `foo`. This is the point of the proof that Coq admirably rejects.
 *)

(** Up next, rewriting. *)