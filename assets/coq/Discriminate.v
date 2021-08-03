(* I was confused at first as to how proof irrelevance could be consistent.
   Shouldn't it be pretty easy to show structurally different terms in Prop
   are inequal, and from there reach a contradiction with our irrelevance axiom?

   Consider this simple Prop:
 *)

Inductive foo : Prop :=
  | bar : foo 
  | baz : foo.

(* Shouldn't inequality of `bar` and `baz` be trivial?
 *)

Goal bar <> baz.
Fail discriminate.
(* The command has indeed failed with message:
   Nota discriminable equality.
 *)
Abort.

(* The tactic fails, and unfortunately does so with an uninformative error
   message. Without knowing how discriminate works under the hood, its difficult
   to determine the fundamental obstacle here.

   Let's check out a similar proof over terms in a Set.
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
    
   This proof term isn't as lean as it could be, owing to its generation by a 
   generalized tactic. Let's clean it up for readability:
 *)

Check ((fun H: 1 = 2 =>
  eq_ind 1 (fun x =>
    match x with 
    | 1 => True
    | _ => False
    end
  ) I 2 H) : 1 <> 2
).

(* In fact, we could further reduce the term by eta reduction:
 *)
Check ((
  eq_ind 1 (fun x =>
    match x with 
    | 1 => True
    | _ => False
    end
  ) I 2) : 1 <> 2).

(* This looks much more digestable. Recall that the type `1 <> 2` is equivalent to
   `1 = 2 -> False`. It should be no suprise then that our proof term is a function 
   taking a proof term of `1 = 2`, and constructing a term of type `False`.

   The crux of our proof is the leading `eq_ind` function. This is in fact the 
   induction definition generated for the `eq` type. Let's check the type.
 *)

Check eq_ind.
(* eq_ind
	 : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y

   In english, this takes a dependent prop P, a proof of said proposition 
   for term x, and finally a proof that `x = y`, before producing a proof 
   of the proposition over y.

   This is certainly intuitive. If x and y are definitionally equal (as is 
   asserted by the `eq` type), then certainly they should be interchangeable.

   Of course, in our example, x=1 and y=2 are definitionally *inequal*. We 
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
 
(* Clearly, `P 1` simplifies to True, and `P 2` simplifies to False.
   Providing this to eq_ind, and the trivial proof of True, `I`, we succesfully
   construct `False` from `1 = 2`.

   So, what prevents us from doing the same thing with `bar` and `baz`?
   Let's try building a similar dependent prop for `foo`:
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

   Coq tells us that our elimination of x (our match term) is invalid, because
   a Prop cannot be eliminated to produce a term of sort Type. This is in fact
   a very nice property Coq enforces. Only terms of sort Prop can depend on 
   the structure/value of other Props. This is what makes axiomatic proof 
   irrelevance consistent, as we mentioned at the beginning of this adventure.
   It is also instrumental in extraction. We can extract the computational
   aspects of a Coq spec (i.e. all of the non-Props), and we can safely erase 
   the Prop terms, since from the perspective of non-Props, the only information 
   they provide is in their static types.

   In this case, our match term in P' eliminates a term of sort Prop and produces a
   Prop. At first glance, this might appear consistent with the rules of Prop
   elimination. The problem is in the type of P', foo -> Prop.
 *)
Check (foo -> Prop).
   
(* foo -> Prop : Type

   Thus, if P' were typable, it would be a Type, constructed by inspection of 
   a Prop `foo`.
 *)