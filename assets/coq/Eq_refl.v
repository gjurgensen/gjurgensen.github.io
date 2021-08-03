(** ** 1. eq_refl *)

(** Far and away the most confusing topic to me in Coq has been equality. When you, reader,
   first came across equalities, you were probably told that you can solve simple equalities 
   by simplifying them, and then once the goal looks like `?x = ?x`, you can finish with 
   magic `reflexivity`.
 *)
Lemma one_one_two: 1 + 1 = 2.
Proof using.
  simpl.
  reflexivity.

(** In fact, we don't need the `simpl` at all. `reflexivity` can solve the goal all by 
   itself. *)

  Restart.
  reflexivity.

(** One might assume that reflexivity is doing some complicated work behind the curtains -
   including simplification. This is not the case, but one could certainly be excused for 
   thinking so. *)

Defined.

(** Of course, not all equalities are so easy. For instance, let's try throwing reflexivity 
   at some fact about lists. *)

Require Import Coq.Lists.List.
Import ListNotations.

Theorem app_nil_r {A}: forall l: list A,
  l ++ [] = l.
Proof using.
  intros *.
  Fail reflexivity.
(* The command has indeed failed with message:
   In environment
   A : Type
   l : list A
   Unable to unify "l" with "l ++ []".
 *)

(** What separates these two proof goals? Why can reflexivity solve the first, but not 
   this one? One might suspect again that it is a matter of simplification. After all,
   `simpl` fails to progress here: *)

Fail progress simpl.

(* The command has indeed failed with message:
   Failed to progress
 *)
(** But this is somewhat of a red herring. `reflexivity` can in a sense do some simplication,
   but it is not doing it so explicitly. But we're getting ahead of ourselves. Let's take 
   a step back and look at the definition of equality. *)

Abort.

Locate "_ = _".
(* Notation
   "x = y" := eq x y : type_scope (default interpretation)
 *)

Print eq.

(* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x *)

(** If you haven't already seen the definition of eq, this may look surprising. The type takes 
   two arguments. But `eq_refl`, the only constructor, takes just one, producing the reflexive 
   equality. How is it that we are able to prove equalities of two terms that are not exactly
   identical structurally?

   For instance, let's try manually constructing a term of type `1 + 1 = 2`. *)
   
Check eq_refl (1 + 1).

(* eq_refl : 1 + 1 = 1 + 1 *)

(** Well that didn't work. I suppose we can try using the right hand side instead. *)

Check eq_refl 2.

(* eq_refl : 2 = 2 *)

(** That didn't work either. What are we missing? To find out, let's cheat and look at the 
   proof term generated by `reflexivity` in our first proof. *)

Print one_one_two.

(* one_one_two = eq_refl
	 : 1 + 1 = 2
 *)
   
(** So reflexivity does generate a simple `eq_refl` term, but somehow it has the right type?
   What magic is going on here? The printed term is in fact hiding `eq_refl`'s argument,
   so I'll provide a more explicit term: *)

Check (eq_refl 2 : 1 + 1 = 2).

(** This is the same proof term we tried before, but this time we are explicitly giving it our 
   own type, which Coq accepts. Indeed, the magic of equality is in the formulation of Coq's
   type system (or to be pedantic, the Calculus of Inductive Construction's type
   system). The most straightforward type of `eq_refl 2` would be `2 = 2`, and so that is 
   what Coq originally showed us when we let Coq pick the type. However, Coq permits the 
   type `1 + 1 = 2`, because `1 + 1` and `2` are *definitionally* equal, and therefore 
   interchangeable from a type perspective. 

   What does it mean for two terms to be definitionally equal? It means that there exists some 
   sequence of reduction steps such that the two terms reduce to identical terms (up to 
   irrelevant subterms).

   `1 + 1` reduces to `2` straightforwardly: *)

Goal 1 + 1 = 2.
  cbv delta.
  cbv iota.
  cbv beta.
  cbv iota.
  cbv beta.
  cbv iota.
  cbv beta.
  cbv iota.
  exact (eq_refl _).

(** Of course, we don't actually need to perform each reduction step. Coq reduces the terms for 
   us to type check the proof term. We could have just performed this final application 
   of `eq_refl`. We can still leave out the argument, since Coq will infer it from the type. *)

  Restart.
  exact (eq_refl _).
Qed.

(** We can see that `reflexivity` isn't actually doing that much work. It appears to be
   essentially performing `exact (eq_refl _)`. I don't know about you, but this was much 
   simpler than I was expecting! 

   Coq's awareness of definitionally equal terms is not limited to the `eq` type. Any 
   two definitionally equal terms can be substituted in any type. Consider this inductively
   defined proposition of list length:
 *)
Inductive length {A} : list A -> nat -> Prop :=
  | length_nil :
      length [] 0
  | length_cons : forall x l n,
      length l n ->
      length (x :: l) (S n).
   
Check (length_cons 42 [] 0 length_nil).

(* length_cons 42 [] 0 length_nil
        : length [42] 1
 *)

(** Coq assigns our proof  term a reasonable type. But we could choose to assign 
    it a slightly different type, with values replaced by definitionally equivalent 
    alternatives.
 *)

Check (length_cons 42 [] 0 length_nil : length [21 + 21] (999*0 + 1)).

(** You might wonder how Coq is able to check that two terms are definitionally equal.
   Recall that Coq will not accept recursive definitions which it cannot verify to be 
   terminating. Coq is therefore strongly normalizing. Two terms can be checked for 
   definitional equality by reducing each to their normal form, then compared up to 
   alpha-conversion.

   Definitional equality is sometimes also called intentional equality or convertibility.
   If you want to learn more about it, you can check out the docs page:
     https://coq.inria.fr/refman/language/core/conversion.html#term-convertible
   
   Let's finish by returning to the `eq` type and theorem `app_nil_r`. *)

Theorem app_nil_r {A}: forall l: list A,
  l ++ [] = l.
Proof using.
  intros *.
  Fail exact (eq_refl _).
 
(* The term "eq_refl" has type "l ++ [] = l ++ []"
   while it is expected to have type "l ++ [] = l" (cannot unify 
   "l ++ []" and "l")
 *)

(** Trying to apply `eq_refl` failed for the same reason that `reflexivity` failed here.
   The left and right hand sides are not definitionally equal. In particular, the left 
   hand side cannot reduce far enough, because of the way the append operation is 
   defined. *)

  unfold "++".
  Fail progress cbv.

(** As expected, we can't reduce further. Let's tidy back up. *)
  
  fold (l ++ []).

(** The crucial intuition here is that the left and right hand side *would* be definitionally 
   equal if we knew the value of `l`.

   This motivates our proof by induction on `l`, thereby exposing its structure. *)

  induction l.
  - exact (eq_refl _).
  - cbn.
    rewrite IHl.
    exact (eq_refl _).
Qed.

(** Note that a crucial step in our proof was to rewrite our goal using our inductive 
   hypothesis. We'll get to rewriting soon, but before we get there, we are first going 
   to talk about *in*equality. *)
