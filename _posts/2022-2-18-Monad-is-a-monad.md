---
layout: post
title: "Monad is a Monad is a Monad"
date: 2022-02-18 00:00:01
tag: Haskell
---

> "... she would carve on the tree Rose is a Rose is a Rose is a Rose is a Rose until it went all the way around." - The World is Round, Gertrude Stein

Many a blog and tutorial alike will tell you that a monad is something other than what it is. Perhaps it is a "box", or a "burrito". Sometimes it is a "computation" (aren't all Haskell terms computations?). Certainly there is some merit to this style of explanation-by-analogy. However, such presentations are necessarily limited to approximations of what a monad really is. Analogies may impart some initial intuition, but sooner than later end up holding our mental model back from reaching the full generality of what a monad really is. And it isn't as complicated as you might expect.

I'd like to explain what a monad really is[^non-categorical], as straightforward as possible, without the analogies. A monad is a monad (is a monad is a monad...).

[^non-categorical]: When I talk about a monad in this post, I mean a monad in the Haskell and functional programming sense, as opposed to the category-theoretic definition. The same applies for our discussion of functors.

# Type Families

A monad is a special kind of type family, along with a couple of important functions.
By a type family, I mean anything with kind `* -> *`. A simple function to and from types. For example, let `t :: * -> *` and `x :: *`. Then `t` is a type family and `x` is a type. `t x :: *` is a type, may be called an instance of the type family `t`. We may also say `x` is the parameterized type in `t x`.

Some examples of type families include `[]`, `Maybe`, `Tree`, `Map k`, and `Either a` (where `k` and `a` are arbitrary types). Each of these families may generally be understood as describing some structured collection on their parameterized type. But we can also concoct some type families which do not admit a notion of structure. For instance, `((->) a)` describes the family of functions with domain `a`.

# Functors

Rather than jumping right to monads, let's work our way there incrementally. A monad is an applicative functor is a functor.
We'll start with the prototypical functor, the `[]` type family. There exists a ubiquitous function for lists, called `map`:

{% highlight haskell %}
map :: (a -> b) -> [a] -> [b]
map f (x : xs) = f x :: map f xs
map _ [] = []
{% endhighlight %}

`map` applies a function to each element of a list. The result is a new list with the same structure, but whose elements have been "mapped" through the function.

A functor is a generalization of `map` to other type families. Let's start by generalizing the type signature of `map`. Recall that we may opt out of the list-specific type syntax, writing instead in the regular prefix application style. Written this way, the type is `map :: (a -> b) -> [] a -> [] b`. Now to generalize the type to arbitrary type family `t :: * -> *`, we would write `map :: (a -> b) -> t a -> t b`. This brings us precisely to our definition of a functor:

{% highlight haskell %}
class Functor f where
    fmap :: (a -> b) -> f a -> f b
{% endhighlight %}

The mapping function for arbitrary functors is called `fmap`, for *f*unctor *map*. The only reason that it isn't called `map` is because that is taken by our list-specific function[^map].

[^map]: Since `map` is just the specialization of `fmap` to the `[]` functor, it is not necessary to have a distinct `map` function. The reason we have one is because the early Haskell developers thought the type of `map` would be more beginner-friendly.

Any functor instance is expected to obey certain laws so that it aligns with our intuitive understanding of what a map should do. 

<!-- 1. Identity: forall x, `fmap id x` = `x` [^2]
2. Associativity: forall f g, `fmap (f . g)` = `(fmap f) . (fmap g)` -->
1. `fmap id x` = `x` [^fmap-id]
2. `fmap (f . g)` = `(fmap f) . (fmap g)`

[^fmap-id]: The equivalent statement `fmap id` = `id` is simpler. However, it may be confusing in that the first instance of `id` takes the type `a -> a`, while the second takes the type `f a -> f a`, where `f` is the functor in question.

These formal laws enforce the informal intuition that a functoral map should preserve the underlying "structure".

Before moving on, I'd suggest spending some time with the idea of functors. Make sure that you are comfortable with them. All of the type families I mentioned earlier are functors; try to imagine how their respective `fmap` definitions would behave and why they would be useful.

<!-- Finally some miscellaneous notes. You will often see the synonymous infix operator `<$>` instead of `fmap`. If you see `f <$> x`, this is equivalent to `fmap f x`. I should also note, the definition of functors given here is not the category-theoretic definition. It is the Haskell definition. It isn't necessary to understand the category theory to understand the role of functors in Haskell. Similarly, I will not provide a category-theoretic definition of monads; only a Haskell definition. -->

# Applicative Functors

I won't introduce applicative functors in full, only the part which is directly relevant to our eventual monad definition. An applicative functor is a functor, which adds two additional functions. The one we care about is called `pure`:

{% highlight haskell %}
class Functor f => Applicative f where
    pure :: a -> f a 
    ...
{% endhighlight %}

The idea behind `pure` is that it "lifts" a value into the most minimal structure. Some examples, given `x :: a`:

1. `pure x :: [a]` = `[x]`
2. `pure x :: Maybe a` = `Just x`
3. `pure x :: Tree a` = `Node x []`

<!-- $$
\begin{align}
\text{`pure x :: [a]`} &= `[x]` \\
`pure x :: Maybe a` &= `Just x` \\
`pure x :: Tree a` &= `Node x []`
\end{align}
$$ -->

<!-- The formal laws can't be expressed without the other definition  -->

Formally, we expect the following law to hold:

1. `fmap f . pure` = `pure . f`

# Monads

Finally, we come to the definition of a monad. A Monad is an applicative functor which adds a function called `join`.

<!-- [^3]: I lied. -->

{% highlight haskell %}
class Applicative m => Monad m where
    join :: m (m a) -> m a
{% endhighlight %}

What `join` does is it flattens two layers of "structure" down to one. Let's again consider some examples with respect to concrete type families.

When we specialize `join` to the monad `[]`, we get `join :: [[a]] -> [a]`. The most "obvious" function of this type is the one which concatenates all the lists together, and that is indeed the correct definition of this `join`.

The specialization of `join` to `Maybe` gets the type `join :: Maybe (Maybe a) -> Maybe a`. This behaves such that `join (Just (Just x))` = `x`, but the `join` of anything else results in `Nothing`.

Our expectation is that `join` doesn't do anything silly or throw away values. For instance `join` on lists could instead always return the empty list, and that would have the right type. Similarly, `join` on `Maybe` could always return `Nothing`. But both of these definitions would go against the spirit of what we want `join` to do.

Formally, we expect the following behavior[^so-attrib]:

[^so-attrib]: This version of the monad laws was taken from a [stack overflow post](https://stackoverflow.com/questions/45829110/monad-laws-expressed-in-terms-of-join-instead-of-bind).

<!-- 1. `join . pure` = `join . fmap pure` = `id :: m a -> m a`
3. `join . join` = `join . fmap join x :: m (m (m a)) -> m a`
4. `join . fmap (fmap f)` = `fmap f . join` -->

1. `join . pure` = `join . fmap pure` = `id`
3. `join . join` = `join . fmap join`
4. `join . fmap (fmap f)` = `fmap f . join`

That's it! We've defined a monad! I bet that wasn't as complicated as you were expecting.
<!-- Although, there is certainly still more to be said. -->

# Bind

Given our definition of a monad, we may define an important infix operator, `>>=`, pronounced "bind":

{% highlight haskell %}
(>>=) :: Monad m => m a -> (a -> m b) -> m b
m >>= f = join (fmap f m)
{% endhighlight %}

We can see that `>>=` is like `fmap`, except the codomain of the function we are mapping is also monadic. Rather than accumulating nested monads, we `join` the result to return to original level of structure.

<!-- You can see that `>>=` is sort of like `fmap`, but the codomain of the function we are mapping is also monadic. Rather than  -->

You may wonder why this function is useful. Let's consider an example. Say we have a partial division function `(/) :: Int -> Int -> Maybe Int` which will return `Nothing` when the divisor is zero. Let `a, b, c, d :: Int`. What if we want to divide `a` by `b`, then the result of that by `c`, and finally divide by `d`? Representing this as a series of maps and joins is going to be quite tedious, but it is quite simple to write it in terms of binds: `a/b >>= (/c) >>= (/d)`.

We often wish to chain together multiple monadic operations, such as in the division example above. `>>=` is incredibly useful in its ability to perform such chaining without accumulating nested monad layers.

<!-- Let's say we have an expression `a/b :: Maybe Int`. Now we want to further subdivide it by `c`. We could use `fmap`, i.e. `fmap (/c) (a/b) :: Maybe (Maybe Int)`, but now we have nested `Maybe`s. We could add a `join` at the end, but far easier is to use a bind: `a/b >>= /c :: Maybe Int`. -->
<!-- And we can keep going to: `a/b >>= /c >>= /d >> /e` represents the division of `a` by `b`, then `c`, `d`, and `e`. -->

<!-- {% highlight haskell %}
x/2
{% endhighlight %} -->



<!--
{% highlight haskell %}
{% endhighlight %}
-->



<!-- Chaining monadic terms together. -->

<!-- You may have seen the `>>=` function before (pronounced "bind").  -->

# Monads (Again)

<!-- The monad definition given in the earlier section is valid and direct, however it is not the definition we'll find in Haskell. -->
The monad definition given in the earlier section is valid and straightforward.
However it is not the definition we'll find in Haskell.
Rather than defining `join` and then deriving `>>=`, Haskell has you define `>>=` and derives `join`[^join_better].

[^join_better]: Presumably, Haskell's monads are defined in terms of `>>=` because this function is much more widely used than `join`. I retain that the definition in terms of `join` is still superior, because it is less of an obligation. `join` is weaker than `>>=`, and the definition of `>>=` will necessarily have overlap with that of the previously defined `fmap`.
<!-- The reason I provided an initial definition in terms of `join` is because I think this definition is better. The reason I think it is better is  -->
<!-- The definition of `>>=` is "bigger" than `join` (as witnessed by `join` being a special case of `>>=`), and `>>=` necessarily overlaps with `fmap`. -->

We've already seen how to derive `>>=` from `join` and `fmap`. If we instead consider `>>=` as primitive, how do we derive
`join`?

{% highlight haskell %}
join = (>>= id)
{% endhighlight %}

When stated in terms of `>>=`, a monad is expected to obey the following laws:

1. `pure a >>= f` = `f a`
2. `m >>= pure` = `m`
3. `m >>= (\x -> n x >>= o)` = `(m >>= n) >>= o`

<!-- Clearly then `join` is a special case of `>>=`. 

It may be evident from this definition why I find it preferable to derive monads in terms of `join`. 
The meaning of `join` is "smaller" than the meaning of `>>=`, in that `join` is a specialization of 

It may be evident from this definition why I find it preferable to derive monads in terms of `join`. `join` is a special case of `>>=` -->

Finally, out of convenience, we introduce the degenerative bind:

{% highlight haskell %}
(>>) :: Monad m => m a -> m b -> m b
m >> n = m >> const n
{% endhighlight %}

It might seem that `>>` throws away the left value, but this is not so. The structure will inform the overall result. For instance, `[1..4] >> [3]` evaluates to `[3, 3, 3, 3]` (each element of the left list is replaced with `[3]`, and then the sublists are concatenated).

# Notation

Many of the functions I've discussed in this post have optional alternative names, notations, and syntaxes.

`fmap` has an infix alias, `<$>`. So `fmap f x` = `f <$> x`. This infix operator is more common in practice.

Monads define their own function called `return` which is often used instead of `pure`.
<!-- Instead of using `pure`, monads actually use a function called `return`. -->
This is purely[^pun] a historical artifact, and it is expected that `return` = `pure`.

[^pun]: No pun intended.

Finally, the (in?)famous `do` notation is used to greatly ease the strain of using `>>=`. The notation `do {a <- b ; ...}` is [syntactic sugar](https://en.wikipedia.org/wiki/Syntactic_sugar) which corresponds to the expression `b >>= \a -> ...`. Similarly, `do {b ; ...}` desugars to `b >> ...`.


# Conclusion

We have seen that a monad is just a special kind of functor, and that `>>=` allows us to chain together monadic actions without accumulating multiple layers of nested monadic structure.
The last piece of the puzzle is an appreciation of monads as a consistently useful abstraction. I think this is where many struggle. The definitions themselves are not terribly complex. But why are monadic interfaces so convenient for dealing with a variety of issues, from IO to error handling? 
There is not a simple answer to this, and I think one may only come to appreciate their usefulness after significant real experience using them.

# Footnotes

