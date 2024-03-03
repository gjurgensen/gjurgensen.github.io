---
title: "Monad is a Monad is a Monad"
date: 2022-02-18 00:00:01
draft: false
tag: Haskell
---

> "... she would carve on the tree Rose is a Rose is a Rose is a Rose is a Rose until it went all the way around." – The World is Round, Gertrude Stein

Many a blog and tutorial alike will tell you that a monad is something other than what it is. Perhaps it is a "box", or a "burrito". Sometimes it is a "computation" (aren't all Haskell terms computations?). Certainly there is some merit to this style of explanation-by-analogy. However, such presentations are necessarily limited to approximations of what a monad really is. Analogies may impart some initial intuition, but sooner or later end up holding our mental model back from reaching the full generality of what a monad really is. And it isn't as complicated as you might expect.

I'd like to explain what a monad really is[^non-categorical], as straightforward as possible, without the analogies. A monad is a monad (is a monad is a monad...).

[^non-categorical]: When I talk about a monad in this post, I mean a monad in the Haskell and functional programming sense, as opposed to the category-theoretic definition. The same applies for our discussion of functors.

## Type Families

<!-- {{<highlight Haskell "hl_inline=true">}}{{</highlight>}} -->
A monad is a special kind of type family, along with a couple of important functions. Let's clarify some terminology.
By a type family, I mean anything with kind {{<highlight Haskell "hl_inline=true">}}* -> *{{</highlight>}}. A simple function to and from types. For example, let {{<highlight Haskell "hl_inline=true">}}t :: * -> *{{</highlight>}} and {{<highlight Haskell "hl_inline=true">}}x :: *{{</highlight>}}. Then {{<highlight Haskell "hl_inline=true">}}t{{</highlight>}} is a type family and {{<highlight Haskell "hl_inline=true">}}x{{</highlight>}} is a type. {{<highlight Haskell "hl_inline=true">}}t x :: *{{</highlight>}} is also a type, and an "instance" of the type family {{<highlight Haskell "hl_inline=true">}}t{{</highlight>}}. We may also say {{<highlight Haskell "hl_inline=true">}}x{{</highlight>}} is the parameterized type in {{<highlight Haskell "hl_inline=true">}}t x{{</highlight>}}.

Some examples of type families include {{<highlight Haskell "hl_inline=true">}}[]{{</highlight>}}, {{<highlight Haskell "hl_inline=true">}}Maybe{{</highlight>}}, {{<highlight Haskell "hl_inline=true">}}Tree{{</highlight>}}, {{<highlight Haskell "hl_inline=true">}}Map k{{</highlight>}}, and {{<highlight Haskell "hl_inline=true">}}Either a{{</highlight>}} (where {{<highlight Haskell "hl_inline=true">}}k{{</highlight>}} and {{<highlight Haskell "hl_inline=true">}}a{{</highlight>}} are arbitrary types). Each of these families may generally be understood as describing some structured collection on their parameterized type. But we can also concoct some type families which do not admit a notion of structure. For instance, {{<highlight Haskell "hl_inline=true">}}((->) a){{</highlight>}} describes the family of functions with domain {{<highlight Haskell "hl_inline=true">}}a{{</highlight>}}.

## Functors

Rather than jumping right to monads, let's work our way there incrementally. A monad is an applicative functor is a functor.
We'll start with the prototypical functor, the {{<highlight Haskell "hl_inline=true">}}[]{{</highlight>}} type family. There exists a ubiquitous function for lists, called {{<highlight Haskell "hl_inline=true">}}map{{</highlight>}}:

```Haskell
map :: (a -> b) -> [a] -> [b]
map f (x : xs) = f x :: map f xs
map _ [] = []
```

{{<highlight Haskell "hl_inline=true">}}map{{</highlight>}} applies a function to each element of a list. The result is a new list with the same structure, but whose elements have been "mapped" through the function.

A functor is a generalization of {{<highlight Haskell "hl_inline=true">}}map{{</highlight>}} to other type families. Let's start by generalizing the type signature of {{<highlight Haskell "hl_inline=true">}}map{{</highlight>}}. Recall that we may opt out of the list-specific type syntax, writing instead in the regular prefix application style. Written this way, the type is {{<highlight Haskell "hl_inline=true">}}map :: (a -> b) -> [] a -> [] b{{</highlight>}}. Now to generalize the type to arbitrary type family {{<highlight Haskell "hl_inline=true">}}t :: * -> *{{</highlight>}}, we would write {{<highlight Haskell "hl_inline=true">}}map :: (a -> b) -> t a -> t b{{</highlight>}}. This brings us precisely to our definition of a functor:

```Haskell
class Functor f where
    fmap :: (a -> b) -> f a -> f b
```

The mapping function for arbitrary functors is called {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}}, for *f*unctor *map*. The only reason that it isn't called {{<highlight Haskell "hl_inline=true">}}map{{</highlight>}} is because that is taken by our list-specific function[^map].

[^map]: Since {{<highlight Haskell "hl_inline=true">}}map{{</highlight>}} is just the specialization of {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}} to the {{<highlight Haskell "hl_inline=true">}}[]{{</highlight>}} functor, it is not necessary to have a distinct {{<highlight Haskell "hl_inline=true">}}map{{</highlight>}} function. The reason we have one is because the early Haskell developers thought the type of {{<highlight Haskell "hl_inline=true">}}map{{</highlight>}} would be more beginner-friendly.

Any functor instance is expected to obey certain laws so that it aligns with our intuitive understanding of what a map should do.

<!-- TODO: Maybe need a separate haskell lexer for inline, which uses the expression language (not the statement language) -->
<!-- 1. Identity: forall x, {{<highlight Haskell "hl_inline=true">}}fmap id x{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}x{{</highlight>}} [^2]
2. Associativity: forall f g, {{<highlight Haskell "hl_inline=true">}}fmap (f . g){{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}(fmap f) . (fmap g){{</highlight>}} -->
1. {{<highlight Haskell "hl_inline=true">}}fmap id x{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}x{{</highlight>}} [^fmap-id]
2. {{<highlight Haskell "hl_inline=true">}}fmap (f . g){{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}(fmap f) . (fmap g){{</highlight>}}

[^fmap-id]: The equivalent statement {{<highlight Haskell "hl_inline=true">}}fmap id{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}id{{</highlight>}} is simpler. However, it may be confusing in that the first instance of {{<highlight Haskell "hl_inline=true">}}id{{</highlight>}} takes the type {{<highlight Haskell "hl_inline=true">}}a -> a{{</highlight>}}, while the second takes the type {{<highlight Haskell "hl_inline=true">}}f a -> f a{{</highlight>}}, where {{<highlight Haskell "hl_inline=true">}}f{{</highlight>}} is the functor in question.

In English, the first law says that mapping the identity function over an object should leave it unchanged. The second law says that sequential map operation may be combined in to a single map.

If these laws seem confusing, try to consider concrete examples. Let's say we are mapping {{<highlight Haskell "hl_inline=true">}}(+ 1){{</highlight>}} over a list, and then we map {{<highlight Haskell "hl_inline=true">}}(* 2){{</highlight>}} over that. Intuitively, wouldn't this be equivalent to a single mapping of {{<highlight Haskell "hl_inline=true">}}\x -> (x + 1) * 2{{</highlight>}}, as enforced by the second law?

Together, these formal laws enforce the informal intuition that a functoral map should preserve the underlying "structure" of the functoral object.

Before moving on, I'd suggest spending some time with the idea of functors. Make sure that you are comfortable with them. All of the type families I mentioned earlier are functors; try to imagine how their respective {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}} definitions would behave and why they would be useful.

<!-- Finally some miscellaneous notes. You will often see the synonymous infix operator {{<highlight Haskell "hl_inline=true">}}<$>{{</highlight>}} instead of {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}}. If you see {{<highlight Haskell "hl_inline=true">}}f <$> x{{</highlight>}}, this is equivalent to {{<highlight Haskell "hl_inline=true">}}fmap f x{{</highlight>}}. I should also note, the definition of functors given here is not the category-theoretic definition. It is the Haskell definition. It isn't necessary to understand the category theory to understand the role of functors in Haskell. Similarly, I will not provide a category-theoretic definition of monads; only a Haskell definition. -->

## Applicative Functors

I won't introduce applicative functors in full, only the part which is directly relevant to our eventual monad definition. An applicative functor is a functor, which adds two additional functions. The one we care about is called {{<highlight Haskell "hl_inline=true">}}pure{{</highlight>}}:

```Haskell
class Functor f => Applicative f where
    pure :: a -> f a
    ...
```

The idea behind {{<highlight Haskell "hl_inline=true">}}pure{{</highlight>}} is that it "lifts" a value into the most minimal structure. Some examples, given {{<highlight Haskell "hl_inline=true">}}x :: a{{</highlight>}}:

1. {{<highlight Haskell "hl_inline=true">}}pure x :: [a]{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}[x]{{</highlight>}}
2. {{<highlight Haskell "hl_inline=true">}}pure x :: Maybe a{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}Just x{{</highlight>}}
3. {{<highlight Haskell "hl_inline=true">}}pure x :: Tree a{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}Node x []{{</highlight>}}

Formally, we expect the following law to hold:

1. {{<highlight Haskell "hl_inline=true">}}fmap f . pure{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}pure . f{{</highlight>}}

Again, when such laws are unclear, I encourage you to consider concrete examples. What does this mean for {{<highlight Haskell "hl_inline=true">}}[]{{</highlight>}}? How about for {{<highlight Haskell "hl_inline=true">}}Maybe{{</highlight>}}?

## Monads

Finally, we come to the definition of a monad. A Monad is an applicative functor which adds a function called {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}}.

```Haskell
class Applicative m => Monad m where
    join :: m (m a) -> m a
```

What {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} does is it flattens two layers of "structure" down to one. Let's again consider some examples with respect to concrete type families.

When we specialize {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} to the monad {{<highlight Haskell "hl_inline=true">}}[]{{</highlight>}}, we get {{<highlight Haskell "hl_inline=true">}}join :: [[a]] -> [a]{{</highlight>}}. The most "obvious" function of this type is the one which concatenates all the lists together, and that is indeed the correct definition of this {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}}.

The specialization of {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} to {{<highlight Haskell "hl_inline=true">}}Maybe{{</highlight>}} gets the type {{<highlight Haskell "hl_inline=true">}}join :: Maybe (Maybe a) -> Maybe a{{</highlight>}}. This behaves such that {{<highlight Haskell "hl_inline=true">}}join (Just (Just x)){{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}x{{</highlight>}}, but the {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} of anything else results in {{<highlight Haskell "hl_inline=true">}}Nothing{{</highlight>}}.

Our expectation is that {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} doesn't do anything silly or throw away values. For instance {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} on lists could instead always return the empty list, and that would have the right type. Similarly, {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} on {{<highlight Haskell "hl_inline=true">}}Maybe{{</highlight>}} could always return {{<highlight Haskell "hl_inline=true">}}Nothing{{</highlight>}}. But both of these definitions would go against the spirit of what we want {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} to do.

Formally, we expect the following behavior[^so-attrib]:

[^so-attrib]: This version of the monad laws was taken from a [stack overflow post](https://stackoverflow.com/questions/45829110/monad-laws-expressed-in-terms-of-join-instead-of-bind).

<!-- 1. {{<highlight Haskell "hl_inline=true">}}join . pure{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}join . fmap pure{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}id :: m a -> m a{{</highlight>}}
3. {{<highlight Haskell "hl_inline=true">}}join . join{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}join . fmap join x :: m (m (m a)) -> m a{{</highlight>}}
4. {{<highlight Haskell "hl_inline=true">}}join . fmap (fmap f){{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}fmap f . join{{</highlight>}} -->

1. {{<highlight Haskell "hl_inline=true">}}join . pure{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}join . fmap pure{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}id{{</highlight>}}
3. {{<highlight Haskell "hl_inline=true">}}join . join{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}join . fmap join{{</highlight>}}
4. {{<highlight Haskell "hl_inline=true">}}join . fmap (fmap f){{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}fmap f . join{{</highlight>}}

That's it! We've defined a monad! I bet that wasn't as complicated as you were expecting.

## Bind

We've defined a monad, but we aren't done yet. Given our definition of a monad, we may define an important infix operator, {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}}, pronounced "bind":

```Haskell
(>>=) :: Monad m => m a -> (a -> m b) -> m b
m >>= f = join (fmap f m)
```

We can see that {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} is like {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}}, except the codomain of the function we are mapping is also monadic. Rather than accumulating nested monads, we {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} the result to return to our original level of structure.

<!-- You can see that {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} is sort of like {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}}, but the codomain of the function we are mapping is also monadic. Rather than  -->

You may wonder why this function is useful. Let's consider an example. Say we have a partial division function {{<highlight Haskell "hl_inline=true">}}(/) :: Int -> Int -> Maybe Int{{</highlight>}} which will return {{<highlight Haskell "hl_inline=true">}}Nothing{{</highlight>}} when the divisor is zero. Let {{<highlight Haskell "hl_inline=true">}}a, b, c, d :: Int{{</highlight>}}. What if we want to divide {{<highlight Haskell "hl_inline=true">}}a{{</highlight>}} by {{<highlight Haskell "hl_inline=true">}}b{{</highlight>}}, then the result of that by {{<highlight Haskell "hl_inline=true">}}c{{</highlight>}}, and finally divide by {{<highlight Haskell "hl_inline=true">}}d{{</highlight>}}? Representing this as a series of maps and joins is going to be quite tedious, but it is quite simple to write it in terms of binds: {{<highlight Haskell "hl_inline=true">}}a/b >>= (/c) >>= (/d){{</highlight>}}.

We often wish to chain together multiple monadic operations, such as in the division example above. {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} is incredibly useful in its ability to perform such chaining without accumulating nested monad layers.

<!-- Let's say we have an expression {{<highlight Haskell "hl_inline=true">}}a/b :: Maybe Int{{</highlight>}}. Now we want to further subdivide it by {{<highlight Haskell "hl_inline=true">}}c{{</highlight>}}. We could use {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}}, i.e. {{<highlight Haskell "hl_inline=true">}}fmap (/c) (a/b) :: Maybe (Maybe Int){{</highlight>}}, but now we have nested {{<highlight Haskell "hl_inline=true">}}Maybe{{</highlight>}}s. We could add a {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} at the end, but far easier is to use a bind: {{<highlight Haskell "hl_inline=true">}}a/b >>= /c :: Maybe Int{{</highlight>}}. -->
<!-- And we can keep going to: {{<highlight Haskell "hl_inline=true">}}a/b >>= /c >>= /d >> /e{{</highlight>}} represents the division of {{<highlight Haskell "hl_inline=true">}}a{{</highlight>}} by {{<highlight Haskell "hl_inline=true">}}b{{</highlight>}}, then {{<highlight Haskell "hl_inline=true">}}c{{</highlight>}}, {{<highlight Haskell "hl_inline=true">}}d{{</highlight>}}, and {{<highlight Haskell "hl_inline=true">}}e{{</highlight>}}. -->

<!-- ```Haskell
x/2
``` -->



<!--
```Haskell
```
-->

## Monads (Again)

<!-- The monad definition given in the earlier section is valid and direct, however it is not the definition we'll find in Haskell. -->
The monad definition given in the earlier section is valid and straightforward.
However it is not the definition we'll find in Haskell.
Rather than defining {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} and then deriving {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}}, Haskell has you define {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} and derives {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}}[^join_better].

[^join_better]: Presumably, Haskell's monads are defined in terms of {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} because this function is much more widely used than {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}}. I maintain that the definition in terms of {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} is still superior, because it is less of an obligation. {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} is weaker than {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}}, and the definition of {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} will necessarily have overlap with that of the previously defined {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}}.
<!-- The reason I provided an initial definition in terms of {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} is because I think this definition is better. The reason I think it is better is  -->
<!-- The definition of {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} is "bigger" than {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} (as witnessed by {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} being a special case of {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}}), and {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} necessarily overlaps with {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}}. -->

We've already seen how to derive {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} from {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} and {{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}}. If we instead consider {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} as primitive, how do we derive
{{<highlight Haskell "hl_inline=true">}}join{{</highlight>}}?

```Haskell
join = (>>= id)
```

When stated in terms of {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}}, a monad is expected to obey the following laws:

1. {{<highlight Haskell "hl_inline=true">}}pure a >>= f{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}f a{{</highlight>}}
2. {{<highlight Haskell "hl_inline=true">}}m >>= pure{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}m{{</highlight>}}
3. {{<highlight Haskell "hl_inline=true">}}m >>= (\x -> n x >>= o){{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}(m >>= n) >>= o{{</highlight>}}

<!-- Clearly then {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} is a special case of {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}}.

It may be evident from this definition why I find it preferable to derive monads in terms of {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}}.
The meaning of {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} is "smaller" than the meaning of {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}}, in that {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} is a specialization of

It may be evident from this definition why I find it preferable to derive monads in terms of {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}}. {{<highlight Haskell "hl_inline=true">}}join{{</highlight>}} is a special case of {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} -->

Finally, out of convenience, we introduce the degenerative bind:

```Haskell
(>>) :: Monad m => m a -> m b -> m b
m >> n = m >> const n
```

Looking at the type, it might seem that {{<highlight Haskell "hl_inline=true">}}>>{{</highlight>}} ignores the left value, but this is not so. The structure will inform the overall result. For instance, {{<highlight Haskell "hl_inline=true">}}[1..4] >> [3]{{</highlight>}} evaluates to {{<highlight Haskell "hl_inline=true">}}[3, 3, 3, 3]{{</highlight>}} (each element of the left list is replaced with {{<highlight Haskell "hl_inline=true">}}[3]{{</highlight>}}, and then the sublists are concatenated).

## Notation

Many of the functions I've discussed in this post have optional alternative names, notations, and syntaxes.

{{<highlight Haskell "hl_inline=true">}}fmap{{</highlight>}} has an infix alias, {{<highlight Haskell "hl_inline=true">}}<$>{{</highlight>}}. So {{<highlight Haskell "hl_inline=true">}}fmap f x{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}f <$> x{{</highlight>}}. This infix operator is more common in practice.

Monads define their own function called {{<highlight Haskell "hl_inline=true">}}return{{</highlight>}} which is often used instead of {{<highlight Haskell "hl_inline=true">}}pure{{</highlight>}}.
<!-- Instead of using {{<highlight Haskell "hl_inline=true">}}pure{{</highlight>}}, monads actually use a function called {{<highlight Haskell "hl_inline=true">}}return{{</highlight>}}. -->
This is purely[^pun] a historical artifact, and it is expected that {{<highlight Haskell "hl_inline=true">}}return{{</highlight>}} = {{<highlight Haskell "hl_inline=true">}}pure{{</highlight>}}.

[^pun]: No pun intended.

Finally, the (in?)famous {{<highlight Haskell "hl_inline=true">}}do{{</highlight>}} notation is used to greatly ease the strain of using {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}}. The notation {{<highlight Haskell "hl_inline=true">}}do {a <- b ; ...}{{</highlight>}} is [syntactic sugar](https://en.wikipedia.org/wiki/Syntactic_sugar) which corresponds to the expression {{<highlight Haskell "hl_inline=true">}}b >>= \a -> ...{{</highlight>}}. Similarly, {{<highlight Haskell "hl_inline=true">}}do {b ; ...}{{</highlight>}} desugars to {{<highlight Haskell "hl_inline=true">}}b >> ...{{</highlight>}}.


## Conclusion

We have seen that a monad is just a special kind of functor, and that {{<highlight Haskell "hl_inline=true">}}>>={{</highlight>}} allows us to chain together monadic actions without accumulating multiple layers of nested monadic structure.
The last piece of the puzzle is an appreciation of monads as a consistently useful abstraction. I think this is where many struggle. The definitions themselves are not terribly complex. But why are monadic interfaces so convenient for dealing with a variety of issues, from IO to error handling?
There is not a simple answer to this, and I think one may only come to appreciate the usefulness of monads through real experience using them.

## Footnotes

