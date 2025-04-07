> module Seq where

> import Prelude hiding ((++), concat, foldr, foldl, Monoid, length, head, tail, init, last, (!!))

> import Data.List qualified as List

This lecture is about different kinds of lists (sequences).
In Haskell, we have access to singly-linked lists. These are
*persistent* data-structures. Let's review their anatomy:

< data [a] where
<   [] :: [a]              -- O(1)
<   (:) :: a -> [a] -> [a] -- O(1)

Every data-constructor can be used in O(1) time, as they just make
data. What this is telling us is that lists are built from the
front -- we can add things and remove things from the front cheaply,
but anything else may require some work.

We also have sugar for lists: `[1, 2, 3]` is represented as:

< 1 : (2 : (3 : []))

Let's take a look at a non-primitive function on list:

> (++) :: [a] -> [a] -> [a] -- pronounce "append"

Append takes two lists and puts them together:
`[1, 2, 3] ++ [4, 5, 6] = [1, 2, 3, 4, 5, 6]`

Let's try and define it. Remember that the vast vast majority
of the time, we need to use pattern matching and recursion.

< [] ++ [] = []
< [] ++ (y:ys) = y : ([] ++ ys)
< (x:xs) ++ ys = x : (xs ++ ys)

This was a bad definition, because it recursively pulled apart
`ys`. This not only does work proportional to both lists, but it
does not share any of the original structure with the result,
which ends up increasing memory usage. Instead we can notice
that `ys` could just be stitched onto the end:

> [] ++ ys = ys
> (x:xs) ++ ys = x : (xs ++ ys)

This definition preserves `ys`, and so it has structural sharing.
We have to tear down `xs`, because we can't see its last cell,
and we can't mutate it. This function is structurally inductive on
`xs`, and does not do more than `O(1)` work on each step outside
of the recursive call, so we can reason this will be linear in the
length `n` of `xs`: O(n).

Let's now use this function to define `concat`, which flattens
nested lists:

> concat :: [[a]] -> [a]
> concat [] = []
> concat (xs : xss) = xs ++ concat xss

Let's assume, all the `xs` in `xss` have average length `n` and
there are `m` of them. The definition is structurally inductive
in `xss`, so takes `m` recursions, and each step will do `n` steps
due to `(++)`. As a result we have O(mn). It'll turn out later that
perhaps we got lucky with this, but this definitely the best we
can do work wise. The length of `concat xss` is N, which is `n*m`,
so it is also O(N) in the length of the output.

Let's see how the order in which we choose to perform (++) can make
a difference. Recall the two prototypical functions for induction
on lists from last year:

> foldr :: (a -> b -> b) -> b -> [a] -> b -- right-associative reduction
> foldl :: (b -> a -> b) -> b -> [a] -> b -- left-associative reduction

`foldr f k` is a "recipe" for right-associative application
of the function `f` to elements of a list and `k`. `foldl f k` is
the "recipe" for left-associative tail-recursion iteration over
the lists.

The effect of `foldr f k` on this list is:

< (:) x ((:) y ((:) z []))
   v      v      v    vv
<  f  x ( f  y ( f  z k ))

Or written infix:

<  x `f` (y `f` (z `f` k))

The effect of `foldl f k` on this same list is:

< f (f (f k x) y) z

Or written infix:

< ((k `f` x) `f` y) `f` z

For completeness, here are their definitions:

> foldr f k [] = k
> foldr f k (x:xs) = f x (foldr f k xs)

> foldl f acc [] = acc
> foldl f acc (x:xs) = foldl f (f acc x) xs

We can use `foldr` to give more concise definitions for
both `(++)` and `concat`. This *in theory* makes it a
bit easier to reason about the complexity, especially
when we assume Haskell is strict.

< xs ++ ys = foldr (:) ys xs
< concat xss = foldr (++) [] xss

For (++), (:) doesn't fit into `foldl` type-wise. But we *could* write `foldl (++) []` for
concat. Does this work? For `foldr` and `foldl` to work the same given the same
`f` and `k` there are two necessary conditions:

* `f` needs to be associative (so it doesn't matter which way we bracket it)
* `k` needs to be a "zero" for `f`, so that `f k x == x` and `f x k == x`.

The mathematical term for an `f` and `k` meeting these properties is a Monoid:

> class Monoid m where
>   mempty :: m           -- which we called `k`
>   (<>)   :: m -> m -> m -- which we called `f`

The above conditions are plainly evident from the Monoid laws:

< mempty <> x = x                -- left-zero
< x <> mempty = x                -- right-zero
< x <> (y <> z) = (x <> y) <> z  -- associativity

As such, we will have the following be true:

    `foldr (<>) mempty` = `foldl (<>) mempty`

Let's see some examples of monoids to just aid our intuition:

> instance Monoid Int where
>   mempty = 0     -- 1
>   (<>)   = (+)   -- (*)

> instance Monoid Bool where
>   mempty = False -- True
>   (<>)   = (||)  -- (&&)

> instance Monoid [a] where
>   mempty = []
>   (<>)   = (++)

As lists are examples of monoids, `foldr (++) []` and `foldl (++) []`
do the same thing. Obviously the way they do it is different, one
works from the left, and the other from the right. So the real question
is: are the complexities of

< concat1 = foldr (++) []

and

< concat2 = foldl (++) []

the same?

I suggest you think about this for a while! The key thing to remember is
that `foldr` builds big expressions on the second argument of `f`, and
`foldl` builds big expressions on the first argument to `f`. With what
you know about `(++)`, hopefully you can see what the difference would be.

Indeed, `foldl (++) []` is O(N^2) and `foldr (++) []` is O(N) (as we
showed earlier). The problem is that the first argument of `++` is
where the work happens, and `foldl` piles up work on that side. As a
result, the first list is traversed `m` times, the second `m-1` and so
on. Oops! Surely this isn't a problem in practice, we know to associate
correctly... right?

Let's take a simple type for defining binary trees, with values in the
leaves and forks that contain two trees:

> data Tree a = Leaf a | Fork (Tree a) (Tree a)

Suppose we wanted to extract all the values in the leaves: we want a
function `values` which will take a tree and return all the values
with left-most leaves at the front of the list and right-most leaves
at the back. This is simply implemented as follows:

> values :: Tree a -> [a]
> values (Leaf x) = [x]
> values (Fork lt rt) = values lt ++ values rt

Let's take an example tree and see what this function will result in:

> t :: Tree Int
> t = Fork (Fork (Leaf 1)
>                (Leaf 2))
>          (Fork (Leaf 3)
>                (Leaf 4))

What `values` does is replace forks with `++`, and leaves with singleton lists:

> vs :: [Int]
> vs = ([1] ++ [2]) ++ ([3] ++ [4])

Examine this closely, and you will notice that there is some leftist
bracketing around `[1] ++ [2]`, which means `[1]` will be traversed
twice. In fact, if a tree is entirely left-biases, `values` will have
O(n^2) complexity. Fundamentally, we have no control over what trees
this function will receive, so we are doomed to accept the O(n^2) complexity
if we use `(++)` as is. If we want to do better (whilst retaining the clean
structure of the function), we will need to switch to a different kind of
list-like structure.

Sequences
---------
Before we can explore different kinds of sequences, we need to forge ourselves
a way of grouping them together under a common unmbrella. In an OOP language,
we would reach for abstract classes or interfaces. In Haskell, we don't have
subtype polymorphism. Ad-hoc polymorphism, in the form of typeclasses, however,
manages to achieve a similar effect (this is not a programming course, so I
won't elaborate on the advantages/disavantages of both, but you can talk to
me about it if you're interested. I'll touch on it a bit when I do my Scala
lectures at the end of this term.)

We will represent all kinds of sequential datastructures by `Seq`, which describes
the operations we'd like them all to have. Some of these can have default implementations.

> class Seq seq where
>   nil    :: seq a
>   cons   :: a -> seq a -> seq a
>   snoc   :: seq a -> a -> seq a
>   snoc xs x = xs `append` (cons x nil)
>   append :: seq a -> seq a -> seq a
>   length :: seq a -> Int
>   -- these weren't in this lecture live, but we'll want them in future
>   head   :: seq a -> a
>   tail   :: seq a -> seq a
>   init   :: seq a -> seq a
>   last   :: seq a -> a
>   (!!)   :: seq a -> Int -> a -- pronounce "bang (gasp)"
>   null   :: seq a -> Bool

We will also add two special ones:

>   toList :: seq a -> [a]    -- [a] is the "canonical sequence"
>   fromList :: [a] -> seq a

We can make a structure adhere to this interface with an instance.

> instance Seq [] where
>   nil = []                                -- O(1)
>   cons = (:)                              -- O(1)
>   --snoc xs x = xs `append` (cons x nil)  -- O(n)
>   append = (++)                           -- O(n)
>   length = List.length                    -- O(n)
>   head = List.head                        -- O(1)
>   tail = List.tail                        -- O(1)
>   init = List.init                        -- O(n)
>   last = List.last                        -- O(n)
>   (!!) = (List.!!)                        -- O(n)

>   toList = id                             -- O(1)
>   fromList = id                           -- O(1)

Unsurprisingly, lists are sequences. What is interesting is
to observe their complexities of operations.
We can make this a bit more insightful by making a new
sequence; let's choose to improve the O(n) complexity of
`len` for `[]`.

> data LenList a = LenList Int [a]

> instance Seq LenList where
>   nil                                  = LenList 0 []                -- O(1)
>   cons x (LenList n xs)                = LenList (n + 1) (x : xs)    -- O(1)
>   --snoc lxs x                         = lxs `append` (cons x nil)   -- O(n)
>   append (LenList m xs) (LenList n ys) = LenList (m + n) (xs ++ ys)  -- O(n)
>   length (LenList n _)                 = n                           -- O(1) yay
>   head (LenList _ xs)                  = head xs                     -- O(1)
>   tail (LenList n xs)                  = LenList (n - 1) (tail xs)   -- O(1)
>   init (LenList n xs)                  = LenList (n - 1) (init xs)   -- O(n)
>   last (LenList _ xs)                  = last xs                     -- O(n)
>   LenList _ xs !! n                    = xs !! n                     -- O(n)
>
>   toList (LenList _ xs) = xs                     -- O(1)
>   fromList xs           = LenList (length xs) xs -- O(n)

As we'll see during this course, there are a few different structures that can
target different aspects of these operations, and their complexities. For instance,
you can imagine a `Seq (Array Int)` instance (we'll meet `Array i a` on Monday),
which would have the following complexities:

nil -> O(1)
cons -> O(n)
snoc -> O(n)
append -> O(n)
length -> O(1)
head -> O(1)
tail -> O(n)
init -> O(n)
last -> O(1)
(!!) -> O(1)

This is better when you don't want the size of the structure to change, but want
good query time. To solve our tree problem, we are interested in a representations
of sequences where at least appending is cheap.

The rationale behind what we are about to do comes from some maths that
isn't really relevant to this course, so we'll focus on pure intiution.
Firstly, let's look at function composition:

(f . g) x = f (g x)

Let's take a look at the effect of different bracketings of function
composition:

((f . g) . h) x = (f . g) (h x)
                = f (g (h x))

(f . (g . h)) x = f ((g . h) x)
                = f (g (h x))

Function composition has a nice property! It doesn't matter
which way round you write it, you get the same thing (and that
thing is bracketed to the RIGHT). If appending had this same property
it sounds as if it would solve our problem! Can we apply this to
lists? Let's start fiddling with an expression and see what we can
uncover

xs ++ (ys ++ zs)                 :: [a]
  = -- let's add an empty list to the end, which according to `xs ++ [] = xs`, does nothing
xs ++ (ys ++ (zs ++ []))
  = -- apply bracketing to the expressions
(xs ++) ((ys ++) ((zs ++) []))
  = -- squint a bit, treating `(xs ++)` as a function, and it looks like function composition!
((xs ++) . (ys ++) . (zs ++)) [] :: [a]

At this point, we've managed to get function composition to appear,
and we know function composition has the right properties we desire.
Can we now intuitively massage this to form the backbone of a possible
representation of a sequential structure?

((xs ++) . (ys ++) . (zs ++)) [] :: [a]
  ~ -- suppose our representation is inside the brackets, then `[]` must be what turns it
    -- back into a list. Could this be `toList`?!
toList ((xs ++) . (ys ++) . (zs ++)) :: [a]
  ~ -- `xs`, `ys`, `zs` are lists, and we need to get them into our representation
    -- before we can work with them. What if, therefore, `(xs ++)` is `fromList`?!
toList (fromList xs . fromList ys . fromList zs) :: [a]

We've spotted *something*, let's unravel: if you look at the type of the expression given
to `toList`, it is apparent that it must be an `[a] -> [a]` function to work with the `(.)`.
This will be our representation:

> data DList a = DList ([a] -> [a])

This is called a "difference list". Let's use the above intuition
to start filling in the instance:

> instance Seq DList where
>   toList (DList dxs) = dxs []        -- O(n)
>   fromList xs        = DList (xs ++) -- O(1)

For the empty list, notice that `id []` is `[]`, this matches up
with `fromList`. Another "correct" definition would be
`DList ([] ++)`, but this does pointless work, and `id` behaves the same,
since `[] ++ xs = xs`.

>   nil                = DList id      -- O(1)

Earlier on, we learnt that lists are monoids:

[] ++ xs = xs
xs ++ [] = xs
xs ++ (ys ++ zs) = (xs ++ ys) ++ zs

id . f = f
f . id = f
f . (g . h) = (f . g) . h

Functions of type (a -> a) are also monoids. This seems
to line up nicely:

>   append (DList dxs) (DList dys) = DList (dxs . dys) -- O(1)

<   cons x (DList dxs) = fromList [x] `append` DList dxs
<                      = DList ([x] ++) `append` DList dxs
<                      = DList (x :) `append` DList dxs
<                      = DList ((x :) . dxs)

>   cons x (DList dxs) = DList ((x :) . dxs)           -- O(1)
>   --snoc dxs x = dxs `append` cons nx nil            -- O(1), by append, cons, nil. (similar simplified definition to above)

So far, *very* promising! Look at all those O(1)s! Surely there must be a
downside to this structure?

>   length = length . toList           -- O(2n) ~ O(n)
>   head   = head . toList             -- O(n)
>   tail   = fromList . tail . toList  -- O(n)
>   init   = fromList . init . toList  -- O(n)
>   last   = last . toList             -- O(n)
>   (!!)   = (!!) . toList             -- O(n)

So, difference lists are *fantastic* for constructing lists.
They are awful at processing them. The good news is, when
we wrote `values` earlier, all we wanted was to build the list.
Let's take our previous definition, generalise the operations
used to the ones from `Seq`, and tell Haskell we want to build
a `DList`:

> values' :: Tree a -> [a]
> values' t = toList (go t)
>   where go :: Tree a -> DList a
>         go (Leaf x) = cons x nil
>         go (Fork lt rt) = go lt `append` go rt

Cool, it compiles :D. The complexity of `go` ends up being O(n) in
the number of nodes in the tree, n. toList is O(m), m <= n, in the number
of leaves in the tree m. `values'` has overall complexity O(n) in the
"size of the tree".

We have seen an asymptotic improvement in the performance of `values`!

Let's see an example, remember `t`:

< t :: Tree Int
< t = Fork (Fork (Leaf 1)
<                (Leaf 2))
<          (Fork (Leaf 3)
<                (Leaf 4))

< vs = values' t
<    = toList (go t)
<    = toList (go (Fork (Fork (Leaf 1)
<                             (Leaf 2))
<                       (Fork (Leaf 3)
<                             (Leaf 4))))
<    = -- lets make a jump, we know that `go` replaces leaves with singletons
<    = -- and forks with appends.
<    = toList (append (append (cons 1 nil)
<                             (cons 2 nil))
<                     (append (cons 3 nil)
<                             (cons 4 nil)))
<    = -- now, let's unwind the DLists
<    = toList (append (append (cons 1 (DList id))
<                             (cons 2 (DList id)))
<                     (append (cons 3 (DList id))
<                             (cons 4 (DList id))))
<    = toList (append (append (DList ((1 :) . id))
<                             (DList ((2 :) . id)))
<                     (append (DList ((3 :) . id))
<                             (DList ((4 :) . id))))
<    = toList (append (append (DList ((1 :)))
<                             (DList ((2 :))))
<                     (append (DList ((3 :)))
<                             (DList ((4 :)))))
<    = toList (append (append (DList ((1 :))) (DList ((2 :))))
<                     (append (DList ((3 :))) (DList ((4 :)))))
<    = toList (append (DList ((1 :) . (2 :)))
<                     (DList ((3 :) . (4 :))))
<    = toList (append (DList ((1 :) . (2 :))) (DList ((3 :) . (4 :))))
<    = toList (DList (((1 :) . (2 :)) . ((3 :) . (4 :))))
<    = (((1 :) . (2 :)) . ((3 :) . (4 :))) []
<    = ((1 :) . (2 :)) (((3 :) . (4 :)) [])
<    = ((1 :) . (2 :)) ((3 :) ((4 :) []))
<    = ((1 :) . (2 :)) (3 : (4 : []))
<    = (1 :) ((2 :) (3 : (4 : [])))
<    =  1 :  ( 2 :  (3 : (4 : [])))
<    = -- or, without simplifying cons
<    =  [1] ++  ( [2] ++  ([3] ++ ([4] ++ [])))

The key thing to note here is that the final `(++)`s will always end up
right-associated, because `(.)` will always ensure they work out that way.

Are difference lists useful?
----------------------------
In a purely functional language, like Haskell, difference lists
are *fantastic* for building lists. Just as long as we don't
look at them along the way.

In an impure language with mutation, like Scala, we can do better.
We can just "add things to the end" of a mutable builder. In fact,
sometimes `toList` is O(1) even for those.

Regardless, the lesson is simple: we like immutable results,
but when constructing, we should favour representations that
have fast building, even with other disadvantages. When we are
ready to return the result of the function, we can "freeze" the
datastructure into the representation we want moving forward.