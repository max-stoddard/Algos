> module Intro where

> import Prelude hiding (minimum)

This lecture will remind us about Haskell, and lazy/strict evaluation


The goals of this course:

* explore different paradigms
* algorithmic thinking
* analyse performance
* mathematical modelling

We'll need to remind ourselves about Haskell! We'll start by defining
an insertion function, which places an element `x` into a list in the
right ordering; we can assume the list `ys` is already sorted.

> -- pre: list is ordered
> insert :: Ord a => a -> [a] -> [a]
> insert x [] = [x]
> insert x (y:ys)
>   | x <= y    = x : y : ys
>   | otherwise = y : insert x ys

The above example reminds us about pattern matching, guards, and
constraints like `Ord a`. A big part of algorithm design, is understanding
how long a function takes to execute. For now, we'll use our intuition.
Later, we'll have a more precise (but longwinded) way of establishing the
cost of a function, and distill some takehomes. The time taken to run
insertion, `T_insert` is in terms of the length of the list:

T_insert(0) = 1
T_insert(n) = 1 + T_insert(n-1)

This is an open-form function, we prefer "closed-form", which computes
non-recursively. One technique to try and figure out the closed form
solution for such a recursively defined function is to unroll the definition
until a pattern emerges:

T_insert(n) = 1 + T_insert(n-1)
            = 1 + (1 + T_insert(n-2))
            = 1 + (1 + .. + 1)
              ^--------------^
                     ^ there will be `n+1` of these ones when fully expanded.
            = n + 1

Using `insert`, we can define the insertion sort algorithm:

> isort :: Ord a => [a] -> [a]
> isort [] = []
> isort (x:xs) = insert x (isort xs)

(some of you may recognise this as `foldr insert []`, however,
we won't worry about that for this course). Again, we can construct
a cost function for `isort`:

T_isort(0) = 1
T_isort(n) = 1 + T_insert(n-1) + T_isort(n-1)

To find the closed-form solution, we can again unroll the definition
and try to identify a pattern:

T_isort(n) = 1 + T_insert(n-1) + T_isort(n-1)
           = 1 + n + T_isort(n-1)
           = 1 + n + (1 + n-1 + ...)
              ^ here there are will be n lots of 1, with the numbers n, n-1, n-2, etc
           = n + (n*(n+1)/2) + 1
              ^ the dominating factor of this expression is the n^2 in (n^2 + n/2), so we can state the complexity class
           ~ O(n^2)

So far, so good. However, Haskell as we know it from COMP40009 is not
actually suitable for doing this kind of analysis on. Let's explore
why...

< head :: [a] -> a
< head (x:_) = x

> minimum :: Ord a => [a] -> a
> minimum xs = head (isort xs)

Here is a `minimum` function, which finds the smallest element in a list.
This implementation first sorts the list, which may take O(n^2) time for
unsorted data, and then returns the first element. Surely then, it takes
O(n^2) time? In fact, this will take O(n) time. To see how this perhaps
surprising result works out, let's carefully evaluate an example. To
help keep things clear, I will use {e} to denote an unevaluated expression,
and e to represent evaluated expressions.

< minimum {[3, 5, 2, 1]}
< = -- desugar list
< minimum {3 : 5 : 2 : 1 : []}
< = -- def minimum
< head {isort (3 : 5 : 2 : 1 : [])}
< = -- head forces argument to expose the top-most constructor
< head (isort {3 : 5 : 2 : 1 : []})
< = -- isort forces argument to expose the top-most constructor
< head (isort (3 : {5 : 2 : 1 : []}))
< = -- argument to isort is a (:), take definition (2)
< head (insert 3 {isort (5 : 2 : 1 : [])})
< = -- insert forces argument to expose the top-most constructor
< head (insert 3 (isort {5 : 2 : 1 : []}))
< = -- continues as from line 96, so let's skip forward
< head (insert 3 (insert 5 (insert 2 (insert 1 {[]}))))
< = -- insert forces argument to expose the top-most constructor
< head (insert 3 (insert 5 (insert 2 (insert 1 []))))
< = -- definition (1) of insert
< head (insert 3 (insert 5 (insert 2 {1 : []})))
< = -- insert forces argument
< head (insert 3 (insert 5 (insert 2 (1 : []))))
< = -- definition (2) of insert, replace guards by if-then-else
< head (insert 3 (insert 5 {if 2 <= 1 then 2 : 1 : [] else 1 : insert 2 []}))
< = -- insert forces its argument to expose top constructor
< head (insert 3 (insert 5 (if {2 <= 1} then {2 : 1 : []} else {1 : insert 2 []})))
< = -- if forces 2 <= 1, evaluates to False
< head (insert 3 (insert 5 (if False then {2 : 1 : []} else {1 : insert 2 []})))
< = -- take second branch, discard first branch
< head (insert 3 (insert 5 {1 : insert 2 []}))
< = -- insert forces argument to expose top constructor
< head (insert 3 (insert 5 (1 : {insert 2 []})))
< = -- definition (2) of insert
< head (insert 3 {if 5 <= 1 then 5 : 1 : insert 2 [] else 1 : insert 5 (insert 2 [])})
< = -- insert forces argument
< head (insert 3 (if {5 <= 1} then {5 : 1 : insert 2 []} else {1 : insert 5 (insert 2 [])}))
< = -- evaluation of 5 <= 1 is False, take second branch
< head (insert 3 {1 : insert 5 (insert 2 [])})
< = -- insert forces argument
< head (insert 3 (1 : {insert 5 (insert 2 [])}))
< = -- definition (2) of insert
< head {if 3 <= 1 then 3 : 1 : insert 5 (insert 2 []) else 1 : insert 3 (insert 5 (insert 2 []))}
< = -- head forces its argument to expose constructor
< head (if {3 <= 1} then {3 : 1 : insert 5 (insert 2 [])} else {1 : insert 3 (insert 5 (insert 2 []))})
< = -- evaluate 3 <= 1 to False, take second branch
< head {1 : insert 3 (insert 5 (insert 2 []))}
< = -- head forces its argument to pattern match
< head (1 : {insert 3 (insert 5 (insert 2 []))})
< = -- definition of head
< 1

Notice that the rest of the list, which involves sorting 3, 5, and 2, was not
evaluated, and was thrown away. The only work actually done here was to
gently bubble the 1 up along the computation enough to return it as the
result. As such, this is O(n). This is because of laziness; let's make
Haskell strict.

    If an algorithm looks at every part of the data inside, and returns fully evaluated
    things, there is no different between lazy and strict.

Let's remind ourselves about the difference between the two:

< repeat :: a -> [a]
< repeat x = x : repeat x

`repeat x` is an infinite list of `x`s.

If Haskell is lazy
< head (repeat 42)
< head (42 : {repeat 42})
< 42

If Haskell is strict
< head (repeat 42)
< head (42 : 42 : 42 : 42 : 42 ...)

Normal Forms
------------
Lazy things are in WHNF (Weak-Head Normal Form), strict things are in NF (Normal Form)

This is usually defined in terms of the lambda calculus

abstraction: \x -> e
application: f x
variables:   x

An expression e is in Normal form when there are no reducible terms.

(\x -> x) x
~>
x

f x

* \x -> e, where e is normal
* x is normal
* f x is normal when f is a variable and both f and x are normal

WHNF is similar but bodies of lambda need not be normal

\x -> (\y -> y) x

`x : (\y ...) 7 xs` is WHNF, `(:) x ()`

NF:
    1
    Just 4
    [1, 2, 3]
    \x -> x + 1
    Just
    \f -> f 7

WHNF (all the above, and):
    1 : repeat 1
    \x -> 3 + 4
    Just (2 + 3)

Expressions (all of the above, and):
    3 + 4
    repeat 1

Instead of just guess-work, we'll try to define a concrete
measure of the cost of evaluating a function (the example above had
was more steps than the cost functions we wrote suggested!). However,
Haskell is too big, so let's limit outsides to a small collection of
constructs:

Expressions are formed as follows:

e, e1, e2 ::= x                    -- variable
            | k                    -- constant (0, [], (:), +, *, null)
            | f e1 .. en           -- application
            | if e then e1 else e2 -- conditional

Functions will always have the form:

f x1 .. xn = e

We can translate our insert function into this language:

< insert x xs =
<   if null xs then x : []
<   else if x <= head xs then x : xs
<   else head xs : insert x (tail xs)

Now we can give a concrete cost-semantics:

`T(f) x1 .. xn` is the number of steps it takes to evaluate `f` with the (fully evaluated)
arguments `x1 .. xn`

when f is primitive (i.e. `null`, `(+)`, `tail` etc):
    `T(f) x1 .. xn = 0`

(in other words, these calls are free)

otherwise (for f x1 .. xn = e):

`T(f) x1 .. xn = 1 + T(e)`

In other words, our own definied functions cost 1 for the call, then the cost of the body

For the expression constructs, we have the following clauses:

```
T(x) = 0  -- in other words, variables are free
T(k) = 0  -- in other words, constants are free
-- evaluating an application is the same as evaluating all the arguments,
-- and then the application of `f` to those arguments (as above)
T(f e1 .. en) = T(f) e1 .. en
              + T(e1) + .. + T(en)
-- evaluating a condition first evaluates the condition, then conditonally
-- evaluates either arm of the conditional.
T(if e then e1 else e2) = T(e) + if e then T(e1) else T(e2)
```

As T(insert) is a rather large example, let's instead create a
cost model for the length function, defined as follows:

< length xs = if null xs then 0 else 1 + length (tail xs)

< T(length xs)
< = -- by T(f e1 .. en) = T(f) e1 .. en + T(e1) + .. + T(en)
< T(length) xs + T(xs)
< = -- by T(x) = 0
< T(length) xs + 0
< = -- by T(f) x1 .. xn = 1 + T(e)
< 1 + T(if null xs then 0 else 1 + length (tail xs))
< = -- by T(if e then e1 else e2) = T(e) + if e then T(e1) else T(e2)
< 1 + T(null xs) + if null xs then T(0) else T(length (tail xs))
< = -- by T(f e1 .. en) = T(f) e1 .. en + T(e1) + .. + T(en)
< 1 + T(null) xs + T(xs) + if null xs then T(0) else T(length (tail xs))
< = -- By T(primitive) = 0, T(x) = 0
< 1 + 0 + 0 + if null xs then T(0) else T(length (tail xs))
< = -- By T(k) = 0
< 1 + if null xs then 0 else T(length (tail xs))
< = -- By T(f e1 .. en) = T(f) e1 .. en + T(e1) + .. + T(en)
< 1 + if null xs then 0 else T(length) (tail xs) + T(tail xs)
< = -- By T(f e1 .. en) = T(f) e1 .. en + T(e1) + .. + T(en)
< 1 + if null xs then 0 else T(length) (tail xs) + T(tail) xs + T(xs)
< = -- By T(primitive) = 0, T(x) = 0
< 1 + if null xs then 0 else T(length) (tail xs) + 0 + 0
< = -- simplify
< 1 + if null xs then 0 else T(length) (tail xs)

At this point, we can stop, as we are back in terms of just
an evaluation of ourselves. This worked out, but was very long-winded
and the language is not particularly fun to work with. As such, the key
take-home from this exercise is to notice that cost is going to
be introduced by a call to our "own" functions. Calls out to primitives
(which here are representing pattern matching too) are considered free.

As one last note, though, we can apply some rules to provide a shortcut
for looking at how to cost-model composition of functions:

T(f(g(x))) = T(f) (g x) + T(g(x))
           = T(f) (g x) + T(g) x + T(x)
           = T(f) (g x) + T(g) x + 0
           = T(f) (g x) + T(g) x

Complexity Classes
------------------

This will follow written up properly ;)