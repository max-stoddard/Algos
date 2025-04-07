This lecture is about divide-and-conquer algorithms and dynamic programming

> module DivideAndConquer where

> import Prelude hiding (partition, splitAt)

Regrettably, reading these notes does not have the same narrative
oomph factor as watching the lecture, curse you imports at top of file!
Spoilers: Haskell has arrays.

> import Data.Array

A divide-and-conquer algorithm is one which:

1. split the problem into sub-problems
2. solve the sub-problems and turn them into sub-solutions
3. we combine the sub-solutions to form a solution

Let's take a look at merge sort, which is divide-and-conquer.
The first step will be how to do our divisions. We'll start
by revising a built-in function in Haskell:

> splitAt :: [a] -> Int -> ([a], [a]) -- O(n)
> splitAt xs n = (take n xs, drop n xs)

This function can be used to make a list small:

> splitHalf :: [a] -> ([a], [a]) -- O(n)
> splitHalf xs = splitAt xs (length xs `div` 2)

This is how we can divide our problem (namely, sorting
a list) into smaller subproblems. We'll just split the
list in half, and solve those smaller ones instead.

We now need to think about step (3), how do we combine
the sub-solutions. The sub-problem is a smaller unsorted
list, the sub-solution is a smaller sorted list.
Let's write a function, `merge`:

> -- pre: both lists are sorted
> merge :: Ord a => [a] -> [a] -> [a] -- O(m + n)
> merge [] ys = ys
> merge xs [] = xs
> merge xxs@(x:xs) yys@(y:ys)
>   | x <= y    = x : merge xs yys
>   | otherwise = y : merge xxs ys

This function is taking two lists and puts all their elements back
together in the right order. The pre-condition here is important:
while we don't know that the lists are sorted with respect to
each other (indeed, they don't have to be), we do know their results
are monotonically increasing. As such, we don't have to worry about
later elements in the list needing to be "bubbled" forward.

Now we have step (1) and (3), we can make a divide-and-conquer algorithm.
To do this we need to solve trivial sub-problems. In this case, the
smallest trivially sortable lists we can thing of would be the empty
list and single list:

> msort :: Ord a => [a] -> [a]
> msort [] = []
> msort [x] = [x]

Now we have a stopping point for our divide-and-conquer,
we can focus on performing the division and reconstitution
itself:

> msort xs =
>    -- step (1) divide into sub-problems
>    let (us, vs) = splitHalf xs
>    -- step (2) solve sub-problems
>        us' = msort us
>        vs' = msort vs
>    -- step (3) recombine sub-solutions
>    in merge us' vs'

What is the complexity of `msort` in n, the length of `xs`?

< T_msort(0) = 1
< T_msort(1) = 1
< T_msort(n) = T_splitHalf(n) + 2 * T_msort(n/2) + T_merge(n/2, n/2)
<            = O(n) + 2 * T_msort(n/2) + O(n)
<            = O(n) + 2 * T_msort(n/2)

So far so good, but now we have a recurrence that needs solving.
Let's try and break it down a bit more than we did in the lecture.
We are starting with:

< T_msort(n) = O(n) + T_msort(n/2) + T_msort(n/2)

Let's unroll this once and see what comes out:

< T_msort(n) = O(n) + (O(n/2) + T_msort(n/4) + T_msort(n/4)) + (O(n/2) + T_msort(n/4) + T_msort(n/4))
<            = O(n) + O(n/2) + O(n/2) + 4*T_msort(n/4)
<            = O(n) + O(n) + 4*T_msort(n/4)

Ok, so after one unrolling, we've got ourselves a second linear pass over
the data. The recurrence is now halved again. We can reason that next time
we will add `4 * O(n/4) = O(n)` steps. So every unroll adds a pass over
the data. But how many times can we divide `n` until we reach either 0 or
1? Well, this would be `log n` times. So, by the time we reach the trivial
cases, we will have `log n` many passes over the whole list... this gives
us:

<            = O(n log n)

In fact, we can do slightly tighter than this. We know in the worst
case we will divide up the list log n times, but we also know that
in the best case we will *also* divide up the list log n times. In
other words, the internal structure of the list makes no difference,
and we can refine this to

<            = Theta(n log n)

Let's take another example. A very famous sorting algorithm is "quicksort".
This is also a divide-and-conquer algorithm.
The sub-problem splitting involves partitioning:

> partition :: (a -> Bool) -> [a] -> ([a], [a]) -- O(n)
> partition p xs = (filter p xs, filter (not . p) xs)

The idea will be to take everything less than an element
and everything greater than it to form two smaller lists:

> allLess :: Ord a => a -> [a] -> ([a], [a]) -- O(n)
> allLess x xs = partition (< x) xs

As before, we can then sort these two unsorted lists,
and it then remains to work out how to reconstitute them.
We can combine the sub-problems by just putting them in the
right order, since we know that the lists are *also*
ordered with respect to each other this time.

> qsort :: Ord a => [a] -> [a]
> qsort [] = []
> qsort (x:xs) =
>   let (us, vs) = allLess x xs
>       us' = qsort us
>       vs' = qsort vs
>   in us' ++ [x] ++ vs'

What is the complexity? Quicksort doesn't always behave the same
way on every list. The best case is where the list input is
optimally unsorted, creating an even n/2 split between the two
lists every time:

< T_qsort(0) = 1
< T_qsort(n) = T_allLess(n-1) + 2 * T_qsort((n-1)/2) + T_++((n-1)/2) + T_++(1)
<            = O(n-1) + 2 * T_qsort((n-1)/2) + O((n-1)/2) + O(1)
<            = O(n) + 2 * T_qsort(n/2) + O(n) + O(1)
<            = O(n) + 2 * T_qsort(n/2)

This is the same recurrence shape as before with msort, so we can jump ahead:

<            = Omega(n log n)

Some of you will wonder if using a `DList` would change anything here.
Indeed, it will reduce the complexity of `T_++((n-1)/2)` to O(1), which
is somewhat of an improvement. However, the cost of the function is still
dominated by the O(n) cost of `allLess`, so there is no *asymptotic*
improvement in the algorithms performance.

However, in the worst case, the list is sorted. When we partition
the list now, the vast vast majority of remaining elements in the
list are going to be in one list or the other. This creates a deep
imbalance. Let's assume the list is sorted in ascending order. This
way, `length us = 0` and `length vs = n - 1`. This will make `++`
cheap, as it happens:

< T_qsort(0) = 1
< T_qsort(n) = T_allLess(n-1) + T_qsort(0) + T_qsort(n-1) + T_++(0) + T_++(1)
<            = O(n) + O(1) + T_qsort(n-1) + O(1) + O(1)
<            = O(n) + T_qsort(n-1)

Unlike with the previous case, we know this pattern as being n^2:

<            = O(n^2)

This quicksort isn't very good :(, so much for "quick".

However, the eagle-eyed among you will note I made a "mistake".
Instead of the head, I should take a random element of the list;
it is expected that this will split the list more evenly.
When we reach the end of the course, we can revisit this idea.

Dynamic Programming
-------------------

Dynamic programming is neither dynamic, nor was it originally
about programming. In the 1950's there was a mathematician
who wanted to do research on these problems. He needed funding
from the military. He made the name exciting, in order to get it.

What *actually* is it? It is divide-and-conquer with a twist:

1. Write a bad solution recursively.
2. We cache the sub-solutions
3. profit?

A classic example of a dynamic programming problem is:

> fib :: Int -> Integer -- O(2^n)
> fib 0 = 1
> fib 1 = 1
> fib n = fib (n - 1) + fib (n - 2)

If we take `fib n`, let's unroll it twice:

< fib n = (fib (n-2) + fib (n-3)) + fib (n - 2)

Notice that we see two lots of `fib(n-2)` here after
unrolling. Every time we do this, we are going to keep
doubling it. This ends up becoming an O(2^n) function!

Dynamic programming helps with this, but retains the
nice formulation. We need an efficient table, we don't know
that, and we feel like we need mutation, we don't have that.
I guess the course is over, and we go home :(.

Or, as the spoilers at the top of the file suggest,
we could use arrays!

< (!!) :: [a] -> Int -> a            -- O(n)
< (!) :: Ix i => Array i a -> i -> a -- O(1)

This might look at bit funny. Why doesn't `(!)` use `Int`s?
Haskell arrays are very general, and can be indexed by a variety
of different types. The class `Ix` describes indexable things:

< index :: Ix i => (i, i) -> i -> Int

However, for simplicity, let's assume we have a special case index
that starts at zero, instead:

For single dimension arrays, the size `n` does not matter, `i` is `i`:
< index0 n i = i

For two dimensional arrays we can flatten it by writing out all of one
dimension before the next. To do this, scale `i` by the size of the
dimension below it:
< index0 (_, n) (i, j) = i * n + j

For three dimensional arrays we do the same, but scale the first coordinate
by the size of *both* dimensions below, and so on:
< index0 (_, n, m) (i, j, k) = i * n * m + j * m + k

The point is, that Haskell arrays are not limited to indexing
on Int, they can be any amount of dimensions, etc.

We can also construct arrays:

< array :: Ix i => (i, i) -> [(i, a)] -> Array i a

Given the upper and lower bounds of the array indices, and
all the associations from indices to their elements, this
will build an *immutable* array. As a helper function,
we can also get all the indices within these bounds with:

< range :: Ix i => (i, i) -> [i]

We are going to build ourselves a helper function for doing
dynamic programming:

> tabulate :: Ix i => (i, i) -> (i -> a) -> Array i a
> tabulate bounds f = array bounds [(i, f i) | i <- range bounds]

This function will take all the indices within the desired bounds
of the array, construct the association for them with the given
function, then bake the array with those associations.

So, one problem solved, but we don't have mutation!
Thankfully, Haskell is a       language, and as such,
it has laziness.

Let's *just* see the transformation performed, and unpack it
afterwards. First step is to take your original function,
and make it a helper function (here called `memo`). Then,
build a table that is large enough to accommodate the full
range of your sub-problems. In our case, the smallest
sub-problem on `fib` was `fib 0` and the largest is the goal
`fib n`. The bounds of our table is `(0, n)`. We should use
the `memo` function to fill the entries. The result of
our function is now a table lookup. Finally, we need to
get rid of the recursion within `memo` and instead replace them
with their own table lookups:

> fib' :: Int -> Integer -- O(n)
> fib' n = table ! n
>   where table :: Array Int Integer
>         table = tabulate (0, n) memo
>
>         memo :: Int -> Integer
>         memo 0 = 1
>         memo 1 = 1
>         memo n = table ! (n - 1) + table ! (n - 2)

This works! Take a long hard look at this definition and compare with the
original. The key here is to be ok with the *mechanics* of this
transformation, not necessarily how it works at runtime -- this is
not a Haskell course! However, some of you will be curious about how
this could be possible, as `table` seemingly refers to itself via `memo`.

The trick here is that Haskell arrays are lazy. That means while Haskell
is happy to allocate the contiguous block of memory for the array up-front,
it will fill the elements with *thunks*. As we ask for a value from the
array, the corresponding *thunk* is forced, and will call `memo` to find
out what's inside. As a result, `memo` will end up looking up other elements,
and these in turn are forced, and this process continues recursively
until a base case for `memo` is hit. At this point, the thunk can be filled
in with the final answer, and subsequent lookups of this element are resolved
immediately (it has been cached!). The recursion will unwind back, resolving
all the in-flight thunks until the entire array is fully evaluated, and the
final answer can be returned outright.

Showing this process diagramatically in a time-static medium like text or a
drawing is very hard, and I don't want to spend the next 1000 lines of this
file showing each time-slice. Instead, you should go and watch the lecture
if you want to see an example of evaluation of `fib' 4` step-by-step, thunk-by-thunk.
The cool bit, essentially, is that by letting laziness do this for us, we
don't need to figure out what order the table should be filled in with,
which *is* something we need to be careful about in strict languages. In this
example, it is clear the array would be filled from 0 to n in that order,
but there are examples where this would take a while to figure out -- that's
a win for us. Haskell will always fill the table in optimally, with minimum
work required.

To summarise, the recipe is: start bad, figure out the shape and size of the
table, make the table (referring to some memo function), rewrite the function
in terms of the table. Done.

How do we reason about the time complexity of a tabulated function?
Find the complexity of a single `memo` call (remember that a table look-up is O(1)).
Then find the size of the table in terms of the problem size `n`.
We assume the entire table will be needed, so the steps will be
`T_f(n) = size(table, n) * T_memo`. For example:

< T_memo(0) = 1
< T_memo(1) = 1
< T_memo(n) = T_!(n-1) + T_!(n-2)
<           = O(1) + O(1)
<           = O(1)

As such, O(n*1) is O(n). However, the *space* complexity
has gone to O(n). This isn't *always* the case, and some
dynamic programming problems have smaller space solutions.

If the problem in question has a "static" known number of
dependencies, and these dependencies are local to each other,
we could do better. Namely, we can create a "sliding window".

As an example, here is a better fib:

> fib'' :: Int -> Integer
> fib'' n = loop 1 1 n
>   where loop :: Integer -> Integer -> Int -> Integer
>         loop i j 0 = i
>         loop i j 1 = j
>         loop i j n = loop j (i + j) (n-1)

This works because fib has 2 known sub-problems at each step,
and they are next-door neighbours. It doesn't work for every
problem, but it is more effective if you can find it! In this
case, the space complexity of this function is O(2).

Just for fun, you might remember the `fibs` discussion from
last years lectures. Here, `fibs` was defined as an infinite
list of all fibonacci numbers, by providing the base cases
first and then writing a self-referential definition in terms
of zipping itself with its own tail. Quite the mind-bender.
Suppose we wrote a `fib'''` function that uses this and
just asks for the nth element:

> fib''' :: Int -> Integer
> fib''' n = fibs !! n
>   where fibs = 1 : 1 : zipWith (+) fibs (tail fibs)

If you suspend the disbelief that this function even
works (evaulate it slowly by hand if you want, you'll hopefully
see how it unwinds), this is "more obviously" demonstrating the
sliding window: we provide the first 2 things up front, then
the start of the list is garbage collected as we walk down filling
in more elements, so the space complexity is still constant, with
only 3 elements of the list in memory at any one time.

Back on topic, let's see another example of a dynamic programming
problem and apply our recipe to it.

Here are the coin denominations of GBP:

> type Pence = Int
> coins :: [Pence]
> coins = [1, 2, 5, 10, 20, 50, 100, 200]

The problem we'll solve is the "exact change problem",
`change` returns the minimum number of coins needed to
make the exact total. So, for example `change 2 = 1` as
to give a customer 2p in change we can give then 1 2p coin.
`change 4 = 2` as we make 4p with 2 2p coins. Our trivial
case is when we need to return no change. Otherwise, we
can break the problem down into smaller chunks by arbitrarily
taking a coin and as long as its less than our goal, `g`, we
subtract this from the total and solve this smaller problem.
To combine our sub-solutions, we add one to each of them to
represent the coin we took off, then take the minimum sub-solution
as our answer. Encoding this naively as divide-and-conquer, we
get:

> change :: Pence -> Int -- O(8^n)
> change 0 = 0
> change g = minimum [ change (g - coin) + 1 | coin <- coins, coin <= g]

Note that for GBP, a more efficient solution is to greedily take
the largest coin at every step, but this does not work for all other
arbitrary denominations of currency. Now, at every step, we may need
to consider one of 8 coins, and assuming they are all less than `g`,
we will have 8-subproblems to solve. This ends up being the even more
horrifying O(8^n).

Let's apply our dynamic programming recipe to this.
The recipe is find the array, make it in terms of itself, and take the right
element.

* The smallest problem is `memo 0`, the largest is `memo g`, so the
  bounds of the table are `(0, g)`.
* `table ! g` is our desired sub-solution

> change' :: Pence -> Int -- O(n)
> change' g = table ! g
>   where table :: Array Pence Int
>         table = tabulate (0, g) memo
>
>         memo :: Pence -> Int -- O(1)
>         memo 0 = 0
>         memo g = minimum -- this list is at most size 8, so O(8)
>                    [ (table ! (g - coin)) + 1 | coin <- coins, coin <= g]

Again, take the time to compare how similar the before and after is.
Now, let's consider the time complexity. Remember, we need to find
the cost of `memo` itself. Worst case, there are 8-subproblems:

< T_memo(0) = 0
< T_memo(n) = T_minimum(8) + 8 * T_!
<           = O(1) + O(1)
<           = O(1)

As such, with `g` many sub-problems and O(1) for each, we have O(g).