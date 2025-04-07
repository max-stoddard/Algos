This lecture continues the discussion on dynamic programming.

> module DynamicProgramming where

For this lecture, we are going to dip into the representations
of lists that we encoded within the lecture on difference lists.

> import Seq (LenList, Seq)
> import qualified Seq

We will also need the arrays and tabulation that were introduced in
the previous lecture

> import Data.Array
> import Tabulate

We are also going to use some helpful functions on lists/functions
to describe our problem solutions clearly.

> import Data.Function (on)
> import Data.List (minimumBy, inits, tails)

Last week we looked at dynamic programming. We had a recipe:

* Make a recursive divide-and-conquer algorithm
* Figure out the size of the set of sub-problems
* Tabulate these into an (lazy) array
* compute elements of the array in terms of table look-ups
* profit.

We are going to look at a more complex example, with higher-dimensionality

The first problem we are going to look at is the edit-distance problem.
Given two strings `str1` and `str2`, `dist str1 str2` gives us the number
of single-character -additions, -removals, or -changes required to transform
one into the other.

< dist "hello" "hello" = 0
< dist "hi" "hey" = 2
< dist "cat" "at" = 1

Before we do anything else, we need to decide how to solve this problem.
Let's look at some more examples:

< dist "bat" "cat" = 1
< dist "at" "at"   = 0
< dist "bat" "at"  = 1
< dist "at" "cat"  = 1
< dist "t" "t"     = 0

It seems like there might be some relation between distances of larger strings
and smaller, but similar strings. This suggests we want to divide-and-conquer.
What would be a trivial sub-problem to solve? Well, if one of the strings is
"", then we know immediately that the distance with the other string is just
the length of that string -- the fastest way to transform the empty string into
any other string is to just add all its characters. We can start filling in
a definition and then think a bit more about how to split up into sub-problems.

> dist :: String -> String -> Int
> dist "" str2 = length str2 -- O(n)
> dist str1 "" = length str1 -- O(m)

With the trivial cases out of the way, we now need to think about how to
break down a larger problem. Because the trivial cases handle empty lists,
we can now assume that our problem is non-empty, so let's consider
`dist (c1:cs1) (c2:cs2)`.

If we look at the `cat` vs `bat` examples above,
we can see that we could, by only considering the first character make three
sub-problems: `dist cs1 (c2:cs2)`, `dist (c1:cs1) cs2`, and then also
`dist cs1 cs2`. The first two sub-problems are allowing us to grow or shrink
the strings, which is important if they are non-equal size. What about the
third? It's suggesting that if we could change `c1` into `c2` then they would
be equal, and we can just remove them both together: if `c1 == c2`, this would
"cost" nothing, but otherwise it will incur the cost of changing one character.
Each of these three sub-problems will potentially have a different cost: with
the "cat" "bat" example, removing characters seemed to be more expensive than
just swapping 'c' for 'b'. We will need to consider all three sub-problems,
but the minimum solution is the one we are interested in. Right, let's code it:

> dist (c1:cs1) (c2:cs2) = minimum
>   [ -- remove character from left
>     dist cs1 (c2:cs2) + 1
>     -- remove character from right
>   , dist (c1:cs1) cs2 + 1
>     -- replace character
>   , dist cs1 cs2 + (if c1 == c2 then 0 else 1)
>   ]

Note that each sub-problem adds 1 to the cost, except for the third, where
we add 0 if the characters didn't need changing. Ok, having done this,
what is the complexity of this function? Every time we recurse, we have
three sub-problems to explore; these subproblems are only 1 character
smaller than their parent problem. Worst case then, when the strings have
length m and n, we would need to removal all characters from one string
and all but one of the other string to reduce to a trival problem of `dist "" [c]`.
That means there is a total of `n + m - 1` recursive calls before we reach
the deepest sub-problem. With three choices at each recursive call, we will have
the *horrific* `O(3^(n + m - 1))`. This sucks.

Ok, so, bad naive divide-and-conquer. Is there hope? Well, let's expand out
an example and see what we can see:

< dist "cat" "bat" = minimum [
<   dist "at" "bat" + 1,
<   dist "cat" "at" + 1,
<   dist "at" "at" + 1,
< ]

Let's expand out the inside sub-problems.

< dist "cat" "bat" = minimum [
<   minimum [
<     dist "t" "bat" + 1,
<     dist "at" "at" + 1,
<     dist "t" "at" + 1
<   ] + 1,
<   minimum [
<     dist "at" "at" + 1,
<     dist "cat" "t" + 1,
<     dist "at" "t" + 1
<   ] + 1
<   minimum [
<     dist "t" "at" + 1,
<     dist "at" "t" + 1,
<     dist "t" "t" + 0
<   ] + 1
< ]

Let's work some *magic* and note that we can distribute the `+ 1`s underneath
the `minimum` without changing the result, and then nested minimums just flatten
down to one without changing the result. We're left with:

< dist "cat" "bat" = minimum [
<     dist "t" "bat" + 2,
<     dist "at" "at" + 2,
<     dist "t" "at" + 2,
<     dist "at" "at" + 2,
<     dist "cat" "t" + 2,
<     dist "at" "t" + 2,
<     dist "t" "at" + 2,
<     dist "at" "t" + 2,
<     dist "t" "t" + 1
< ]

Now, looking at this 2-level unrolled problem, we can spot some
repeated sub-problems: `dist "at" "at"`, `dist "t" "at"` and
`dist "at" "t"`. Right then, if part of our branching factor is
considering repeated work, we now know a strategy for improving
the situation: use dynamic programming to store the *repeated*
sub-problems, and reduce the overall complexity!

Problem is, we can't reasonably come up with an `Ix String` instance,
because there are no sensible *generic* bounds on how big and small
the indices get. So we'll need to change representation of the
problem if we care going to make progress. Take a look at the
structure of the recursion in our function and notice that the
strings get decomposed and smaller each time (or stay the same).
Instead, perhaps we can reformulate our problem in terms of how
much string is left to process?

Let's take a first stab at that and see what happens:

> dist' :: String -> String -> Int
> dist' str1 str2 = go m n
>   where go :: Int -> Int -> Int
>         go 0 j = j -- this time, these cases are cheaper!
>         go i 0 = i
>         go i j = minimum [
>             -- i = length c1:cs1, j = length c2:cs2 from the original
>             -- the first sub-problem was cs1 and c2:cs2, so we now have:
>             go (i - 1) j + 1,
>             -- similarly, we have
>             go i (j - 1) + 1,
>             -- and now we hit a problem because we need c1 and c2!
>             go (i - 1) (j - 1) + if c1 == c2 then 0 else 1
>           ]
>           -- we can do that by indexing into the original `str1` and `str2`
>           where c1 = str1 !! (m - i)
>                 c2 = str2 !! (n - j)
>
>         m = length str1
>         n = length str2

Ok, so this works. What's the complexity? Before we had `O(3^(m + n))`. This time,
we have the same worst sub-problem search depth, however at each sub-problem we
are doing an `O(n)` and `O(m)` lookup on the string with `(!!)`. That increases the
complexity of the solution since we keep having to walk down the strings each time.
Before, by deconstructing the strings and making them smaller, we were able to only
ever need to look at the head characters of the string, which was O(1). Ok, so this
is a problem, but we do know about a representation where `(!)` takes constant time...
arrays!

Let's build a helper function to make an array-backed implementation
of a string:

> type Text = Array Int Char
>
> fromString :: String -> Text -- O(n)
> fromString cs = listArray (0, n-1) cs
>   where n = length cs

With this, we can traverse the suffixes, but where we can lookup
characters along the way cheaply. While we could show that step out explicitly,
hopefully you can imagine what changes. Instead, let's now apply `tabulate` and
improve our implementation. Remember, the steps are "figure out bounds of the table"
-- here the smallest problem would be `(0, 0)`, and the largest problem is `(m, n)`;
find the sub-problem with your answer and return that -- `table ! (m, n)`; and feed
the `table` with a non-recursive `memo` function that lookup other table entries:

> dist'' :: String -> String -> Int -- O(m*n)
> dist'' cs1 cs2 = table ! (m, n)
>   where table :: Array (Int, Int) Int
>         table = tabulate ((0, 0), (m, n)) (uncurry memo)
>
>         memo :: Int -> Int -> Int
>         memo 0 j = j
>         memo i 0 = i
>         memo i j = minimum
>           [ table ! (i-1, j) + 1
>           , table ! (i, j-1) + 1
>           , table ! (i-1, j-1) + if c1 == c2 then 0 else 1
>           ]
>           where c1 = str1 ! (m - i)
>                 c2 = str2 ! (n - j)
>
>         m = length cs1
>         n = length cs2
>
>         str1, str2 :: Text
>         str1 = fromString cs1
>         str2 = fromString cs2

This time the work done in each `memo` call is O(1) (as we have now removed the
O(n) `(!!)`). The table size is `n * m`, so in total, the complexity of `dist''`
is now `O(mn)`. This is a great improvement!

Evidence of Work
----------------
For our next step, let's think about the numbers that are coming back from
`dist`. They are work that we've performed, but we have no knowledge of the
"proof" behind the solution. Often, it's nice to have a *constructive* answer,
that doesn't just say how much, but *which*. Let's think about the change
problem again from last week.

< change 456 = 5

So, we are a cashier at the till. Someone needs £4.56 in change, and the till
tells us that we need to give them 5 coins. Not particularly useful for us,
is it. It would be nice instead if we could be told *which* coins to hand back...
Let's modify our existing (tabulated) function for change to provide evidence
of the solution. Before, we would say that `change 0 = 0`; now we will say that
`change 0 = []`, i.e. a list of no coins. Where previously we would compute
a sub-problem by subtracting a coin from the total and adding 1 to the answer
(`change (g - coin) + 1` for some `coin`), now we will record the coin we chose:
`coin : change (g - coin)`. This is a really interesting observation, actually:
there is a natural correspondence between `Int` and `[a]`, where `[] ~ 0` and
`(:) ~ (+1)` -- thinking in this way, relating data to numbers, is a recurring
theme in the course. For further thought, there is a relationship between `Maybe a`
and `Bool` too, where `Nothing ~ False` and `Just ~ True` (except we have a witness
of how we determined `True`). Let's see how the function changes, and think about
the consequences:

> type Pence = Int
> coins :: [Pence]
> coins = [1, 2, 5, 10, 20, 50, 100, 200]
>
>
> change :: Pence -> [Pence]
> change g = table ! g
>   where table :: Array Pence [Pence]
>         table = tabulate (0, g) memo
>
>         memo :: Pence -> [Pence]
>         memo 0 = []
>         memo g = minimumBy (compare `on` length)
>           [coin : (table ! (g - coin)) | coin <- coins, coin <= g]

So one interesting thing that happened here is on line 276. Instead of
taking the `minimum` solution, we have to take the `minimumBy` the lengths
of the solution lists (compare `on` length is a Haskellism for writing this).
Well, `minimum` on a list of size at most 8 is `O(8)`, but `minimumBy` will
be O(8*T_length), which is, of course, `O(n)`. That's not good! This
change function is O(n^2) time instead of O(n). However, in the lecture
on sequences we also met a structure whose job it is to handle O(1)
length...

> change' :: Pence -> [Pence] -- O(n)
> change' g = Seq.toList (table ! g)
>   where table :: Array Pence (LenList Pence)
>         table = tabulate (0, g) memo
>
>         memo :: Pence -> LenList Pence
>         memo 0 = Seq.nil
>         memo g = minimumBy (compare `on` Seq.length)
>           [Seq.cons coin (table ! (g - coin)) | coin <- coins, coin <= g]

With a quick swap out for operations on the `Seq` interface, and a concrete
representation of `LenList`, we have recovered the O(1) complexity for `memo`,
and this function is back to O(n). The lesson here is that we should change
representation when it suits us. Revisiting `change` was motivation for our
final dynamic-programming battle!

The new `change` was good, because we learnt what coins we needed.
It would be nice if knew this for the changes between strings.

< edits "cat" "bat" = ["cat", "bat"]
< edits "frog" "turtle" = ["frog","tfrog","turog","turtog","turtlg","turtle"]

Notice that the number of strings in `edits` is always one more than the `dist`
would return; this is because we keep the original string in the list to show
the full step by step transformation (think about the dist being the number
of commas in the list, if it helps). The `dist` between any two consecutive
elements in this list is always 1. Ok, so, let's try and massage our original
formulation into one that provides the diff-lists.

First, it's again useful to think about the trivial sub-problems. Before, we
knew that when one string is the empty string, the distance is the length of
the other string. This time, we'll need to have a bunch of lists that build up from
(or reduce down to) the empty list. For example:

< edits "" "cat" = ["", "c", "ca", "cat"]
< edits "dog" "" = ["dog", "og", "g", ""]

This can be done with the `inits` and `tails` functions in Haskell, as it happens:

> editsBad :: String -> String -> [String]
> editsBad "" cs2 = inits cs2
> editsBad cs1 "" = tails cs1

So, now we need to consider how to reconstruct our solutions from the sub-problems.
This time, let's try and look at three example sub-problems from a larger one (remember,
we would take the smallest of them):

< edits "d" "cat" -->
<   edits "" "cat" = ["", "c", "ca", "cat"]
<   edits "d" "at" = ["d", "ad", "at"]
<   edits "" "at"  = ["", "a", "at"]

The two possible solutions would be `["d", "c", "ca", "cat"]` or `["d", "cd", "cad", "cat"]`. So, either of the second two
sub-problems could lead to an optimal solution, but what is the link between either of them and these two posisble solutions?

Well, both of the solutions have a `"d"` at the front, missing from the sub-solutions. Let's think in terms of the non-optimal
first sub-solution, which would result in `["d", "", "c", "ca", "cat"]` if we added "d" at the front of it. That looks ok, it's
just not an optimal solution. So, instead of +1, perhaps we add `cs1` onto the front of each of them. But now focus on the rest of the solution
lists without the "d". We need to transform: `["d", "ad", "at"] --> ["cd", "cad", "cat"]` or `["", "a", "at"] --> ["c", "ca", "cat"]`.
The `c2` is a `'c'`, so it looks like we need to add `c2` onto the front of every element of these lists. Ok, let's see how that
works out:

> editsBad (c1:cs1) (c2:cs2) = minimumBy (compare `on` length)
>   [ (c1:cs1) : editsBad cs1 (c2:cs2)
>   , (c1:cs1) : map (c2 :) (editsBad (c1:cs1) cs2)
>   , (if c1 == c2 then id else ((c1:cs1) :)) (map (c2 :) (editsBad cs1 cs2))
>   ]

What's going on in that last case? Well, if `c1 == c2`, then we added 0 in our original
solution, we know that `(:)` only corresponds to `(+1)`. Since the letters didn't actually
change, we wouldn't want to end up with something like `edits "cat" "cat" = ["cat", "cat", "cat", "cat"]`, right?
However, we still need to `map (c2 :)` over them, otherwise we would instead get `[""]` as our result back instead
(see above reasoning!)

Ok, now this is done we already know that using a `LenList` will improve the complexity of the `minimumBy`,
so we should just do that. I took the liberty of implementing a generalisation of `tails` and `inits` that
works for all `Seq` structures, so we will use those too:

> edits :: String -> String -> [String]
> edits str1 str2 = Seq.toList (go str1 str2)
>   where go :: String -> String -> LenList String
>         go "" cs2 = Seq.inits cs2
>         go cs1 "" = Seq.tails cs1
>         go (c1:cs1) (c2:cs2) =
>           minimumBy (compare `on` Seq.length)
>             [ Seq.cons (c1:cs1) (go cs1 (c2:cs2))
>             , Seq.cons (c1:cs1) (Seq.map (c2 :) (go (c1:cs1) cs2))
>             , (if c1 == c2 then id else Seq.cons (c1:cs1))
>                 (Seq.map (c2 :) (go cs1 cs2))
>             ]

Now, let's improve this with out indices trick! The only consideration
we need here is that we can't just `inits` and `tails` cs1 and cs2, since
they are now indices, so we need to take the substring from i and j, respectively.
Similarly, we need to take a substring when adding `cs1` onto the front of our
result list in the recursive case. Other than that, this is a similar final
function to `dist''`, but with the full list of results returned.

> edits' :: String -> String -> [String]
> edits' cs1 cs2 = Seq.toList (table ! (m, n))
>   where table :: Array (Int, Int) (LenList String)
>         table = tabulate ((0, 0), (m, n)) (uncurry memo)
>
>         memo :: Int -> Int -> LenList String
>         memo 0 j = Seq.inits (drop (n - j) cs2)
>         memo i 0 = Seq.tails (drop (m - i) cs1)
>         memo i j =
>           minimumBy (compare `on` Seq.length)
>             [ Seq.cons cs1' (table ! (i-1, j))
>             , Seq.cons cs1' (Seq.map (c2 :) (table ! (i, j - 1)))
>             , (if c1 == c2 then id else Seq.cons cs1')
>                 (Seq.map (c2 :) (table ! (i-1, j-1)))
>             ]
>             where c1 = str1 ! (m - i)
>                   c2 = str2 ! (n - j)
>                   cs1' = drop (m - i) cs1
>
>         m = length cs1
>         n = length cs2
>
>         str1, str2 :: Text
>         str1 = fromString cs1
>         str2 = fromString cs2

Unlike `dist''`, however, the need to use `drop` and `inits`/`tails`
means that the complexity is not as good as `O(mn)`, however, as it
happens Haskell's laziness will actually avoid most of this substringing
work, only doing it for the critical path through the table that yields
the full solution. We of course, don't need to think about that in this
course, it's just fun to know.

As of next week, Haskell will go back to being "just" a strict language.