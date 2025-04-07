> module RandomAccessList where

> import Prelude hiding (head, init, last, tail, length, null, (!!))

> import Seq (Seq(..), DList)
> import Data.Maybe (catMaybes)

In this lecture, we will come up with a representation of lists with constant appending
and prepending, but with log(n) indexing.
This is a representation of natural numbers, with `Z` representing 0, and `S` representing (+1):

> data Nat = Z | S Nat

There is a deep correspondance between natural numbers and lists

< inc :: Nat -> Nat
< inc n = S n

< cons :: a -> [a] -> [a]
< cons x xs = x : xs

< dec :: Nat -> Nat
< dec (S n) = n

< tail :: [a] -> [a]
< tail (_ : xs) = xs

< add :: Nat -> Nat -> Nat
< add Z n = n
< add (S m) n = S (add m n)

< (++) :: [a] -> [a] -> [a]
< [] ++ ys = ys
< (x:xs) ++ ys = x : (xs ++ ys)

Addition on peano naturals is quite inefficient, and the
representation can be clumsy to work with at scale. As
computer scientists, we prefer *binary* numbers. Why?

Binary numbers are a much denser representation, which is
easier to read while still being efficient to work with.

> data Bit = O | I deriving (Show, Eq, Enum)
> type Binary = [Bit]

> -- to save myself endless pain
> instance Num Bit where fromInteger = toEnum . fromInteger

We will describe binary numbers as lists of bits, in a
reversed notation from the one we are commonly used to:

> thirteen :: Binary
> thirteen = [1, 0, 1, 1] -- 0b1101

              ^1 ^2 ^4 ^8

In the `Binary` representation, what is `0`?

> zero :: Binary
> zero = [] -- or [0], or [0, 0]..

Let's define how to increment these binary numbers

> inc :: Binary -> Binary -- ~O(1)
> inc [] = [1]
> inc (0 : bs) = 1 : bs
> inc (1 : bs) = 0 : inc bs

What is the complexity of `inc`? We have that a list of
n bits set to 1 will have to walk the entire list in order
to increment. This means `inc` is O(n)... right?

Well, if we increment a number full of ones, it now becomes
full of zeros. Incrementing with a leading zero is constant
time, and we have a while to go before we run into a large
number of leading ones again. Perhaps we can come up with
a better *amortised* complexity. We suspect that this might be
better than linear, which means there are really only a
small handful of complexities available to us: log or constant.

> leadingOnes :: Binary -> Int
> leadingOnes = Seq.length . takeWhile (== 1)
>
> bitCount :: Binary -> Int
> bitCount = Seq.length . filter (== 1)

We have that

< C_inc(n) = leadingOnes n + 1

This works when `n=0`, so this accurately describes the cost in all cases,
which is nice.

So we have an equation to solve:

leadingOnes n + 1 <= A_inc(n) - (Phi(inc(n)) - Phi(n))

A nice strategy for finding a good potential function, Phi, is
to consider how it must behave at the edge of an expensive case.
We want that

Phi(n_ex') = Phi(n_ex) - C_inc(n_ex)

In this case, given that the C_inc will also drop to 0 after the
expensive operation, we might assume that we could just take that
to be our Phi, and everything will work out. Indeed, this will
work in the expensive case:

leadingOnes n + 1 <= A_inc(n) - (Phi(inc n) - Phi(n))
leadingOnes n + 1 <= A_inc(n) - (0 - leadingOnes n)
leadingOnes n + 1 <= A_inc(n) + leadingOnes n
1 <= A_inc(n)

But `leadingOnes` is too volatile! Why?
Consider its value just before we reach an expensive case, which
is always at odd numbers -- it will be 0!

leadingOnes n + 1      <= A_inc(n) - (Phi(inc n) - Phi(n))
leadingOnes n + 1      <= A_inc(n) - (leadingOnes(inc n) - leadingOnes(n))
1                      <= A_inc(n) - (leadingOnes(inc n) - 0)
leadingOnes(inc n) + 1 <= A_inc(n)

Oops! we've just constrained the amortised complexity to be
no better than the cost. This is worst case O(n) in bit-length,
or O(log(n)) in number, depending on how you want to think about it.

So, the problem here is that `leadingOnes` is too chaotic, and
seemingly forgets about expensiveness as it approaches: while it
works for the expensive case, the odd cases will now all be broken.
Instead, we could consider a measure that grows more smoothly as
we get closer to the most expensive case. What `leadingOnes` hasn't
accounted for is the build-up of ones to the *right* of the first
zero, which will eventually all contribute to the most expensive
case when the zero disappears. Instead, let's set `Phi` to be:

< Phi(n) = bitCount n

This has the desired property that the difference between
Phi(2^n-1) and Phi(2^n) is still `leadingOnes (2^n-1)`,
but this time we have that `Phi(2^n-1) - Phi(2^n-2)` will be
1. We can see from the graph that the potential, while it
can decrease after a "small" expense, will still slowly grow
more smoothly. This time:

leadingOnes n + 1 <= A_inc(n) - (Phi(inc(n)) - Phi(n))
leadingOnes n + 1 <= A_inc(n) - (bitCount(inc(n)) - bitCount(n))
leadingOnes n + 1 <= A_inc(n) - (1 - bitCount(n))
leadingOnes n + 1 <= A_inc(n) - 1 + bitCount(n)
leadingOnes n - bitCount(n) + 2 <= A_inc(n)
2 <= A_inc(n)

There we go, we can happily stipulate that A_inc(n) = 2.

So, why do we care about this? Well, other than giving us another
example of amortised complexity, it is also leading us towards
yet another representation of sequential data. If Peano naturals
were related to our simple cons-lists, what is it that *binary*
naturals correspond to, and what properties might it afford us?

When we considered the Peanos, we had that, say, 5 was `S (S (S (S (S Z))))`.
In list form, this is a list with 5 elements (and each `(:)` stores more
information than an `S`).
When we consider binary numbers, they are a list of bits, where each bit contributes
a power of two to the total number. If thinking about this relating to a list,
how many elements would each bit store? It would be storing 2^n elements.

It turns out that what we would be after here is a list of *trees*, each of
which storing two to the power of some number of elements *perfectly*.
If a binary number has a zero in a position in its list, that would correspond
to no tree of values.

> data BinList a = BinList !Int [Maybe (Bush a)] deriving Show
> data Bush a = Leaf a | Fork (Bush a) (Bush a) deriving Show

> instance Seq BinList where
>   nil :: BinList a
>   nil = BinList 0 []
>
>   length :: BinList a -> Int
>   length (BinList n _) = n

So, let's think about cons. Remember before that there was a
relationship between `cons` and `inc` for Peanos and lists. So
too is there a relationship between `inc` for Binary and `cons`
for `BinList`:

>   cons :: a -> BinList a -> BinList a
>   cons x (BinList n ts) = BinList (n + 1) (inc (Leaf x) ts)
>     where inc :: Bush a -> [Maybe (Bush a)] -> [Maybe (Bush a)] -- ~O(1)
>           inc t [] = [Just t]
>           inc t (Nothing : ts) = Just t : ts
>           inc t (Just t' : ts) = Nothing : inc (Fork t t') ts

If we compare the structure of `inc` here to the `inc` we defined
on binary numbers earlier, we see they have the same shape. The complexities
of each line still match up the same way, and they have the same characteristics.
We could do the analysis again, but we can reduce it to our already solved
problem. If you want to make sure, the cost is the number of leading `Just`s
and the potential function is the number of `Just`s across the whole list.
So, why are we bothering to do this at all, other than just finding something
interesting? Well, we know that a balanced binary tree is both predictable
and has depth `log(m)` when it is perfectly containing `m` things. We know that
binary numbers contain `log(n)` bits too. So what I suspect is that we can
define indexing in `log(n) + log(m) = O(log(n))` time!

Our strategy here is to walk down the list of bushes until we find the
power of two that we are interested in. If the index is larger than the
size of the current inspected "bit", we need to look further on. If there
were values there, we need to subtract those values from the index. When
the index is less than the size of the current tree, we now look inside it.
To do this, we will divide by 2 every step, and then search either the left
or the right.

>   (!!) :: BinList a -> Int -> a -- O(log(n))
>   BinList n ts !! i
>     | i < 0 || i >= n = error "index out of bounds"
>     | otherwise       = findBush ts i 1
>     where findBush :: [Maybe (Bush a)] -> Int -> Int -> a
>           -- no values to find here, we must be further up!
>           findBush (Nothing : ts) i szT = findBush ts i (szT * 2)
>           findBush (Just t : ts) i szT
>             -- i lives inside t
>             | i < szT = findIndex t i (szT `div` 2)
>             -- this is not the bush we wanted
>             | otherwise = findBush ts (i - szT) (szT * 2)
>
>           -- Pre: the element is found in this bush
>           findIndex :: Bush a -> Int -> Int -> a
>           findIndex (Leaf x) 0 0 = x
>           findIndex (Fork lt rt) i szSub
>              | i < szSub = findIndex lt i (szSub `div` 2)
>              | otherwise = findIndex rt (i - szSub) (szSub `div` 2)

It suffices to implement both `head` and `last` in terms of the
now cheaper indexing function:

>   head :: BinList a -> a -- O(log(n))
>   head = (!! 0)

>   last :: BinList a -> a -- O(log(n))
>   last xs = xs !! (length xs - 1)

Turning the structure back into a list involves an old friend.

>   toList :: BinList a -> [a] -- O(n)
>   toList (BinList _ ts) = toList (foldr (append . values) nil (catMaybes ts))
>     where values :: Bush a -> DList a
>           values (Leaf x) = cons x nil
>           values (Fork lt rt) = values lt `append` values rt

The function `catMaybes` just takes a `[Maybe a]` and returns a `[a]`
only for the values that were `Just`s.
The implementations of `fromList` and `append` can
make simple use of our amortised `cons` function, which
does the job well enough:

>   fromList :: [a] -> BinList a -- O(n)
>   fromList = foldr cons nil

>   append :: BinList a -> BinList a -> BinList a -- O(m)
>   append xs ys = foldr cons ys (toList xs)

`tail` is very interesting, as it corresponds to decrementing
a binary number! This time, we need to carry the "bit" backwards,
and each time it has to be split in half before it can be slotted
back in. The final tree spat out will have size 1, which is the element
we want to discard.

>   tail :: BinList a -> BinList a -- ~O(1)?
>   tail (BinList n ts) = BinList (n - 1) (snd (dec ts))
>     where dec :: [Maybe (Bush a)] -> (Bush a, [Maybe (Bush a)])
>           dec (Just t : ts) = (t, ts)
>           -- this case is most interesting, the tree returned by the recursion is twice our size
>           -- we need to break it in half, and feed the rest back
>           dec (Nothing : ts) = let (Fork t t', ts') = dec ts in (t, Just t' : ts')

In isolation, you can show that `tail` is O(1) by considering a flipped
reasoning (imagine adding to a `~n` number).
However, this operation is somewhat problematic. When we can both
`inc` and `dec` a number, the amortised analysis no longer works:
if we have a `BinList` with 2^n-1 elements, and then repeatedly `cons`
then `tail` it, we will remain stuck in the `O(n)` case. Instead,
this highlights a limitation of this structure, which we should document.
Does this mean that amortised complexity is entirely broken then? We proved
they could both be O(1)!

The problem is that our potential function is not parameterised for
a single operation, it actually must account for the nearby expensiveness
of any of the available operations. In the `foldr cons nil`, for instance,
we only consider `cons` in isolation, but in general, our `Phi` would need
to account for `tail` too. As such, we have to come up with a potential function
that is representative of *both* operations. One idea would be to combine them
and take the max potential, but along these expensive operation boundaries we'll
find that the potential before and the potential after ends up being the same
and doesn't cancel out the cost:

< Phi(bs) = max (bitCount bs) (length bs - bitCount bs)

In the expensive case, it happens to be that `bitCount bs == length bs`, which
is also the case for `leadingOnes bs`. So, we have:

< leadingOnes bs + 1 <= A_inc(bs) - (Phi(inc bs) - Phi(bs))
< leadingOnes bs + 1 <= A_inc(bs) - (Phi(inc bs) - bitCount bs)
< leadingOnes bs + 1 <= A_inc(bs) - ((length (inc bs) - bitCount (inc bs)) - bitCount bs)
< leadingOnes bs + 1 <= A_inc(bs) - ((length (inc bs) - 1) - bitCount bs)
< leadingOnes bs + 1 <= A_inc(bs) - ((length bs + 1 - 1) - bitCount bs)
< leadingOnes bs + 1 <= A_inc(bs) - (length bs - bitCount bs)
< length bs + 1 <= A_inc(bs) - (length bs - length bs)
< length bs + 1 <= A_inc(bs)

And there it is friends, with the corrected `Phi`, we end up with `inc` being O(n).

In practice, there is a slightly different formulation of an `RAList`
that avoids this problem, where up to two trees of the same size can sit
next to each other in the front of the list. They have values in both forks and the leaves,
which means a new element can fuse two adjacent equal sized trees in a single
step (no amortisation necessary; but where would be the fun in that!). However,
in this representation, indexing becomes a lot trickier (the element at the top of
the tree is at a lower index than those below it) and we have lost the lovely
correspondance with numbers. For completeness, I'll implement this version too
in the notes.

Before we go though, we have two more operations to fill in: `init`, sadly, is a pain.
The problem is that we would need to shuffle all the values around by one in addition
to doing our subtraction algorithm. This will need to move around every element, so it
would be O(n). To save hassle, we might as well go via regular lists:

>   init :: BinList a -> BinList a -- O(n)
>   init = fromList . init . toList

>   null :: BinList a -> Bool
>   null = (== 0) . length

Extra: Random-Access Lists
--------------------------
So, while our `BinList` above was a nice exercise in practicing
amortised complexity and noticing relationships between numbers
and datastructures, it has a flaw that the inclusion of `tail`
and `cons` together ruins our amortised analysis.
Instead, we can tweak this structure to effectively remove the
`Nothing`s in the list.

> data NETree a = Tip a | Node (NETree a) a (NETree a) deriving Show
> data RAList a = RAList !Int [(Int, NETree a)] deriving Show

In this structure, an `NETree a` (non-empty tree) will always
contain 2^(n+1)-1 elements for depth `n`: 2^n leaves plus more
in the nodes along the way. In the `RAList`, every `NETree a`
is paired up with its number of elements. The invariance of the
structure is that every element in the list has an increasing
size, except for the first two trees, which *may* be the same size.
It turns out this is enough to improve the situation significantly.

> instance Seq RAList where
>    nil :: RAList a
>    nil = RAList 0 []

Remember, we have a new invariance on the structure. When both the
first trees are the same size, we can always combine them to make
a tree of the next size up by adding a single element into a `Node`
that links them. This might sit next to a new tree of the same size
as it, or it might be on its own. Because two trees of the same size
will always eagerly merge when possible, there is no danger of this
invariance being broken:

>    cons :: a -> RAList a -> RAList a -- O(1)
>    cons x (RAList n ((sz1, t1) : (sz2, t2) : ts))
>      -- the trees are equal size, which means we could construct
>      -- a larger tree that is equally perfect
>      | sz1 == sz2 = RAList (n + 1) ((sz1 + sz2 + 1, Node t1 x t2) : ts)
>    -- otherwise, we just need to add a new tip
>    cons x (RAList n ts) = RAList (n + 1) ((1, Tip x) : ts)

With no recursion here, this `cons` is guaranteed O(1): neat!
Tail is also easy to define without recursion

>    tail :: RAList a -> RAList a -- O(1)
>    -- it is easy to drop a tip
>    tail (RAList n ((1, Tip _):ts)) = RAList (n-1) ts
>    -- dropping a tree requires splitting and discarding the top
>    -- this will make two trees of the same size sat next to each other
>    -- the next tree in this list is guaranteed to be double the size at least,
>    -- so the invariance is preserved.
>    tail (RAList n ((sz, Node t1 _ t2):ts)) = RAList (n-1) ((szSub, t1) : (szSub, t2) : ts)
>      where szSub = sz `div` 2

For indexing, the first part of the algorithm where we
find our tree, is pretty much the same:

>    (!!) :: RAList a -> Int -> a -- O(log(n))
>    RAList n ts !! i
>      | i < 0 || i >= n = error "index out of bounds"
>      | otherwise       = findTree ts i
>      where findTree :: [(Int, NETree a)] -> Int -> a -- O(log(n))
>            findTree ((szT, t) : ts) i
>              -- this this our tree!
>              | i < szT = findIndex t i ((szT - 1) `div` 2)
>              -- this is not the tree we're looking for
>              | otherwise = findTree ts (i - szT)

Then it gets trickier. We have to be very careful
to think about the structure of the indices as we go through.
The top of the tree is always index 0, then the next szSub
elements are found on the left, and the remaining szSub elements
are found on the right.

>            findIndex :: NETree a -> Int -> Int -> a -- O(log(n))
>            findIndex (Tip x) 0 0 = x
>            findIndex (Node t1 x t2) i szSub
>              | i == 0     = x
>              | i <= szSub = findIndex t1 (i - 1) szSub'
>              | otherwise  = findIndex t2 (i - szSub - 1) szSub'
>              where szSub' = (szSub - 1) `div` 2

When we turn this structure back into a list,
we need to be careful about the order in which we visit the elements, but it's
otherwise much the same:

>    toList :: RAList a -> [a] -- O(n)
>    toList (RAList _ ts) = toList (foldr (append . values . snd) nil ts)
>      where values :: NETree a -> DList a
>            values (Tip x) = cons x nil
>            values (Node t1 x t2) = cons x (append (values t1) (values t2))

Now the rest of the functions proceed as they did before:

>    head :: RAList a -> a -- O(log(n))
>    head = (!! 0)
>
>    last :: RAList a -> a -- O(log(n))
>    last xs = xs !! (length xs - 1)
>
>    length :: RAList a -> Int -- O(1)
>    length (RAList n _) = n
>
>    null :: RAList a -> Bool -- O(1)
>    null = (== 0) . length
>
>    init :: RAList a -> RAList a -- O(n)
>    init = fromList . init . toList
>
>    fromList :: [a] -> RAList a -- O(n)
>    fromList = foldr cons nil
>
>    append :: RAList a -> RAList a -> RAList a -- O(m)
>    append xs ys = foldr cons ys (toList xs)

So, we adjusted our structure somewhat and now all is well.
But we originally based our representation on a number system
where incrementing in the absence of decrementing is amortised
O(1). Can we map this back to a number system again? Yes we
can, it's very weird:

Where binary works like this:

< 10100110 = 128*1 + 64*0 + 32*1 + 16*0 + 8*0 + 4*1 + 2*1 + 1*0 = 166

We can notice that our new number system allows *two* consecutive digits
to both have the same value. Namely, each digit is (2^n)-1, and we can
sometimes have 2 of them. We notice that we can only have two of the
least-significant digit, as there is no recursion in our corresponding
`cons` -- this is an invariance of the number system, and indeed of RAList.
So, let's see what 166 is:

< 1010101 = 127*1 + 63*0 + 31*1 + 15*0 + 7*1 + 3*0 + 1*1 = 166

Ok, well what about an example with 2 in it?

44 - 31 = 13
13 - 7  = 6
6 - 3   = 3
3 - 3   = 0

So we have 10120. What about 45:

45 - 31 = 14
14 - 7  = 7
7  - 7  = 0

So we have 10200

This is really interesting, because at any one time, at most two bits flip
when you increment or decrement. As such, we have O(1) operations for these
assuming you can "jump" straight to the least-significant set bit. For our
tree, the storing of the size allowed us to remove `Nothing` and in turn lets
us to "jump" straight to the least-significant bits.