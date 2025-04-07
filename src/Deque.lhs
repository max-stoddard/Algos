> module Deque where

> import Seq (Seq(..))
> import qualified Seq

This lecture will explore *amortised complexity* via a new Seq, called:
So for in this course, we've been writing algorithms and datastructures
where complexity of each operation is fixed and isolated.
In this lecture we will see examples of operations that in isolation
look expensive, but when considered in groups are cheap.
For instance, we might have an operation `f` which costs O(n)
the first time we use it, then O(1) for the next n times we use it.
That means a total of O(2n) for the n calls, leaving an average of
O(2) per call. This is what we called *amortized* analysis.

How does happen in practice? The key is that datastructures
often invariances. These invariances can sometimes fiddle with
complexities in odd ways.

In first year, you'd have learnt that `(:)` was an O(1) function,
but `snoc` was O(n). Similarly, while `head` and `tail` are O(1),
`last` and `init` are both O(n).
It would be nice to have a sequence where `head`, `cons`, `tail`
all have the same properties as `last`, `snoc`, and `init`.
We also want them to be fast. To do this, we will introduce a new
structure, called a `Deque`:

> data Deque a = Deque Int [a] [a] deriving Show

The `Int` here is not necessary, but it will be helpful
to reduce cases later on: it represents the size of the
structure.

So, given the list `xs = [1, 2, 3, 4, 5, 6]`, we have the
following (currently) legal Deques:

< [ Deque 6 [1,2,3,4,5,6] []
< , Deque 6 [1,2,3,4,5] [6]
< , Deque 6 [1,2,3,4] [6,5]
< , Deque 6 [1,2,3] [6,5,4]
< , Deque 6 [1,2] [6,5,4,3]
< , Deque 6 [1] [6,5,4,3,2]
< , Deque 6 [] [6,5,4,3,2,1]
< ]

Basically, the first list are elements at the front of the
structure, and the second is elements at the back, organised
in reverse. One invariance we can notice right away is that
`Deque n us sv` represents the list `us ++ reverse sv`.
This will be helpful in our implementation of `Seq`:

> instance Seq Deque where
>   toList :: Deque a -> [a]
>   toList (Deque n us sv) = us ++ reverse sv
>
>   nil :: Deque a
>   nil = Deque 0 [] []
>

Currently we have one invariance, but we will see it's
not enough. We can give some easy definitions for `cons`
and `snoc`:

<   cons :: a -> Deque a -> Deque a -- O(1)
<   cons u (Deque n us sv) = Deque (n+1) (u:us) sv
<
<   snoc :: Deque a -> a -> Deque a -- O(1)
<   snoc (Deque n us sv) v = Deque (n+1) us (v:sv)

Ok symmetry is appearing, nature is healing. Now let's
turn our attention to how to construct a `Deque` from
a list. Here is an "obvious" one:

<   fromList :: [a] -> Deque a -- O(n)
<   fromList xs = Deque (Seq.length xs) xs []

This definition works. Is it fair? The problem is
that this is not symmetric, and `last` would
clearly be expensive. While we don't need to
maintain symmetry at all times (and indeed this would
hurt performance), we should at least be fair here.

>   fromList :: [a] -> Deque a
>   fromList xs = Deque n us (reverse vs)
>     where n = Seq.length xs
>           (us, vs) = splitAt (div n 2) xs

This definition is more fair. It's not an invariance though,
so things can still "go wrong".

< last (cons 1 (cons 2 (cons 3 nil)))
<   = last (Deque 3 [1, 2, 3] [])

< head (nil `snoc` 1 `snoc` 2 `snoc` 3)
<   = head (Deque 3 [] [3, 2, 1])

These are not what we were looking for intuitively,
we are looking for something that is *somewhat* balanced,
but totally balancing would be too much work, as now
`cons` and `snoc` are necessarily O(n).

< (==>) :: Bool -> Bool -> Bool
< False ==> _ = True
< True ==> p = p

We will add an invariance for *minimally* rebalancing:

  (null sv ==> length us <= 1) && (null us ==> length sv <= 1)

Which we read as "if either list is empty, the other is at most size 1". Alternatively:

  (n >= 2) ==> not (null us) && not (null sv)

If there are more than 2 elements in the queue then neither list can be empty.
The impact on the deques from earlier is:

< [ Deque 6 [1,2,3,4,5,6] [] -- ILLEGAL
< , Deque 6 [1,2,3,4,5] [6]
< , Deque 6 [1,2,3,4] [6,5]
< , Deque 6 [1,2,3] [6,5,4]
< , Deque 6 [1,2] [6,5,4,3]
< , Deque 6 [1] [6,5,4,3,2]
< , Deque 6 [] [6,5,4,3,2,1] -- ILLEGAL
< ]

Now that we have this invariance we MUST keep it in mind. Both when we are
constructing things, but also when we are defining operations that consume
the Queue: if at some point a definition seems a bit strange, or like it's
missing something, that probably is indicating that the invariance is at play.
carefully consider the invariance, then carry on.

This will be enough to give us guaranteed constant time `head` and `last`:

>   head :: Deque a -> a -- O(1)
>   head (Deque _ [] [v]) = v -- we know if one list is empty the other is empty or singleton
>   head (Deque _ (u:_) _) = u
>
>   last :: Deque a -> a -- O(1)
>   last (Deque _ [u] []) = u
>   last (Deque _ _  (v:_)) = v

Symmetrical! Note that this is possible because of the invariance (though these
functions are still partial, because `head` and `last` don't work on empty things).
If you go back up and look at the `cons` and `snoc` definitions above, you'll notice
that they are commented out. Why? Well, suppose we `cons u (Deque 1 [x] [])`, the
current definition would break the invariance! With some small adjustments we can
make them work again retaining their O(1) complexity:

>   cons :: a -> Deque a -> Deque a -- O(1)
>   cons u (Deque n sv []) = Deque (n+1) [u] sv
>   cons u (Deque n us sv) = Deque (n+1) (u:us) sv
>
>   snoc :: Deque a -> a -> Deque a -- O(1)
>   snoc (Deque n [] us) v = Deque (n+1) us [v]
>   snoc (Deque n us sv) v = Deque (n+1) us (v:sv)

Remember, if these definitions look confusing, consider the invariance!
At this point we have `head`, `last`, `cons`, and `snoc` all taking O(1),
yay.

We have two operations remaining that we are interested
in, `tail` and `init`:

>   tail :: Deque a -> Deque a -- ~O(1)
>   tail (Deque 0 _ _) = undefined                -- O(1)
>   tail (Deque 1 _ _) = nil                      -- O(1)

At this point in the function, we can be sure that `n >= 2`, so
we need to be careful of the invariance. If the first list is
singleton, then tail would otherwise make it empty, but then
this may disrupt the invariance. As such, we should now rebalance
the lists using our `fromList` function, costing O(n):

>   tail (Deque _ [_] sv) = fromList (reverse sv) -- O(n)

Otherwise, we know that `length us >= 2`, so we are safe to
remove an element cheaply without danger of breaking the
invariance.

>   tail (Deque n (_:us) sv) = Deque (n-1) us sv  -- O(1)

A similar, symmetric definition follows for `init`:

>   init :: Deque a -> Deque a -- ~O(1)
>   init (Deque 0 _ _) = undefined
>   init (Deque 1 _ _) = nil
>   init (Deque _ us [_]) = fromList us
>   init (Deque n us (_:sv)) = Deque (n-1) us sv

Sadly, it appears as if, though symmetric, the
functions `init` and `tail` are expensive as O(n).
In reality, we are going to learn that this is
NOT the case (see the associated .pdf). You might also
be able to see why by looking at the following sequence of
16 tails.

< [ Deque 16 [1] [16,15,14,13,12,11,10,9,8,7,6,5,4,3,2] -- O(n)
< , Deque 15 [2,3,4,5,6,7,8] [16,15,14,13,12,11,10,9]   -- O(1)
< , Deque 14 [3,4,5,6,7,8] [16,15,14,13,12,11,10,9],    -- O(1)
< , Deque 13 [4,5,6,7,8] [16,15,14,13,12,11,10,9],      -- O(1)
< , Deque 12 [5,6,7,8] [16,15,14,13,12,11,10,9],        -- O(1)
< , Deque 11 [6,7,8] [16,15,14,13,12,11,10,9],          -- O(1)
< , Deque 10 [7,8] [16,15,14,13,12,11,10,9],            -- O(1)
< , Deque 9 [8] [16,15,14,13,12,11,10,9],               -- O(n/2)
< , Deque 8 [9,10,11,12] [16,15,14,13]                  -- O(1)
< , Deque 7 [10,11,12] [16,15,14,13]                    -- O(1)
< , Deque 6 [11,12] [16,15,14,13],                      -- O(1)
< , Deque 5 [12] [16,15,14,13],                         -- O(n/4)
< , Deque 4 [13,14] [16,15],                            -- O(1)
< , Deque 3 [14] [16,15],                               -- O(n/8)
< , Deque 2 [15] [16],                                  -- O(1)
< , Deque 1 [] [16],                                    -- O(1)
< , Deque 0 [] []
< ]

If you sum these you'll get `n + n / 2 + n / 4 + n / 8... = 2n` and then a bunch of
O(1)s, for a total cost of O(3n) for n tails. In other words, `tail` is `O(1)`.

You can think about amortization as a piggy-bank: we overpay and save every
time we do something cheap, so that we have pocket money to pay for nice
expensive tails. Let's now look at formally reasoning about this.

Amortized Analysis
------------------

We need three things:

* A cost function, C_opi(xsi): this is the true cost of the operation
  opi at the state xsi.
* An amortized cost function A_opi(xsi): this is the amortised cost
  of opi when applied to xsi.
* A "potential" function (because now we are physicists), Phi(xs):
  a measure of how close the next expensive operation will be.
  Phi(xs) >= 0.

Basically, these three functions, will form a relationship:

C_opi(xsi) <= A_opi(xs) - (Phi(xs') - Phi(xsi))

If this relationship is true, then the operation has complexity
A_op. The derivation of why this ends up being true is laid out
in the pdf. Effectively though, the Phi function allows us to
record the fact that A sometimes overpays, so that there is enough
cost to cancel out the expensive operations later. Since we get
to pick both Phi and A for ourselves, it seems disingenuous, but
it does work properly. You cannot simply pick *any* Phi function;
pick poorly and the A will not be good. The key here is that it
is the *difference* between Phi from one state to the next -- you
need it so that just before something expensive, Phi is at its largest
value, and that just after something expensive, it is at its smallest.
That way, the difference will be enough to match the C_opex.
Let's just see an example, and work through it. Let's start by
determining the true cost of `tail`:

< tail :: Deque a -> Deque a -- ~O(1)
< tail (Deque 0 _ _) = undefined                -- O(1)
< tail (Deque 1 _ _) = nil                      -- O(1)
< tail (Deque _ [_] sv) = fromList (reverse sv) -- O(n)
< tail (Deque n (_:us) sv) = Deque (n-1) us sv  -- O(1)

< C_tail(Deque 1 _ _)     = 1
< C_tail(Deque _ [_] _)   = n - 1
< C_tail(Deque _ (_:_) _) = 1

Hopefully you can see that these match up to the above discussion.
Now, we need to decide on our `A`. With linear time for tail in the
worst case, we can only really do better if we pick log or constant.
We will pick constant for now, if the maths didn't work out we could
readjust. For full generality, I will pick some constant `k`, which
we will learn the constraints on later.

< A_tail(xs) = k

Now, for the Phi. This is the hard bit of amortised analysis. Again,
our intuition here needs to be that the Phi before and after the
worst-case tail has to have a difference
of around `n`, the true cost of expensive `tail`, to allow us to
properly offset the cost. We are therefore aiming for around 0 when
the deque is balanced, and `n` when it is maximally imbalanced.
There are a few formulations of `Phi` that might meet this criteria,
and here is one of them:

< Phi(Deque n us sv) = max (length sv - length us) 0

When `length us` is `1`, we are about to hit the expensive case next,
and the length of `sv` will be `n - 1`, resulting in a potential of `n - 2`.
After this tail, the length of sv and us will be at most 1 apart from eachother,
so we have an overall difference of around `n`. This will be enough.
We trust in the process, and work through the equation.

C_opi(xsi) <= A_opi(xs) - (Phi(xs') - Phi(xsi))

We now have to consider the three different cases offered by the true cost
function. Lets start with the singleton deque case:

C_tail(Deque 1 _ _) <= A_tail(Deque 1 _ _) - (Phi(nil) - Phi(Deque 1 _ _))
1 <= A_tail(Deque 1 _ _) - (Phi(nil) - Phi(Deque 1 _ _))
1 <= k - (Phi(nil) - Phi(Deque 1 _ _))
1 <= k - (0 - Phi(Deque 1 _ _))
-- worst case, we end up with `0` as the potential of the singleton deque
1 <= k - (0 - 0)
1 <= k

So far so good, k must be >= 1.

For this case, n >= 2

C_tail(Deque n (_:us) sv) <= A_tail(Deque n (_:us) sv) - (Phi(Deque (n-1) us sv) - Phi(Deque n (_:us) sv))
1 <= k - (Phi(Deque (n-1) us sv) - Phi(Deque n (_:us) sv))
1 <= k - (max (length sv - length us) 0 - (max (length sv - length (_:us)) 0))

Suppose us is longer than sv: `0 - 0`, giving us `1 <= k`
Otherwise let `length sv = m` and `length us = n`:

1 <= k - ((m - n) - (m - (n + 1)))
1 <= k - (m - n - m + n + 1)
1 <= k - 1
2 <= k

This case has left us more constained, we now need ~O(2) at least.
Last case, this time the cost on the left is n - 1:

C_tail(Deque n [_] sv) <= k - (Phi(fromList (reverse sv)) - Phi(Deque n [_] sv))
n - 1 <= k - (Phi(fromList (reverse sv)) - Phi(Deque n [_] sv))
n - 1 <= k - (1 - Phi(Deque n [_] sv))
n - 1 <= k - (1 - (n - 2))
n - 1 <= k - (1 - n + 2)
n - 1 <= k - (-n + 3)
n - 1 <= k + n - 3
2 <= k

Cool, so when `k = 2`, all three of these equations will be true. This gives us
a result that `tail` is O(2). Earlier on when we did the sums, we learnt that
`tail` applied `n` times ended up being `O(3n)`. Well, the amortized analysis
assumes that the initial Phi(xs0) = 0 (see pdf), so the example above should have started
from a balanced queue (the next line down). If you follow from there you will
also reason that the cost of `tail` is O(2). Obviously, the individual constant
doesn't really matter, the point is we proved it for some constant, so O(1) is
the complexity of tail amortized.

Don't worry, we will see more examples next week, which will give us more
insight into this process. You should go away, however, and try and prove the
following falsehood:

`reverse` = ~O(1)

To "do" this, you've picked `A_reverse(_) = k`, so find a Phi(xs) such that
Phi(reverse xs) - Phi(xs) = C_reverse(xs) = n. This would be the necessary
requirement for your proof; you should realise pretty quickly that because
reverses never have "expensive" and "cheap" cases, it's impossible to find
a `Phi` function that can end up having this difference. That should help you
realise that the `Phi` isn't just some "hack", it actually only works when
there is a meaningful difference between states, and that the operation does
vary in its costs throughout.

For completeness, here are the remaining unimplemented functions from Seq:

>   length (Deque n _ _) = n
>   null = (== 0) . Seq.length
>   q !! i = toList q Seq.!! i
>
>   -- for fun, I'll try and implement append more intelligently:
>   append :: Deque a -> Deque a -> Deque a -- O(m)
>   append q (Deque 0 _ _) = q
>   append (Deque m us sv) (Deque 1 us' []) = Deque (m + 1) (us ++ reverse sv) us'
>   append (Deque m us sv) (Deque n us' sv'@(_:_)) =
>     -- it is possible for m == 0, but us' will rebalance, and we know sv' can be
>     -- on its own as it is non-empty
>     Deque (n + m) (us ++ reverse sv ++ us') sv'