> module Poset where

> import qualified Seq
> import Data.List qualified as List

In this lecture, we will leave `Seq` behind, and start looking at a new
class of datastructure.
So far in this course, we've been looking at sequential datastructures, where
the order of the elements matter. We've seen efficient linear seqeunces, like
`[]` and `Deque`, efficient constructors like `DList`, and efficient indexed
sequences like `BinList` and `RAList`.

But these types of structures, by their nature, will end up with linear time
*searches* for data within the set. That's ok, but sometimes we do want to have
a better complexity for queries. This is the role of Sets and Maps.

< elem :: Eq a => a -> [a] -> [a] -- O(n)
< elem x [] = False
< elem x (y:ys) = x == y || elem x ys

Such sets will adhere to a *partial-ordering*, called `Poset`. We could also
explore hash-based sets as a different direction, but we won't in this course.
A `Poset` will have an ordering imposed, via `Ord`, in the relevant operations;
which is a limitation of Haskell's typeclass system (and why we can't also support
hash-sets with this interface):

> class Poset set where
>   empty :: set a
>   insert :: Ord a => a -> set a -> set a
>   delete :: Ord a => a -> set a -> set a
>
>   singleton :: Ord a => a -> set a
>   singleton x = insert x empty
>
>   -- query functions (we expect these to be fast)
>   member :: Ord a => a -> set a -> Bool
>   minValue :: Ord a => set a -> a
>   maxValue :: Ord a => set a -> a
>
>   fromList :: Ord a => [a] -> set a
>   fromList = foldr insert empty
>   fromOrdList :: Ord a => [a] -> set a
>   fromOrdList = fromList
>
>   toList :: set a -> [a]
>
>   -- composites
>   union :: Ord a => set a -> set a -> set a
>   union s1 s2 = foldr insert s1 (toList s2)
>   difference :: Ord a => set a -> set a -> set a
>   difference s1 s2 = foldr delete s1 (toList s2)
>   intersection :: Ord a => set a -> set a -> set a
>   intersection s1 s2 = fromList (filter (`member` s2) (toList s1))

An example of a *bad* poset would be to try and use `[]`. As lists
have a linear structure, we can do no better than to search linearly
through the list for something, even if we know the list is sorted.

> instance Poset [] where
>   empty = [] -- O(1)
>   insert x [] = [x] -- O(n)
>   insert x yys@(y:ys)
>     | x == y    = yys
>     | x < y     = x : yys
>     | otherwise = y : insert x ys
>   delete = List.delete -- O(n)
>
>   member = elem -- O(n)
>   minValue = head -- O(1)
>   maxValue = last -- O(n)
>
>   toList = id -- O(1)

While it is easy enough to implement a set using lists, it doesn't make
use of the Ordering constraint available to us. Note, a set-like structure does
not preserve duplicates as we were used to for sequential structures. For "good"
set structures, most of the operations should be `O(log(n))` or better.

Usually, when we think `log` we think... trees!

< data Tree a = Tip | Node (Tree a) a (Tree a)

< instance Poset Tree where
<   empty = Tip
<
<   insert :: Ord a => a -> Tree a -> Tree a -- O(n)
<   insert x Tip = Node Tip x Tip
<   insert x t@(Node lt y rt) = case compare x y of
<     EQ -> t -- if x is in the set, we don't need to do anything
<     LT -> Node (insert x lt) y rt
<     RT -> Node lt y (insert x rt)

This is a "frozen" representation of the divide step of quicksort (think about the partition
flowing down each branch)! As it happens, all of the construction functions
for datastructures we see for ordered data correspond to some sorting algorithm frozen
in time. That gives us some intuition about their performance
characteristics. Indeed, the pathological case of quicksort is where the data is sorted,
and a very biased partitioning of the list is performed. Similarly, the `fromList` derived
from `foldr insert empty` will produce very biased trees when the data is sorted.
While we are here, take a look back at the list set representation: `foldr insert empty` is
also describing part of a sorting algorithm, namely *insertion sort*.

While this O(n) insertion is probably not what we were looking for, let's carry on by defining
the `toList` function using an old friend:

<   toList :: Tree a -> [a] -- O(n)
<   toList = Seq.toList . go
<      where go :: Tree a -> Seq.DList a
<            go Tip = Seq.nil
<            go (Node lt x rt) = go lt `Seq.append` Seq.cons x (go rt)

This completes the quicksort (well, not quite, this removes duplicates!):

< quicksort :: Ord a => [a] -> [a]
< quicksort = toList . fromList @Tree

We know that quicksort suffers from issues when the data is already sorted.
So too will this tree, as there is no guarantee made about its balancing.
Instead, let's abandon this and define a self-balancing tree called an
AVL tree. One thing that AVL trees need is access to their height in O(1) time:

> data Tree a = Node !Int (Tree a) a (Tree a)
>             | Tip
>             deriving Show

> height :: Tree a -> Int
> height Tip = 0
> height (Node h _ _ _) = h

Obviously, for this `height` to be useful, it actually needs to reflect the
structure of the tree. This is imposed as an invariance on the structure;
to save us time later on, let's create what's known as a *smart constructor*.
This is something we use in place of a regular constructor to allow us to
abstract away some detail that we don't care about:

> node :: Tree a -> a -> Tree a -> Tree a
> node lt x rt = Node (max (height lt) (height rt) + 1) lt x rt

Now, when we don't know anything about the height of a tree we are constructing
from context, it will be useful to use `node` to build the values. However,
one property we wanted from this tree compared to the previous attempt is we
also expect it to be *balanced*. To obtain this, we will add an additional invariant
to the tree `Node _ lt _ rt`:

> balanced :: Tree a -> Tree a -> Bool
> balanced lt rt = abs (height lt - height rt) <= 1

Effectively, we only allow each pair of sub-trees to be at most one different
in height -- zero wouldn't work, or we couldn't have non-perfect trees.
Right, let's turn this datastructure into a Poset! Along the way, we are going
to need to write some additional smart-constructors, I'll leave them up here with the
datastructure itself, as we cannot "break" the flow of the instance. Go down to the
instance *NOW* and then come back up here to understand the internal mechanics of
the smart-constructors `balanceL` and `balanceR`...

The first challenge we encounter is the need to ensure that a newly constructed
tree is balanced. We assume that we know where an imbalance may have occurred to
save some work:

> balanceL :: Tree a -> a -> Tree a -> Tree a -- O(1)
> balanceL lt x rt
>  | balanced lt rt = node lt x rt
> -- Pre: height lt > height rt + 1

Once we have established the tree is imbalanced, we are in one of two cases
(in AVL.pdf, these are cases A or B). Basically, we are interested in which
of the two children of `lt` is the taller one. The similar case is where the
left-most tree is tallest. In this case, we just need to "rotate" the trees
to ensure everyone has the same height (again, see the diagrams for this).

>  | height llt >= height lrt = rotr (node lt x rt)

If the "middle" tree is tallest, this is a bit trickier to handle, because
we can't rotate the whole tree without imbalancing it again. Instead, we
need to rotate `lt` to get a left-biased tree that matches the case above,
then we already know how to handle that.

>  | otherwise                = rotr (node (rotl lt) x rt)
>  where Node _ llt _ lrt = lt

Now, for the rotations themselves. If you've refered to the diagrams
in AVL.pdf, you can read these definitions as coming directly from
those diagrams (but rendered as pattern matches). This is part of the
reason we like the persistent datastructures, because balancing can be
very simply implemented as pattern matches, and not fiddly manual (destructive)
pointer manipulations.

> rotr :: Tree a -> Tree a -- O(1)
> -- Pre: llt is taller than or equal to lrt and rt
> rotr (Node _ (Node _ llt u lrt) v rt) = node llt u (node lrt v rt)
>
> rotl :: Tree a -> Tree a -- O(1)
> -- Pre: rrt is taller than or equal to rlt and lt
> rotl (Node _ lt u (Node _ rlt v rrt)) = node (node lt u rlt) v rrt

The other case for balancing is symmetric:

> balanceR :: Tree a -> a -> Tree a -> Tree a -- O(1)
> balanceR lt x rt
>  | balanced lt rt = node lt x rt
> -- Pre: height lt + 1 < height rt
>  | height rrt >= height rlt = rotl (node lt x rt)
>  | otherwise                = rotl (node lt x (rotr rt))
>  where Node _ rlt _ rrt = rt

You may now return downstairs for `delete`...

The Instance
------------

> instance Poset Tree where
>   empty :: Tree a
>   empty = Tip
>
>   singleton :: a -> Tree a
>   singleton x = node Tip x Tip
>
>   member :: Ord a => a -> Tree a -> Bool -- O(log(n)), because tree is balanced
>   member _ Tip = False
>   member x (Node _ lt y rt) = case compare x y of
>     LT -> member x lt
>     EQ -> True
>     GT -> member x rt

We can borrow the `toList` function from the previous instance on trees.

>   toList :: Tree a -> [a] -- O(n)
>   toList = Seq.toList . go
>      where go :: Tree a -> Seq.DList a
>            go Tip = Seq.nil
>            go (Node _ lt x rt) = go lt `Seq.append` Seq.cons x (go rt)

When we insert, we want to avoid the pitfalls of the previous iteration
of `Tree` we tried. We must guarantee that the resulting tree is balanced
after the insertion. That will guarantee O(log(n)) complexity later on.

>   insert :: Ord a => a -> Tree a -> Tree a -- O(log(n))
>   insert x Tip = singleton x -- these are balanced wrt each other
>   insert x t@(Node h lt y rt) = case compare x y of
>     EQ -> t

Right, in this case, we need to insert into the tree. We know that the
tree `t` is *currently* balanced, but consider where `height lt == height rt + 1`:
inserting into the left tree *may* create an imbalance such that `height lt' == height rt + 2`
-- this just won't do! Instead, let's suppose the existence of `balanceL` and `balanceR`
smart-constructors that will rebalance the tree to preserve the invariance of the sub-trees:

>     LT -> balanceL (insert x lt) y rt
>     GT -> balanceR lt y (insert x rt)

To be clear, `balanceL` is used when the *left*-tree has grown *or* the right-tree has shrunk.
The opposite is true for `balanceL`. At this point, head back upstairs and look at the implementation
of `balanceL` (and `balanceR`, but it's entirely symmetric).

Now, let's try deletion, which is a bit tricker.

>   delete :: Ord a => a -> Tree a -> Tree a -- O(log(n))
>   delete _ Tip = Tip
>   delete x (Node _ lt y rt) = case compare x y of

We start off straightfoward, if the element is found to either the
left or right, we delete it recursively. Remember this could cause an
imbalance, but in these cases we remember that the sub-tree *shrinks*:
as a result we use the opposite balance than for insertion.

>     LT -> balanceR (delete x lt) y rt
>     GT -> balanceL lt y (delete x rt)

However, when the element to remove is found at our node, we need to
be very careful, because we need a new element to root the tree!
By invariance, we know that the two halves of the tree are balanced
with respect to each other, so we can assume this for the `glue` function,
which will implement this case.

>     EQ -> glue lt rt

As we'll see, implementing `glue` will require two more functions, `extractMin`
and `extractMax`; these can be used to clean up the last two functions of the
instance.

>   minValue :: Ord a => Tree a -> a -- O(log(n))
>   minValue (Node _ lt x rt) = fst (extractMin lt x rt)
>
>   maxValue :: Ord a => Tree a -> a -- O(log(n))
>   maxValue (Node _ lt x rt) = fst (extractMax lt x rt)

This leaves us needing a way of connecting two trees together, which
are balanced with respect to each other.

> glue :: Tree a -> Tree a -> Tree a -- O(log(n))
> -- Pre: `balanced lt rt`
> glue Tip rt = rt
> glue lt Tip = lt

Now that we've ruled out both empty cases, we know that both trees
are definitely nodes.

> glue lt@(Node lh llt lx lrt) rt@(Node rh rlt rx rrt)

In this first case, the height `rh` is guaranteed to be `lh + 1`.
That means that this is a good candidate to select the new root
element from. Selecting a root *may* reduce the height of the
tree by one, but that would at worst leave it equal to `lh`, which
is still balanced; as such, we do not need to balance.

>   | lh < rh   = let (x, rt') = extractMin rlt rx rrt in node lt x rt'

Otherwise, the trees are either equal in height or `lh == rh + 1`. This
suggests that we can remove an element from `lt` to serve as the new
root. Once we've done this, we will be in one of two cases: `lh' == rh`
or `lh' == rh - 1`; either way this is also balanced.

>   | otherwise = let (x, lt') = extractMax llt lx lrt in node lt' x rt

The final functions we need then, are those that extract the smallest/largest
element out of a tree. In an ideal world, these are total functions to avoid
any missing cases; to that end, I've basically broken up nodes so that they
are passed in as three arguments and not just one. This ensures we always
have an element to return and a residual tree. The burden is on the caller to
pattern match on a node to use the function.

> extractMin :: Tree a -> a -> Tree a -> (a, Tree a) -- O(log(n))

The smallest element in a tree is found all the way to the left. A node
with a left-tip will contain the smallest element:

> extractMin Tip min rest = (min, rest)

Otherwise, we know that there is another node to explore on the left, so
take it apart and feed it to another `extractMin`.

> extractMin (Node _ llt lx lrt) x rt =
>   let (min, rest) = extractMin llt lx lrt

Once that's done, we have a left-over tree, `rest` and our minimum. The
minimum can be passed straight on up, but we need to combine this residual
tree with our `rt`, to form a larger tree. Before we extracted the minimum
of `lt`, we know that `balanced lt rt`; as such, `rest` could be at most
one smaller that `lt` was, and so we need to balance on the right when combining:

>   in (min, balanceR rest x rt)

Removing the maximum is symmetric.

> extractMax :: Tree a -> a -> Tree a -> (a, Tree a) -- O(log(n))
> extractMax rest max Tip = (max, rest)
> extractMax lt x (Node _ rlt rx rrt) =
>   let (max, rest) = extractMax rlt rx rrt
>   in (max, balanceL lt x rest)

Because of the need to find a new root element for the tree, deletion is
often trickier for balanced trees. In the next lecture, we will explore a
different tree which is more permissive in the imbalance, and this makes
`delete` even harder to define. Indeed, we won't do it in the lecture at
all.

So, what are the takeaways from this lecture? The first is to recognise that
datastructures often represent algorithms frozen in time, which is a nice
insight that lets us reason about them. We know because of the correspondance
between sorted structures and sorting algorithms, that `toList . fromList` on
these structures cannot be better than O(n log n) in general. It also provides
an insight on the performance characteristics of the other operations involving
logs and therefore trees. Another takeaway is the importance of invariance
preservation -- it is always easiest if you produce smart-constructors that
help intriniscally preserve the invariance. While we noticed places where you
didn't need to call `balanceX`, for instance, it doesn't hurt to do so (and
the structure can be optimised later). Focus on correctness *first* and optimisation
second, when it becomes an issue.