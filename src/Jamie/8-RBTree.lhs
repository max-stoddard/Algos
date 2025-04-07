This lecture will see another counting system, and another datastructure
for sets: the red-black tree

> module RBTree where

> import Poset hiding (Tree(..))
> import Seq qualified
> import Data.List qualified as List (delete)

Red-black trees are an example of a self-balancing tree that allows for
more bias than an AVL tree does. It will also turn out that constructing
these trees from sorted data can be done in linear time via and amortized
O(1) "consing".

The idea of a red-black tree is to allow for a more lopsided balancing
for each node compared with an AVL tree. Each node is given a colour,
either red or black (hence the name); invariances about which nodes can
appear within which other nodes help control the balance of the structure.

> data Colour = R | B deriving Show
> data RBTree a = Tip | Node Colour (RBTree a) a (RBTree a) deriving Show

The two key invariances, other than the usual sorted-tree constraint, are:

* Every `Node R` has a `Node B` as a parent (and the root may not be R).
* Along every path from root to `Tip`, there are an equal number of `Node B`s

If there are no `Node R`s then the tree is perfectly balanced; otherwise,
there can be at most the same number of `Node R`s as there is `Node B`s,
which means branches can be up-to twice as big as the least red path.
See RBTree.pdf part 1 for diagrams.

Before we start defining the instance, we will need some smart-constructors.

> blacken :: RBTree a -> RBTree a
> blacken (Node R lt x rt) = Node B lt x rt
> blacken t = t

This function just turns a red node black -- this is needed to ensure
that the root of the tree is always a black node: this is a necessary
condition of the invariance, as all red nodes have a black parent node.

The other key function is balance, which has a few different cases to
consider. The reason for these cases comes from the manner of insertion,
which is covered later, so here is a spoiler: when we insert into an RBTree,
we'll see we only ever insert a *red* node. This doesn't affect the number
of black nodes in the tree, which is good, but might have a red parent, which
is bad. Because we need to preserve the number of black nodes at every point,
we'll realise that it is only possible to address a R/R conflict when there
are four trees to play with. As such, we look for a black node with a red child
and corresponding grandchild: there are four such ways this could occur:

> balance :: Colour -> RBTree a -> a -> RBTree a -> RBTree a
> balance B (Node R (Node R t1 u t2) v t3) w t4 = Node R (Node B t1 u t2) v (Node B t3 w t4)
> balance B (Node R t1 u (Node R t2 v t3)) w t4 = Node R (Node B t1 u t2) v (Node B t3 w t4)
> balance B t1 u (Node R (Node R t2 v t3) w t4) = Node R (Node B t1 u t2) v (Node B t3 w t4)
> balance B t1 u (Node R t2 v (Node R t3 w t4)) = Node R (Node B t1 u t2) v (Node B t3 w t4)
> balance c lt x rt = Node c lt x rt

See the diagrams on RBTree.pdf part 2 to see how this corresponds to
what we wanted. The nice thing is this balance function is straightforward
to define: in a mutable implementation there are 6 cases to consider, and
all involve more delicate pointer fiddling. At this point, we can consider
the instance, which is broadly straightforward...

The instance
------------

> instance Poset RBTree where
>    empty = Tip
>
>    singleton :: a -> RBTree a
>    singleton x = Node B Tip x Tip

This is the same member function we know and love:

>    member :: Ord a => a -> RBTree a -> Bool -- O(log n)
>    member x Tip = False
>    member x (Node _ lt y rt) = case compare x y of
>      EQ -> True
>      LT -> member x lt
>      GT -> member x rt

For insertion, we have a very similar structure to AVL trees,
with the key difference that we have to make sure to remove any
root-most red nodes, and also use our new `balance` function.

>    insert :: Ord a => a -> RBTree a -> RBTree a
>    insert x = blacken . insert' x
>      where insert' x Tip = Node R Tip x Tip
>            insert' x t@(Node c lt y rt) = case compare x y of
>              EQ -> t
>              LT -> balance c (insert' x lt) y rt
>              GT -> balance c lt y (insert' x rt)

Significantly harder is deletion. In an AVL tree, it suffices
to remove one of the leaf nodes and move it higher up, rebalancing
its parent as you go. If the node you remove is red, that's not
a problem, however, you may end up having to remove a black node:
this would mean that path down the tree has one less black node than
all its siblings! Fixing this is very hard: one approach is to
introduce two new colours: double-black and negative-black, which
allow you to track the broken invariance as you traverse back up,
and fix it later. This introduces a further 4 balancing cases, so
let's not do that. Instead, I'll be very cheeky and define a
different `delete`:

>    delete :: Ord a => a -> RBTree a -> RBTree a -- O(n)
>    delete x  = fromOrdList . List.delete x . toList

Note that when we use `toList`, we create a sorted list;
deletion does not change the ordering in the list, so we could
use a `fromOrdList` to construct the tree. `fromList` is O(n log n),
but as we'll see, we can do better than that for RBTrees, and get
an overall O(n) complexity. That's the hard bit of this lecture.
Let's clean up the other functions first:

>    toList :: RBTree a -> [a]
>    toList = Seq.toList . go
>      where go :: RBTree a -> Seq.DList a
>            go Tip = Seq.nil
>            go (Node _ lt x rt) = go lt `Seq.append` Seq.cons x (go rt)
>
>    minValue :: RBTree a -> a
>    minValue (Node _ Tip x _) = x
>    minValue (Node _ lt _ _)  = minValue lt
>
>    maxValue :: RBTree a -> a
>    maxValue (Node _ _ x Tip) = x
>    maxValue (Node _ _ _ rt)  = maxValue rt

`fromOrdList`
-------------
Before you can read the following definition, you need to
read the things below it (alas, I can't decouple these things
without breaking the instance). Come back here later :)

Now that you're back, what we've done up to this point is
used `foldr cons []` to turn the sorted list into a numerical
structure involving a list of digits of "one" or "two" red-black
trees of a perfect shape with all black-nodes. We need to collapse
this list down again into the final tree. Remember that earlier,
we took our "in-flight" RBTrees and laid them out with the left-most
leaf at one end and root at the other -- this spine of the tree are
the values that sit along the digits, with their right-children
dangling below. We just need to connect up that spine properly again
to make things work. We'll do that from the left:

>    fromOrdList :: [a] -> RBTree a -- O(n)
>    fromOrdList = foldl glue Tip . foldr cons []
>       where glue :: RBTree a -> Digit a -> RBTree a

When we have just one tree of a certain size, that can just be a
black node connecting the already folded tree `t` as the left-child
and the value dangling under the digit as the right-child.

>             glue t (One x t') = Node B t x t'

Otherwise, we have two trees of the same size. That's ok, because
any path down the tree is allowed to be twice the size of the smallest
by introducing a red node every other node. In this case, we take the
already folded up tree `t1`, and root it at `u` with `t2` as its sibling,
make it red, then make *that* the left-child of another node with `v` and
`t3`. The key here is that the `Two` digit allows us to introduce the
red nodes in the structure. This can also be seen from looking at the
diagrams from before carefully (just read from right-to-left) and
also shown diagrammatically in RBTree.pdf part 4.

>             glue t1 (Two u t2 v t3) = Node B (Node R t1 u t2) v t3

GO HERE FIRST:
Ok, it's time to go to RBTree.pdf part 3: here we'll draw out all the
intermediate trees on our way to building a large tree from balanced
data. What I've done after is to pick up the left-hand spine of the
tree and hang it up as if on a washing line. When you've got this
representation, you can imagine each point on the spine being an
element of a list of *partially-complete* trees (i.e. the roots are
missing their left-children).

Look at these lists, you'll see that when red nodes appear in the list,
they are next to a black rooted partial-tree of the same size. This may
seem familiar to the numeric system derived for RandomAccessLists:
`BinList` showed how sequences can match up to counting systems, in this
case plain binary, and then `RAList` showed an example of a counting
system where the digit 2 could appear, represented by two trees of the
same size together. In our case here, it appears as if there are no
"zeros"; instead we see one or two trees of every size up to the largest
sized partial-tree.

Read a bit further down the pdf, and you'll see how incrementing in this
system of only 1s and 2s still has the same shape as regular binary incrementing.
We knew this to be amortised O(1), and a similar argument can be made for this
new system: for further intuition about the system, see the recorded lecture.
Ok, so, we've noticed that the shape of a red-black tree as its being built
from sorted data, matches with some kind of strange number system.
We know that numbers in a binaryish format have ~O(1) complexity for
incrementing, we know that structures that follow that shape have ~O(1)
consing, so we can count our way through the list of elements and
in O(n) end up with a final "number" that we turn into a tree. Let's
focus on defining `cons` for this system: the diagrams in the pdf will
hopefully be helpful for seeing what happens in various cases,
including the carrying when we add 1 to a 2.

> data Digit a = One a (RBTree a)
>              | Two a (RBTree a) a (RBTree a)

> cons :: a -> [Digit a] -> [Digit a] -- ~O(1)
> cons x ds = inc x Tip ds
>   where inc :: a -> RBTree a -> [Digit a] -> [Digit a] -- ~O(1)
>         inc x t [] = [One x t]
>         inc x t (One y t' : ds) = Two x t y t' : ds
>         inc x t (Two y1 t1 y2 t2 : ds) = One x t : inc y1 (Node B t1 y2 t2) ds

The intuition for understanding the carrying in the last case
is to recognise that in the two case we have a red tree and a black
tree. When we need to carry it is because a new value has been added:
remember we only add red nodes, so this will cause a R/R conflict that
is resolved by rebalancing. This rebalancing will push `t2` and `y2`
to the *right* of `y1`, to allow for more black nodes on its left. A cascading
carry will occur if the rebalancing resulted in another R/R conflict
(the `Two` digit next in the list will have a `R` on its left!)
The difference between the actual rebalancing and this is that the
numeric system "bakes in" these rebalances as it goes, since we
know how the final tree will be shaped. If you're stuck, try doing
the inserts at the start of part 3 by hand and observing where those
R/R conflicts appear and how they resolve.

You can now return to the end of the instance for the merging.