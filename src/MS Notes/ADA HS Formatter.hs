import Prelude hiding (head, tail, init, last,(!!), length,(++))
import Data.Array (Array, listArray, (!))
import Data.List (minimumBy)
import Data.Function (on)
import Data.Array (Array)

-- ##### LISTS #####

-- List Defintion 
-- data [a] = []        -- [] :: [a]
--          | (:) a [a] -- (:) :: a -> [a] -> [a]

-- Append O(n), n is left list len
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

-- Fold O(n)
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

-- Flatten (O(n) due to foldr)
concatFoldr :: [[a]] -> [a]
concatFoldr = foldr (++) []

-- ##### ABSTRACT #####



-- Seq interface (list)
class Seq seq where
  nil    :: seq a
  cons   :: a -> seq a -> seq a
  snoc   :: seq a -> a -> seq a
  snoc xs x = xs `append` (cons x nil)
  append :: seq a -> seq a -> seq a
  length :: seq a -> Int
  head   :: seq a -> a
  tail   :: seq a -> seq a
  init   :: seq a -> seq a
  last   :: seq a -> a
  (!!)   :: seq a -> Int -> a
  toList :: seq a -> [a]
  fromList :: [a] -> seq a
 
-- Default List
instance Seq [] where
  nil = []             -- O(1)
  cons = (:)           -- O(1)
  -- snoc xs x         -- O(n)
  length = List.length -- O(n)
  head = List.head     -- O(1)
  tail = List.tail     -- O(1)
  init = List.init     -- O(n)
  last = List.last     -- O(n)
  (!!) = (List.!!)     -- O(n)
  toList = id          -- O(1)
  fromList = id        -- O(1)

-- Length List
data LenList a = LenList Int [a]
instance Seq LenList where
 append (LenList m xs) (LenList n ys) 
   = LenList (m + n) (xs ++ ys)                   --O(n)
 nil                   = LenList 0 []             --O(1)
 cons x (LenList n xs) = LenList (n + 1) (x : xs) --O(1)
 --snoc lxs x                                     --O(n)
 length (LenList n _)  = n                        --O(1)
 head (LenList _ xs)   = head xs                  --O(1)
 tail (LenList n xs)   = LenList (n - 1) (tail xs)--O(1)
 init (LenList n xs)   = LenList (n - 1) (init xs)--O(n)
 last (LenList _ xs)   = last xs                  --O(n)
 LenList _ xs !! n     = xs !! n                  --O(n)
 toList (LenList _ xs) = xs                       --O(1)
 fromList xs           = LenList (length xs) xs   --O(n)

-- Array
nil    -- O(1)
cons   -- O(n)
snoc   -- O(n)
append -- O(n)
length -- O(1)
head   -- O(1)
tail   -- O(n)
init   -- O(n)
last   -- O(1)
(!!)   -- O(1)

-- Tree
data Tree a = Leaf a | Fork (Tree a) (Tree a)

-- Difference lists for building (Prefer structures with fast insert delete)when building
data DList a = DList ([a] -> [a])
instance Seq DList where
 -- snoc dsx x                      -- O(1)
 append (DList dxs) (DList dys) 
   = DList (dxs . dys)              -- O(1)
 cons x (DList dxs)
  = DList ((x :) . dxs)             -- O(1)
 nil    = DList id                  -- O(1)
 length = length . toList           -- O(2n) ~ O(n)
 head   = head . toList             -- O(n)
 tail   = fromList . tail . toList  -- O(n)
 init   = fromList . init . toList  -- O(n)
 last   = last . toList             -- O(n)
 (!!)   = (!!) . toList             -- O(n)
 toList (DList dxs) = dxs []        -- O(n)
 fromList xs        = DList (xs ++) -- O(1)
 
-- ##### DIVIDE & CONQUER #####
 
-- Mergesort

splitAt :: [a] -> Int -> ([a], [a]) -- O(n)
splitAt xs n = (take n xs, drop n xs)
splitHalf :: [a] -> ([a], [a])      -- O(n)
splitHalf xs = splitAt xs (length xs `div` 2)

-- pre: both lists are sorted
merge :: Ord a => [a] -> [a] -> [a] -- O(m + n)
merge [] ys = ys
merge xs [] = xs
merge xxs@(x:xs) yys@(y:ys)
  | x <= y    = x : merge xs yys
  | otherwise = y : merge xxs ys

msort :: Ord a => [a] -> [a]
msort [] = []
msort [x] = [x]
msort xs = 
   let (us, vs) = splitHalf xs -- 1. divide
       us' = msort us -- 2. solve
       vs' = msort vs
   in merge us' vs' -- 3. recombine

-- Quicksort
partition :: (a -> Bool) -> [a] -> ([a], [a]) -- O(n)
partition p xs = (filter p xs, filter (not . p) xs)

allLess :: Ord a => a -> [a] -> ([a], [a]) -- O(n)
allLess x xs = partition (< x) xs

-- Omega(n log n) (should use random pivot)
qsort :: Ord a => [a] -> [a]
qsort [] = []
qsort (x:xs) =
  let (us, vs) = allLess x xs
      us' = qsort us
      vs' = qsort vs
  in us' ++ [x] ++ vs'

-- ##### 7+8) Dynamic Programming #####

-- Edit Distance (Minimum number of insert/delete/substitution required
-- to transform string to another


type Text = Array Int Char

fromString :: String -> Text
fromString cs = listArray (0, length cs - 1) cs

dist'' :: String -> String -> Int
dist'' cs1 cs2 = table ! (m, n)
  where
    -- Convert strings into array form for O(1) indexing:
    str1, str2 :: Text
    str1 = fromString cs1
    str2 = fromString cs2

    -- Bounds: (m,n) is the "largest" subproblem
    m = length cs1
    n = length cs2

    -- Tabulate all subproblems up to size (m,n)
    table :: Array (Int, Int) Int
    table = tabulate ((0,0), (m,n)) (uncurry memo)

    memo :: Int -> Int -> Int
    memo 0 j = j
    memo i 0 = i
    memo i j = minimum
      [ table ! (i-1, j)   + 1            -- remove from left
      , table ! (i,   j-1) + 1            -- remove from right
      , table ! (i-1, j-1) + cost         -- replace if needed
      ]
      where
        c1 = str1 ! (m - i)
        c2 = str2 ! (n - j)
        cost = if c1 == c2 then 0 else 1

-- Change problem


type Pence = Int
coins :: [Pence]
coins = [1,2,5,10,20,50,100,200]

change :: Pence -> [Pence]
change g = table ! g
  where
    table :: Array Pence [Pence]
    table = tabulate (0, g) memo

    -- Returns the best coin decomposition for each value
    memo :: Pence -> [Pence]
    memo 0 = []
    memo amt =
      minimumBy (compare `on` length)
        [ coin : table ! (amt - coin)
        | coin <- coins, coin <= amt
        ]

-- This version is O(n^2) because 'minimumBy (compare `on` length)' scans entire
-- result-lists which can be O(n) in length each time.

-- To fix that, we can use a 'LenList' that stores length in O(1):
change' :: Pence -> [Pence]
change' g = Seq.toList (table ! g)
  where
    table :: Array Pence (Seq.LenList Pence)
    table = tabulate (0, g) memo

    memo :: Pence -> Seq.LenList Pence
    memo 0 = Seq.nil
    memo amt =
      minimumBy (compare `on` Seq.length)
        [ Seq.cons coin (table ! (amt - coin))
        | coin <- coins, coin <= amt
        ]


-- Edit distance with path
edits' :: String -> String -> [String]
edits' cs1 cs2 = Seq.toList (table ! (m, n))
  where
    str1, str2 :: Text
    str1 = fromString cs1
    str2 = fromString cs2

    m = length cs1
    n = length cs2

    table :: Array (Int, Int) (Seq.LenList String)
    table = tabulate ((0,0),(m,n)) (uncurry memo)

    -- Each (i, j) yields a LenList of the full transformation path
    memo :: Int -> Int -> Seq.LenList String
    memo 0 j = Seq.inits (drop (n - j) cs2)  -- building up from ""
    memo i 0 = Seq.tails (drop (m - i) cs1)  -- breaking down to ""
    memo i j =
      minimumBy (compare `on` Seq.length)
        [ Seq.cons cs1'                  (table ! (i-1, j))       -- remove left char
        , Seq.cons cs1' (Seq.map (c2 :) (table ! (i,   j-1)))      -- insert right char
        , if c1 == c2
          then Seq.map (c2 :) (table ! (i-1, j-1))                 -- matched, no new step
          else Seq.cons cs1' (Seq.map (c2 :) (table ! (i-1, j-1))) -- replaced char
        ]
      where
        c1 = str1 ! (m - i)
        c2 = str2 ! (n - j)
        cs1' = drop (m - i) cs1

-- ##### 9. Amortized Analysis #####

data Deque a = Deque Int [a] [a] deriving Show
-- us ++ reverse sv

instance Seq Deque where

  ------------------------------------------------------------------------
  -- 1. Basic conversions
  ------------------------------------------------------------------------

  -- Turn a Deque into a list:
  toList :: Deque a -> [a]
  toList (Deque _ us sv) = us ++ reverse sv

  -- Empty Deque
  nil :: Deque a
  nil = Deque 0 [] []

  -- fromList (balanced):
  -- Split the input list roughly in half so neither internal list is large
  fromList :: [a] -> Deque a
  fromList xs = Deque n us (reverse vs)
    where
      n        = length xs
      (us, vs) = splitAt (n `div` 2) xs

  ------------------------------------------------------------------------
  -- 2. cons and snoc
  ------------------------------------------------------------------------
  -- cons: prepend an element in O(1), ensuring invariance
  cons :: a -> Deque a -> Deque a
  cons u (Deque n sv [])    = Deque (n+1) [u] sv
  cons u (Deque n us sv)    = Deque (n+1) (u:us) sv

  -- snoc: append an element in O(1), ensuring invariance
  snoc :: Deque a -> a -> Deque a
  snoc (Deque n [] us)   v  = Deque (n+1) us [v]
  snoc (Deque n us sv)   v  = Deque (n+1) us (v:sv)

  ------------------------------------------------------------------------
  -- 3. head and last
  ------------------------------------------------------------------------
  -- Both in O(1), thanks to our invariance that ensures we can find a
  -- front/back element cheaply.
  head :: Deque a -> a
  head (Deque _ [] [v]) = v
  head (Deque _ (u:_) _) = u
  -- partial if empty

  last :: Deque a -> a
  last (Deque _ [u] []) = u
  last (Deque _ _  (v:_)) = v
  -- partial if empty

  ------------------------------------------------------------------------
  -- 4. tail and init: Amortised O(1)
  ------------------------------------------------------------------------
  -- tail drops the front element, rebalancing when we cause an empty front.
  -- (That rebalancing may be O(n), but rarely enough to keep the amortised cost O(1).)
  tail :: Deque a -> Deque a
  tail (Deque 0 _ _)         = undefined   -- partial
  tail (Deque 1 _ _)         = nil         -- just remove last element
  tail (Deque _ [_] sv)      = fromList (reverse sv)   -- rebalances in O(n)
  tail (Deque n (_ : us) sv) = Deque (n-1) us sv        -- O(1) in normal case

  -- init drops the last element, in a symmetrical way
  init :: Deque a -> Deque a
  init (Deque 0 _ _)         = undefined
  init (Deque 1 _ _)         = nil
  init (Deque _ us [_])      = fromList us
  init (Deque n us (_ : sv)) = Deque (n-1) us sv

  ------------------------------------------------------------------------
  -- 5. Other sequence operations
  ------------------------------------------------------------------------
  length :: Deque a -> Int
  length (Deque n _ _) = n

  null :: Deque a -> Bool
  null = (== 0) . length

  -- For '!!', we can (lazily) convert to a list. Not the best, but a simple definition:
  (!!) :: Deque a -> Int -> a
  q !! i = toList q !! i

  -- append can be done in O(m). Usually rebalancing once:
  append :: Deque a -> Deque a -> Deque a
  append q (Deque 0 _ _) = q
  append (Deque m us sv) (Deque 1 us' []) =
    Deque (m+1) (us ++ reverse sv) us'
  append (Deque m us sv) (Deque n us' sv'@(_:_)) =
    Deque (m+n) (us ++ reverse sv ++ us') sv'

-- ##### 11. Random Access Lists #####

data Nat = Z | S Nat
data Bit = O | I deriving (Show, Eq, Enum)
type Binary = [Bit]

zero :: Binary
zero = [] -- Or [0]

-- On many incs O(1) amortised
inc :: Binary -> Binary
inc [] = [1]
inc (O : bs) = I : bs
inc (I : bs) = O : inc bs

-- BinList
data Bush a = Leaf a | Fork (Bush a) (Bush a) deriving Show
data BinList a = BinList !Int [Maybe (Bush a)] deriving Show

instance Seq BinList where

  -- Empty
  nil :: BinList a
  nil = BinList 0 []

  -- Size is stored as an Int
  length :: BinList a -> Int
  length (BinList n _) = n

  -- Null check
  null :: BinList a -> Bool
  null = (== 0) . length

  --------------------------------------------------------------------
  -- 1) cons in ~O(1) amortised
  --------------------------------------------------------------------
  cons :: a -> BinList a -> BinList a
  cons x (BinList n ts) = BinList (n + 1) (inc (Leaf x) ts)
    where
      inc :: Bush a -> [Maybe (Bush a)] -> [Maybe (Bush a)]
      inc t []              = [Just t]
      inc t (Nothing : ts) = Just t : ts
      inc t (Just t' : ts) = Nothing : inc (Fork t t') ts

  --------------------------------------------------------------------
  -- 2) tail in ~O(1) amortised
  --------------------------------------------------------------------
  tail :: BinList a -> BinList a
  tail (BinList n ts) = BinList (n - 1) (snd (dec ts))
    where
      dec :: [Maybe (Bush a)] -> (Bush a, [Maybe (Bush a)])
      dec (Just t : ts)     = (t, ts)
      dec (Nothing : ts)    =
        let (Fork t t', ts') = dec ts
        in (t, Just t' : ts')

  --------------------------------------------------------------------
  -- 3) Indexing (!!) in O(log n)
  --------------------------------------------------------------------
  (!!) :: BinList a -> Int -> a
  BinList n ts !! i
    | i < 0 || i >= n = error "out of bounds"
    | otherwise       = findBush ts i 1
    where
      findBush :: [Maybe (Bush a)] -> Int -> Int -> a
      findBush (Nothing : bs) i szT      = findBush bs i (2 * szT)
      findBush (Just t : bs) i szT
        | i < szT    = findIndex t i (szT `div` 2)
        | otherwise  = findBush bs (i - szT) (2 * szT)

      findIndex :: Bush a -> Int -> Int -> a
      findIndex (Leaf x) 0 0        = x
      findIndex (Fork lt rt) i szSub
        | i < szSub  = findIndex lt i (szSub `div` 2)
        | otherwise  = findIndex rt (i - szSub) (szSub `div` 2)

  -- head & last can reuse (!!)
  head :: BinList a -> a
  head xs = xs !! 0

  last :: BinList a -> a
  last xs = xs !! (length xs - 1)

  --------------------------------------------------------------------
  -- 4) Conversions and other operations
  --------------------------------------------------------------------
  toList :: BinList a -> [a]
  toList (BinList _ ts) =
    toList (foldr (append . values) nil (catMaybes ts))
    where
      values :: Bush a -> DList a
      values (Leaf x)    = cons x nil
      values (Fork l r)  = values l `append` values r

  fromList :: [a] -> BinList a
  fromList = foldr cons nil

  append :: BinList a -> BinList a -> BinList a
  append xs ys = foldr cons ys (toList xs)

  init :: BinList a -> BinList a
  init = fromList . Prelude.init . toList  -- O(n)

data NETree a = Tip a
              | Node (NETree a) a (NETree a)
  deriving Show

data RAList a = RAList !Int [(Int, NETree a)]
  deriving Show

instance Seq RAList where
  nil :: RAList a
  nil = RAList 0 []

  length :: RAList a -> Int
  length (RAList n _) = n

  null :: RAList a -> Bool
  null = (== 0) . length

  --------------------------------------------------------------------
  -- 1) cons in O(1) worst-case
  --------------------------------------------------------------------
  cons :: a -> RAList a -> RAList a
  cons x (RAList n ((sz1,t1):(sz2,t2):ts))
    | sz1 == sz2
      = RAList (n+1) ((sz1+sz2+1, Node t1 x t2) : ts)
  cons x (RAList n ts)
      = RAList (n+1) ((1, Tip x) : ts)

  --------------------------------------------------------------------
  -- 2) tail in O(1) worst-case
  --------------------------------------------------------------------
  tail :: RAList a -> RAList a
  tail (RAList n ((1, Tip _):ts)) =
    RAList (n-1) ts
  tail (RAList n ((sz, Node lt x rt):ts)) =
    -- size is 'sz', so each subtree has size szSub
    RAList (n-1) ((szSub, lt) : (szSub, rt) : ts)
    where szSub = sz `div` 2

  --------------------------------------------------------------------
  -- 3) Indexing (!!) in O(log n)
  --------------------------------------------------------------------
  (!!) :: RAList a -> Int -> a
  RAList n ts !! i
    | i < 0 || i >= n = error "out of bounds"
    | otherwise       = findTree ts i
    where
      findTree :: [(Int, NETree a)] -> Int -> a
      findTree ((szT, t):ts) i
        | i < szT   = findIndex t i ((szT - 1) `div` 2)
        | otherwise = findTree ts (i - szT)

      findIndex :: NETree a -> Int -> Int -> a
      findIndex (Tip x) 0 0 = x
      findIndex (Node lt x rt) i szSub
        | i == 0     = x
        | i <= szSub = findIndex lt (i-1) ((szSub - 1) `div` 2)
        | otherwise  = findIndex rt (i - szSub - 1) ((szSub - 1) `div` 2)

  -- head and last in O(log n), reusing (!!)
  head :: RAList a -> a
  head xs = xs !! 0

  last :: RAList a -> a
  last xs = xs !! (length xs - 1)

  toList :: RAList a -> [a]
  toList (RAList _ ts) =
    toList (foldr (append . values . snd) nil ts)
    where
      values :: NETree a -> DList a
      values (Tip x)      = cons x nil
      values (Node l x r) = cons x (append (values l) (values r))

  init :: RAList a -> RAList a -- O(n)
  init = fromList . Prelude.init . toList

  fromList :: [a] -> RAList a -- O(n)
  fromList = foldr cons nil

  append :: RAList a -> RAList a -> RAList a -- O(m)
  append xs ys = foldr cons ys (toList xs)


-- ##### Searching, Poset, AVL Tree #####

-- Aim: Is somethin in set or not
class Poset set where -- Partially ordered
  empty :: set a
  insert :: Ord a => a -> set a -> set a
  delete :: Ord a => a -> set a -> set a
  
  singleton :: Ord a => a -> set a
  singleton x = insert x empty
  
  member :: Ord a => a -> set a -> Bool
  minValue :: Ord a => set a -> a
  maxValue :: Ord a => set a -> a
  
  fromList :: Ord a => [a] -> set a
  fromList = foldr insert empty
  toList :: set a -> [a]
  fromOrdList :: Ord a => [a] -> set a
	
  union :: Ord a => set a -> set a -> set a
  difference :: Ord a => set a -> set a -> set a
  intersection :: Ord a => set a -> set a -> set a
  
-- Bad poset !!!
instance Poset [] where
  empty = [] -- O(1)
  insert x [] = [x] -- 
  insert x yys@(y:ys) = case compare x y of -- O(n)
    EQ -> yys
    LT -> x : yys
    GT -> y : insert x ys
  delete = List.delete -- O(n)
  
  member = elem -- O(n)
  minValue = head -- O(1)
  maxValue = last -- O(n)
  
  toList = id -- O(1)
  
-- 2nd bad but better Poset
data TreeBad a = Tip | Node (Tree a) a (Tree a)

instance Poset TreeBad where
  empty = Tip
  
  insert x Tip = Node Tip x Tip -- Can be O(n) as no balancing if ordered
  insert x t@(Node lt y rt) = case compare x y of
    EQ -> t
    LT -> Node (insert x lt) y rt
    GR -> Node lt y (insert x rt)
  
-- Good Balancing Implementation
data Tree a = Tip | Node Int (Tree a) a (Tree a)

height :: Tree a -> a -- O(1)
height Tip = 0
height (Node h _ _ _) = h

node :: Tree a -> a -> Tree a -> Tree a -- O(1)
node lt x rt = Node (max (height lt) (height rt) + 1) lt x rt

-- Pre: height lt >= height rt
balanceL :: Tree a -> a -> Tree a -> Tree a
balanceL lt u rt

-- Pre: height lt <= height rt
balanceR :: Tree a -> a -> Tree a -> Tree a
balanceR lt x rt

instance Poset Tree where
  empty = Tip
  
  member x Tip = False -- O(log(n))
  member x t@(Node _ lt y rt) = case compare x y of
    EQ -> True
    LT -> member x lt
    GT -> member x rt
    
  