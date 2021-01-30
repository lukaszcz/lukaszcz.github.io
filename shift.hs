-- This file demonstrates three versions of the shift function with
-- different runtime behaviours.

-- quadratic complexity, because (++) is linear in its first argument,
-- and the overall number of steps (calls to shift0) is also linear
shift0 :: Int -> [a] -> [a]
shift0 0 as = as
shift0 n (a:as) = shift0 (n-1) (as ++ [a])
-- (as ++ [a]) is matched on in the next step, so its first element
-- needs to be computed immediately (this becomes more and more costly
-- in each step, with runtime proportional to i in the i-th step)
shift0 _ [] = []

-- linear complexity, the best solution
shift1 :: Int -> [a] -> [a]
shift1 n as = loop n as []
  where
    loop 0 as acc = as ++ reverse acc
    loop n (a:as) acc = loop (n-1) as (a:acc)
    -- evaluating (a:acc) takes constant time
    loop _ [] acc = reverse acc

-- quadratic complexity, but about (length as - n) initial elements of
-- the result may be computed quickly thanks to lazy evaluation (the
-- accumulator acc is not matched on in loop, so it does not have to
-- be evaluated till the very end)
shift2 :: Int -> [a] -> [a]
shift2 n as = loop n as []
  where
    loop 0 as acc = as ++ acc
    -- above acc still contains an unevaluated Haskell expression
    -- created in the previous steps of loop; the complexity of
    -- evaluating the first i elements of acc is proportional to i*n
    loop n (a:as) acc = loop (n-1) as (acc ++ [a])
    -- (acc ++ [a]) is not matched on in the next step, so it is not
    -- evaluated right away
    loop _ [] acc = acc

lst0 = shift0 3 [1,2,3,4,5,6]
lst1 = shift1 3 [1,2,3,4,5,6]
lst2 = shift2 3 [1,2,3,4,5,6]

long = replicate 1000000 2 -- create a list with one million elements

lst1_0 = take 10 (shift0 500000 long) -- really slow (takes forever)
lst1_1 = take 10 (shift1 500000 long) -- fast
lst1_2 = take 10 (shift2 500000 long) -- fast

-- (length l) forces Haskell to fully evaluate l
lst2_0 = length (shift0 500000 long) -- really slow
lst2_1 = length (shift1 500000 long) -- fast
lst2_2 = length (shift2 500000 long) -- really slow

lst3_0 = length (take 500000 (shift0 500000 long)) -- really slow
lst3_1 = length (take 500000 (shift1 500000 long)) -- fast
lst3_2 = length (take 500000 (shift2 500000 long)) -- fast

lst4_0 = length (take 500100 (shift0 500000 long)) -- really slow
lst4_1 = length (take 500100 (shift1 500000 long)) -- fast
lst4_2 = length (take 500100 (shift2 500000 long)) -- moderately slow (a few seconds)

lst5_0 = length (take 501000 (shift0 500000 long)) -- really slow
lst5_1 = length (take 501000 (shift1 500000 long)) -- fast
lst5_2 = length (take 501000 (shift2 500000 long)) -- quite slow (a few minutes)

lst6_0 = length (take 510000 (shift0 500000 long)) -- really slow
lst6_1 = length (take 510000 (shift1 500000 long)) -- fast
lst6_2 = length (take 510000 (shift2 500000 long)) -- really slow (forever)
