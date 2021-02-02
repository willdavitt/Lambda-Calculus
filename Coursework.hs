
-------------------------
-------- PART A --------- 
-------------------------


import Data.List

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
--  deriving Show

instance Show Term where
  show = pretty

example :: Term
example = Lambda "a" (Lambda "x" (Apply (Apply (Lambda "y" (Apply (Variable "a") (Variable "c"))) (Variable "x")) (Variable "b")))

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m


------------------------- Assignment 1

numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))


-------------------------

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

------------------------- Assignment 2

variables :: [Var]
variables = map (:[]) ['a'..'z'] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

filterVariables :: [Var] -> [Var] -> [Var]
filterVariables xs []     = xs 
filterVariables xs (y:ys) = filter (/=y) (filterVariables xs ys)

fresh :: [Var] -> Var
fresh = head . filterVariables variables

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x n) = merge [x] (used n)
used (Apply  n m) = merge (used n) (used m)


------------------------- Assignment 3


rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z n)
    | z == x    = Lambda z n
    | otherwise = Lambda z (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
    | x == y    = n
    | otherwise = Variable y
substitute x n (Lambda y m)
    | x == y    = Lambda y m
    | otherwise = Lambda z (substitute x n (rename y z m))
    where z = fresh (used n `merge` used m `merge` [x,y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)

------------------------- Assignment 4

beta :: Term -> [Term]
beta (Apply (Lambda x n) m) =
  [substitute x m n] ++
  [Apply (Lambda x n') m  | n' <- beta n] ++
  [Apply (Lambda x n)  m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m  | n' <- beta n] ++
  [Apply n  m' | m' <- beta m]
beta (Lambda x n) = [Lambda x n' | n' <- beta n]
beta (Variable _) = []


normalize :: Term -> Term
normalize n
  | null ns   = n
  | otherwise = normalize (head ns) 
  where ns = beta n

run :: Term -> IO ()
run n = do
  print n
  let ns = beta n
  if null ns then
    return ()
  else
    run (head ns)

 
-------------------------

suc    = Lambda "n" (Lambda "f" (Lambda "x" (Apply (Variable "f") (Apply (Apply (Variable "n") (Variable "f")) (Variable "x")))))
add    = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m") (Variable "f")) (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))))))
mul    = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m") (Apply (Variable "n") (Variable "f"))) (Variable "x")))))
dec    = Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Apply (Variable "n") (Lambda "g" (Lambda "h" (Apply (Variable "h") (Apply (Variable "g") (Variable "f")))))) (Lambda "u" (Variable "x"))) (Lambda "x" (Variable "x")))))
minus  = Lambda "n" (Lambda "m" (Apply (Apply (Variable "m") dec) (Variable "n")))

test = Apply (Lambda "a" (Variable "z")) (Variable "a")

ex1 :: Term
ex1 = Lambda "x" (Variable "x")

ex2 :: Term
ex2 = Lambda "y" (Apply (Variable "y") (Variable "z"))

ex3 :: Term
ex3 = Lambda "w" (Variable "r")

ex4 :: Term
ex4 = Lambda "q" (Variable "t")

-------------------------
-------- PART B --------- 
-------------------------

------------------------- Assignment 5

free :: Term -> [Var]
free xs = free' xs

free' :: Term -> [Var]
free' (Variable x) = [x]
free' (Lambda x n) = [n' | n' <- free' n, x/=n']
free' (Apply  n m) = merge (free' n) (  free' m)

abstractions :: Term -> [Var] -> Term
abstractions n [] = n
abstractions n (x:xs)= Lambda x (abstractions n xs)

applications :: Term -> [Term] -> Term
applications n [] = n
applications n (x:xs) = applications (Apply n x) xs

lift :: Term -> Term
lift n = applications (abstractions n (free n) ) x
    where
      x = map (Variable) (free n)



super :: Term -> Term
super (Variable x) = (Variable x)
super (Lambda x n) = lift (Lambda x (getN n))
super (Apply  n m) = Apply (super n) (super m)

getN :: Term -> Term
getN (Variable x) = (Variable x)
getN (Lambda x n) = Lambda x(getN n)
getN (Apply  n m) = super (Apply n m)

------------------------- Assignment 6

data Expr =
    V Var
  | A Expr Expr
  

toTerm :: Expr -> Term
toTerm (V a) = (Variable a)
toTerm (A a b) = (Apply (toTerm a) (toTerm b))

instance Show Expr where
  show = show . toTerm

type Inst = (Var , [Var], Expr)

data Prog = Prog [Inst]


instance Show Prog where
  show (Prog ls) = unlines (map showInst ks)
    where
      ks = map showParts ls
      n  = maximum (map (length . fst) ks)
      showParts (x,xs,e) = (x ++ " " ++ unwords xs , show e)
      showInst (s,t) = take n (s ++ repeat ' ') ++ " = " ++ t


names = ['$':show i | i <- [1..] ]

-------------------------

stripAbs :: Term -> ([Var],Term)
stripAbs (Lambda x n) = (strip' (Lambda x n), (doThat n))
stripAbs (Apply  n m) = ([],(Apply  n m))
stripAbs (Variable x) = ([],(Variable x))

strip' :: Term -> [Var]
strip' (Lambda x n) = x : (strip' n)
strip' (Apply  n m) = []
strip' (Variable x) = []

doThat :: Term -> Term
doThat (Lambda x n) = doThat n
doThat (Apply  n m) = (Apply  n m)
doThat (Variable x) = (Variable x)

takeAbs :: Term -> [Term]
takeAbs (Lambda x n) = [(Lambda x n)]
takeAbs (Apply n m) = (takeAbs n) ++ (takeAbs m)
takeAbs (Variable x) = []


toExpr :: [Var] -> Term -> Expr
toExpr vs (Variable x) = V x
toExpr (v:vs) (Lambda x n) = V v
toExpr (v:vs) (Apply a b) = A (toExpr (fst((splitAt' (getNumL a) (v:vs)))) a) (toExpr (snd((splitAt' (getNumL a) (v:vs)))) b) 
toExpr [] (Apply n m) = A (toExpr [] n) (toExpr [] m)

getNumL :: Term -> Int
getNumL (Apply a b) = (getNumL a) + (getNumL b)
getNumL (Variable v) = 0
getNumL (Lambda x n) = 1 

splitAt' :: Int -> [a] -> ([a], [a])
splitAt' 0 xs     = ([], xs)
splitAt' _ []     = ([], [])
splitAt' n (x:xs) = (x:xs', xs'')
  where
    (xs', xs'') = splitAt' (n - 1) xs

toInst :: [Var] -> (Var,Term) -> (Inst,[(Var,Term)],[Var])
toInst freshNames pair = ( (fst(pair) ,fst(stripAbs(snd(pair))), toExpr (freshNames) (snd(stripAbs(snd(pair))))), (zip (freshNames) (takeAbs((snd((stripAbs(snd(pair)))))))), getSpare freshNames (map (fst) (zip (freshNames) (takeAbs((snd((stripAbs(snd(pair))))))))) )

--getSpare :: [Var] -> [Var] -> [Var]
--getSpare freshNames usedNames = freshNames // usedNames

getSpare :: Ord a => [a] -> [a] -> [a]
getSpare [] _ = []
getSpare (x:xs) ys
    | elem x ys = getSpare xs ys
    | otherwise = x : getSpare xs ys



prog :: Term -> Prog
prog t = Prog (aux names [("$main", (super t))])
  where
    aux :: [Var] -> [(Var,Term)] -> [Inst]
    aux (n:ns) (x:xs) = (fst3(toInst (n:ns) x)) : (aux (lst3 (toInst (n:ns) x)) (xs ++ (snd3(toInst (n:ns) x))))
    aux freshName [] = []

fst3 :: (a, b, c) -> a
fst3 (x,_,_) = x

snd3 :: (a, b, c) -> b
snd3 (_,x,_) = x

lst3 :: (a, b, c) -> c
lst3 (_,_,x) = x

example2 = Apply (Variable "S") (Apply (Apply example (numeral 0)) (Variable "0"))
example3 = Apply (Apply add (numeral 1)) (Apply (Apply mul (numeral 2)) (numeral 3))
example4 = Apply (Apply example3 (Variable "S")) (Variable "0")

------------------------- Assignment 7

sub :: [(Var,Expr)] -> Expr -> Expr
sub ps (A m n) = A (sub ps m) (sub ps n)
sub (p:ps) (V a)
    | a == fst(p) = snd(p)
    | otherwise = sub ps (V a)
sub [] (V a) = (V a)

--abc ac
--2nd part of instruction
-- length second part of instruction
step :: [Inst] -> [Expr] -> IO [Expr]
step inst ((V a):ss)
    | (snd(step' inst (V a))) == 1 = do
            if (length (snd3 (fst( step' inst (V a)) )) ) <= (length (ss)) then        
                        return ((sub (zip (snd3 ( fst( step' inst (V a)))) ss) (lst3  ( fst( step' inst (V a))))) : (snd (splitAt' (length( zip (snd3 (fst( step' inst (V a)) )) ss ) ) ss)))
            else do 
                error "step: insufficient arguments on stack"
    | otherwise = do 
                       print a
                       return ss
step (i:is) ((A n m):ns) = do return (n:(m:ns))
step (i:is) [] = error "step: insufficient arguments on stack"



-- check enough on stack for operation
-- -Use length and length of instruction we select. len(stack) >= len(var instruction)
-- cons new expression to the top of stack
--Function to get instruction given a name
-- 
step':: [Inst] -> Expr -> (Inst,Int)
step' ((x,y,z):is) (V a)
    | x == a = ((x,y,z),1)
    | otherwise = step' (is) (V a)
step' [] (V a) = (("asdf", [], V "tester"),0)

supernormalize :: Term -> IO ()
supernormalize n = step2 (prog n) ([V "$main"])




step2 :: Prog -> [Expr] -> IO ()
step2 (Prog(x: is)) ((V a):ss)
     | (((snd(step' (x: is) (V a))) == 1)&& ((length (snd3 (fst( step' (x: is) (V a)) )) ) <= (length (ss)))) = step2 (Prog(x: is)) ((sub (zip (snd3 ( fst( step' (x: is) (V a)))) ss) (lst3  ( fst( step' (x: is) (V a))))) : (snd (splitAt' (length( zip (snd3 (fst( step' (x: is) (V a)) )) ss ) ) ss)))
     | (((snd(step' (x: is) (V a))) == 1)&& ((length (snd3 (fst( step' (x: is) (V a)) )) ) > (length (ss)))) = error "step: insufficient arguments on stack"
     | otherwise = do
            print a
            step2 (Prog(x: is)) ss
step2 (Prog(x: is)) ((A n m):ns) = step2 (Prog(x: is)) (n:(m:ns))
step2 (Prog(x: is)) [] = return ()




   