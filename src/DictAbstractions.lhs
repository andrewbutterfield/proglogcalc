\section{Dictionary Abstractions}\label{ha:dict-abs}
\begin{code}
module DictAbstractions where
import Utilities
import qualified Data.Map as M
import Data.List
import Data.Char
--import NiceSymbols
import Debug.Trace
import CalcPPrint
import CalcTypes
import CalcAlphabets
import CalcPredicates
\end{code}


We support abstractions of common composite patterns,
most implemented as dictionary entry builder functions.

We want to support a wide range of binary operators,
and well as predicate transformers of interest.


\subsection{Variable Abstractions}

First, we deal with simple ways to provide \texttt{PredEntry}
for simple predicate variables:
\begin{code}
pvarEntry :: String -> [String] -> (Pred, Dict)
pvarEntry nm alf
 = ( PVar nm
   , entry nm
      $ PredEntry [] ppPVar alf (pNoChg nm) (pNoChg nm)
   )
 where ppPVar _ _ _ _ = ppa nm
\end{code}

\newpage
\subsection{Predicate Abstractions}

\subsubsection{Prefix Predicate Transformer}

\RLEQNS{
   \textbf{\textsf{PT}} P &=& \ldots
}
\begin{code}
prefixPT :: String                       -- name
         -> Int                          -- precedence
         -> Maybe ( Dict
                    -> Pred -> Pred) -- optional defn expander
         -> ( Pred -> Pred           -- builder
            , Dict)                    -- entry
prefixPT n_PT precPT optDefnPT
 = let

     mkPT pr = Comp n_PT [pr]

     appSep
      | length n_PT == 1 && (not . isAlpha $ head n_PT)  =  ""
      | otherwise                                        =  " "

     ppPT sCP d p [pr]
      = paren p precPT
            $ pplist [ppa n_PT, ppa appSep, sCP precPT 1 pr]
     ppPT sCP d p _ = pps styleRed $ ppa $ error n_PT
     error nm = "invalid-"++nm++", only one argument allowed"

     defnPT d [pr]
       = case optDefnPT of
          Nothing        ->  Nothing
          Just expandPT  ->  Just (n_PT, expandPT d pr, True)

   in ( mkPT
      , entry n_PT $ PredEntry subAny ppPT [] defnPT noDefn )
\end{code}

\newpage
\subsection{Binary Predicate Operator Abstractions}

We have a generic type for a function that builds
a composite predicate given a list of same:
\begin{code}
type MkPredOp = String -> (Pred -> Bool) -> [Pred] -> Pred
\end{code}
In addition, we sometimes want to simply return a simplifed list
of sub-predicates:
\begin{code}
type MkSimpPreds = (Pred -> Bool) -> [Pred] -> [Pred]
\end{code}

We can construct a generic operator builder parameterised
by a \texttt{MkPredOp} builder function:
\begin{code}
pOpMk :: MkPredOp
      -> String
      -> Int
      -> ( [Pred] -> Pred
         , Dict)
pOpMk mkop n_OP precOP
 = let

     isOP (Comp name _)  =  name == n_OP
     isOP _              =  False

     mkOP [pr] = pr
     mkOP prs = mkop n_OP isOP prs

     ppOP sCP d p [pr] = sCP p 1 pr
     ppOP sCP d p prs
      = paren p precOP
          $ ppopen (pad n_OP)
          $ ppwalk 1 (sCP precOP) prs


   in ( mkOP
      , entry n_OP $ PredEntry subAny ppOP [] noDefn noDefn )

\end{code}

\newpage
\subsubsection{Semigroup Operators}

\RLEQNS{
   (a \oplus b) \oplus c &=& a \oplus (b \oplus c)
}
\begin{code}
popSemiG :: String
         -> Int
         -> ( [Pred] -> Pred
            , Dict)
popSemiG n_SGR precSGR = pOpMk mkAssocP n_SGR precSGR
\end{code}

Abelian/Idempotent variants:
\begin{code}
popSemiGA n_SGR precSGR = pOpMk mkCommAssocP n_SGR precSGR
popSemiGAI n_SGR precSGR = pOpMk mkIdemCommAssocP n_SGR precSGR
\end{code}

\newpage
\subsubsection{Monoid Operators}

\RLEQNS{
   (a \oplus b) \oplus c &=& a \oplus (b \oplus c)
\\ 1 \oplus a &= a =& a \oplus 1
}
First, a generic paramterised builder:
\begin{code}
pMonMk :: MkSimpPreds
       -> String
       -> Pred
       -> Int
       -> ( [Pred] -> Pred
          , Dict)
pMonMk mksimpp n_MND unit precMND
 = let

     isMND (Comp name _)  =  name == n_MND
     isMND _              =  False

     mkMND prs
      = case mksimpp isMND prs of
          []    ->  unit
          [pr]  ->  pr
          prs   ->  Comp n_MND prs

     ppMND sCP d p []   = sCP p 0 unit
     ppMND sCP d p [pr] = sCP p 1 pr
     ppMND sCP d p prs
      = paren p precMND
          $ ppopen (pad n_MND)
          $ ppwalk 1 (sCP precMND) prs

     simpMND d prs  = psMonoid d (n_MND++"-simplify") mkMND  unit prs

   in ( mkMND
      , entry n_MND $ PredEntry subAny ppMND [] noDefn simpMND )
\end{code}



\newpage
\subsubsection{Monoid Simplification}~

Given associative binary operator $\otimes$ with and unit $1$
this embodies the following laws:
\RLEQNS{
   1 \otimes x & = x = & x \otimes 1
\\ \bigotimes_{i \in \setof{1}} x_i &=& x_1
}
\begin{code}
psMonoid :: Dict
         -> String               -- op. name
         -> ([Pred] -> Pred) -- op. builder
         -> Pred               -- unit
         -> [Pred]             -- op. arguments
         -> RWResult
psMonoid d tag op unit prs
 = ret $ simpM [] prs
 where

   simpM srp [] = reverse srp
   simpM srp (pr:prs)
    | pr == unit  =  simpM     srp  prs
    | otherwise   =  simpM (pr:srp) prs

   ret []          =  Just (tag, unit, diff )
   ret [pr]        =  Just (tag, pr, diff )
   ret prs'
    | prs' == prs  =  Nothing
    | null prs'    =  Just (tag, unit, diff )
    | otherwise    =  Just (tag, op prs', diff )
\end{code}

Associative binary operators with  unit elements.
\begin{code}
popMonoid :: String  -- operator name
          -> Pred    -- unit predicate
          -> Int     -- operator precedence
          -> ( [Pred] -> Pred
             , Dict )
popMonoid = pMonMk mkAssocPs
\end{code}

Variants:
\begin{code}
popMonoidA = pMonMk mkCommAssocPs
popMonoidAI = pMonMk mkIdemCommAssocPs
\end{code}

\newpage
\subsubsection{Semi-Lattice Operators}

\RLEQNS{
   (a \oplus b) \oplus c &=& a \oplus (b \oplus c)
\\ 1 \oplus a &= a =& a \oplus 1
\\ 0 \oplus a &= 0 =& a \oplus 0
}

Associative binary operators with both unit and zero elements.
Here we defer zero annihilation to the simplifier.
\begin{code}
pSemiLMk :: MkSimpPreds
         -> String
         -> Pred
         -> Pred
         -> Int
         -> ( [Pred] -> Pred
            , Dict )
pSemiLMk mksimpp n_SL zero unit precSL
 = let

     isSL (Comp name _)  =  name == n_SL
     isSL _              =  False

     mkSL prs
      = case mksimpp isSL prs of
         []    ->  unit
         [pr]  ->  pr
         prs'  ->  Comp n_SL prs'

     ppSL sCP d p []   = sCP p 0 unit
     ppSL sCP d p [pr] = sCP p 1 pr
     ppSL sCP d p prs
      = paren p precSL
          $ ppopen (pad n_SL)
          $ ppwalk 1 (sCP precSL) prs

     simpSL d prs  = psLattice d (n_SL++"-simplify") mkSL zero unit prs

   in ( mkSL
      , entry n_SL $ PredEntry subAny ppSL [] noDefn simpSL )
\end{code}


\newpage
\subsubsection{Lattice Simplification}~

Given associative binary operator $\otimes$ with zero $0$ and unit $1$
this embodies the following laws:
\RLEQNS{
   0 \otimes x & = 0 = & x \otimes 0
\\ 1 \otimes x & = x = & x \otimes 1
\\ \bigotimes_{i \in \setof{1}} x_i &=& x_1
}
\begin{code}
psLattice :: Dict
          -> String             -- op. name
          -> ([Pred] -> Pred)   -- op. builder
          -> Pred               -- zero
          -> Pred               -- unit
          -> [Pred]             -- op. arguments
          -> RWResult
psLattice d tag op zero unit prs
 = ret $ simpL [] prs
 where

   simpL srp [] = reverse srp
   simpL srp (pr:prs)
    | pr == zero  =  [zero]
    | pr == unit  =  simpL     srp  prs
    | otherwise   =  simpL (pr:srp) prs

   ret []          =  Just (tag, unit, diff )
   ret [pr]        =  Just (tag, pr, diff )
   ret prs'
    | prs' == prs  =  Nothing
    | null prs'    =  Just (tag, unit, diff )
    | otherwise    =  Just (tag, op prs', diff )
\end{code}

\begin{code}
popSemiLattice :: String
              -> Pred
              -> Pred
              -> Int
              -> ( [Pred] -> Pred
                 , Dict)
popSemiLattice = pSemiLMk mkAssocPs
\end{code}
Now, some commutative/idempotent variants:
\begin{code}
popSemiLatticeA = pSemiLMk mkCommAssocPs
popSemiLatticeAI = pSemiLMk mkIdemCommAssocPs
\end{code}

\newpage
\subsection{Expression Abstractions}

\subsubsection{Binary Operators}

\begin{code}
opNonAssoc :: String                  -- dictionary name
           -> String                  -- infix symbol
           -> ( Expr -> Expr -> Expr  -- op builder
              , Dict )                -- dictionary entry
opNonAssoc nm op
 = ( mkOp, entryOp )
 where
   mkOp e1 e2 =  App nm [e1,e2]

   ppOp d [e1,e2] = "("++edshow d e1++op++edshow d e2++")"
   ppOp _ _ = "[invalid-"++op++"]"

   entryOp
    = entry nm $ ExprEntry subAny ppOp noDefn noEval noEq
\end{code}

\newpage
\subsection{Smart Builders}

\subsubsection{Associative Flattening }~

First, building a flattened associative list:
\begin{code}
mkAssoc :: (t -> Bool) -> (t -> [t]) -> [t] -> [t] -> [t]
mkAssoc isOp subt st [] = reverse st
mkAssoc isOp subt st (t:ts)
 | isOp t = mkAssoc isOp subt (reverse (subt t)++st) ts
 | otherwise  = mkAssoc isOp subt (t:st) ts

mkAssocP :: MkPredOp
mkAssocP op isOp = Comp op . mkAssoc isOp predPrs []

mkAssocPs :: (Pred -> Bool) -> [Pred] -> [Pred]
mkAssocPs isOp = mkAssoc isOp predPrs []

predPrs :: Pred -> [Pred]
predPrs (Comp _ prs) = prs  ;  predPrs _ = []
\end{code}

\subsubsection{Commutative Ordering }~

This allows us to sort a list of terms
\begin{code}
mkComm :: Ord t => [t] -> [t]
mkComm = sort
\end{code}

\subsubsection{Idempotent Duplicate Removal}~

Remove duplicates --- we assume list is sorted
\begin{code}
mkIdem :: Eq t => [t] -> [t]
mkIdem (t:ts@(t':_))
 | t == t' = mkIdem ts
 | otherwise  =  t : mkIdem ts
mkIdem ts = ts
\end{code}

\subsubsection{Mixing and Matching}

Commutativity and Associativity
\begin{code}
mkCommAssocPs isOp = mkComm . mkAssocPs isOp
mkCommAssocP :: MkPredOp
mkCommAssocP op isOp = Comp op . mkCommAssocPs isOp
\end{code}

Idempotency, Commutativity and Associativity
\begin{code}
mkIdemCommAssocPs isOp = mkIdem . mkComm . mkAssocPs isOp
mkIdemCommAssocP :: MkPredOp
mkIdemCommAssocP op isOp = Comp op . mkIdemCommAssocPs isOp
\end{code}
