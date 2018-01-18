% $Id: FSets.lhs,v 1.2 2002/04/12 22:49:12 marku Exp $
%
\documentstyle[12pt,a4,z-eves,haskell]{article}
\parindent 0pt
\parskip 1.5ex plus 1pt
\oddsidemargin 0 in
\evensidemargin 0 in
\marginparwidth 0.75 in
\textwidth 6.375 true in
\newcommand{\FUNC}[1]{\subsection{#1}}

\title{A Haskell implementation of Z data types}
\author{
        Mark Utting \\
        Software Verification Research Centre \\
        University of Queensland \\
        St. Lucia, QLD 4072 \\
        AUSTRALIA \\[1ex]
        Email: {\tt marku@cs.uq.edu.au} \\
        Phone: +61 7 365 1653
       }
\date{}
\begin{document}
\maketitle

This report describes a Haskell~\cite{haskell-1.2} module that
implements finite versions of the set, relation and function types
from Z \cite{hayes:spec-case-studies} \cite{spivey:z-notation}.
It uses the literate script convention, where each executable
Haskell line begins with a \verb.>. character.

\begin{haskell*}

> module FiniteSets
>  ( Set, 
>      set, emptyset, union, inter, diff, gen_union, gen_inter,
>      mem, not_mem, subset, psubset, disjoint, 
>      card, set2list, powerset, upto, set_from_ordered_list,
>    Pairable,
>      is_pair, pair_fst, pair_snd, haskell_pair,
>    Reln(..),
>      reln, dom, ran, domres, domsub, ranres, ransub,
>      semi, inverse, image, identity, iter, transclosure,
>    Func(..),
>      func, is_func, is_injective, fapply, fdefapply,
>      fovr, funion, fclash,
>    -- Sundry useful functions
>      merge, mergesort, while, remdups, implies, iff
>  )
> where
>
> infixr 1 `implies`
> infixr 0 `iff`

\end{haskell*}

\section{Finite Sets: ({\tt Set a})}

This finite set type is derived from page 228 of Bird and
Wadler~\cite{bird:intro-to-func-prog}. 
However, several functions are renamed and many functions are added so that
all of the set operations of Z are supported.  Table \ref{table-set-ops}
shows the relationship between Z set operators and the corresponding
functions defined in this module
($S$ and $T$ stand for arbitrary (finite) set expressions and $X$
stands for a (possibly infinite) Haskell type or its Z equivalent).
Note that functions such as \verb.union.,
\verb.inter. and \verb.in. are typically used as infix functions ({\em
e.g.}, \verb.a `mem` xs.).

\begin{table}
\begin{center}
\begin{tabular}{|c|c|}
\hline
  Z expression          & Haskell expression  \\
\hline
\hline
  $\finset X$           & \verb.Set X. \\
  $\power S$            & \verb.powerset S. \\
  $\power_1 S$          & \verb.powerset S `diff` set []. \\
  $A \upto B$           & \verb.A `upto` B. \\
  $S = T$               & \verb.S == T. \\
  $S \neq T$            & \verb.S /= T. \\
  $S \in T$             & \verb.S `mem` T. \\
  $S \not\in T$         & \verb.S `not_mem` T. \\
  $\{\,\}$              & \verb.emptyset. or \verb.set []. \\
  $\{a,b,c\}$           & \verb.set [a,b,c]. \\
  $S \subseteq T$       & \verb.S `subset` T. \\
  $S \subset T$         & \verb.S `psubset` T. \\
  $S \cup T$            & \verb.S `union` T. \\
  $S \cap T$            & \verb.S `inter` T. \\
  $S \backslash T$      & \verb.S `diff` T. \\
  $\bigcup S$           & \verb.gen_union S. \\
  $\bigcap S$           & \verb.gen_inter S. \\
  $\disjoint [S1,\ldots,Sn]$
                        & \verb.disjoint [S1,..,Sn]. \\
  $\{x:S \mid P(x) 
      \spot f(x)\}$     & \verb.set [f x | x <- set2list S, P x]. \\
\hline
\end{tabular}
\end{center}
\caption{Set expressions in Z and Haskell.}
\label{table-set-ops}
\end{table}


\subsection{Constructor Function}

The {\tt set} function constructs a set from a list of elements.
The only constraint on the input list is that it must contain
a finite number of values whose type is totally ordered
({\em i.e.}, for any two elements $a$ and $b$, either $a \le b$
or $b \le a$ must be true).
In particular, the input list may contain duplicates and
does not need to be sorted in any particular order.

In contrast, the \verb.set_from_ordered_list. function has a
precondition that its input list must be ordered in strictly
ascending order with no duplicates.
\begin{haskell*}

> emptyset     :: (Ord a) => Set a

> set          :: (Ord a) => [a] -> Set a

> set_from_ordered_list  :: (Ord a) => [a] -> Set a

\end{haskell*}


\subsection{Set Operations}

The three binary operators, {\tt union}, {\tt inter} and {\tt diff} are
the same as in Bird and Wadler, except that {\tt differ} has
been renamed to {\tt diff}.  It is recommended that they be written as
infix functions.  The {\tt gen\_union} and {\tt gen\_inter} functions return
the distributed union and intersection respectively of a finite set
of sets.  The empty set is an acceptable
argument to {\tt gen\_union} (and returns the empty set)
but the argument to {\tt gen\_inter} must contain at least one set.

\begin{haskell*}

> union        :: (Ord a) => Set a -> Set a -> Set a
> inter        :: (Ord a) => Set a -> Set a -> Set a
> diff         :: (Ord a) => Set a -> Set a -> Set a
> gen_union    :: (Ord a) => Set (Set a)    -> Set a
> gen_inter    :: (Ord a) => Set (Set a)    -> Set a

\end{haskell*}


\subsection{Predicates}

Apart from \verb.disjoint., which takes a sequence (list) of sets,
these functions are intended to be used as infix functions.
Note that \verb.disjoint [xs,ys,zs]. is equivalent to
\begin{verbatim}
    xs `inter` ys = set [] &&
    xs `inter` zs = set [] &&
    ys `inter` zs = set [] .
\end{verbatim}
\begin{haskell*}

> mem          :: (Ord a) =>     a -> Set a -> Bool
> not_mem      :: (Ord a) =>     a -> Set a -> Bool
> subset       :: (Ord a) => Set a -> Set a -> Bool
> psubset      :: (Ord a) => Set a -> Set a -> Bool
> disjoint     :: (Ord a) =>        [Set a] -> Bool

\end{haskell*}


\subsection{Sundry Functions}

The {\tt card} function gives the number of elements in a set.
The {\tt set2list} function returns a list sorted in ascending order
containing the elements of the given set, without any duplicates.
The \verb.powerset. function returns the set of all subsets of
a given set.
\begin{haskell*}

> card         :: (Ord a) => Set a -> Int
> set2list     :: (Ord a) => Set a -> [a]
> powerset     :: (Ord a) => Set a -> Set (Set a)
> upto         :: (Ord a,Enum a) => a -> a -> Set a

\end{haskell*}

The \verb.set2list. function is typically used to simulate set
comprehensions using list comprehensions.  For example, if \verb.xs.
contains a set of integers and \verb.pred. is some predicate over integers,
the Z set comprehension
\[
        \{ x \in xs | pred(x) \spot x^2 - x \}
\]
would be written in Haskell as
\begin{haskell}
    [ x^2 - x | x <- set2list xs, pred x ] .
\end{haskell}
Note that this returns a list of numbers rather than a set,
but the list can easily be converted back into a set by
using the \verb.set. function, giving
\begin{haskell}
    set [ x^2 - x | x <- set2list xs, pred x ] .
\end{haskell}

The functions defined so far cover all of the set operations defined in the
standard Z library \cite{spivey:z-notation}, except for some derived
operators (such as the non-empty power set constructor: $\power_1$) 
that are easily expressed using other functions.  


\subsection{Implementation}

Our implementation of sets uses lists sorted in ascending order
with no duplicates.
This allows the common operations to have worst case
performance of $O(N)$ in the size of the set, except for {\tt set}
which is $O(N \times \ln N)$ for unsorted input lists (but $O(N)$
for sorted input lists).
If {\tt mem} is by far the most common operation upon
sets, balanced binary trees may be a better representation.

Since the implementation assumes that elements can be totally
ordered, the element type must be an instance of the \verb.Ord.
class.  A consequence of this is that sets must also be totally
ordered, since we want to allow sets to contain sets.
However, the user will generally not be interested in this ordering
over sets (it is not the same as the subset ordering), so we
regard it as being a side effect of the current implementation rather 
than as a desired property of sets.

\begin{haskell*}

> newtype Ord a => Set a = MkSet [a] deriving (Eq,Ord)

> emptyset = MkSet []

> set xs = (MkSet . remdups . mergesort) xs

> set_from_ordered_list xs = MkSet xs

-->  | set2list(set xs) == xs = MkSet xs
-->  | otherwise             = error "set_from_ordered_list precondition broken" 

\end{haskell*}

The implementations of set union, intersection and difference are all
variations of a merge operation.  We could define union
using \verb.remdups. and \verb.merge., but give a direct
definition for symmetry with intersection and difference.
\begin{haskell*}

> union (MkSet xs) (MkSet ys) = MkSet (union_elems xs ys)
> inter (MkSet xs) (MkSet ys) = MkSet (inter_elems xs ys)
> diff  (MkSet xs) (MkSet ys) = MkSet (diff_elems xs ys)

> union_elems [] ys      = ys
> union_elems (x:xs) []  = x:xs
> union_elems (x:xs) (y:ys)  -- merge, removing duplicates
>       | x < y          = x : union_elems xs (y:ys)
>       | x == y         = x : union_elems xs ys
>       | x > y          = y : union_elems (x:xs) ys

> inter_elems [] ys      = []
> inter_elems (x:xs) []  = []
> inter_elems (x:xs) (y:ys)
>       | x < y          = inter_elems xs (y:ys)
>       | x == y         = x : inter_elems xs ys
>       | x > y          = inter_elems (x:xs) ys

> diff_elems [] ys      = []
> diff_elems (x:xs) []  = x:xs
> diff_elems (x:xs) (y:ys)
>       | x < y          = x : diff_elems xs (y:ys)
>       | x == y         = diff_elems xs ys
>       | x > y          = diff_elems (x:xs) ys

> gen_union (MkSet xs)   = foldr union (set []) xs

> gen_inter (MkSet xs)   = foldr1 inter xs

\end{haskell*}

Rather than use the standard {\tt elem} function to implement {\tt
mem} we give an implementation that takes advantage of the list being
sorted.  This means that it is only necessary to search half the list
on average.  
\begin{haskell*}

> x `mem` (MkSet xs)   = x `mem_impl` xs
> x `not_mem` xs       = not (x `mem` xs)

> x `mem_impl` []      = False
> x `mem_impl` (y:xs)
>       | x > y       = x `mem_impl` xs
>       | x == y      = True
>       | x < y       = False


> xs `subset` ys      = xs `diff` ys == set []

> xs `psubset` ys     = xs `subset` ys && xs /= ys

> disjoint xs 
>     = and [ a `inter` b == set [] 
>               | (i,a) <- numxs, (j,b) <- numxs, i < j ]
>       where
>       numxs = zip [1..] xs

\end{haskell*}

The remaining functions have simple implementations, since
our representation of sets does not contain duplicates and
is already sorted in ascending order.  Note that \verb.upto.
can avoid the overhead of sorting and removing duplicates, 
because Haskell enumeration expressions \verb![a..b]! always
generates results in strictly ascending order (this is not always 
true of \verb![a,b..c]! however).
\begin{haskell*}

> card (MkSet xs)     = length xs

> set2list (MkSet xs) = xs

> powerset (MkSet xs) = set (map set (powset xs))
>      where powset []     = [[]]
>            powset (x:xs) = [ x:ys | ys <- powxs ] ++ powxs
>                            where powxs = powset xs

> upto a b = MkSet [a..b]

\end{haskell*}

The following definitions 
allow sets to be printed and parsed as \verb.{a, b, c}..
They are taken from the VDM \verb.SetMap. module by
Nick North (email: \verb|ndn@seg.npl.co.uk|); available
by anonymous ftp from \verb|ftp.dcs.glasgow.ac.uk|.
If you don't like the syntax, you can change the brackets and the
item separator by changing the following three constants.
\begin{haskell*}

> smb    =  "{"
> sme    =  "}"
> smsep  =  ","
> instance (Ord a, Show a) => Show (Set a) where
>    showsPrec d (MkSet [])      =  showString smb . showString sme
>    showsPrec d (MkSet (x:xs))  =
>        showString smb . shows x . foldr g (showString sme) xs
>       where
>       g x' s  =  showString (smsep ++ " ") . shows x' . s
>
> instance (Ord a, Read a) => Read (Set a) where
>    readsPrec p  =
>       readParen False
>           (\r -> [(set xs, t) | (tok,s) <- lex r, tok == smb,
>                                      (xs,t)  <- readset s])
>       where
>       readset s  = [([],t)   | (tok,t) <- lex s, tok == sme] ++
>                    [(x:xs,u) | (x,t)   <- reads s, (xs,u) <- readrest t]
>       readrest s = [([],t)   | (tok,t) <- lex s, tok == sme] ++
>                    [(x:xs,v) | (tok,t) <- lex s, tok == smsep,
>                                (x,u)   <- reads t,
>                                (xs,v)  <- readrest u]

\end{haskell*}



\section{Finite Relations: ({\tt Reln a b})}

As in Z, we model relations as a set of pairs.  Since we
want all the set operations to be directly applicable to relations,
we define the \verb.Reln. type as a synonym for the type of
finite sets that contain pairs.  In fact, the elements need not be
Haskell pairs, but must be instances of the verb.Pairable. class.
The \verb.reln. function
constructs a relation from a list of pairs.  It is similar
to the set constructor, but has a stronger precondition: all
elements must be pairs.
\begin{haskell*}

> class Ord p => Pairable p where
>     is_pair      :: p -> Bool
>     pair_fst     :: Ord a => p -> a    -- Precondition: is_pair
>     pair_snd     :: Ord b => p -> b    -- Precondition: is_pair
>     make_pair    :: (Ord a, Ord b) => a -> b -> p

> instance (Ord a, Ord b) => Pairable (a,b) where
>     is_pair  (a,b) = True
>     pair_fst (a,b) = a
>     pair_snd (a,b) = b
>     make_pair a b  = (a,b)

> newtype Pairable p => Reln p = Reln [p]  -- sorted with no dups

> reln  :: (Pairable p, Ord a, Ord b) => [(a,b)]  -> Reln p
> reln  = Reln . map (uncurry make_pair) . remdups . mergesort

> reln2list :: (Pairable p) => Reln p -> [p]
> reln2list (Reln ps) = ps

\end{haskell*}

\begin{table}
\begin{center}
\begin{tabular}{|c|c|}
\hline
  Z expression          & Haskell expression  \\
\hline
\hline
  $X \rel X'$           & \verb.Reln X X'. \\
  $\{ (a,1), (b,2) \}$
                        & \verb.set [(a,1), (b,2)]. \\
  $\dom R$              & \verb.dom R. \\
  $\ran R$              & \verb.ran R. \\
  $S \dres R$           & \verb.S `domres` R. \\
  $S \ndres R$          & \verb.S `domsub` R. \\
  $R \rres S$           & \verb.R `ranres` S. \\
  $R \nrres S$          & \verb.R `ransub` S. \\
  $R \comp R'$          & \verb.R `semi` R'. \\
  $R \limg S \rimg$     & \verb.R `image` S. \\
  $R\inv$               & \verb.inverse R. \\
  $\id$                 & \verb.identity S. \\
  $R^k$                 & \verb.R `iter` k. \\
  $R\plus$              & \verb.transclosure R. \\
%  $R\star$              & \verb.transclosure R `union` identity S.
%                                \footnote{Where S is the base set
%                                          over which R is defined.} \\
\hline
\end{tabular}
\end{center}
\caption{Relation expressions in Z and Haskell.}
\label{table-reln-ops}
\end{table}

We can now define the following operators on relations.
The relationship between the Z operator names and the
names used here is shown in table \ref{table-reln-ops}.
Note that \verb.dom. is short for {\em domain} and 
\verb.ran. is short for {\em range}.
Be warned that \verb.iter. only accepts iterations of one
or greater, because zero generates the identity relation
(see \verb.identity.) and we cannot do this unless we know
the complete underlying set of the given relation (and that it is finite).
\begin{haskell*}

> dom          :: (Pairable p, Ord a) => Reln p -> Set a
> ran          :: (Pairable p, Ord b) => Reln p -> Set b
> domres       :: (Pairable p, Ord a) => Set a  -> Reln p   -> Reln p
> domsub       :: (Pairable p, Ord a) => Set a  -> Reln p   -> Reln p
> ranres       :: (Pairable p, Ord b) => Reln p -> Set b    -> Reln p
> ransub       :: (Pairable p, Ord b) => Reln p -> Set b    -> Reln p
> semi         :: (Pairable p, Pairable p2,
>                  Pairable p3)       => Reln p -> Reln p2  -> Reln p3
> image        :: (Pairable p, Ord a, Ord b) => Reln p -> Set a -> Set b
> inverse      :: (Pairable p, Pairable p2) => Reln p   -> Reln p2
> identity     :: (Pairable p, Ord a) => Set a    -> Reln p
> iter         :: (Pairable p) => Reln p -> Int      -> Reln p
> transclosure :: (Pairable p) =>           Reln p   -> Reln p

\end{haskell*}

\subsection{Implementation}

The implementation of \verb.dom. and \verb.ran. is a direct
translation of the usual set comprehension definition.
\begin{haskell*}

> dom = set . map pair_fst . reln2list
> ran = set . map pair_snd . reln2list

\end{haskell*}

The following implementations of domain and range restriction
and subtraction have complexity $O(\#rs \times \#s)$, which
could be improved considerably by taking advantage of ordering.

\begin{haskell*}

> domres s rs = Reln[p | p <- reln2list rs, pair_fst p `mem` s]
> ranres rs s = Reln[p | p <- reln2list rs, pair_snd p `mem` s]
> domsub s rs = Reln[p | p <- reln2list rs, pair_fst p `not_mem` s]
> ransub rs s = Reln[p | p <- reln2list rs, pair_snd p `not_mem` s]

\end{haskell*}

The simple implementation of \verb.semi. (called \verb.semi_spec.) has
complexity $O(\#xs \times \#ys)$.  The more sophisticated implementation
that is used for the exported \verb.semi. takes the inverse of the first
relation then does a single pass which calculates the cartesian product
wherever the domains intersect.  The worst case complexity of this
implementation is the same as for \verb.semi_spec., but the average case is
much better.

\begin{haskell*}

> semi_spec (MkSet xs) (MkSet ys)
>    = set [ (x,y') | (x,x') <- xs, (y,y') <- ys, x' == y ]

> semi xs (MkSet ys) = set (match xs' ys)
>    where
>    MkSet xs' = inverse xs
>    match [] _ = []
>    match _ [] = []
>    match xs@((x,x'):xtail) ys@((y,y'):ytail)
>        | x < y  = match xtail ys
>        | x > y  = match xs ytail
>        | x == y = [(a,b) | a <- x':map snd eqx, b <- y':map snd eqy]
>                   ++ match neqx neqy
>                   where
>                   (eqx,neqx) = span (\p -> fst p == x) xtail
>                   (eqy,neqy) = span (\p -> fst p == y) ytail

\end{haskell*}

Disregarding the $O(N \times \ln(N))$ overhead for turning a list
into a set, the implementation of \verb.inverse. has complexity
$O(\#rs)$, whereas that of \verb.image. is $O(\#rs \times \#s)$.
However, \verb.image. could be $O(\#rs + \#s)$ if
we used an intersection-like algorithm.
\begin{haskell*}

> image rs s = set [ y | (x,y) <- set2list rs, x `mem` s]

> inverse rs = reln[(pair_snd p, pair_fst p) | p <- reln2list rs]

\end{haskell*}

The remaining functions compose a relation with itself various
numbers of times (zero for \verb.identity., a given number for
\verb.iter. and one or more for \verb.transclosure.).

\begin{haskell*}

> identity s    = set [(x,x) | x <- set2list s]

> iter rs 1     = rs
> iter rs (k+1) = rs `semi` iter rs k

> transclosure rs = grow rs rs
>     where 
>     grow orig curr
>         = if new == set []
>           then curr
>           else grow orig (curr `union` new)
>           where new = (orig `semi` curr) `diff` curr

\end{haskell*}


\section{Finite Functions: ({\tt Func a b})}
% ==========================================

Functions are a special case of relations, so
all the relation and set operators are applicable to functions
(though the result may be a relation rather than a function).

Since functions are already available in Haskell, one could ask why it is
useful to provide an ADT that represents functions explicitly?  The
advantage of representing functions as data structures is that it becomes
possible to perform operations such as calculating the domain and 
range of a function, test two functions for equality and print
the definition of a function.  The disadvantage is that we can only
usefully represent finite functions.

The following definitions define \verb.Func. as a synonym for
\verb.Reln., to make programs more readable.  The \verb.is_func.
predicate tests a relation to determine if it is in fact a
function.  The \verb.is_injective. predicate tests a relation
to see if it is a one-to-one function.  The \verb.func. operation
constructs a function from a list of pairs---it is identical to
\verb.reln., but generates an error message if the result is not a
function. 

\begin{haskell*}

> newtype Pairable p => Func p = Func p

> is_func      :: Reln p -> Bool
> is_func rs = card (dom rs) == card rs

> is_injective :: Reln p -> Bool
> is_injective rs = is_func rs && card (ran rs) == card rs

> func :: Pairable p => [(a,b)] -> Func p
> func ps
>    = if is_func rs 
>      then rs 
>      else error "func: list contains duplicate domain elements."
>      where rs = reln ps

\end{haskell*}


\subsection{Finite Function Operations}

Application of a function to a value is performed by the {\tt fapply}
function.  The given value must be in the domain of the function.
Alternatively, if you call {\tt fdefapply} you can supply an additional
default value that will be returned if the function argument is not in the
domain of the function.

% This can
% easily be tested by calling {\tt in\_dom}, which is equivalent to
% testing for membership in the domain of a function, but is provided
% directly because it is such a common operation.  

The {\tt fovr} and {\tt funion} operators (usually written infix) combine
two functions into one.  The difference is that {\tt funion} requires the
two argument functions to agree wherever their domains intersect, whereas
{\tt fovr} ({\em function override}) combines any two functions and gives
priority to the {\em second} function whenever a common domain value
appears in both inputs.  Note that \verb.funion. has exactly the same
effect as \verb.union., except that it raises an error if the resulting
relation is not a function.

The {\tt fclash} operator compares two functions
and returns the domain elements that appear in both functions but are
mapped to different range elements.  So, if {\tt fclash} returns an empty
set, then {\tt funion} can be safely applied.  Although the \verb.funion.,
\verb.fovr. and \verb.fclash. operations could be generalised to operate 
on relations rather than just on functions, the current implementations
assume that the inputs are functions.

\begin{haskell*}

> fapply    ::      Func p -> a -> b
> fdefapply :: b -> Func p -> a -> b
> fovr      :: Func p -> Func p -> Func p
> funion    :: Func p -> Func p -> Func p
> fclash    :: Func p -> Func p -> Set a

\end{haskell*}


\subsection{Implementation}

\begin{haskell*}

> fapply rs v
>    = fdefapply (error "fapply: argument is not in domain of function") 
>        rs v

> fdefapply def (MkSet xs) v
>    = f def xs v
>      where
>      f def [] v
>         = def
>      f def ((x,x'):xs) v
>         | v < x  = def
>         | v == x = x'
>         | v > x  = f def xs v

\end{haskell*}

The implementations of {\tt fovr} and {\tt funion} are very similar to the
implementation of set union.  The implementation
of \verb.fclash. is similar to that of set intersection.
All three operations have complexity of $O(\#xs + \#ys)$.
\begin{haskell*}

> fovr (MkSet xs) (MkSet ys) = set (fovr' xs ys)
>   where
>     fovr' [] ys          = ys
>     fovr' (x:xs) []      = x:xs
>     fovr' ((x,x'):xs) ((y,y'):ys)
>       | x < y            = (x,x') : fovr' xs ((y,y'):ys)
>       | x == y           = (y,y') : fovr' xs ys
>       | x > y            = (y,y') : fovr' ((x,x'):xs) ys

> funion (MkSet xs) (MkSet ys) = set (funion' xs ys)
>   where
>   funion' [] ys@(_:_)    = ys
>   funion' xs@(_:_) []    = xs
>   funion' ((x,x'):xs) ((y,y'):ys)
>     | x < y              = (x,x') : funion' xs ((y,y'):ys)
>     | x == y && x' == y' = (x,x') : funion' xs ys
>     | x > y              = (y,y') : funion' ((x,x'):xs) ys
>     | otherwise          = error "funion: functions clash"

> fclash (MkSet xs) (MkSet ys) = set (clash xs ys)
>   where
>   clash [] ys            = []
>   clash (x:xs) []        = []
>   clash ((x,x'):xs) ((y,y'):ys)
>     | x < y              = clash xs ((y,y'):ys)
>     | x == y && x' == y' = clash xs ys
>     | x == y && x' /= y' = x : clash xs ys
>     | x > y              = clash ((x,x'):xs) ys

\end{haskell*}


\section{Sundry Useful Functions}

\FUNC{Mergesort} 
Sorts a list into ascending order with $O(N \times \ln N)$ worst case
time, but with $O(N)$ best case performance when the list is already
ordered.  The elements in the list must come from a type which is
totally ordered.

\begin{haskell*}
 
> mergesort :: Ord a => [a] -> [a]
> mergesort xs 
>    = (head . while gt1 mergepairs . ascend_runs) xs
>      where 
>      gt1 [_] = False
>      gt1 _   = True

> merge []       ys    =  ys
> merge xs@(_:_) []    =  xs
> merge (x:xs)  (y:ys) 
>        | x < y       =  x : merge xs (y:ys)
>        | x == y      =  x : merge xs (y:ys)
>        | x > y       =  y : merge (x:xs) ys

> while :: (a -> Bool) -> (a -> a) -> a -> a
> while tst f xs
>    = if tst xs
>      then while tst f (f xs)
>      else xs

> mergepairs  :: Ord a => [[a]] -> [[a]]
> mergepairs []        = []
> mergepairs [a]       = [a]
> mergepairs (a:b:xs)  = merge a b : mergepairs xs

> ascend_runs :: Ord a => [a] -> [[a]]
> ascend_runs []       = [[]]
> ascend_runs (x:xs) = asc_runs x xs
>    where
>    asc_runs v []     = [[v]]
>    asc_runs v (x:xs)
>        | v <= x      = (v:ys) : zs
>        | v > x       = [v] : asc_runs x xs
>        where ys:zs = asc_runs x xs

\end{haskell*}

\FUNC{Remdups} 
Removes adjacent duplicates from a list.  A corollary
of this is that if the input list is sorted (in ascending or
descending order) then the output list will only contain unique
values.  
\begin{haskell*}

> remdups :: (Eq a) => [a] -> [a]
> remdups []         = []
> remdups [a]        = [a]
> remdups (a:b:as)
>   | a == b         = remdups (b:as)
>   | otherwise      = a : remdups (b:as)

\end{haskell*}

\FUNC{Logical Operators}
For ease of translating Z predicates to Haskell, we define two
Z-like logical connectives, \verb.implies. and \verb.iff..  Note that
the Z $\land$, $\lor$ and $\lnot$ operators can be translated
to the standard Haskell operators \verb.&&., \verb.||. and \verb.not.,
respectively.  Of course, the semantics of the Haskell operators
is slightly more restricted than the Z operators, since the Haskell
operators typically evaluate the left argument before the right,
so they may be undefined (i.e., not terminate) in some cases where 
the Z operators are defined.
\begin{haskell*}

> implies :: Bool -> Bool -> Bool
> implies a b = not a || b
>
> iff :: Bool -> Bool -> Bool
> iff a b = a == b

\end{haskell*}

\bibliographystyle{alpha}
\bibliography{spec,func}
\end{document}
