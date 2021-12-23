% $Id: FiniteSets.lhs,v 1.14 2005/02/19 16:00:50 marku Exp $
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
>  ( FinSet,
>      set, emptyset, union, inter, diff, gen_union, gen_inter,
>      mem, not_mem, subset, psubset, disjoint,
>      card, set2list, powerset, set_from_ordered_list,
>      make_zfset,   -- returns a ZExpr  (either ZFSet or ZSetDisplay)
>    FinReln,
>      reln, is_reln, dom, ran, domres, domsub, ranres, ransub,
>      semi, inverse, image, identity, iter, transclosure, override,
>    FinFunc,
>      func, is_func, is_injective, fapply, ferrapply,
>      funion, fclash,
>    -- Sundry useful functions
>      is_seq,
>      merge, mergesort, while, remdups
>  )
> where
>
> import AST    -- defines the ZValues type (members of FinSet).

\end{haskell*}

\section{Finite Sets: ({\tt FinSet})}

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
  $\power S$            & \verb.powerset S. \\
  $\power_1 S$          & \verb.powerset S `diff` set [set []]. \\
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

The {\tt set} function constructs a set from a finite list of elements.
The input list may contain duplicates and
does not need to be sorted in any particular order.

In contrast, the \verb.set_from_ordered_list. function has a
precondition that its input list must be ordered in strictly
ascending order with no duplicates.
\begin{haskell*}

> emptyset               ::             FinSet
> set                    :: [ZValue] -> FinSet
> set_from_ordered_list  :: [ZValue] -> FinSet
> make_zfset             :: [ZValue] -> ZExpr

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

> union        :: FinSet -> FinSet -> FinSet
> inter        :: FinSet -> FinSet -> FinSet
> diff         :: FinSet -> FinSet -> FinSet
> gen_union    ::         [FinSet] -> FinSet
> gen_inter    ::         [FinSet] -> FinSet

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

> mem          :: ZValue -> FinSet -> Bool
> not_mem      :: ZValue -> FinSet -> Bool
> subset       :: FinSet -> FinSet -> Bool
> psubset      :: FinSet -> FinSet -> Bool
> disjoint     ::         [FinSet] -> Bool

\end{haskell*}


\subsection{Sundry Functions}

The {\tt card} function gives the number of elements in a set.
The {\tt set2list} function returns a list sorted in ascending order
containing the elements of the given set, without any duplicates.
The \verb.powerset. function returns the set of all subsets of
a given set (\verb.powerset1. is similar, but does not include
the empty set).
\begin{haskell*}

> card         :: FinSet -> Int
> set2list     :: FinSet -> [ZValue]
> powerset     :: FinSet -> FinSet

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
with no duplicates.  In fact, \verb.FinSet. is just a type
synonym for \verb.[ZValue]., but users should not rely on this,
since it may change in the future.

Using sorted lists allows the common operations to have worst case
performance of $O(N)$ in the size of the set, except for {\tt set}
which is $O(N \times \ln N)$ for unsorted input lists (but $O(N)$
for sorted input lists).
If {\tt mem} is by far the most common operation upon
sets, balanced binary trees may be a better representation.

Since the implementation assumes that elements can be totally
ordered, \verb.ZValues. must be an instance of the \verb.Ord.
class.  A consequence of this is that sets must also be totally
ordered, since we want to allow sets to contain sets.
However, the user will generally not be interested in this ordering
over sets (it is not the same as the subset ordering), so we
regard it as being a side effect of the current implementation rather
than as a desired property of sets.

\begin{haskell*}

> assert :: Bool -> String -> a -> a
> -- assert _ _ val = val   -- uncomment this to disable asserts.
> assert True s val = val
> assert False s _  = error s


> type FinSet = [ZValue]

> emptyset = []

> set = remdups . mergesort

> set_from_ordered_list xs
>  = assert (set2list(set xs) == xs)
>           "set_from_ordered_list precondition broken"
>    xs

> make_zfset vals
>  | all isCanonical vals2 = ZFSet vals2
>  | otherwise             = ZSetDisplay vals2
>  where
>  vals2 = set vals

\end{haskell*}

The implementations of set union, intersection and difference are all
variations of a merge operation.  We could define union
using \verb.remdups. and \verb.merge., but give a direct
definition for symmetry with intersection and difference.
\begin{haskell*}

> union (xs) (ys) = (union_elems xs ys)
> inter (xs) (ys) = (inter_elems xs ys)
> diff  (xs) (ys) = (diff_elems xs ys)

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

> gen_union (xs)   = foldr union (set []) xs

> gen_inter (xs)   = foldr1 inter xs

\end{haskell*}

Rather than use the standard {\tt elem} function to implement {\tt
mem} we give an implementation that takes advantage of the list being
sorted.  This means that it is only necessary to search half the list
on average.
\begin{haskell*}

> x `mem` (xs)        = x `mem_impl` xs
> x `not_mem` xs      = not (x `mem` xs)

> x `mem_impl` []     = False
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
is already sorted in ascending order.
\begin{haskell*}

> card (xs)     = length xs

> set2list (xs) = xs

> powerset (xs) = set (map (ZFSet . set) (powset xs))
>      where powset []     = [[]]
>            powset (x:xs) = [ x:ys | ys <- powxs ] ++ powxs
>                            where powxs = powset xs

\end{haskell*}


\section{Finite Relations: ({\tt FinReln})}

As in Z, we model relations as a set of pairs.  Since we
want all the set operations to be directly applicable to relations,
we define the \verb.Reln. type as a synonym for the type of
finite sets that contain pairs.  The \verb.reln. function
constructs a relation from a list of pairs.  It is identical
to the set constructor, but is provided to make programs
more readable (it may also check that all elements are pairs).
\begin{haskell*}

> type FinReln = FinSet

> reln         :: [ZValue]  -> FinReln
> reln ps      = set ps

> is_reln      :: FinSet -> Bool
> is_reln ps   = all is_pair ps

\end{haskell*}

\begin{table}
\begin{center}
\begin{tabular}{|c|c|}
\hline
  Z expression          & Haskell expression  \\
\hline
\hline
  $\{ (a,1), (b,2) \}$
			& \verb.reln [(a,1), (b,2)]. \\
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

> dom          :: FinReln -> FinSet
> ran          :: FinReln -> FinSet
> domres       :: FinSet  -> FinReln -> FinReln
> domsub       :: FinSet  -> FinReln -> FinReln
> ranres       :: FinReln -> FinSet  -> FinReln
> ransub       :: FinReln -> FinSet  -> FinReln
> semi         :: FinReln -> FinReln -> FinReln
> image        :: FinReln -> FinSet  -> FinSet
> inverse      ::            FinReln -> FinReln
> identity     ::            FinSet  -> FinReln
> iter         :: FinReln -> Int     -> FinReln
> transclosure ::            FinReln -> FinReln
> override     :: FinReln -> FinReln -> FinReln

\end{haskell*}

\subsection{Implementation}

The implementation of \verb.dom. and \verb.ran. is a direct
translation of the usual set comprehension definition.
\begin{haskell*}

> dom rs = set [ x | ZTuple [x,y] <- set2list rs ]
> ran rs = set [ y | ZTuple [x,y] <- set2list rs ]

\end{haskell*}

The following implementations of domain and range restriction
and subtraction have complexity $O(\#rs \times \#s)$, which
could be improved considerably by taking advantage of ordering.

\begin{haskell*}

> domres s rs = set [p | p@(ZTuple [x,y]) <- set2list rs, x `mem` s]
> ranres rs s = set [p | p@(ZTuple [x,y]) <- set2list rs, y `mem` s]
> domsub s rs = set [p | p@(ZTuple [x,y]) <- set2list rs, x `not_mem` s]
> ransub rs s = set [p | p@(ZTuple [x,y]) <- set2list rs, y `not_mem` s]

\end{haskell*}

The simple implementation of \verb.semi. (called \verb.semi_spec.) has
complexity $O(\#xs \times \#ys)$.  The more sophisticated implementation
that is used for the exported \verb.semi. takes the inverse of the first
relation then does a single pass which calculates the cartesian product
wherever the domains intersect.  The worst case complexity of this
implementation is the same as for \verb.semi_spec., but the average case is
much better.

\begin{haskell*}

> semi_spec (xs) (ys)
>    = set [ ZTuple[x,y'] | ZTuple[x,x']<-xs, ZTuple[y,y']<-ys, x'==y ]

> semi xs (ys) = set (match xs' ys)
>    where
>    xs' = inverse xs
>    match [] _ = []
>    match _ [] = []
>    match xs@(ZTuple [x, x'] : xtail) ys@(ZTuple [y, y'] : ytail)
>        | x < y  = match xtail ys
>        | x > y  = match xs ytail
>        | x == y = [ZTuple [a, b] | a <- x':map pair_snd eqx,
>                                    b <- y':map pair_snd eqy ]
>                   ++ match neqx neqy
>                   where
>                   (eqx,neqx) = span ((== x) . pair_fst) xtail
>                   (eqy,neqy) = span ((== y) . pair_fst) ytail

\end{haskell*}

Disregarding the $O(N \times \ln(N))$ overhead for turning a list
into a set, the implementation of \verb.inverse. has complexity
$O(\#rs)$, whereas that of \verb.image. is $O(\#rs \times \#s)$.
However, \verb.image. could be $O(\#rs + \#s)$ if
we used an intersection-like algorithm.
\begin{haskell*}

> image rs s = set [ y | ZTuple [x,y] <- set2list rs, x `mem` s]

> inverse rs = set [ZTuple [y,x] | ZTuple [x,y] <- set2list rs]

\end{haskell*}

The remaining functions compose a relation with itself various
numbers of times (zero for \verb.identity., a given number for
\verb.iter. and one or more for \verb.transclosure.).

\begin{haskell*}

> identity s    = set [ZTuple [x,x] | x <- set2list s]

> iter rs 1     = rs
> iter rs k     = rs `semi` iter rs (k-1)

> transclosure rs = grow rs rs
>     where
>     grow orig curr
>         = if new == set []
>           then curr
>           else grow orig (curr `union` new)
>           where new = (orig `semi` curr) `diff` curr

> r1 `override` r2 = (dom r2 `domsub` r1) `union` r2

\end{haskell*}


\section{Finite Functions: ({\tt FinFunc})}
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

The following definitions define \verb.FinFunc. as a synonym for
\verb.FinReln., to make programs more readable.  The \verb.is_func.
predicate tests a relation to determine if it is in fact a
function.  The \verb.is_injective. predicate tests a relation
(or a set) to see if it is a one-to-one function.  The \verb.func. operation
constructs a function from a list of pairs---it is identical to
\verb.reln., but generates an error message if the result is not a
function.  Finally, \verb.is_seq. tests a relation (or a set)
to see if it is a function whose domain is contiguous integers
from 1 upwards.

\begin{haskell*}

> type FinFunc = FinReln

> is_func      :: FinSet -> Bool
> is_func rs = card (dom rs) == card rs

> is_injective :: FinSet -> Bool
> is_injective rs = is_func rs && card (ran rs) == card rs

> func :: [ZValue] -> FinFunc
> func ps
>    = assert (is_func rs) "func: list contains duplicate domain elements."
>      rs
>    where rs = reln ps

> is_seq :: FinReln -> Bool
> is_seq rs = is_seq2 1 rs
>   where
>   is_seq2 n []  = True
>   is_seq2 n (ZTuple [ZInt i, _] : rs)
>     | n==i      = is_seq2 (n+1) rs
>     | otherwise = False
>   is_seq2 _ _   = False

\end{haskell*}


\subsection{Finite Function Operations}

Application of a function to a value is performed by the {\tt fapply}
function.  The given value must be in the domain of the function.
Alternatively, if you call {\tt ferrapply} you can supply an additional
default value that will be returned if the function argument is not in the
domain of the function and a transformation function for the successful
result.

% This can
% easily be tested by calling {\tt in\_dom}, which is equivalent to
% testing for membership in the domain of a function, but is provided
% directly because it is such a common operation.

The {\tt funion} operator (usually written infix) combines
two functions into one.  It requires the
two argument functions to agree wherever their domains intersect.
In contrast, {\tt override} ({\em relation override}) combines
two relations by giving priority to the {\em second} relation
whenever a common domain value appears in both inputs.
Note that \verb.funion. has exactly the same effect as \verb.union.,
except that it raises an error if the resulting relation is not a function.

The {\tt fclash} operator compares two functions
and returns the domain elements that appear in both functions but are
mapped to different range elements.  So, if {\tt fclash} returns an empty
set, then {\tt funion} can be safely applied.

\begin{haskell*}

> fapply    ::                       FinFunc -> ZValue -> ZValue
> ferrapply :: a -> (ZValue -> a) -> FinFunc -> ZValue -> a
> funion    :: FinFunc -> FinFunc -> FinFunc
> fclash    :: FinFunc -> FinFunc -> FinSet

\end{haskell*}


\subsection{Implementation}

\begin{haskell*}

> fapply
>    = ferrapply (error "fapply: argument is not in domain of function") id

> ferrapply err f [] v = err
> ferrapply err f (ZTuple [x,y] : xs) v
>  | v < x      = err
>  | v == x     = if uniq then f y else err
>  | otherwise  = ferrapply err f xs v
>  where
>  uniq = xs==[] || pair_fst(head xs) /= v
> -- We should never find non-pair values if it is a function.
> -- But just in case, the best error we can return is 'err'.
> ferrapply err f _ _ = err

\end{haskell*}

The implementation of {\tt funion} is quite similar to the
implementation of set union.  The implementation
of \verb.fclash. is similar to that of set intersection.
Both operations have complexity of $O(\#xs + \#ys)$.
\begin{haskell*}

> funion (xs) (ys) = set (funion' xs ys)
>   where
>   funion' [] ys@(_:_)    = ys
>   funion' xs@(_:_) []    = xs
>   funion' (a@(ZTuple [x,x']):xs) (b@(ZTuple [y,y']):ys)
>     | x < y              = a : funion' xs     (b:ys)
>     | x == y && x' == y' = a : funion' xs     ys
>     | x > y              = b : funion' (a:xs) ys
>     | otherwise          = error "funion: functions clash"

> fclash (xs) (ys) = set (clash xs ys)
>   where
>   clash [] ys            = []
>   clash (x:xs) []        = []
>   clash (a@(ZTuple [x,x']):xs) (b@(ZTuple [y,y']):ys)
>     | x < y              = clash xs (b:ys)
>     | x == y && x' == y' = clash xs ys
>     | x == y && x' /= y' = x : clash xs ys
>     | x > y              = clash (a:xs) ys

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
> merge xl@(x:xs)  yl@(y:ys)
>        | x < y       =  x : merge xs yl
>        | x == y      =  x : merge xs yl
>        | x > y       =  y : merge xl ys

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

\bibliographystyle{alpha}
\bibliography{spec,func}
\end{document}
