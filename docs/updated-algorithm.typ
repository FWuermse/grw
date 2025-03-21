#import "@preview/algo:0.3.4": algo, i, d, comment, code
#import "./template.typ": *
#import "./theme.typ": *
= Updated Algorithm <updatedalgo>

We have seen five improvements to the `Rew` algorithm for constraint and proof generation of a rewrite. We will now propose an updated algorithm that combines all mentioned optimisations. This roughly ressembles the algorithm that has evolved in the Coq core library over the last decade by combining the algorithms for leibniz-equality rewriting, rewriting under binders, generalised rewriting, and the `setoid_rewrite` module.

We call the algorithm in @subterm `Subterm` as a reference to the original name of the generalised rewriting implementation in Coq and to differenciate between the previously seen `Rew` algorithm referred to in the paper by Matthieu @sozeau:inria-00628904.

The `Subterm` algorithm has an additional argument $r$ that refers to the relation that is now passed down from the top rather than being inferred at the end. Similarly to `Rew` we first check whether the input term $t$ unifies directly and return in that case. Otherwise we follow a similar pattern matching.

We first match for function application but consider a sequence now. In practice we can differenciate nested applications and application sequences by the paranthesis. We treat the following Lean term $(((f space e_1) space  e_2) space (g space e_3))$ as an application sequence $(f) space (e_1) space (e_2) space (g space e_3)$ and only follow a recursive application call for $g space e_3$.

Under the assumption that we only obtain well-formed applications we know that the function type $f$ must be unique among the application. When $f$ has the type $alpha -> beta -> gamma$ for instance we can only apply an argument of type $alpha$ or a sequence mathing the function type. Therefore $f$ cannot occur again directly in the same sequence but only in nested applications. This implies that when $f$ directly unifies with a left hand side of a rewrite relation $rho$ we can assume that no other argument unifies. This is not the case when f occurs again nested in one or multiple arguments. In such a case we can rewrite again using the updated term $u$, infer $r$ early for $p$ combine the proofs using transitivity of $r$ which is either $<-$, $->$, or a metavariable that we assign during the proof search. More details will be covered in @Implementation.

If the rewrite does not occur in the rewrite function of the topmost application sequence we enter the default case where we create the mentioned a respectful chain for the entire sequence of the arguments. We define the `prefixIsId` and `fn` variables in lines 14 and 15 to track leading identity rewrites. In each loop iteration we update this variable until we reach an argument that can be rewritten. Up until that point we curry the arguments to `fn`. Whenever we have leading identity rewrites we also start building the updated term $u$ defined in line 15 by applying the arguments unchanged. If `prefixIsId` remains `true` we just return `identity`. 

Once we start iterating over non-identity arguments we collect the recursive proofs and carrier relation types retrieved in line 17 in the `proofs` and `types` variables of type list defined in line 13. Whenever we reach recursive identity rewrites after successfully rewriting at least one argument we create `ProperProxy` metavariables as mentioned in the last section. We explicitly extend the constraint set $Psi$ by the relation and proof metavariables of the identity rewrites. In the case of successful rewrites we already obtained the updated constraint set $Psi'$ which contains $r'$ and $p$ at this point.

Finally all collected types and proofs can be used to create a `Proper` metavariable $mono("Proper") ("types"_0 ==> dots ==> "types"_n ==> r) "fn"$. Note that $"proofs"_0$ does not neccessarily refer to the first rewrite and fn does not neccessarily refer to the $e_0$ in case there were identity rewrites. In this algorithm we also use the simplified notation of metavariable application in which we refer to the only constructor `Proper.proper`.

We mentioned cases where we cannot infer the relation and thus have to fall back on the use of `Subrelation`. This can happen in two cases. Either we do not enter any case because we immediately unify. In this case our proof is merely the input theorem $rho$. The type of $rho$ is $r space t space u$ for a rewrite relation $r$, the initial term $t$ and the output term $u$. The desired relation in @subterm is thus unused and we have to infer the implication for the final rewrite using a subrelation $mono("Subrelation") r (<-)$.

The other case where we we fail to infer (or pass down) the relation is for function rewrites on the first element of an application e.g. a rewrite on $f$ in $f space a space b space c$. As we cannot force the output type for a chain of pointwise relation proofs we have to bridge that gap with a subrelation inference in line 11 of the `Subterm` algorithm in @subterm.

#figure(
algo(
  row-gutter: 5pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type", "for", "in", "do", "foldr"),
  title: $"Subterm"_rho$,
  parameters: ($Psi$, $t$, $r$)
)[
  ($Psi'$, $r'$, $u'$, unifyable) := $"unify"_rho$($Psi$, $t$)\
  if unifyable then:#i\
    return ($Psi'$, $r'$, $u'$, $rho$)#d\
  match $t$ with\
  $|$ $e_0 dots e_n$ $=>$#i\
    ($"_"$, $"_"$, u, unifyable') := $"unify"_rho$($Psi$, $e_0$)\
    if unifyable' then:#i\
      proof := $?_"rel" : "relation" $ type($t$)\
      for $e : tau$ in $e_0 dots e_n$ do#i\
        proof := pointwiseRelation $tau$ proof#d\
      $?_s$ : Subrelation r proof\
      return ($Psi' union space ?_"rel"$, $?_"rel"$, $u space e_1 space dots space e_n$, $?_s space rho space e_1 space dots space e_n$)#d\
    types, proofs := {}\
    prefixIsId := true\
    fn, u := $e_0$\
    for $e : tau$ in $e_0 dots e_n$ do#i\
      $(Psi', "result")$ := $"Subterm"_rho$($Psi$, $e$, $?_r : "relation" tau$)\
      if prefixIsId then#i\
        if $"result" = "identity"$#i\
          fn := fn e\
          u := u e\
          continue#d\
        else#i\
          prefixIsId := false#d#d\
    match result with\
    $|$ identity $=>$#i\
      $Psi$ := $Psi union {?_r : "relation" tau, ?_p : "ProperProxy" tau space ?_r t}$\
      types := types ++ ${?_r}$\
      proofs := proofs ++ ${?_p}$\
      u := u e#d\
    $|$ success ($r'$, $u'$, $p$) $=>$#i\
      $Psi$ := $Psi union Psi'$\
      types := types ++ $r'$\
      proofs := proofs ++ $p$\
      u := u u'#d#d\
    if pprefixIsId then#i\
      return ($Psi$, identity)#d\
    $?_p$ := Proper ($"types"_0 ==> dots ==> "types"_n ==> r$) fn\
    return ($Psi$, success ($r$, $u$, $?_p "proofs"_0 dots "proofs"_n$))#d\
$|$ $lambda$ x : $tau$. b $=>$#i\
  ($Psi'$, success ($r$, $u$, $p$)) := #smallcaps($"Rew"_rho$)$(Psi, b, r)$\
  return ($Psi'$, pointwiseRelation $tau$ $r$, $lambda$ x : $tau$. u, $lambda$ x : $tau$. p)#d\
$|$ $forall x : tau, b$ $=>$#i\
  ($Psi'$, $r$, $u$, unifyable) := $"unify*"_rho$($Psi$, $b$)\
  if unifyable then:#i\
    return ($Psi'$, $r$, $u$, $rho$)#d\
  ($Psi'$, success ($r'$, $"all" (lambda x : tau. b')$, $p$)) := #smallcaps($"Rew"_rho$)$(Psi, "all" (lambda x : tau. b), r)$\
  return ($Psi'$, $r'$, $forall$ x : $tau$, $b'$, $p$)#d\
$|$ $sigma -> tau$ $=>$#i\
  ($Psi'$, success ($r$, $"impl" sigma' space tau'$, $p$)) := #smallcaps($"Rew"_rho$)$(Psi, "impl" sigma space tau, r)$\
  return ($Psi'$, $r$, $sigma' -> tau'$, $p$)#d\
$|$ t' $=>$#i\
  return ($Psi$, identity)
], caption: [Improved Algorithm for Genralised Rewriting.]) <subterm>