#import "@preview/algo:0.3.4": algo, i, d, comment, code
#import "./template.typ": *
#import "./theme.typ": *
#import "./graph.typ": *
= Updated Algorithm <updatedalgo>

We have seen five improvements to the `Rew` algorithm for constraint and proof generation of a rewrite. We will now propose an updated algorithm that combines all mentioned optimisations. This roughly ressembles the algorithm that has evolved in the Coq core library over the last decade by combining the algorithms for Leibniz Equality rewriting, rewriting under binders, generalised rewriting, and the `setoid_rewrite` module.

We call the algorithm in @subterm `Subterm` as a reference to the original name of the generalised rewriting implementation in Coq and to differenciate between the previously seen `Rew` algorithm.

The `Subterm` algorithm has an additional argument $r$ that refers to the relation that is now passed down from the top rather than being inferred at the end. Similarly to `Rew`, we first check whether the input term $t$ unifies directly and return in that case. Otherwise, we follow a similar pattern matching approach.

We first match for function application but consider a sequence now. In practice, we can differenciate nested applications and application sequences by the semantic paranthesis. We treat the following Lean term $((((f space e_1) space  e_2) space (g space e_3)) space e_4)$ as an application sequence $(f) space (e_1) space (e_2) space (g space e_3) space (e_4)$ and only follow a recursive application call for $g space e_3$.

Under the assumption that we only obtain well-formed applications, we know that the function type $f$ must be unique among the application. When $f$ has the type $alpha -> beta -> gamma$ for instance, we can only apply an argument of type $alpha$ or a sequence matching the function type. Therefore, $f$ cannot occur again directly in the same sequence but only in nested applications. This implies that when $f$ directly unifies with a left-hand side of a rewrite relation $rho$, we can assume that no other argument directly unifies. This is not the case when f occurs again nested in one or multiple arguments. In such a case, we can rewrite again using the updated term $u$, infer $r$ early for $p$, and combine the proofs using transitivity of $r$ which is either $<-$, $->$, or a metavariable that we assign during the proof search. We will cover more details about this edge-case in @Implementation.

If the rewrite does not occur in the rewrite function of the topmost application sequence, we enter the default case where we create the mentioned respectful chain for the entire sequence of the arguments. We define the `prefixIsId` and `fn` variables in lines 14 and 15 to track leading identity rewrites. In each loop iteration, we update this variable until we reach an argument that can be rewritten. Up until that point, we curry the arguments to `fn`. Whenever we have leading identity rewrites, we also start building the updated term $u$, defined in line 15, by applying the arguments unchanged. If `prefixIsId` remains `true`, we just return `identity` for the entire sequence. 

Once we start iterating over non-identity arguments, we collect the recursive proofs and carrier relation types retrieved in line 17 in the variables named `proofs` and `types`. Both of those variables in line 13 represent lists. Whenever we reach recursive identity rewrites after successfully rewriting at least one argument, we create `ProperProxy` metavariables as mentioned in the last section. We explicitly extend the constraint set $Psi$ by the relation and proof metavariables of the identity rewrites. In the case of successful rewrites, we already obtained the updated constraint set $Psi'$ which contains $r'$ and $p$ at this point.

Finally, all collected types and proofs can be applied to the `Proper` metavariable $?p : mono("Proper") ("types"_0 ==> dots ==> "types"_n ==> r) mono("fn")$ to generate the rewrite proof. Note that $mono("proofs")_0$ does not neccessarily refer to the first rewrite, and `fn` does not neccessarily refer to the $e_0$ in case there were identity rewrites. In this algorithm, we also use the simplified notation of metavariable application in which we refer to the only constructor `Proper.proper`.

We mentioned cases where we cannot infer the relation and thus have to fall back on the use of `Subrelation`. This can happen in two cases. The first case is when we do not enter any match-arm because we immediately unify. In this case, our proof is merely the input theorem $rho$. The type of $rho$ is $r space t space u$ for a rewrite relation $r$, the initial term $t$, and the output term $u$. The desired relation in @subterm is thus unused, and we have to infer the implication for the final rewrite using a subrelation $mono("Subrelation") r space (<-)$.

The other case where we we fail to infer (or pass down) the relation is for function rewrites on the first element of an application e.g. a rewrite on $f$ in $f space a space b space c$. As we cannot force the output type for a chain of pointwise-relation proofs, we have to bridge that gap with a subrelation inference in line 11 of the `Subterm` algorithm in @subterm.

#figure(
algo(
  row-gutter: 5pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type", "for", "in", "do", "foldr", "mvar", "hyp"),
  title: $"Subterm"_rho$,
  parameters: ($t$, $r$)
)[
  ($Psi'$, $r'$, $u'$, unifiable) := $"unify"_rho$($t$)\
  if unifiable then:#i\
    return ($Psi'$, $r'$, $u'$, $rho$)#d\
  match $t$ with\
  $|$ $e_0 dots e_n$ $=>$#i\
    ($Psi'$, $"_"$, u, unifiable') := $"unify"_rho$($e_0$)\
    if unifiable' then:#i\
      proof := $?_"rel" : "relation" $ type($t$)\
      for $e : tau$ in $e_0 dots e_n$ do#i\
        proof := pointwiseRelation $tau$ proof#d\
      $?_s$ := mvar(Subrelation r proof)\
      return ($Psi' union space {?_s, ?_"rel"$}, $?_"rel"$, $u space e_1 space dots space e_n$, $?_s space rho space e_1 space dots space e_n$)#d\
    types, proofs := {}\
    prefixIsId := true\
    fn, u := $e_0$\
    for $e : tau$ in $e_0 dots e_n$ do#i\
      $(Psi', "result")$ := $"Subterm"_rho$($e$, mvar($"relation" tau$))\
      if prefixIsId then#i\
        if $"result" = "identity"$#i\
          fn := fn e\
          u := u e\
          continue#d\
        else#i\
          prefixIsId := false#d#d\
    match result with\
    $|$ identity $=>$#i\
      $?_r$ := mvar(relation $tau$)\
      $?_p$ := mvar($"ProperProxy" tau space ?_r t$)\
      $Psi$ := $Psi union {?_r, ?_p}$\
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
    $?_p$ := mvar(Proper ($"types"_0 ==> dots ==> "types"_n ==> r$) fn)\
    return ($Psi$, success ($r$, $u$, $?_p "proofs"_0 dots "proofs"_n$))#d\
$|$ $lambda$ x : $tau$. b $=>$#i\
  hyp(x)\
  ($Psi'$, success ($r$, $u$, $p$)) := #smallcaps($"Rew"_rho$)$(Psi, b, r)$\
  return ($Psi'$, pointwiseRelation $tau$ $r$, $lambda$ x : $tau$. u, $lambda$ x : $tau$. p)#d\
$|$ $forall x : tau, b$ $=>$#i\
  ($Psi'$, $r$, $u$, unifiable) := $"unify*"_rho$($Psi$, $b$)\
  if unifiable then:#i\
    return ($Psi'$, $r$, $u$, $rho$)#d\
  ($Psi'$, success ($r'$, $"all" (lambda x : tau. b')$, $p$)) := #smallcaps($"Rew"_rho$)$(Psi, "all" (lambda x : tau. b), r)$\
  return ($Psi'$, $r'$, $forall$ x : $tau$, $b'$, $p$)#d\
$|$ $sigma -> tau$ $=>$#i\
  ($Psi'$, success ($r$, $"impl" sigma' space tau'$, $p$)) := #smallcaps($"Rew"_rho$)$(Psi, "impl" sigma space tau, r)$\
  return ($Psi'$, $r$, $sigma' -> tau'$, $p$)#d\
$|$ t' $=>$#i\
  return ($Psi$, identity)
], caption: [Improved Algorithm for Genralised Rewriting.]) <subterm>

We have to adjust the algorithm for relation inference slightly to handle both algorithms. We introduce the new sum type `RewriteResult` with the constructors `identity` and `success`. The `success` constructor holds the same tuple as seen in the `Rew` output and the `identity` constructor holds no further information. The modified version in @infersubp matches for those two constructors and infers the relation only if neccessary.

#figure(
algo(
  row-gutter: 5pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type"),
  title: $"InferRel"$,
  parameters: ($"res" : mono("RewriteResult")$, $t : "Prop"$)
)[
  match res with\
  $|$ `identity` $=>$#i\ return (`impl_self` : $t <- t$)#d\
  $|$ `success` ($Psi$, $r$, $u$, $p$) $=>$#i\
  if r == ($<-$) then#i\ 
    return p#d\
  else#i\
    ?s : Subrelation r ($<-$)\
    return ?s t u p
], caption: [Modified algorithm for relation inference.]) <infersubp>

Let us observe the invocation graph and the generated constraints, similar to what we have seen earlier, for the updated version of the algorithm. In order to highlight the optimisation for leading identity rewrites, we change the example from $(p -> q) and (p -> q)$ to $(q -> p) and (q -> p)$. This has no effect on the original `Rew` algorithm because the number of recursive calls and the amount of generated constraints would not be different. Thus, this example is still suited for a comparison.

When invoking $mono("Subterm")_h (emptyset, (q -> p) and (q -> p), (<-))$, we now explicitly ask for a proof of $t <- u$. The tree in @calltreelongexample2 only has a maximum depth of three now compared to six for the previous example graph in @calltreelongexample. The proofs in each level also look smaller because the metavariables $?p 1$, $?p 2$, and $?p 3$ are of more expressive `Proper` types.

Leading identity rewrites occur in both sub-branches of the main invocation so that $?p 1$ and $?p 2$ both shrink and curry the unchanged term. This results in fewer metavariables that have to be solved by a proof search afterwards. $?p 1$, for instance, could have at most six metavariables if a rewrite occurred in all three subterms. Even in that worst-case scenario, the `Rew` algorithm would result in two more (eight in total) metavariables.

We can also see that we do not need the final subrelation step as seen in @calltreelongexample because we pass the expected relation down from the start. We end up with five metavariables in this example whereas the `Rew` algorithm produces 23 metavariables. This means that the proof of the same proposition has less holes.

#figure(updatedgraph(46em), caption: [Call-Tree of $mono("Rew"_h)(emptyset, (q -> p) and (q -> p))$.]) <calltreelongexample2>