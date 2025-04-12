#import "@preview/algo:0.3.4": algo, i, d, comment, code
#import "./template.typ": *
#import "./theme.typ": *
#import "./graph.typ": *

= Optimised Algorithm for Rewriting

We have seen five improvements to the `Rew` algorithm for constraint and proof generation of a rewrite. We will now propose an updated algorithm that combines all mentioned optimisations. This roughly resembles the algorithm that has evolved in the Coq core library over the last decade by combining the algorithms for Leibniz Equality rewriting, rewriting under binders, generalised rewriting, and the `setoid_rewrite` module.

== Improved Algorithm Specification <updatedalgo>

We call the algorithm in @subterm `ORew` as it is an optimised version of the previously seen `Rew` algorithm. The `ORew` algorithm has an additional argument $r$ that refers to the relation that is now passed down from the top rather than being inferred at the end. Similarly to `Rew`, we first check whether the input term $t$ unifies directly and return in that case. Otherwise, we follow a similar pattern matching approach.

We first match for function application but consider a sequence now. For instance, we treat the following Lean term $(mono("app") (mono("app") (mono("app") (mono("app") f space e_1) space  e_2) space (mono("app") g space e_3)) space e_4)$ as an application sequence $[(f), (e_1), (e_2), (g space e_3), (e_4)]$ and only follow a recursive application call for $(mono("app") g space e_3)$.

Under the assumption that we only obtain well-formed applications, we know that the function type $f$ must be unique among the application sequence. When $f$ has the type $alpha -> beta -> gamma$ for instance, we can only apply an argument of type $alpha$ or a sequence matching the function type. Therefore, $alpha -> beta -> gamma$ cannot be the type of any other argument in the same sequence but only the type of nested applications. This implies that when $f$ directly unifies with a left-hand side of a rewrite relation $rho$, we can assume that no other argument directly unifies.

If the rewrite does not occur in the rewrite function of the topmost application sequence, we enter the default case where we create the mentioned respectful chain for the entire sequence of the arguments. We define the `prefixIsId` and `fn` variables in lines 14 and 15 to track leading identity rewrites. In each loop iteration, we update this variable until we reach an argument that can be rewritten. Up until that point, we curry the arguments to `fn`. Whenever we have leading identity rewrites, we also start building the updated term $u$, defined in line 15, by applying the arguments unchanged. If `prefixIsId` remains `true`, we just return `identity` for the entire sequence. 

Once we start iterating over non-identity arguments, we collect the recursive proofs and carrier relation types retrieved in line 18 in the variables named `proofs` and `types`. Both of those variables in line 13 represent lists. Whenever we reach recursive identity rewrites after successfully rewriting at least one argument, we create `ProperProxy` metavariables as mentioned in the last section. We explicitly extend the constraint set $Psi$ by the relation and proof metavariables of the identity rewrites. In the case of successful rewrites, we already obtained the constraint set $Psi''$ which contains $r_i$ and $p_i$ at this point.

Finally, all collected types and proofs can be applied to the `Proper` metavariable $?p : mono("Proper") ("types[0]" ==> dots ==> "types[len(types) - 1]" ==> r) mono("fn")$ to generate the rewrite proof. Note that $mono("proofs[0]")$ does not neccessarily refer to the first rewrite, and `fn` does not neccessarily refer to the $e_0$ in case there were identity rewrites. In this algorithm, we also use the simplified notation of metavariable application in which we refer to the only constructor `Proper.proper`.

We mentioned cases where we cannot infer the relation and thus have to fall back on the use of `Subrelation`. This can happen in two cases. The first case is when we do not enter any match-arm because we immediately unify. In this case, our proof is merely the input theorem $rho$. The type of $rho$ is $r space t space u$ for a rewrite relation $r$, the initial term $t$, and the output term $u$. The desired relation in @subterm is thus unused, and we have to infer the implication for the final rewrite using a subrelation $mono("Subrelation") r space (<-)$.

The other case where we we fail to infer (or pass down) the relation is for function rewrites on the first element of an application e.g. a rewrite on $f$ in $f space a space b space c$. As we cannot force the output type for a chain of pointwise-relation proofs, we have to bridge that gap with a subrelation inference in line 11 of the `ORew` algorithm in @subterm.

#figure(
algo(
  row-gutter: 5pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type", "for", "in", "do", "foldr", "mvar", "hyp", "continue"),
  title: $"ORew"_rho$,
  parameters: ($t$, $r$)
)[
  ($Psi'$, $r'$, $u'$, unifiable) := $"unify"_rho$($t$)\
  if unifiable then:#i\
    return ($Psi'$, $r'$, $u'$, $rho$)#d\
  match $t$ with\
  $|$ $e_0 dots e_n$ $=>$#i\
    ($Psi''$, $"_"$, $u''$, $"unifiable"'$) := $"unify"_rho$($e_0$)\
    if $"unifiable"'$ then:#i\
      proof := $?_"rel" : "relation" $ type($t$)\
      for $e : tau$ in $e_0 dots e_n$ do#i\
        proof := pointwiseRelation $tau$ proof#d\
      $?_s$ := mvar(Subrelation r proof)\
      return ($Psi'' union space {?_s, ?_"rel"}$, $?_"rel"$, $u space e_1 space dots space e_n$, $?_s space rho space e_1 space dots space e_n$)#d\
    types, proofs := []\
    prefixIsId := true\
    fn, $u$ := $e_0$\
    $Psi := {}$\
    for $e_i : tau_i$ in $e_0 dots e_n$ do#i\
      $(Psi'', "result")$ := $"ORew"_rho$($e_i$, mvar($"relation" tau_i$))\
      if prefixIsId then:#i\
        if $"result" = "identity"$ then:#i\
          fn := fn $e_i$\
          $u := u space e_i$\
          continue#d\
        else#i\
          prefixIsId := false#d#d\
    match result with\
    $|$ identity $=>$#i\
      $?_r$ := mvar(relation $tau_i$)\
      $?_p$ := mvar($"ProperProxy" tau_i space ?_r t$)\
      $Psi$ := $Psi union {?_r, ?_p}$\
      types := types ++ $[?_r]$\
      proofs := proofs ++ $[?_p]$\
      $u := u space e_i$#d\
    $|$ success ($r_i$, $u_i$, $p_i$) $=>$#i\
      $Psi$ := $Psi union Psi''$\
      types := types ++ $[r_i]$\
      proofs := proofs ++ $[p_i]$\
      $u := u space u_i$#d#d\
    if pprefixIsId then:#i\
      return ($Psi$, identity)#d\
    $?_p$ := mvar(Proper ($"types[0]" ==> dots ==> "types[len(types) - 1]" ==> r$) fn)\
    return ($Psi$, success ($r$, $u$, $?_p " proofs[0]" dots "proofs[len(proofs) - 1]"$))#d\
$|$ $lambda$ x : $tau$. b $=>$#i\
  hyp(x)\
  ($Psi$, success ($r$, $u$, $p$)) := #smallcaps($"ORew"_rho$)$(b, r)$\
  return ($Psi$, pointwiseRelation $tau$ $r$, $lambda$ x : $tau$. u, $lambda$ x : $tau$. p)#d\
$|$ $forall x : tau, b$ $=>$#i\
  ($Psi$, $r$, $u$, unifiable) := $"unify*"_rho$($b$)\
  if unifiable then:#i\
    return ($Psi$, $r$, $u$, $rho$)#d\
  ($Psi$, success ($r'$, $"all" (lambda x : tau. b')$, $p$)) := #smallcaps($"ORew"_rho$)$("all" (lambda x : tau. b), r)$\
  return ($Psi$, $r'$, $forall$ x : $tau$, $b'$, $p$)#d\
$|$ $sigma -> tau$ $=>$#i\
  ($Psi$, success ($r$, $"impl" sigma' space tau'$, $p$)) := #smallcaps($"ORew"_rho$)$("impl" sigma space tau, r)$\
  return ($Psi$, $r$, $sigma' -> tau'$, $p$)#d\
$|$ t' $=>$#i\
  return ($Psi$, identity)
], caption: [Improved algorithm for rewriting.]) <subterm>

== Compatibility Corrections <compcorrections>

The algorithm presented so far presents the essence of the rewriting implementation of Coq. We mentioned that for sequences of applications where the first argument, the function $f$, unifies with the rewriting theorem we do not need to explore the remaining arguments further. Although, this is how Coq treats rewrites on functions, it is inconsistent with the `Rew` algorithm where all occurrences are replaced due to the nature of treating all applications binary. To be consistent with the `Rew` algorithm we need to make a crucial change to our `ORew` algorithm that exceeds the capabilities of Coq's implementation.

In order to rewrite the function of an application in Coq, we have to define the according subrelation, pointwise relation @sozeau:inria-00628904, and relation constraints as seen in @subterm. Consider a rewrite theorem $rho : r space f space g$. The terms $f$ and $g$ are of type $alpha -> mono("Prop") -> beta -> mono("Prop")$. Rewriting $f$ to $g$ in a term $f space a space (a = a) space b$ where $a$ is of type $alpha$ and $b$ of type $beta$, Coq's algorithm provides a proof e.g. with $(<-)$ as the desired relation for $f space a space (a = a) space b <- g space a space (a = a) space b$. In our `ORew` algorithm, we would enter the path starting at line 8 in @subterm and produce the according proof. However, when changing the term to $f space a space (f space a space (a = a) space b) space b$, Coq currently only provides a proof for $f space a space (f space a space (a = a) space b) space b <- g space a space (f space a space (a = a) space b) space b$. We can see that only the outer $f$ is rewritten by Coq's implementation, but the inner $f$ is unchanged. In the special case where $r$ is equality, Coq applies the algorithm for Leibniz Equality and replaces both occurrences of $f$.

To correct this inconsistency, we propose a modification to the so-far by Coq inspired `ORew` algorithm. When we encounter a multiple nested occurrences of a function $f$ that unifies with the left-hand side of a rewrite theorem $rho$, we can replace the first occurrence as seen in lines 7-12 in @subterm. Now the updated term $u$ contains one less occurrence of $f$, and $p$ is a proof of the rewrite over a relation $r$. Given those outputs, we can then immediately rewrite again using the updated term $u$, infer the desired relation $r$ early for $p$, and combine the proofs using transitivity of $r$.

#definition("Transitive")[
  ```lean
  class Transitive {α : Sort u} (rel : relation α) where
    trans : ∀ x y z, rel x y → rel y z → rel x z
  ```
] <TransitiveDef>

The reason we must perform a subrelation inference to the desired relation passed as argument to `ORew` immediately is to ensure that both terms are proofs over an identical relation which is required by the `Transitive` typeclass defined in @TransitiveDef that we need. When we operate on `Prop` directly, the inferred relation is either $(<-)$ or $(->)$ and therefore already transitive. In the other case, we are in a nested call of the application case and thus work with a metavariable of type $mono("relation " tau)$ that we can force to be transitive during the proof search. This does not change our invariants as we always treat relations general enough so that it does not matter whether we work with metavariables of type $mono("relation " tau)$ or given instances of that type.

During the recursive rewrite on $u$, the first occurrence was already replaced by $g$ and we follow the procedure for application arguments starting at line 13 in @subterm. This would invoke yet another recursive invocation where $f$ is again the function rewrite. This is how we can rewrite a term, for instance $f space a space (f space a space (f space a space (a = a) space b) space b) space b$, directly to $g space a space (g space a space (g space a space (a = a) space b) space b) space b$ and thus truly generate the same rewrites that `Rew` produces. The downside of this approach is that with many occurrences of $f$, we generate almost as many `Subrelation` metavariables as the `Rew` algorithm would for this example. The `Transitive` instances, however, are trivial to solve and can even be closed during the constraint generation as all implications are transitive. Our extension described in @multifalgo can be exchanged with line 12 in the `ORew` algorithm to remidiate the inconsistencies. Note that the function $mono("InferRel")^*$ is a slight modification of the previously seen relation inference algorithm where the desired relation can be passed down.

#figure(
algo(
  row-gutter: 5pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type", "mvar"),
)[
  ($Psi'''$, result) := $"ORew"_rho (u space e_1 space dots space e_n, r))$\
  match result with\
  $|$ identity ⇒ return ($Psi'' union space {?_s, ?_"rel"}$, $?_"rel"$, $u space e_1 space dots space e_n$, $?_s space rho space e_1 space dots space e_n$)\
  $|$ success ($r'''$, $u'''$, $p$) ⇒ #i\
    $p_l$ := $"InferRel"^*$($Psi'' union space {?_s, ?_"rel"}$, $?_"rel"$, $u space e_1 space dots space e_n$, $?_s space rho space e_1 space dots space e_n$, $r$)\
    $p_r$ := $"InferRel"^*$($Psi'''$, $r'''$, $u'''$, $p$, $r$)\
    $?_"tr"$ := mvar(Transitive r)\
    return ($Psi'' union Psi''' union {?_"tr"}$, $r$, $u'''$, $?_"tr" space t space (u space e_1 space dots space e_n) space u''' space p_l space p_r$)\
], caption: [Correction for the `ORew` algorithm.]) <multifalgo>

Lastly, we have to adjust the algorithm for relation inference slightly to handle both the `Rew` and `ORew` algorithms. We refer to the two rewrite statuses seen in @subterm as `RewriteResult` with the constructors `identity` and `success`. The `success` constructor holds the same tuple as seen in the `Rew` output and the `identity` constructor holds no further information. We will omit this `success` constructor for readability and assume it is used whenever we return the according value and do not explicitly use `identity`. The modified version in @infersubp matches for those two constructors and infers the relation only if necessary.

#figure(
algo(
  row-gutter: 5pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type"),
  title: $"InferRel"$,
  parameters: ($"res" : mono("RewriteResult")$, $t : "Prop"$)
)[
  match res with\
  $|$ ($Psi$, `identity`) $=>$#i\ return (`impl_self` : $t <- t$)#d\
  $|$ ($Psi$, `success` ($r$, $u$, $p$)) $=>$#i\
  if r == ($<-$) then:#i\ 
    return p#d\
  else#i\
    ?s : Subrelation r ($<-$)\
    return ?s t u p
], caption: [Modified algorithm for relation inference.]) <infersubp>

== Illustrated Generation of Refined Proofs

Let us observe the call tree and the generated constraints, similar to what we have seen earlier, for the updated version of the algorithm. In order to highlight the optimisation for leading identity rewrites, we change the example from $(p -> q) and (p -> q)$ to $(q -> p) and (q -> p)$. This has no effect on the original `Rew` algorithm because the number of recursive calls and the amount of generated constraints would not be different. Thus, this example is still suited for a comparison.

When invoking $mono("ORew")_h ((q -> p) and (q -> p), (<-))$, we now explicitly ask for a proof of $t <- u$. The tree in @calltreelongexample2 only has a maximum depth of three now compared to six for the previous example graph in @calltreelongexample. The proofs in each level also look smaller because the metavariables $?p 1$, $?p 2$, and $?p 3$ are of more expressive `Proper` types.

Leading identity rewrites occur in both sub-branches of the main invocation so that $?p 1$ and $?p 2$ both shrink and curry the unchanged term. This results in fewer metavariables that have to be solved by a proof search afterwards. The type of a metavariable $?p 1$, for instance, could itself contain at most six metavariables if a rewrite occurred in all three subterms. Even in that worst-case scenario, the `Rew` algorithm would result in two more (eight in total) metavariables.

We can also see that we do not need the final subrelation step as seen in @calltreelongexample because we pass the expected relation down from the start. We end up with five metavariables in this example whereas the `Rew` algorithm produces 23 metavariables. This means that the proof of the same proposition has fewer holes.

#figure(updatedgraph(46em), caption: [Call-Tree of $mono("ORew"_h)((q -> p) and (q -> p), <-)$.]) <calltreelongexample2>