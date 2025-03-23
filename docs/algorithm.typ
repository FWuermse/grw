#import "./graph.typ": *
#import "./template.typ": *
#import "./theme.typ": *
#import "@preview/algo:0.3.4": algo, i, d, comment, code
= Algorithm for Genralised Rewriting <PaperAlgo>

The core idea of the approach for rewriting proposed in @sozeau:inria-00628904 is to break down generalised rewriting into two parts. The first part is an algorithm that generates a large proof skeleton for the rewrite leveraging `Proper`, `respectful`, and `Subrelation` as seen above. In previous examples we have seeen that while we know what types such a proof must have we don't always know the actual instances of the `Proper` or `Subrelation` classes. They each only have a single constructor. We know that a proof for a `Subrelation` term must be constructed with `Subrelation.subrelation` meaning a proof that for a given relation $q$ and a given relation $r$, all $x$ and $y$ must satisfy $q space x space y -> r space x space y$ and similarly for `Proper` proofs. We may however not always know the proof for $forall x y, q space x space y -> r space x space y$. This is why the algorithm uses metavariables for those instances and for some sub-expressions. For instance a proof skeleton for a simple atomic term $p : mono("Prop")$ and a proof $h : r space p space q$ would be a proof $mono("Subrelation.subrelation (Prop)") space r space (<-) space ?_m space p space q space h$. Notice that $?_m$ is a metavariable of type $mono("Subrelation" space r space (<-))$ which unfolds to $forall x y, r space x space y -> (x <- y)$. The application $?_m space p space q space h$ gives us the desired rewrite. The assignment for the metavariable $?_m$ is unknown and left as a hole in this proof. With more nested terms this algorithm collects multiple unassigned metavariables.

This is where the second part of the proposed approach, a proof search, comes into play. In Coq this proof search is realized using typeclass resolution #cite(<sozeau:inria-00628904>) #cite(<casteran:hal-00702455>). Type class resolution in Coq searches through user defined instances of a type class and applies those instances. For example the typeclass instance `iff_impl_subrelation` is an instance for the `Subrelation` typeclass in Coq that provides a proof for $mono("Subrelation" (<->) space (<-))$ which can be leveraged whenever the rewrite relation is $(<->)$.

The algorithm in @rewalgo is an imperative translation of the declarative algorithm proposed in @sozeau:inria-00628904 that follows our implementation in Lean 4. The algorithm is syntax directed and covers every term that can be constructed in Lean. Note that terms in Lean 4 can be of type `bvar`, `fvar`, `mvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`, `lit`, `mdata`, and `proj`. The algorithm divides between `app`, `lam`, `forallE`, and `const`. As the names suggest `app` refers to function applications, `lam` to lambda expressions, `forallE` to dependnet function types, and `const` to constants.

All remaining cases are also treated as constants (`const`). The algorithm takes an empty constraint set $Psi$, a term $t$ in that we want to rewrite and a proof $rho$ that is of the type $r space a space b$ where $r$ is a relation, $a$ is a term we want to rewrite in $t$ and $b$ is the value we want to replace $a$ with. The algorithm outputs a tuple ($Psi$, $r$, $u$, $p$). $Psi$ is the modified, initially provided set which contains all holes (also referred to as constraints) in the rewrite proof that cannot be determined at the time. Those holes in the proof are represented as metavariables in Lean. The idea of collecting those constraints seperately in a set is to solve them prior to applying the resulting rewrite proof. If we apply a proof contraining open holes Lean would set them as goals for the user to solve. To avoid this we remember what needs to be solved before applying the proof. $r$ is the carrier relation for the rewrite proof. $u$ refers to the modified term and finally $p$ is the proof for the rewrite containing the metavariables in $Psi$. At the beginning we always check whether the term we want to rewrite unifies directly for the given proof $rho$. In that case the proof-result for a rewrite would just be $rho$. Because $rho$ (and any proof-result of this algorithm) is not of the type $t <- u$ we will wrap the output of the algorithm in a proof for $"Subrelation" r space (<-)$. @infersub represents a small algorithm responsible for that subrelation wrapping. When rewriting with `Rew`, we can simply invoke $mono("InferRel") (mono("success Rew")_rho (emptyset, t), t)$. We will cover `InferRel` and the `RewriteResult` type in depth in @updatedalgo.

Unification is the process of identifying whether two expressions can be identically substituted or unified @unification. In Lean 4 this refers to checking for definitional equality @carneiro2019type of the two terms after binding all variables bound by all-quantifiers. For instance the expressions $forall x_0 dots x_n, a$ and a term $a'$ would unify if and only if $a' equiv a$.

When we want to rewrite a term $t$ with the left-hand-side of a rewrite theorem $rho : r space a space a'$ we need to check for unification of $a$ with a subterm of $t$. However sometimes we may want to rewrite right-to-left. To achieve this we instead check if $a'$ unifies with a subterm of $t$. In Lean's `rewrite` tactic the direction can be stated with an arrow $mono("rewrite [") <- rho mono("]")$ for right-to-left and per default $mono("rewrite [") rho mono("]")$ for left-to-right rewrites. Throughout this thesis we will always assume that a rewrite is left-to-right as it is very simple to change the direction. The only change required for the algorithm to work right-to-left is to update the `unify` function that we will see in this section. 

Whenever a term $t$ does not unify directly we examine its structure and use a different approach depending on whether $t$ is an application, lambda, dependent/non-dependent arrow, or constant. Whenever we encounter an application $f space e$ we perform a recursive call on both $f$ and $e$. We use the obtained carrier relation $r_f$, proof, and term to construct a proof that $r_f$ is a subrelation of $r_e ==> ?_T$. This is where the first holes occur that we collect in the constraint set. This generates a proof for $r space t space u$. Recall that we construct a $"Subrelation" r space (<-)$ after invoking `Rew` which leads to a proof of $t <- u$.

For rewrites inside lambda terms we bind $x : tau$ to the local context and perform a recursive rewrite on the body of the lambda. The resulting proof wrapped in a fresh lambda expression binding $x : tau$ represents the proof for $r space (lambda x:tau. b) space (lambda x:tau. b')$ again progressing to $(lambda x:tau. b) <- (lambda x:tau. b')$ eventually.

All other cases leverage either the lambda or application cases by converting them slightly to fit in the scheme. The non-dependent arrow case is simply transformed into an artificial function that represents an arrow. This has the advantage that locally declared functions (`impl` in this case) are considered constants in Lean and thus reuse the already defined application case. Similarly, for the case of an all-quantifier that uses a local dependent function `all`.

Finally, we will take a look at the last case that is triggered whenever none of the above cases match. This is the case for constants such as `all`, `impl`, or simply for atoms that do not unify at the beginning of the `Rew` function. In this case we construct another metavariable of type $"Proper" tau space ?_r t'$ that is treated as a hole at the bottom of the proof tree. It essentially represents a syntactic hole for a proof of an identity rewrite from $t$ to $t$ over a relation that is also a metavariable. This will always happen for this algorithm as we never specify the desired relation for the proof and generate metavariables whenever we do not know the relation.

#figure(
algo(
  row-gutter: 5pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type"),
  title: $"Rew"_rho$,
  parameters: ($Psi$, $t$)
)[
  ($Psi'$, $r'$, $u'$, unifyable) := $"unify"_rho$($Psi$, $t$)\
  if unifyable then:#i\
    return ($Psi'$, $r'$, $u'$, $rho$)#d\
  match $t$ with\
  $|$ $f$ $e$ $=>$#i\
    ($Psi'$, $r_f$, $u_f$, $p_f$) := #smallcaps($"Rew"_rho$)$(Psi, f)$\
    ($Psi''$, $r_e$, $u_e$, $p_e$) := #smallcaps($"Rew"_rho$)$(Psi', e)$\
    $Psi'''$ := {$?_T$ : relation type($f space e$), $?_"sub"$ : subrelation $r_f (r_e ==> ?_T)$}\
    return ($Psi'' union Psi'''$, $?_T$, $"app" u_f u_e$, $?_"sub" f space u_f space p_f space e space u_e space p_e$)#d\
  $|$ $lambda$ x : $tau$. b $=>$#i\
    ($Psi'$, $r$, $u$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, b)$\
    return ($Psi'$, pointwiseRelation $tau$ $r$, $lambda$ x : $tau$. u, $lambda$ x : $tau$. p)#d\
  $|$ $forall x : tau, b$ $=>$#i\
    ($Psi'$, $r$, $u$, unifyable) := $"unify*"_rho$($Psi$, $b$)\
    if unifyable then:#i\
      return ($Psi'$, $r$, $u$, $rho$)#d\
    ($Psi'$, $r'$, $"all" (lambda x : tau. b')$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, "all" (lambda x : tau. b))$\
    return ($Psi'$, $r'$, $forall$ x : $tau$, $b'$, $p$)#d\
  $|$ $sigma -> tau$ $=>$#i\
    ($Psi'$, $r$, $"impl" sigma' space tau'$, $p$) := #smallcaps($"Rew"_rho$)$(Psi, "impl" sigma space tau)$\
    return ($Psi'$, $r$, $sigma' -> tau'$, $p$)#d\
  $|$ t' $=>$#i\
    return ($Psi union {?_r : $ relation type($t$), $?_m : "Proper" tau space?_r space t'}$, $?_r$, $t'$, $?_m$)
], caption: [Imperative Algorithm for Generalised Rewriting @sozeau:inria-00628904.]) <rewalgo>

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
], caption: [Algorithm for Relation Inference.]) <infersub>

There is also two places where a rewrite can occur. Either on the goal we are trying to solve or on a hypotheses that we want to change before applying. Similarly to the direction of the rewrite we will only consider rewriting on the goal as part of the algorithm. The only required change for the algorithm to also work on a hypotheses is to change the right-to-left implication $(<-)$ to a left-to-right implication $(->)$. Whenever we mention the right-to-left implication explicitly in this thesis we could exchange it for $(->)$ for the proof to work on hypotheses.

== Example <examplesection>

Let's recall the rewrite from $p and q$ to $q and q$ for a given relation $r$ that is a subrelation of $(<-)$ and a given proof $h : r space p space q$. The algorithm first tries to unify the entire term $p and q$ with the left-hand side of our proof ($p$). Conjunctions in Lean are defined by the `And` structure and thus our term $t$ is interpreted as $mono("And") p space q$ which must be read as $(mono("And") space p) space q$. This falls into the `app` case such that we first interpret $(mono("And") p)$ followed by $q$. Again $(mono("And") p)$ doesn't unify with $p$ and follows another `app` iteration for `And` and $p$. `And` itself does not unify and does not match any other category. So the algorithm treats it as an atom (`const`) and generates a metavariable $?_(mono("And_")r) : mono("relation") (mono("relation Prop"))$ and passes ($?_(mono("And_")m) : mono("Proper") (mono("relation") mono("Prop")) space ?_(mono("And_")r) mono("And")$) for the proof of identity. The next term in line ($p$) does indeed unify with $p$ and is therefore replaced with $q$. For now the proof-placeholder will be just $h$. After the two recursive `Rew`-invocations terminate we combine the proofs and carrier relations for a proof of $r space (mono("And") space p) space (mono("And") space q)$. We start with another hole $?_(mono("And_")p) : "subrelation" ?_(mono("And_")r) (r ==> (?_T : "relation (Prop" -> "Prop)"))$. Recall that `Subrelation` is a typeclass with only constructor `subrelation`. Thus, any metavariable of type `Subrelation` must be of that constructor and eventually unfolds to $forall r_1 space r_2, ?_"rel" space r_1 space r_2 -> forall x space y, r space x space y -> ?_T space x space y -> ?_T (r_1 space x) space (r_2 space y)$. This allows us to construct the desired proof by carefully applying the arguments $?_(mono("And_")p) mono("And") mono("And") space ?_(mono("And_")m) space p space q space h$. By instantiating $r_1$ and $r_2$ with the `And` relation and $x$ and $y$ with $p$ and $q$ we receive our desired rewrite proof for this part of the term $?_(mono("And_")T) $.

We will see more metavariables of type `Subrelation` or `Proper` applied to its arguments throughout this thesis where we don't unfold the definition in order to remain readability of the terms. Recall the all-quantifiers and sub-proofs of those definitions to relate to the multiple arguments.

The next rewrite to be evaluated is the identity rewrite for $q$. We follow the same procedure as for the `And` rewrite generating $?_(q"_"r) : mono("relation Prop")$ and the proof ($?_(q"_"m) : mono("Proper Prop") space ?_(q"_"r) space q$). The final merge step will combine both proofs in another subrelation $(?_(mono("And_")p"_"q) : mono("subrelation") space ?_T (?_(q"_"r) ==> (?_T' : mono("relation Prop"))))$. The algorithm then outputs $?_(mono("And_")p"_"q) space (mono("And") p) space (mono("And") q) space (?_(mono("And_")p) mono("And") mono("And") space ?_(mono("And_")m) space p space q space h) space q space q space ?_(q"_"m)$ which is a proof for $?_T' space (p and q) space (q and q)$.

There are two issues with this proof. The first issue is that the rewrite proof output of $"Rew"_h (emptyset, p and q)$ is not an implication ($<-$) but an unknown relation $?_T'$. This can easily be fixed by creating another metavariable $?_"final"$ as a placeholder for a proof that $?_T'$ is a subrelation for ($<-$). This is the purpose of the algorithm in @infersub. That brings us to the second problem that the proofs contains many holes that need to be replaced with proofs. The paper @sozeau:inria-00628904 suggests a proof search that operates depth first search on the constraint set (set of metavariables).

For the example of $p and q$ we collect the metavariables as we create them and end up with the final constraint set ${?_T, ?_(mono("And_")r), ?_(mono("And_")m), ?_(mono("And_")p), ?_(q"_"r), ?_(q"_"m), ?_(mono("And_")p"_"q), ?_T', ?_"final"}$. In our Lean 4 implementation we initially solved those goals using aesop @aesop with a custom rule set containing the theorems and tactics mentioned in the Coq Morphism library @coqmorphism.

For larger instances we developed our own proof search that is tailored to the constraints generated by the algorithm. The main difference with our custom search tactic was that we backtrack for all goals and not just the one we selected. The reason for this is that in the generated constraint set shares metavariables that can be solved easily by themselves but require more specific solutions when considering other constraints.

The conjuction proof $?_p : mono("Proper") ((=) ==> ?_r ==> (<-)) space (and)$ mentioned in @Introduction for instance contains two metavariables. $?_p$ refers to the proof for the `Proper` instance and $?_r : mono("relation Prop")$ is a relation used to force a `Proper` of a specific rewrite type. We have seen that multiple values may work for $?_r$. However, in a proof search that operates per goal it would be feasable to first solve $?_r$ with the implication relation. This would affect the metavariable $?_p$ to change to $mono("Proper") ((=) ==> (->) ==> (<-))$ which is not solvable without knowing the parameters of $?_p$. Thus, in such a case we have to backtrack from the goal $?_p$ to a different assignment of $?_r$ and try another path.

== Challenges in Practice

The algorithm proposed by @sozeau:inria-00628904 can rewrite behind binders and within arbitrary terms in our Lean 4 implementation. However, when trying to solve larger instances we run into serious performance issues. There are two main reasons for this.

The first challenge when applying this approach in practice is that even for terms where no rewrite occurs the amount of generated constraints is quadratic in terms of the depth of a term tree. The proof search itself is exponential for the amount of constraints. This gives us a strong motivation to reduce the amount of constraint where possible.

The other reason those constraints are difficult to solve is that nested subrelation proofs are more difficult to find than just `Proper` and `respectful` instances. This is because as we have seen most arguments in the middle of a proper respectful chain must merely be reflexive and the resulting proper instance can then be shown using deconstruction of the constructor and reflexivity.

Let us consider another example where the constraints become more difficult to solve. To visualize the generated proof better we will skip the individual steps and show a graph that represents the rewrite-sequence where each edge represents the return value passed by a recursive invocation of the `Rew` algorithm.

Each node is split into two rows where the first row shows the term $t$ to be rewritten in column one, the carrier relation $r$ over the proof of $r space t space u$ in the second column, and finally the resulting term $u$ in the final column. The second row is a commulative collection of the generated metavariables that must be solved in order to complete the proof. To keep an overview over the generated metavariables we refer to metavariables of type `relation` $tau$ as $?r_i$ with $i in NN$ being the index of the variable. Similarly metavariables of type `Proper` are represented as $?p_i$ also including its index $i$. Finally variables that follow the naming $?s_i$ are the $i$-indexed metavariables of type `Subrelation`.

In order to further improve readability we use the same notation as seen in @examplesection where we assume that the application of a metavariable of type `Proper` or `Subrelation` is constructed by their unique constructors. This means its application arguments are passed directly to the `Proper.proper` or `Subrelation.subrelation` function type so that $?s_0 space r space q space x space y space h$ unfolds to `Subrelation.subrelation` $r space q space x space y : q space x space y -> r space x space y$. We also omit the implicit parameters referring to the types of a `Proper` or `Subrelation` term and assume that if a proof $?p_0$ is a proof over the relation $r_0 : mono("relation") tau$ then the implicit argument for the proof $?p_0$ is $tau$ and similarly for subrelations. We use $eq^Delta$ as a placeholder to avoid long repeating terms. Whenever we pass more than three arguments as seen in $s 1$ to a metavariable we implicitly unfold `respectful` definitions and assign values for $x, y$ and $r space x space y$. So we read $s 1 =^Delta ?s_1 space (->) space (->) space ?p_1 space p space q space h$ as passing the arrows and $?p_1$ to the unfolded `Subrelation.subrelation` definition and $p, q$, and $h$ to the resulting unfolded `respectful` definition and refer to the resulting proof as $s 1$.

#figure(exgraph(46em), caption: [Call-Tree of $mono("Rew"_h)(emptyset, (p -> q) and (p -> q))$.]) <calltreelongexample>

The example shown in @calltreelongexample considers the rewrite of $(p -> q) and (p -> q)$ given a proof $h$ which is equality in this case. We can see that we start generating constraints for the leaves of the proof tree where we use $h$ as a proof whenever a subterm unifies with $p$ or generate metavariables for terms that fall into the `const` category. We can also observe that the amount of constraints roughly doubles in size as we move through the tree vertically. Using a depth first search proof search approach we have an exponential growth with the number of metavariables created by the proof skeleton. We can see that the multiple occurrences of $->$, $and$, and $q$ result in two metavariables each. By the time we reach the final rewrite proof for the complete term in the lowermost node the constraint set contains 23 metavariables. Six of them are constraints for subrelation terms, five proper metavariables, and finally eleven relations that must essentially be guessed if not elmininated by other theorems during the proof search. Because this growth-factor is not feasable for larger terms we will consider a few optimisations to the constraint generation approach in the following section.