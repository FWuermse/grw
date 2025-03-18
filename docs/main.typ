#import "./template.typ": *
#import "./theme.typ": *
#import "@preview/dashy-todo:0.0.1": todo
#import "@preview/glossarium:0.5.1": make-glossary, register-glossary, print-glossary, gls, glspl
#import "@preview/algo:0.3.4": algo, i, d, comment, code


#let title = "Generalised Rewriting for Lean"
#let author = "Florian Würmseer"

#show: official.with(
  title: title,
  author: author,
  thesis-type: "Master Thesis",
  submission_date: datetime.today().display(),
  matriculation: "12760815",
  advisor: "Jannis Limperg",
  supervisor: "Prof. Dr. Jasmin Blanchette"
)

#set page(numbering : "1")

#counter(page).update(1)

= Introduction <Introduction>

TODO: Sturcture: Algorithm has two parts, constraint gen is our focus, why is it bad?, how can we optimize it?, is it still the same?, how do metavariables change?...
TODO: mention why we even need rewrite proofs (we're extending Lean and not changing it's core theory and defeq stuff.)

Rewriting in theorem provers is the process of replacing a subterm of an expression with another term. When and if such a rewrite can happen depends on the context, i.e., the information we have about the two terms. In Lean, rewriting is possible when two terms $t$ and $u$ are equal $t = u$ or with respect to the `propext` axiom when two propositions $p : mono("Prop")$ and $q : mono("Prop")$ imply each other $p <-> q$. This allows us to replace a term in a goal we want to solve or inside one of our hypothesis when doing reasoning in Lean.

This allows us to proof mathematical propositions such as the commutativity for multiplication. In the below example we can see a lean proof of the commutativity of multiplication given that addition is commutative:

#show raw.where(block: true): code => {
  show raw.line: line => {
    let max = int(calc.log(line.count));
    let zeroes = range(max - int(line.number / 10));
    text(fill: gray)[#zeroes.fold("", (c, i) => c + " ")#str(line.number)]
    h(1em)
    line.body
  }
  code
}

```lean
theorem mul_comm (m n : ℕ) :
  mul m n = mul n m := by
  induction m with
  | zero => apply mul_zero
  | succ m' ih =>
    simp [mul]
    rewrite [mul_succ]
    rewrite [add_comm]
    rewrite [ih]
    rfl
```

In this example we want to proof that for any natural numbers $n$ and $m$ the multiplication $n dot m$ is equal to $m dot n$. In Lean, we do this using structural induction #footnote[Structural induction means that the induction follows the structure of the inductive type.] on the inductive type $NN$ which consists only of two constructors, `zero` for constructing 0 and `succ` for constructing any successor number. After unfolding the `mul` definition in line 6 we are left with a goal: $("succ" m) dot n = n + (n dot m)$. The `mul_succ` theorem has the type $("succ" m) dot n = (m dot n) + n$. The theorems left-hand side matches the left hand side of the theorem and thus we can rewrite it (replacing the left-hand side of the goal with the right hand side of our theorem). The resulting goal is $(m dot n) + n = n + (n dot m)$ which can be closed by another rewrite with an addition-commutativity theorem and finally the induction hypothesis ($m dot n = n dot m$) which also proves equality and can thus be used in a rewrite.

While this is sufficient considering the many helpful theorems and tactics Lean 4 offers, there are some cases @iris TODO where it would be helpful to consider more general rewrites that exceed equality and if and only if. When we try to solve a goal in a theorem prover we usually have a given set of hypothesis and can access theorems that we've already proven as well as tactics that can apply multiple theorems. When we want to rewrite a goal which contains a term $t$ that we want to change to a term $u$ we can perform a rewrite by simply showing that $u$ implies $t$, and thus it suffices to show $u$. The relation ($<->$) is convenient because it gives us such an implication per definition. However, it is possible to perform a rewrite using any relation that can lead to the desired implication.

In the Lean and Coq theorem provers relations on a type $alpha$ are defined by $alpha arrow alpha arrow mono("Prop")$. When we want to proove a goal $t : mono("Prop")$ and have the hypothesis of $u : mono("Prop")$ as well as a proof $h$ of $r space t space u$ given $r$ is a relation $mono("Prop") arrow mono("Prop") arrow mono("Prop")$ we can proof the statement given we have the additional information that $r$ implies ($<-$), essentially ($<-$) is a subrelation of $r$. When those hypotheses are in place the proof is straight forward for this minimal example. By Leans definition of subrelations it suffices to show $r space t space ?_t$ and $?_t$. The question marks refer to missing values that can be filled with any given term that matches its type (metavariables in Lean or existential variables in Coq). Metavariables are also used to represent goals in Lean. Metavariables of a certain type $tau$ in can be assigned with any value $Gamma tack e : tau$ in the current context $Gamma$ (hypotheses, theorems, etc.). When we assign a metavariable that represents a goal we also close the goal. Another way to use metavariables is to use them as placeholders in any given Lean term when the value is unknown at the time of creation. It is also possible to share a metavariable $?_x$ across multiple terms as seen in this example. Assigning it with a value $v$ also assigns every occurrence of $?_x$ with $v$. We can thus assign $?_t$ with $u$ and use our hypothesis that proves $u$ to complete the proof of our simple rewrite.

This approach is tedious to be performed manually especially when the goal is more complicated or the term we intend to rewrite is bound by lambda expressions or an all quantifier. When we want to prove a goal $p and q$ with the same context for instance, and we need to rewrite $p$ to $q$ inside the left-hand side of the conjunction (replace $p$ the  without modifying the remaining term), the proof of that rewrite requires us to set a new subgoal $p and q -> q and q$, solve that by the rule for conjunction introduction leaving $t$ and $u$ as sub-subgoals. $u$ can be proven by our hypothesis and the proof for $t$ is the same procedure as for the minimal rewrite example above. Even this approach is specific to conjunctions and can't be extended for other propositions.

A better approach for a general way of rewriting with arbitrary relations is the Morphism framework introduced by Mattheiu Sozeau @sozeau:inria-00628904 consisting of `respectful` and `Proper` definitions that can construct proofs for arbitrary terms using a syntax-directed algorithm. The `Proper` definition in @ProperDef merely takes a relation $r$ and an element $m$ in that relation demanding reflexivity of that element. Whenever this definition holds we call $m$ a `Proper` element of $r$ meaning that $m$ is a morphism for $r$. The `respectful` definition seen in @respectfulDef denoted as ($==>$) is Coqs notion for signatures. This definition can produce very general implications for a variety of functions. For instance, the contrapositive theorem $forall a b : mono("Prop"), (a -> b) -> (not b -> not a)$ can be stated as $((->) ==> (<-)) space (not) space (not)$. We can even simplify the contrapositive theorem by leveraging `Proper` and `respectful` with $"Proper" ((->) ==> (<-)) space (not)$. We can use the same framework to specify the above rewrite $p and q -> q and q$ in a more general way for instance when we create a term $?_p$ of type $"Proper" ((=) ==> (<->) ==> (<-)) space (and)$ translates to $forall x y, x = y -> forall x' y', x' <-> y' -> (x and x' <- y and y')$. When instantiating the variables in $?_p$ for instance with $p, q, h : p = q, q, q, (h' : b <-> b)$ we would get a proof for $(p and q <- q and q)$.

Note that for this case it does not matter whether we have ($<->$), ($<-$), or ($=$) as the middle argument for the respectful chain. In fact any reflexive relation over `Prop` would work here. Proceeding with this framework we have to be mindful of what problems we can simplify with `Proper` and `respectful` proofs, which relations we use inside such a chain, how to choose the first and final relation, and finally what element we want to be Proper under the sequence of `respectful` relations.

#definition("Proper")[
  ```lean
  class Proper (r : relation α) (m : α) where
    proper : r m m
  ```
] <ProperDef>

#definition("respectful")[
  ```lean
  def respectful (r : relation α) (r' : relation β) : relation (α → β) :=
    λ f g ↦ ∀ x y, r x y → r' (f x) (g y)
  ```
] <respectfulDef>

The Coq library for morphisms has many theorems that operate on `Proper` and `respectful` terms which helps to construct and solve theorems containing morphisms and signatures. This allows us to use the same structure and theorems for rewrites in different terms. The proof construction for $p and q <- q and q$ and $p or q <- q or q$. This generalisation is the base for an algorithm proposed by Matthieu @sozeau:inria-00628904 that automatically produces rewrite proofs for any given `Proper` relation where the term to be rewritten can be behind binders and nested in other structures. There is one more definition that makes the proposed algorithm more powerful. When we have $"Proper" (A ==> B) space f$, and we know that $B$ is a subrelation of $C$ we can imply $"Proper" (A ==> C) space f$.

#definition("Subrelation")[
  ```lean
  class Subrelation (q r : α → α → Prop) :=
    subrelation : ∀ {x y}, q x y → r x y
  ```
]

In this thesis we will take a deeper look at the algorithm for generalised rewriting in type theory @sozeau:inria-00628904, compare it to the actual implementation of generalised rewriting in Coq, extract the differences between the two, and show that those algorithms provide the same rewrite proofs.

This highlights our contributions are the following:
- Implement the algorithm seen in the paper in Lean 4
- Capture the essence of the optimized algorithm that evolved in Coq over ten years for the first time
- Implement the optimized algorithm in Lean 4
- Show that both alogrithm lead to the same rewrite proofs

= Algorithm for Genralised Rewriting <PaperAlgo>

The core idea of the approach for rewriting proposed in @sozeau:inria-00628904 is to break down generalised rewriting into two parts. The first part is an algorithm that generates a large proof skeleton for the rewrite leveraging `Proper`, `respectful`, and `Subrelation` as seen above. In previous examples we have seeen that while we know what types such a proof must have we don't always know the actual instances of the `Proper` or `Subrelation` classes. They each only have a single constructor. We know that a proof for a `Subrelation` term must be constructed with `Subrelation.subrelation` meaning a proof that for a given relation $q$ and a given relation $r$, all $x$ and $y$ must satisfy $q space x space y -> r space x space y$ and similarly for `Proper` proofs. We may however now always know the proof for $forall x y, q space x space y -> r space x space y$. This is why the algorithm uses metavariables for those instances and for some sub-expressions. For instance a proof skeleton for a simple atomic term $p : mono("Prop")$ and a proof $h : r space p space q$ would be a proof $mono("Subrelation.subrelation (Prop)") r space (<-) space ?_m space p space q space h$. Notice that $?_m$ is a metavariable of type $mono("Subrelation" r space (<-))$ which unfolds to $forall x y, r space x space y -> (x <- y)$. The application $?_m space p space q space h$ gives us the desired rewrite. The assignment for the metavariable $?_m$ is unknown and left as a hole in this proof. With more nested terms this algorithm collects multiple unassigned metavariables.

This is where the second part of the proposed approach, a proof search comes into play. In Coq this proof search is realised using type class relsoltuion. Type class resolution in Coq searches through user defined instances of a type class and applies those instances. For example the instance `iff_impl_subrelation` is an instance for the subrelation typeclass in Coq that provides a proof for $mono("Subrelation" (<->) space (<-))$ which can be leveraged whenever the rewrite relation is $(<->)$.

The algorithm in TODO:algoref is an imperative translation of the declarative algorithm proposed in @sozeau:inria-00628904 that we implemented in Lean 4. The algorithm is syntax directed and covers every term that can be constructed in Lean. Note that terms in Lean 4 can be of type `bvar`, `fvar`, `mvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`, `lit`, `mdata`, and `proj`. The algorithm divides between `app`, `lam`, `forallE`, and `const`. All remaining cases are treated as constants (`const`). The algorithm takes an empty constraint set $Psi$, a term $t$ in that we want to rewrite and a constant proof $rho$ that is of the type $r a b$ where $r$ is a relation, $a$ is a term we want to rewrite in $t$ and $b$ is the value we want to replace $a$ with. The algorithm outputs a modified set $Psi$ which contains all holes in the rewrite proof that can't be determined in some of the cases of the algorithm (represented in metavariables in Lean), a carrier relation $r$ for the rewrite, the modified term $u$ and finally the proof for the rewrite. At the beginning we always check whether the term we want to rewrite unifies directly for the given proof $rho$. In that case the proof-result for a rewrite would just be $rho$. Because $rho$ (and any proof-result of this algorithm) is not of the type $t <- u$ we will wrap the output of the algorithm in a proof for $"Subrelation" r space (<-)$.

Whenever the term does not unify directly we examine the structure and use a different approach depending on whether $t$ is an application, lambda, dependent/non-dependent arrow, or constant. Whenever we encounter an application $f space e$ we perform a recursive call on both $f$ and $e$. We use the obtained carrier relation, proof, and term to construct a proof that $r_f$ is a subrelation of $r_e ==> ?_T$. This is where the first holes occur that we collect in the constraint set. This generates a proof for $r t u$. Recall that we construct a $"Subrelation" r space (<-)$ after invoking `Rew` which leads to a proof of $t <- u$.

For rewrites inside lambda terms we bind $x : tau$ to the local context and perform a recursive rewrite on the body of the lambda. The resulting proof wrapped in a fresh lambda expression binding $x : tau$ represents the proof for $r space (lambda x:tau. b) space (lambda x:tau. b')$ again progressing to $(lambda x:tau. b) <- (lambda x:tau. b')$ eventually.

All other cases leverage either the lambda or application cases by converting them slightly to fit in the scheme. The non-dependent arrow case is simply transformed into a function that represents an arrow. This has the advantage that locally declared functions (`impl` in this case) are considered constants in Lean and thus reuse the already defined application case. Similarly, for the case of an all quantifier that uses a local dependent function `all`.

Finally, we will take a look the last case is triggered whenever none of the above cases match. This is the case for constants such as `all`, `impl`, or simply for atoms that don't unify at the beginning of the `Rew` function. In this case we construct another metavariable of type $"Proper" tau space ?_r t'$ that is treated as a hole at the bottom of the proof tree and essentially represents and identity rewrite from $t$ to $t$. This will always happen for this algorithm as we never specify the desired relation for the proof and generate metavariables whenever we don't know the relation.

== Examples

Let's recall the rewrite from $p and q$ to $q and q$ for a given relation $r$ that is a subrelation of $(<-)$ and a given proof $h : r space p space q$. The algorithm first tries to unify the entire term $p and q$ with the left-hand side of our proof ($p$). Conjunctions in Lean are defined by the `And` structure and thus our term $t$ is interpreted as $mono("And") p q$ which must be read as $(mono("And") p) q$. This falls into the `app` case such that we first interpret $(mono("And") p)$ followed by $q$. Again $(mono("And") p)$ doesn't unify with $p$ and follows another `app` iteration for `And` and $p$. `And` itself does not unify and does not match any other category. So the algorithm treats it as an atom (`const`) and generates a metavariable $?_(mono("And_")r) : "relation" ("relation Prop")$ and passes ($?_(mono("And_")m) : "Proper" ("relation" mono("Prop")) space ?_(mono("And_")r) mono("And")$) for the proof of identity. The next term in line ($p$) does indeed unify with $p$ and is therefore replaced with $t$. For now the proof-placeholder will be just $h$. After the two recursive `Rew`-invocations terminate we combine the proofs and carrier relations for a proof of $r space (mono("And") space p) space (mono("And") space q)$. We start with another hole $?_(mono("And_")p) : "subrelation" ?_(mono("And_")r) (r ==> (?_T : "relation (Prop" -> "Prop)"))$. Recall that `Subrelation` is a typeclass with only constructor `subrelation`. Thus, any metavariable of type `Subrelation` must be of that constructor and eventually unfolds to $forall r_1 space r_2, ?_"rel" space r_1 space r_2 -> forall x space y, r space x space y -> ?_T space x space y -> ?_T (r_1 space x) space (r_2 space y)$. This allows us to construct the desired proof by carefully applying the arguments $?_(mono("And_")p) mono("And") mono("And") space ?_(mono("And_")m) space p space q space h$. By instantiating $r_1$ and $r_2$ with the `And` relation and $p$ and $q$ for $x$ and $y$ we receive our desired rewrite proof for this part of the term $?_(mono("And_")T) $.

We will see more metavariables of type `Subrelation` or `Proper` applied to its arguments throughout this thesis where we don't unfold the definition in order to remain readability of the terms. Recall the all-quantifiers and sub-proofs to relate to the multiple arguments.

The next rewrite to be evaluated is the identity rewrite for $q$. We follow the same procedure as for the `And` rewrite generating $?_(q"_"r) : mono("relation Prop")$ and the proof ($?_(q"_"m) : mono("Proper Prop") space ?_(q"_"r) space q$). The final merge step will combine both proofs in another subrelation $(?_(mono("And_")p"_"q) : mono("subrelation") space ?_T (?_(q"_"r) ==> (?_T' : mono("relation Prop"))))$. The algorithm then outputs $?_(mono("And_")p"_"q) space (mono("And") p) space (mono("And") q) space (?_(mono("And_")p) mono("And") mono("And") space ?_(mono("And_")m) space p space q space h) space q space q space ?_(q"_"m)$ which is a proof for $?_T' space (p and q) space (q and q)$.

There are two issues with this proof. The first issue is that the rewrite proof output of $"Rew"_h (emptyset, p and q)$ is not an implication ($<-$) but an unknown relation $?_T'$. This can easily be fixed by creating another metavariable $?_"final"$ as a placeholder for a proof that $?_T'$ is a subrelation for ($<-$). That brings us to the second problem that the proofs contains many holes that need to be replaced with proofs. The paper @sozeau:inria-00628904 suggests a proof search that operates depth first search on the constraint set (set of metavariables).

For the example of $p and q$ we collect the metavariables as we create them and end up with the final constraint set ${?_T, ?_(mono("And_")r), ?_(mono("And_")m), ?_(mono("And_")p), ?_(q"_"r), ?_(q"_"m), ?_(mono("And_")p"_"q), ?_T', ?_"final"}$. In our Lean 4 implementation we initially solved those goals using aesop TODO cite using a custom rule set containing the theorems and tactics mentioned in the Coq Morphism library TODO cite. For larger instances we developed our own proof search that is tailored to the constraints generated by the algorithm. The main difference of our custom search tactic was that we backtracked for all goals and not just the one we selected. The reason for this is that in the generated constraint set shares metavariables that can be solved easily by themselves but require more specific solutions when considering other constraint. For instance when we have two metavariables in the previously seen conjuction proof $?_p : mono("Proper") ((=) ==> ?_r ==> (<-)) (and)$ contains two metavariables. $?_p$ refers to the proof for the rewrite and $?_r : mono("relation Prop")$ is a relation used to force a `Proper` of a specific rewrite type. We've seen that multiple values may work for $?_r$. However in a proof search that operates per goal it would be feasable to first solve $?_r$ with the implication relation. This would affect the metavariable $?_p$ to change to $mono("Proper") ((=) ==> (->) ==> (<-))$ which is not solvable. Thus, in such a case we have to backtrack to $?_r$ and try another path.

== Challenges in Practice

The algorithm proposed by @sozeau:inria-00628904 can rewrite behind binders and within arbitrary terms in our Lean 4 implementation. However, when trying to solve larger instances we run into serious performance issues. There are two main reasons for this.

The first challenge when applying this approach in practice is that even for terms where no rewrite occurs the amount of generated constraints is quadratic in the number of sub-terms, thus exponential in terms of the depth of a term tree TODO: double check. The proof search itself is exponential TOOD.

The other reason those constraints are difficult to solve is that nested subrelation proofs are more difficult to find than just `Proper` and `respectful` instances.

Let's consider another example where the constraints become more difficult to solve. To visualize the proof better we will skip the individual steps and show a graph in which each node holds the terms $t$ and $u$ of a recursive call as well as the proof and its newly generated metavariables. 

TODO render

#algo(
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
] <algo>

#algo(
  row-gutter: 5pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type"),
  title: $"InferRel"$,
  parameters: ($p$, $r : "relation Prop"$, $t : "Prop"$, $u : "Prop"$)
)[
  if r == ($<-$) then#i\ 
    return p#d\
  else#i\
    ?s : Subrelation r ($<-$)\
    return ?s t u p
] <algo>

= Optimisations

The actual Coq implementation of generalised rewriting contains a few optimisations not mentioned in the paper. Through reverse engineering a large amount of the coq core module we were able to extract the most crucial optimisations and applied them to our imperative algorithm specification. The alogrithm we've seen so far stresses the use of applications and aims to convert other terms into application-terms. Thus, most of the following optimisations focus on simplifying application proofs.

== Identity and Success Status

In our examples we saw that even rewrites where most terms do not contain the left hand side term of the rewrite relation. However we would still examine those terms and produce two metavariables just to create a proof of identity $h : t -> t$. This can be simplified by differenciating between subterms depending on whether they can be rewritten or recursively rewritten or remain the same. We change the output type of the algorithm to a sum type with two variants. The `identity` variant carries no further information and signals that a term cannot be rewritten. The other variant `success` carries the same information as seen before, in essence, the carrier relation, the updated term, and the proof of the rewrite. Now every time all of the recursive invokations result in identity rewrites the current rewrite will also be an identity rewrite. For instance, an application $f and e$ where both $"Rew"_rho (Psi, f)$ and $"Rew"_rho (Psi, e)$ result in identity rewrites the result for $"Rew"_rho (Psi, f space e)$ will also result in an identity rewrite. When considering a term $q and q and p and q and q$ given $h : p <-> q$ we would only consider the $q$ in the middle and would not create proofs and carrier relations for the four conjunctions and four $q$'s. The worst case complexity is still the same here, however in practice we usually have a lot of cases that cannot be rewritten specially as we transform arrow and pi types to id applications aswell.

== Top-down Relation Passing

The algorithm described so far generates mata variables for relations whenever we don't know which relation we're supposed generate a proof for. We then return those relations recursively and build subrelations to infer the desired relation (eventually ($<-$)). We consider this a bottom-up approach where those metavariables originate from the leafs of such a term tree and are passed upwards. This creates a lot of subrelation constraints that were not necessary in the first place. We can avoid this by passing an additional parameter to recursive calls (top-down) that contains the desired relation for a proof. We do this by initially providing ($<-$) as the desired relation and pass it along in the lambda, pi, and arrow case. In recursive call as part of the application case we generate a metavariable for a relation of the type of the applicant we rewrite for and pass it to both recursive calls. This invalidates the need for subrelations in the application rule and at the top of the term. TODO example.

== Applications as Sequence

When introducing the `Proper` and `respectful` definitions we gave an example for a possible rewrite proof of $p and q -> q and q$, $mono("Proper") ((=) ==> (<->) ==> (<-)) space (and)$. This is a very compact proof for such a rewrite. However the above algorithm would not be able to produce a respectful chain with three arguments due to the fact that applications are treated binary and thus result in no more than one respectful arrow $(==>)$ wrapped in subrelations. This can be improved by considering and entire sequence of applications. This helps us to simplify the two `Proper` proofs connected with a `Subrelation` proof that we've seen for the $p and q -> q and q$ rewrite to a single proper instance with two arrows. In combination with using a `success`/`identity` status this gives us more context for an entire sequence of applications. For instance we know that the entire application is an `identity` rewrite by iterating over earch applicant and ultimately just return `identity`. We can also use this in combination with the top-down appraoch to insert the desired relation for a specific rewrite (e.g. $(<-$) at the end, and the relation $r$ representing the rewrite argument as the source. Such a proof for $mono("Proper") (r ==> dots ==> (<-)) space (f : mono("Prop") -> dots -> mono("Prop"))$ leads directly to the desired right-to-left implication and does not require a final subrelation over the outcome of $mono("Rew"_rho) (Psi, f space e_0 space dots space e_n, r)$.

== Leading Identity Rewrites

We mentioned 

+ id/success status
+ Pass expected relation to avoid subrelation
+ Eval app for all args
+ Ignore prefix id rewrites for app
+ ProperProxy

== Updated Algorithm

TODO explaination

TODO special cases where we still need subrelation

#algo(
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
] <algo>

== Equality of the Generated Proofs

We saw that in the average case the improved algorithm generates significantly less constraints and leads to more concise proofs. In the following we want to show that the two proposed algorithms for constraint generation provide the same rewrite proofs allthough with different metavariables.

#theorem()[If the algorithm $mono("Rew")_rho (Psi, t : tau)$ provides a proof for $?_r space t space u$ where $?_r$ is of type $mono("relation") tau$ and $t != u$ for any given $tau$, $t$, $rho$, and $Psi$ then the modified algorithm $mono("Subterm")_rho (Psi, t, ?_r)$ provides either a proof for $?_r space t space u$ if the relation inference $?_r$ succeeds (See TODO) or otherwise a proof of $?_r' space t space u$ where $?_r' : mono("relation" tau)$ is a fresh metavariable of the same type. If $t = u$ the `Subterm` algorithm with the same arguments returns just the flag `identity` whereas the `Rew` algorithm provides a proof $p : ?_r space t space t$.]

#proof()[We show the premise by structural induction over the term $t$. The cases for lambda, pi, and arrow only differ by the additional status field. It suffices to show that applying a proof of identity ($?_r space t space t$) is equivalent to leaving $t$ unchanged. The application case can be proven by induction over the application subterms $e_0 space dots space e_n$. We start with the base case $n = 2$ (a function with one argument) and have to consider the three cases (identity, success), (success, identity), (identity, identity) under the assumption that the case (success, success) is not possible with a binary well-formed Lean application as for any $f e$ the types $f : sigma -> tau$ and $e : sigma$ cannot be the same, thus cannot both unify:

*$"Case binary application with" n = 2 space (e_0 space e_1)$*

*Case $e_0 space e_1$ with $rho : r space e_0 space u$*

The minimal case of a function application with one argument where the function unifies and the argument does not.

*Proof Resulting from Rew*\
  Given the outputs $r_e_0 : "relation" alpha -> tau$, $u : alpha -> tau$, and $p_e_0 : r_e_0 space e_0 space u$ of $mono("Rew")_rho (Psi, e_0)$ and the given outputs $r_e_1 : "relation" alpha$ and $p_e_1 : space r_e_1 space e_1 space e_1$ of $mono("Rew")_rho (Psi, e_1)$ the `Rew` algorithm combines the proofs and carrier relations into a final proof of $r_tau : (e_0 space e_1) space (u space e_1)$ where $r_tau$ is of type `relation` $tau$:

$#align(center)[
  $"Subrelation.subrelation" (alpha → tau) space r_e_0 space (r_e_1 ==> r_tau) \ (?_s : "Subrelation" space r_e_0 space (r_e_1 ==> r_tau)) space e₀ space u space p_e_0 space e₁ space e₁ space p_e_1 & : r_tau space (e_0 space e_1) space (u space e_1)$]$

*Proof Resulting from Subterm*:\
  Given $e_0 : alpha -> tau$ and $e_1 : alpha$ where $e_0$ unifies with the left hand side we follow the case where we build pointwise relation constraints (TODO: ref algo line 8) and obtain the following proof of $r_tau (e_0 space e_1) space (u space e_1)$ from the `Subterm` algorithm where $r_tau$ is of type `relation` $tau$ and $r$ of type `relation` $alpha -> tau$:

$#align(center)[$
  "Subrelation.subrelation" (alpha → tau) space r space ("pointwiseRelation" alpha space r_tau) \ space (?_s : "Subrelation" r space ("pointwiseRelation" alpha space r_tau)) space e₀ space u space h space e₁ & : space r_tau space (e₀ space e₁) space (u space e₁)$]$

The equivalence of the two produced proofs holds by proof irrelevance.
TODO: word it differently

*Case $e_0 space e_1$ with $rho : r space e_1 space u$*

When only the left hand side of this minimal binary application unifies with $rho_"lhs"$:\
*Proof Resulting from Rew*:\
  Given the outputs $r_e_0 : "relation" alpha -> tau$ and $p_e_0 : r_e_0 space e_0 space e_0$ of $mono("Rew")_rho (Psi, e_0)$ and the given outputs $r_e_1 : "relation" alpha$, $u : alpha$, and $p_e_1 : r_e_1 space e_1 space u$ of $mono("Rew")_rho (Psi, e_1)$ the `Rew` algorithm combines the proofs and carrier relations into a final proof of $r_tau : (e_0 space e_1) space (e_0 space u)$ where $r_tau$ is of type `relation` $tau$:

  $#align(center)[
  $"Subrelation.subrelation" (alpha → tau) space r_e_0 space (r_e_1 ⟹ r_tau) space (?_s : "Subrelation" r_e_0 space (r_e_1 ⟹ r_tau)) &\ space e_0 space e_0 space p_e_0 space e_1 space u space p_e_1 & : r_tau space (e_0 space e_1) space (e_0 space u)$]$

*Proof Resulting from Subterm*:\

  With function argument unifying we recursively invoke $mono("Subterm"_rho) (Psi, e_0, r_tau : "relation" tau)$ and $mono("Subterm"_rho) (Psi, e_1, r_tau)$. The first is flagged `identity` and thus returns no information. The latter results in a relation $r_e_1 : "relation" alpha$, and a proof $p_e_1 : r_e_1 space e_1 space u$. The algorithm then constructs a proof of $r_tau space (e_0 space e_1) space (e_0 space u)$:

  $#align(center)[
  $"Proper.proper" (alpha → tau) space (r_e_1 ⟹ r_tau) space e_0 space (?_p : "Proper" (r_e_1 ⟹ r_tau) space e_0) space e_1 space u space p_e_1 & : r_tau (e_0 space e_1) space (e_0 space u)$]$

Our assumption that $mono("Rew")_rho (Psi, e_0 space e_1)$ returning $r_tau space (e_0 space e_1) space (e_0 space u)$ implies $mono("Subterm"_rho) (Psi, e_0 space e_1, r_tau)$ returning $r_tau space (e_0 space e_1) space (e_0 space u)$ holds.

*Case $e_0 space e_1$ where $rho$ does not unify given $rho : r space u space u'$*
*Proof Resulting from Rew*:\

  Given the outputs $r_e_0 : "relation" alpha -> tau$ and $p_e_0 : r_e_0 space e_0 space e_0$ of $mono("Rew")_rho (Psi, e_0)$ and the given outputs $r_e_1 : "relation" alpha$ and $p_e_1 : space r_e_1 space e_1 space e_1$ of $mono("Rew")_rho (Psi, e_1)$ the `Rew` algorithm combines the proofs and carrier relations into a final proof of identity $r_tau (e_0 space e_1) space (e_0 space e_1)$ under the relation $r_tau$ of type `relation` $tau$:

$#align(center)[
$"Subrel.subrelation" (alpha → tau) space r_e_0 space (r_e_1 ⟹ r_tau) space (?_s : "Subrelation" r_e_0 (r_e_1 ⟹ r_tau)) \ space e_0 space e_0 space p_e_0 space e_1 space e_1 space p_e_1 & : r_tau space (e_0 space e_1) space (e_0 space e_1)$]$

*Proof Resulting from Subterm*:\
  While `Subterm` would simply return `identity` for such a rewrite, exiting at (TODO line 37). As `Rew` returns proof of $r_tau space t space t$ this case also holds.

*Inductive case for $n + 1$ application subterms*

We can now assume that we have a given application sequence where both algorithms produce the same rewrite proofs (carrier relation may still differ). Our induction hypotheses states that:

$(Psi', r, e_0 ' space dots space e_n ', p : r space (e_0 space dots space e_n) space (e_0' space dots space e_n')) := mono("Rew"_rho) (Psi, e_0 space dots space e_n)$ implies:\ $(Psi'', r',e_0 ' space dots space e_n ', p' : r space (e_0 space dots e_n) space (e_0 ' space dots space e_n ')) := mono("Subterm"_rho) (Psi, e_0 space dots space e_n, r)$ if $e_0 space dots space e_n != e_0 ' space dots space e_n '$ \ and $(Psi'', mono("identity")) := mono("Subterm"_rho) (Psi, e_0 space dots space e_n, r)$ otherwise.

We must now also show that:\ $(Psi', r, e_0 ' space dots space e_n ' space e_(n+1) ', p : r space (e_0 space dots e_n space e_(n+1)) space (e_0 ' space dots e_n ' space e_(n+1) ')) := mono("Rew"_rho) (Psi, e_0 space dots space e_n space e_(n+1) ')$\
implies the following if $e_0 space dots space e_(n+1) != e_0 ' space dots space e_(n+1) '$:\
$(Psi'', r', e_0 ' space dots space e_n ' space e_(n+1) ', p' : r' space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1) ')) := mono("Subterm"_rho) (Psi, e_0 space dots space e_n space e_(n+1), r)$ 
and $(Psi'', mono("identity")) := mono("Subterm"_rho) (Psi, e_0 space dots space e_n space e_(n+1), r)$ otherwise.

There are four cases for the inductive step. Either the previous sequence was an identity rewrite in which case we must divide between another identity rewrite or a successful rewrite. If the previous sequence contains a successful rewrite we also have the scenarios of another rewrite or a final identity. This differenciation is crucial to align with the Leading Identity Rewrite and Identity/Success Status optimisation.

*Case $e_0 space dots space e_n space e_(n+1)$ where a rewrite occurred in $e_0 space dots space e_n$ and $e_(n+1)$ unifies with $rho_"lhs"$*

*Proof Resulting from Rew*

We can proof this similarly to the base case as we always treat applications binary here and read left-to-right. We know from our induction hypotheses that we obtain a single relation, proof, and rewritten term from the rewrite on $e_1 space dots space e_n$. Let the relation be $r_e_n : "relation" (alpha_0 space dots space alpha_n space tau)$. As we only consider well-formed applications and we are considering the last element of such an application we can imply that $r_e_n$ must be a an arrow type. Let the recursively obtained proof be $p_e_n : r_e_n (e_0 ' space dots space e_n ') space (e_0 space dots space e_n)$, and thus $e_0 ' space dots space e_n '$ the rewritten term. Similarly the recursive invocation $mono("Rew")_rho (Psi, e_(n+1))$ outputs $r_e_(n+1) : "relation" alpha_(n+1)$, $u : alpha_(n+1)$, $p : r_e_(n+1) space e_(n+1) space u$. $r_tau$ is again the carrier relation for the resulting proof after combining the previous and current application rewrites to a proof of $r_tau (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1) ')$:

$#align(center)[
  $"Subrelation.subrelation" (alpha_(n+1) -> tau) space r_e_n space (r_tau ==> r_e_(n+1)) space (?_s: "Subrelation" r_e_n space (r_tau ==> r_e_(n+1))) space (e_0 space dots space e_n) space (e_0 ' space dots space e_n ') space p_e_n space e_(n+1) space u space p_e_(n+1) : r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1) ')$]$

*Proof Resulting from Subterm*

Knowing that unification of $e_(n+1)$ with the left hand side of $rho$ implies that $e_0$ was not rewritten and eliminates the possibility that the proof of the rewrite on $e_0 space dots space e_n$ consists of pointwise relation chains. Thus, we know that the current proof is a yet incomplete Proper respectful chain $"Proper.proper" (alpha_0 space dots space alpha_n space tau) space (?_r_0 ==> dots ==> ?_r_n ==> r_(alpha_n -> tau)) space e_0 space e_0 ' space p_e_0 space dots space e_n space e_n ' space p_e_n$ which has the type $r_(alpha_n -> tau) space (e_0 space dots space e_n) space (e_0 ' space dots space e_n ')$ where $r_(alpha_n -> tau) : "relation" alpha_n -> tau$ is the desired output relation. The recursive call on $mono("Subterm"_rho) (Psi, e_(n+1), )$ returns the carrier relation $r_e_(n+1) : "relation" alpha_(n+1)$, the updated term $e_(n+1) '$, and the proof $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1) '$. The algorithm then embeds the results into the current proof and returns a final proof of $r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1) ')$ with $r_tau$ being of type `relation` $tau$:

$"Proper.proper" (alpha_0 space dots space alpha_n space alpha_(n+1) space tau) space (?_r_0 ==> dots ==> ?_r_n ==> r_e_(n+1) ==> r_tau) space e_0 space e_0 ' space p_e_0 space dots space e_n space e_n ' space p_e_n space e_(n+1) space e_(n+1) ' space p_e_(n+1) : r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1) ')$

This case holds by our assumption TODO: index assumption cases.

*Case $e_0 space dots space e_n space e_(n+1)$ where a rewrite occurred in $e_0 space dots space e_n$ and $e_(n+1)$ does not unify with $rho_"lhs"$*

*Proof Resulting from Rew*

This case is similar to the previous one as `Rew` doesn't change depending on how the proof looks. Let the relation be $r_e_n : "relation" (alpha_0 space dots space alpha_n)$. Let the proof be $p_e_n : r_e_n (e_0 ' space dots space e_n ') space (e_0 space dots space e_n)$, and $e_0 ' space dots space e_n '$ the rewritten term. The recursive invocation $mono("Rew")_rho (Psi, e_(n+1))$ outputs $r_e_(n+1) : "relation" alpha_(n+1)$, $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1)$. $r_tau$ is again the carrier relation for the resulting proof after combining the previous and current application rewrites to a proof of $r_tau (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1))$:

$#align(center)[
  $"Subrelation.subrelation" (alpha_(n+1) -> tau) space r_e_n space (r_tau ==> r_e_(n+1)) space (?_s : "Subrelation" r_e_n space (r_tau ==> r_e_(n+1))) space (e_0 space dots space e_n) space (e_0 ' space dots space e_n ')
  p_e_n space e_(n+1) space e_(n+1) space p_e_(n+1) : r_tau (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1))$]$

*Proof Resulting from Subterm*

When a previous rewrite occurrd we have to consider two sub-cases. Either the rewrite occurred on the very first argument $e_0$ and thus constructs a pointwise relation chain or some arguments of $e_1 space dots e_n$ were rewritten in which case we must consider a respectful chain.

In case of the successful rewrite on $e_0$ we obtain the desired proof $r_tau space (e_0 space dots space e_(n+1)) space (e_0 ' space e_1 space dots space e_(n+1))$ given the newly created carrier relation $r_tau : "relation" tau$ and the given $r_e_0$ of type `relation` $alpha_0 -> space dots space alpha_n -> tau$:

$#align(center)[$"Subrelation.subrelation" (alpha_0 space dots space alpha_(n + 1) space tau) space r_e_0 space ("pointwiseRelation" alpha_0 (dots ("pointwiseRelation" alpha_(n+1) space r_tau)dots) space
  (?_s : "Subrelation" r_e_0 space ("pointwiseRelation" alpha_0 (dots ("pointwiseRelation" alpha_(n+1) space r_tau)dots)) space e_0 space e_0 ' space p_e_0 space e_1 space dots space e_(n+1) : r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n space e_(n+1))$]$

In the other case we obtain the desired proof $r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1))$ given the newly created carrier relation $r_e_(n+1) : "relation" alpha_(n+1)$ and identity proof $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1)$:

$#align(center)[$"Proper.proper" (alpha_0 -> dots -> alpha_n -> "Prop") space (?_r_0 ==> dots ==> ?_r_n ==> ?r_(n+1) ==> r_tau) space e_0 space (?_p : "Proper" (?_r_0 ==> dots ==> ?_r_n ==> ?r_(n+1) ==> r_tau) space e_0) space e_1 space e_1 ' space p_e_1 space dots space e_(n+1) space e_(n+1) ' space p_e_(n+1) : r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 ' space dots space e_n ' space e_(n+1))$]$

Both sub-cases hold by our assumption.

*Case $e_0 space dots space e_n space e_(n+1)$ where no rewrite occurred in $e_0 space dots space e_n$ and $e_(n+1)$ unifies with $rho_"lhs"$*

*Proof resulting from Rew*

Let the identity proof be $p_e_n : r_e_n space (e_0 space dots space e_n) space (e_0 space dots space e_n)$. The recursive invocation $mono("Rew")_rho (Psi, e_(n+1))$ outputs the relation $r_e_(n+1) : "relation" alpha_(n+1)$, the updated term $e_(n+1) '$, and the proof $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1) '$. $r_tau$ is the carrier relation for the resulting proof after combining the previous and current application rewrites to a proof of $r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 space dots space e_n space e_(n+1) ')$:

$#align(center)[
  $"Subrelation.subrelation" (alpha_(n+1) -> tau) space r_e_n space (r_tau ==> r_e_(n+1)) space (?_s : "Subrelation" r_e_n space (r_tau ==> r_e_(n+1))) space (e_0 space dots space e_n) space (e_0 space dots space e_n ) space p_e_n space e_(n+1) space e_(n+1) ' space p_e_(n+1) : r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 space dots space e_n space e_(n+1) ')$]$

*Proof Resulting from Subterm*

The subterm algorithm ignores arguments up until they can be rewritten. Thus, the application $e_0 space dots space e_n$ remains unchanged and we build the Proper constraint based of the relation $r$, the new term $e_(n+1) '$, and the proof $p : r space e_(n+1) space e_(n+1) '$ and curry all unchanged arguments $e_0 space dots space e_n$. The algorithm results in a proof for $r_tau e_0 space dots space e_(n+1) space e_0 space dots space e_(n+1) '$ with $r_tau$ of type `relation` $tau$:

$#align(center)[$"Proper.proper" (alpha -> tau) space (r ⟹ r_tau) space (e_0 space dots space e_n) space ("Proper" (r ⟹ r_tau) space (e_0 space dots space e_n)) space e_(n+1) space e_(n+1) ' space p : r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 space dots space e_n space e_(n+1) ')$]$

The premise holds by proof irrelevance.

*Case $e_0 space dots space e_n space e_(n+1)$ where no rewrite occurred in $e_0 space dots space e_n$ and $e_(n+1)$ does not unify with $rho_"lhs"$*

*Proof Resulting from Rew*

Let the carrier $r_e_n : "relation" alpha_n -> tau$ identity proof be $p_e_n : r_e_n (e_0 space dots space e_n) space (e_0 space dots space e_n)$. The recursive invocation $mono("Rew")_rho (Psi, e_(n+1))$ outputs the relation $r_e_(n+1) : "relation" alpha_0$ and the second identity proof $p_e_(n+1) : r_e_(n+1) space e_(n+1) space e_(n+1)$. $r_tau$ is the carrier relation for the resulting proof after combining the previous and current application rewrites to a proof of $r_tau (e_0 space dots space e_n space e_(n+1)) space (e_0 space dots space e_n space e_(n+1))$ with $r_tau$ of type `relation` $tau$:

$#align(center)[
  $"Subrelation.subrelation" (alpha_(n+1) -> dots -> tau) space r_e_n space (r_tau ==> r_e_(n+1)) space (?_s : "Subrelation" r_e_n space (r_tau ==> r_e_(n+1))) space (e_0 space dots space e_n) space (e_0 space dots space e_n)
  p_e_n space e_(n+1) space e_(n+1) space p_e_(n+1) : r_tau space (e_0 space dots space e_n space e_(n+1)) space (e_0 space dots space e_n space e_(n+1))$]$

*Proof Resulting from Subterm*

The subterm algorithm terminates at (TODO line 37) and merely returns `identity` which holds with our assumption and the fact that the `Rew` algorithm provides a proof of $r_tau space t space t$ in this case.

]

To show that both algorithms result in the same rewrites we need to prove another theorem about the transition to implications.

#theorem()[If the return values $p$, $?_r$, and $u$ of $mono("Rew")_rho (Psi, t : mono("Prop"))$ passed to $mono("InferRel") (p, ?_r, t, u)$ provide a proof $?_s$ for $t <- u$ with $t != u$ then the return values $p'$, $?_r '$, and $u'$ of the modified algorithm $mono("Subterm")_rho (Psi, t, <-)$ passed to $mono("InferRel") (p', ?_r', t, u)$ also provide a proof $?_s '$ for $t <- u$. \ $mono("Subterm")$ just returns `identity` if $mono("InferRel") compose mono("Rew")$ returns a proof $t <- t$.]

#proof()[To prove that both algorithms result in the same rewrite proof if the rewrite changes $t$ can be shown with the following case distinction:

=== Case $t$ can be rewritten to $u$ and $p' = (t <- u)$

In this case the `InferRel` algorithm leaves $p'$ unchanged so that $?_s ' = p'$ and $?_s : t <- u$. The output of `InferRel` $?_s$ given the return values of `Rew` also returns a proof for $t <- u$ by constructing the subrelation constraint: $"Subrelation.subrelation Prop" space ?_r space (<-) space (?_s : "Subrelation" space ?_r space (<-)) space t space u : t <- u$

=== Case $t$ can be rewritten to $u$ and $p' != t <- u$

In case the internal relation inference of the `Subterm` algorithm fails the proofs $p$ and $p'$ are of the same structure but contrain different relation metavariables of type `Prop`. This means the `InferRel` function treats them the same producing $"Subrelation.subrelation Prop" space ?_r space (<-) space (?_s : "Subrelation" space ?_r space (<-)) space t space u : t <- u$ for the proof based `Rew` and $"Subrelation.subrelation Prop" space ?_r ' space (<-) space (?_s' : "Subrelation" space ?_r ' space (<-)) space t space u : t <- u$ for the proof based on `Subterm`. Those are again equal by proof irrelevance.

=== Case $t$ can only be rewritten to $u$ if $t = u$

If there is no constructive rewrite then the optimized algorithm generates no proof and returns with an `identity` status. The `Rew` algorithm produces a proof $p : ?_r t t$ in such a case and infers it to a proof $?_s : t <- t$ in the second case of `InferRel`: $"Subrelation.subrelation Prop" space ?_r space (<-) space (?_s : "Subrelation" space ?_r space (<-)) space t space t : t <- t$ which, when applied, is equivalent to leaving $t$ unchanged as the `Subterm` algorithm would.
]

#pagebreak()

= Related Work

= Conclusion

#pagebreak()

#bibliography("refs.bib", full: true, title: "References")
