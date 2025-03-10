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

Rewriting in theorem provers is the process of replacing a subterm of an expression with another term. When and if such a rewrite can happen depends on the context, i.e., the information we have about the two terms. In Lean, rewriting is possible when two terms $t$ and $u$ are equal $t = u$ or with respect to the `propext` axiom when two propositions $p : mono("Prop")$ and $q : mono("Prop")$ imply each other $p <-> q$. This allows us to replace a term in a goal we want to solve or inside one of our hypothesis when doing reasoning in Lean.

This allows us to proof mathematical propositions such as the commutativity for multiplication. In the below example we can see a lean proof of the commutativity of multiplication given that additon is commutative:

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

In this example we want to proof that for any natural numbers $n$ and $m$ the multiplication $n dot m$ is equal to $m dot n$. In Lean, we do this using structural induction #footnote[Structural induction means that the induction follows the structure of the inductive type.] on the inductive type $NN$ which consists only of two constructors, `zero` for constructing 0 and `succ` for constructing any successor number. After unfolding the `mul` definition in line 6 we are left with a goal $("succ" m) dot n = n + (n dot m)$. The `mul_succ` theorem has the type $("succ" m) dot n = (m dot n) + n$. The theorems left hand side matches the left hand side of the theorem and thus we can rewrite it (replacing the left hand side of the goal with the right hand side of our theorem). The resulting goal is $(m dot n) + n = n + (n dot m)$ which can be closed by another rewrite with an addition commutativity theorem and finally the induction hypothesis ($m dot n = n dot m$) which also proves equality and can thus be used in a rewrite.

While this is sufficient considering the many helpful theorems and tactics Lean 4 offers, there are some cases @iris TODO where it would be helpful to consider more general rewrites that exceed equality and if and only if. When we try to solve a goal in a theorem prover we usually have a given set of hypothesis and can access theorems that we've already proven as well as tactics that can apply multiple theorems. When we want to rewrite a goal which contains a term $t$ that we want to change to a term $u$ we can perform a rewrite by simply showing that $u$ implies $t$ and thus it suffices to show $u$. The relation ($<->$) is convenient because it gives us such an implication per definition. However it is possible to perform a rewrite using any relation that can lead to the desired implication.

In the Lean and Coq theorem provers relations on a type $alpha$ are defined by $alpha arrow alpha arrow mono("Prop")$. When we want to proove a goal $t : mono("Prop")$ and have the hypothesis of $u : mono("Prop")$ as well as a proof $h$ of $r space t space u$ given $r$ is a relation $mono("Prop") arrow mono("Prop") arrow mono("Prop")$ we can proof the statement given we have the additional information that $r$ implies ($<-$), essentially ($<-$) is a subrelation of $r$. When those hypotheses are in place the proof is straight forward for this minimal example. By Leans definition of subrelations it suffices to show $r space t space ?_t$ and $?_t$. The question marks refer to missing values that can be filled with any given term that matches its type (metavariables in Lean or existential variables in Coq). Metavariables are also used to represent goals in Lean. Metavariables of a certain type $tau$ in can be assigned with any value $Gamma tack e : tau$ in the current context $Gamma$ (hypotheses, theorems, etc.). When we assign a metavariable that represents a goal we also close the goal. Another way to use metavariables is to use them as placeholders in any given Lean term when the value is unknown at the time of creation. It is also possible to share a metavariable $?_x$ accross multiple terms as seen in this example. Assigning it with a value $v$ also assigns every occurance of $?_x$ with $v$. We can thus assign $?_t$ with $u$ and use our hypothesis that proves $u$ to complete the proof of our simple rewrite.

This approach is tedious to be performed manually especially when the goal is more complicated or the term we intend to rewrite is bound by lambda expressions or an all quantifier. When we want to prove a goal $p and q$ with the same context for instance, and we need to rewrite $p$ to $q$ inside the left-hand side of the conjunction (replace $p$ the  without modifying the remaining term), the proof of that rewrite requires us to set a new subgoal $p and q -> q and q$, solve that by the rule for conjunction introduction leaving $t$ and $u$ as sub-subgoals. $u$ can be proven by our hypothesis and the proof for $t$ is the same procedure as for the minimal rewrite example above. Even this approach is specific to conjunctions and can't be extended for other propositions.

A better approach for a general way of rewriting with arbitrary relations is the Morphism framework introduced by Mattheiu Sozeau @sozeau:inria-00628904 consisting of `respectful` and `Proper` definitions that can construct proofs for arbitrary terms using a syntax-directed algorithm. The `Proper` definition in @ProperDef merely takes a relation $r$ and an element $m$ in that relation demanding reflexivity of that element. Whenever this definition holds we call $m$ a `Proper` element of $r$ meaning that $m$ is a morphism for $r$. The `respectful` definition seen in @respectfulDef denoted as ($==>$) is Coqs notion for signatures. This definition can produce very general implications for a variety of functions. For instance, the contrapositive theorem $forall a b : mono("Prop"), (a -> b) -> (not b -> not a)$ can be stated as $((->) ==> (<-)) space (not) space (not)$. We can even simplify the contrapositive theorem by leveraging `Proper` and `respectful` with $"Proper" ((->) ==> (<-)) space (not)$. We can use the same framework to specify the above rewrite $p and q -> q and q$ in a more general way for instance when we create a term $?_p$ of type $"Proper" ((=) ==> (<->) ==> (<-)) space (and)$ translates to $forall x y, x = y -> forall x' y', x' <-> y' -> (x and x' <- y and y')$. When instantiating the variables in $?_p$ for instance with $p, q, h : p = q, q, q, (h' : b <-> b)$ we would get a proof for $(p and q <- q and q)$.

Note that for this case it does not matter whether we have ($<->$), ($->$), or ($=$) as the middle argument for the respectful chain. In fact any reflexive relation over `Prop` would work here. Proceeding with this framework we have to be mindful of what problems we can simplify with `Proper` and `respectful` proofs, which relations we use inside such a chain, how to choose the first and final relation, and finally what element we want to be Proper under the sequence of `respectful` relations.

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

The Coq library for morphisms has many theorems that operate on `Proper` and `respectful` terms which helps to construct and solve theorems containing morphisms and signatures. This allows us to use the same structrue and theorems for rewrites in different terms. The proof construction for $p and q <- q and q$ and $p or q <- q or q$. This generalisation is the base for an algorithm proposed by Matthieu @sozeau:inria-00628904 that automatically produces rewrite proofs for any given `Proper` relation where the term to be rewritten can be behind binders and nested in other structures. There is one more definition that makes the proposed algorithm more powerful. When we have $"Proper" (A ==> B) space f$ and we know that $B$ is a subrelation of $C$ we can imply $"Proper" (A ==> C) space f$.

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

The core idea of the approach for rewriting proposed in @sozeau:inria-00628904 is to break down generalised rewriting into two parts. The first part is an algorithm that generates a large proof skeleton for the rewrite leveraging `Proper`, `respectful`, and `Subrelation` as seen above. In previous examples we have seeen that while we know what types such a proof must have we don't always know the actual instances of the `Proper` or `Subrelation` classes. They each only have a single constructor. We know that a proof for a `Subrelation` term must be constructed with `Subrelation.subrelation` meaning a proof that for a given relation $q$ and a given relation $r$, all $x$ and $y$ must satisfy $q space x space y -> r space x space y$ and similarly for `Proper` proofs. We may however now always know the proof for $forall x y, q space x space y -> r space x space y$. This is why the algorithm uses metavariables for those instances and for some of the subterms. For instance a proof skeleton for a simple atomic term $p : mono("Prop")$ and a proof $h : r space p space q$ would be a proof $mono("Subrelation.subrelation (Prop)") r space (<-) space ?_m space p space q space h$. Notice that $?_m$ is a metavariable of type $mono("Subrelation" r space (<-))$ which unfolds to $forall x y, r space x space y -> (x <- y)$. The application $?_m space p space q space h$ gives us the desired rewrite. The assignment for the metavariable $?_m$ is unknown and left as a hole in this proof. With more nested terms this alrithm collects multiple unassigned metavariables.

This is where the second part of the proposed approach, a proof search comes into play. In Coq this proof search is realised using type class relsoltuion. Type class resolution in Coq searches through user defined instances of a type class and applies those instances. For example the instance `iff_impl_subrelation` is an instance for the subrelation typeclass in Coq that provides a proof for $mono("Subrelation" (<->) space (<-))$ which can be leveraged whenever the rewrite relation is $(<->)$.

The algorithm in TODO:algoref is an imperative translation of the declarative algorithm proposed in @sozeau:inria-00628904 that we implemented in Lean 4. The algorithm is syntax directed and covers every term that can be constructed in Lean. Note that terms in Lean 4 can be of type `bvar`, `fvar`, `mvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`, `lit`, `mdata`, and `proj`. The algorithm divides between `app`, `lam`, `forallE`, and `const`. All remaining cases are treated as constants (`const`). The algorithm takes an empty constraint set $Psi$, a term $t$ in that we want to rewrite and a constant proof $rho$ that is of the type $r a b$ where $r$ is a relation, $a$ is a term we want to rewrite in $t$ and $b$ is the value we want to replace $a$ with. The algorithm outputs a modified set $Psi$ which contains all holes in the rewrite proof that can't be determined in some of the cases of the algorithm (represented in metavariables in Lean), a carrier relation $r$ for the rewrite, the modified term $u$ and finally the proof for the rewrite. At the beginning we always check whether the term we want to rewrite unifies directly for the given proof $rho$. In that case the proof-result for a rewrite would just be $rho$. Because $rho$ (and any proof-result of this algorithm) is not of the type $t <- u$ we will wrap the output of the algorithm in a proof for $"Subrelation" r space (<-)$.

Whenever the term does not unify directly we examine the structure and use a different approach depending on whether $t$ is an application, lambda, dependent/non-dependent arrow, or constant. Whenever we encounter an application $f space e$ we perform a recursive call on both $f$ and $e$. We use the obtained carrier relation, proof, and term to construct a proof that $r_f$ is a subrelation of $r_e ==> ?_T$. This is where the first holes occur that we collect in the constraint set. This generates a proof for $r t u$. Recall that we construct a $"Subrelation" r space (<-)$ after invoking `Rew` which leads to a proof of $t <- u$.

For rewrites inside lambda terms we bind $x : tau$ to the local context and perform a recursive rewrite on the body of the lambda. The resulting proof wrapped in a fresh lambda expression binding $x : tau$ represents the proof for $r space (lambda x:tau. b) space (lambda x:tau. b')$ again progressing to $(lambda x:tau. b) <- (lambda x:tau. b')$ eventually.

All other cases leverage either the lambda or application cases by converting them slightly to fit in the scheme. The non-dependent arrow case is simply transformed into a function that represents an arrow. This has the advantage that locally declared functions (`impl` in this case) are considered constants in Lean and thus reuse the already defined application case. Similarly, for the case of an all quantifier that uses a local dependent function `all`.

Finally, we will take a look the last case is triggered whenever none of the above cases match. This is the case for constants such as `all`, `impl`, or simply for atoms that don't unify at the beginning of the `Rew` function. In this case we construct another metavariable of type $"Proper" tau space ?_r t'$ that is treated as a hole at the bottom of the proof tree and essentially represents and identity rewrite from $t$ to $t$. This will always happen for this algorithm as we never specify the desired relation for the proof and generate metavariables whenever we don't know the relation.

== Examples

Let's recall the rewrite from $p and q$ to $q and q$ for a given relation $r$ that is a subrelation of $(<-)$ and a given proof $h : r space p space q$. The algorithm first tries to unify the entire term $p and q$ with the left-hand side of our proof ($p$). Conjunctions in Lean are defined by the `And` structure and thus our term $t$ is interpreted as $mono("And") p q$ which must be read as $(mono("And") p) q$. This falls into the `app` case such that we first interpret $(mono("And") p)$ followed by $q$. Again $(mono("And") p)$ doesn't unify with $p$ and follows another `app` iteration for `And` and $p$. `And` itself does not unify and does not match any other category. So the algorithm treats it as an atom (`const`) and generates a metavariable $?_(mono("And_")r) : "relation" ("relation Prop")$ and passes ($?_(mono("And_")m) : "Proper" ("relation" mono("Prop")) space ?_(mono("And_")r) mono("And")$) for the proof of identity. The next term in line ($p$) does indeed unify with $p$ and is therefore replaced with $t$. For now the proof-placeholder will be just $h$. After the two recursive Rew-calls terminate we combine the proofs and carrier relations for a proof of $r space (mono("And") space p) space (mono("And") space q)$. We start with another hole $?_(mono("And_")p) : "subrelation" ?_(mono("And_")r) (r ==> (?_T : "relation (Prop" -> "Prop)"))$. Recall that `Subrelation` is a typeclass with only constructor `subrelation`. Thus any metavariable of type `Subrelation` must be of that constructor and eventually unfolds to $forall r_1 space r_2, ?_"rel" space r_1 space r_2 -> forall x space y, r space x space y -> ?_T space x space y -> ?_T (r_1 space x) space (r_2 space y)$. This allows us to construct the desired proof by carefully applying the arguments $?_(mono("And_")p) mono("And") mono("And") space ?_(mono("And_")m) space p space q space h$. By instantiating $r_1$ and $r_2$ with the `And` relation and $p$ and $q$ for $x$ and $y$ we receive our desired rewrite proof for this part of the term $?_(mono("And_")T) $.

The next rewrite to be evaluated is the identity rewrite for $q$. We follow the same proceedure as for the `And` rewrite generating $?_(q"_"r) : mono("relation Prop")$ and the proof ($?_(q"_"m) : mono("Proper Prop") space ?_(q"_"r) space q$). The final merge step will combine both proofs in another subrelation $(?_(mono("And_")p"_"q) : mono("subrelation") space ?_T (?_(q"_"r) ==> (?_T' : mono("relation Prop"))))$. The algorithm then outputs $?_(mono("And_")p"_"q) space (mono("And") p) space (mono("And") q) space (?_(mono("And_")p) mono("And") mono("And") space ?_(mono("And_")m) space p space q space h) space q space q space ?_(q"_"m)$ which is a proof for $?_T' space (p and q) space (q and q)$.

There are two issues with this proof. The first issue is that the rewrite proof output of $"Rew"_h (emptyset, p and q)$ is not an implication ($<-$) but an unknown relation $?_T'$. This can easily be fixed by creating another metavariable $?_"final"$ as a placeholder for a proof that $?_T'$ is a subrelation for ($<-$). That brings us to the second problem that the proofs contains many holes that need to be replaced with proofs. The paper @sozeau:inria-00628904 suggests a proof search that operates depth first search on the constraint set (set of metavariables).

For the example of $p and q$ we collect the metavariables as we create them and end up with the final constraint set ${?_T, ?_(mono("And_")r), ?_(mono("And_")m), ?_(mono("And_")p), ?_(q"_"r), ?_(q"_"m), ?_(mono("And_")p"_"q), ?_T', ?_"final"}$. In our Lean 4 implementation we solved those goals using aesop TODO cite using a custom rule set containing the theorems and tactics mentioned in the Coq Morphism library TODO cite.

== Challenges in Practice

The algorithm proposed by @sozeau:inria-00628904 can rewrite behind binders and within arbitrary terms in our Lean 4 implementation. However when trying to solve larger instances we run into serious performance issues. There are two main reasons for this.

The first challenge when applying this approach in practice is that even for terms where no rewrite occurs the amount of generated constraints is quadratic in the number of subterms, thus exponential in terms of the depth of a term tree TODO: double check. The proof search itself is exponential TOOD.

The other reason those constraints are difficult to solve is that nested subrelation proofs are more difficult to find than just `Proper` and `respectful` instances.

TODO: blowup example

#algo(
  row-gutter: 7pt,
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
    return ($Psi'' union Psi'''$, $?_T$, $"app" u_f u_e$, $?_"sub" f u_f p_f e u_e p_e$)#d\
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

== Optimisations

The actual Coq implementation of generalised rewriting contains a few optimisations not mentioned in the paper. Through reverse engineering a large amount of the coq core module we were able to extract the most crucial optimisations and applied them to our imperative algorithm specification. The alogrithm we've seen so far stresses the use of applications and aims to convert other terms into application-terms. Thus, most of the following optimisations focus on simplifying application proofs.

=== Identity and Success Status

In our examples we saw that even rewrites where most terms do not contain the left hand side term of the rewrite relation. However we would still examine those terms and produce two metavariables just to create a proof of identity $h : t -> t$. This can be simplified by differenciating between subterms depending on whether they can be rewritten or recursively rewritten or remain the same. We change the output type of the algorithm to a sum type with two variants. The `identity` variant carries no further information and signals that a term cannot be rewritten. The other variant `success` carries the same information as seen before, in essence, the carrier relation, the updated term, and the proof of the rewrite. Now every time all of the recursive invokations result in identity rewrites the current rewrite will also be an identity rewrite. For instance, an application $f and e$ where both $"Rew"_rho (Psi, f)$ and $"Rew"_rho (Psi, e)$ result in identity rewrites the result for $"Rew"_rho (Psi, f space e)$ will also result in an identity rewrite. When considering a term $q and q and p and q and q$ given $h : p <-> q$ we would only consider the $q$ in the middle and would not create proofs and carrier relations for the four conjunctions and four $q$'s. The worst case complexity is still the same here, however in practice we usually have a lot of cases that cannot be rewritten specially as we transform arrow and pi types to id applications aswell.

=== Top-down Relation Passing

The algorithm described so far generates mata variables for relations whenever we don't know which relation we're supposed generate a proof for. We then return those relations recursively and build subrelations to infer the desired relation (eventually ($<-$)). We consider this a bottom-up approach where those metavariables originate from the leafs of such a term tree and are passed upwards. This creates a lot of subrelation constraints that were not necessary in the first place. We can avoid this by passing an additional parameter to recursive calls (top-down) that contains the desired relation for a proof. We do this by initially providing ($<-$) as the desired relation and pass it along in the lambda, pi, and arrow case. In recursive call as part of the application case we generate a metavariable for a relation of the type of the applicant we rewrite for and pass it to both recursive calls. This invalidates the need for subrelations in the application rule and at the top of the term. TODO example.

=== Interpret Applications as Sequence

When introducing the `Proper` and `respectful` definitions we gave an example for a possible rewrite proof of $p and q -> q and q$, $mono("Proper") ((=) ==> (<->) ==> (<-)) space (and)$. This is a very compact proof for such a rewrite. However the above algorithm would not be able to produce a respectful chain with three arguments due to the fact that applications are treated binary and thus result in no more than one respectful arrow $(==>)$ wrapped in subrelations. This can be improved by considering and entire sequence of applications. This helps us to simplify the two `Proper` proofs connected with a `Subrelation` proof that we've seen for the $p and q -> q and q$ rewrite to a single proper instance with two arrows. In combination with using a `success`/`identity` status this gives us more context for an entire sequence of applications. For instance we know that the entire application is an `identity` rewrite by iterating over earch applicant and ultimately just return `identity`. We can also use this in combination with the top-down appraoch to insert the desired relation for a specific rewrite (e.g. $(<-$) at the end, and the relation $r$ representing the rewrite argument as the source. Such a proof for $mono("Proper") (r ==> dots ==> (<-)) space (f : mono("Prop") -> dots -> mono("Prop"))$ leads directly to the desired right-to-left implication and does not require a final subrelation over the outcome of $mono("Rew"_rho) (Psi, f space e_0 space dots space e_n, r)$.

=== Leading Identity Rewrites



We mentioned 

+ id/success status
+ Pass expected relation to avoid subrelation
+ Eval app for all args
+ Ignore prefix id rewrites for app
+ ProperProxy

== Updated Algorithm

TODO explaination

TODO special cases where we still need subrelation

TODO cases from lambda with result/identity

#algo(
  row-gutter: 7pt,
  keywords: ("if", "else", "then", "match", "return", "with", "type", "for", "in", "do"),
  title: $"Subterm"_rho$,
  parameters: ($Psi$, $t$, $r$)
)[
  ($Psi'$, $r'$, $u'$, unifyable) := $"unify"_rho$($Psi$, $t$)\
  if unifyable then:#i\
    return ($Psi'$, $r'$, $u'$, $rho$)#d\
  match $t$ with\
  $|$ $e_1 dots e_n$ $=>$#i\
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

#pagebreak()

= Related Work

= Conclusion

#pagebreak()

#bibliography("refs.bib", full: true, title: "References")
