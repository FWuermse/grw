#import "./template.typ": *
#import "./theme.typ": *
= Optimisations

The actual Coq implementation of generalised rewriting contains a few optimisations that were not mentioned in the paper or documentation. Through reverse engineering a large amount of the Coq core module, we were able to extract the most crucial optimisations and applied them to our imperative algorithm specification. The algorithm we have seen so far stresses the rewriting of applications and aims to convert other terms into application-terms. Thus, most of the following optimisations focus on simplifying rewrite proofs for application terms.

== Identity and Success Status <idsuccstatus>

In our examples, we saw that many terms do not contain the left-hand side term of the rewrite theorem $rho$. However, we would still examine those terms and produce two metavariables just to create a proof of identity $h : t -> t$. This can be simplified by classifying subterms depending on whether they can be directly or recursively rewritten or remain the same. We change the output type of the algorithm to a sum type with two variants. The `identity` variant carries no further information and signals that a term cannot be rewritten. The other variant `success` carries the same information as seen before, in essence, the carrier relation, the updated term, and the proof of the rewrite. Now every time all the recursive invocations result in identity rewrites, the current rewrite will also be an identity rewrite. For instance, when both recursive calls $"Rew"_rho (Psi, f)$ and $"Rew"_rho (Psi, e)$ of an application $f space e$ result in identity rewrites, then the result for $"Rew"_rho (Psi, f space e)$ will also result in an identity rewrite. When considering a term $q and q and p and q and q$ given $h : p <-> q$, we would only consider the $p$ in the middle and would not create proofs and nested carrier relations for the four conjunction atoms and the four $q$s. The worst case complexity is still the same here. However, in practice, we usually have many cases that cannot be rewritten especially as we indirectly transform arrow and Pi types to identity applications as well.

== Top-Down Relation Passing

The algorithm described so far generates metavariables for relations whenever we do not know which relation we're supposed to generate a proof for. We then return those relations recursively and build subrelations to infer the desired relation (eventually ($<-$)). We consider this a bottom-up approach where those metavariables originate from the leafs of such a term tree and are passed upwards. This creates a lot of subrelation constraints that were not necessary in the first place. We can avoid this by passing an additional parameter to recursive calls (top-down) that contains the desired relation for a proof. We do this by initially providing ($<-$) as the desired relation and pass it along in the lambda, Pi, and arrow case. In the recursive calls as part of the application case, we generate a metavariable for a relation of the type of the application subterm we rewrite for and pass it to both recursive calls. This removes the need for subrelations in the application rule and at the top of the term. There are some exceptions for edge cases that we will explore in the following sections.

Let us consider a simple rewrite of an application $f space e$ where $e$ can be rewritten. With the original algorithm, we would create a metavariable for the identity proof of $f$ and the carrier relation $?_r_f$ for $f$. $e$ would be rewritten providing a rewrite proof and carrier relation $?_r_e$. When combining the two, we would create another relation metavariable $?_r_(f e)$. The `Rew` algorithm returns a proof over $?_r_(f e)$, and we have to wrap another subrelation constraint $?_s$ around it to obtain the final rewrite. We can eliminate the last subrelation constraint $?_s$ and the need for $?_r_(f e)$ by passing the desired output relation (e.g., $<-$) to the algorithm. We can then directly place the given relation in the spot where $?_r_(f e)$ was.

For this optimisation to work, however, we still have to create metavariables whenever the desired relation changes. This happens when we break the term $t$ further down. For instance, when recursively rewriting a function argument, its type is different from the type of the whole application. In that case, we create a metavariable of the given type and pass it down. There are some edge cases where we cannot leverage the provided relation and have to fall back on at most one final subrelation inference. For instance, this can happen when the input term directly unifies and returns without creating any constraints.

== Applications as Sequence

When introducing the `Proper` and `respectful` definitions, we gave an example for a possible rewrite proof of $p and q -> q and q$ using $mono("Proper") ((=) ==> (<->) ==> (<-)) space (and)$. This is a very compact proof for such a rewrite. However, the above algorithm would not be able to directly produce a respectful chain with three arguments due to the fact that applications are treated as binary applications and thus result in no more than one respectful arrow $(==>)$ wrapped in subrelations. This can be improved by considering the entire sequence of applications. This helps us to simplify the two `Proper` proofs connected with a `Subrelation` proof that we've seen for the $p and q -> q and q$ rewrite (See @examplesection) to a single proper instance with two arrows. In combination with using a `success`/`identity` status, this gives us more context for an entire sequence of applications. For instance, we know that the entire application is an `identity` rewrite by iterating over the function and each argument. In that case, we ultimately just return `identity`. We can also use this in combination with the top-down approach for relation passing to insert the desired implication for a specific rewrite (e.g., $(<-$)) at the end and the relation $r$ representing the rewrite argument as the source. Such a proof for $mono("Proper") (r ==> dots ==> (<-)) space (f : mono("Prop") -> dots -> mono("Prop"))$ leads directly to the desired right-to-left implication and does not require a final subrelation over the outcome of $mono("Rew"_rho) (Psi, f space e_0 space dots space e_n, r)$.

== Leading Identity Rewrites

We mentioned that when considering the entire sequence, we have more context for optimisations. In this and the following sections we denote application sequences as $e_0 space dots space e_n$ where $e_0$ represents the function of an application term and $e_n$ the last argument with $n in NN$. One of them is not to include function arguments $e_i space dots e_j$ with $i,j in NN and 0 <= i <= j <= |e_0 space dots space e_n|$ inside a `Proper` constraint's respectful chain if the function and every argument before $e_i$ is an identity rewrite. This reduces the complexity and size of a respectful chain and thus makes it easier to solve the resulting constraints. This also helps to minimise the amount of metavariables that we have to infer and guess.

For instance, when considering a rewrite of a function application $f space e_0 space e_1 space e_2$ with $f : alpha_0 -> alpha_1 -> alpha_2 -> mono("Prop")$ where only $e_2$ can be successfully rewritten using $rho : r space e_2 space u$, we would produce the proper sequence $mono("Proper") (r_e_0 ==> r_e_1 ==> r_e_2 ==> (<-)) f$. This includes the two relations $r_e_0$ and $r_e_1$. Technically, we know that those relations can be guessed as arbitrary reflexive relations because $e_0$ and $e_1$ are rewritten to their identities $e_0$ and $e_1$.

We can simplify such terms by currying @curry the two identity arguments to the function and shrink the respectful chain to $mono("Proper") (r_e_2 ==> (<-)) space (f space e_0 space e_1)$ to obtain the same proof. $mono("Proper") (r_e_0 ==> r_e_1 ==> r_e_2 ==> (<-))$ has the type $(alpha_0 -> alpha_1 -> alpha_2 -> mono("Prop")) -> mono("Prop")$ and therefore produces the desired proof when applied to $f$. When we reduce the term to $mono("Proper") (r_e_2 ==> (<-))$, the type changes to $(alpha_2 -> mono("Prop")) -> mono("Prop")$, and the application $f space e_0 space e_1$ has this desired type $alpha_2 -> mono("Prop")$.

In this example, we are left with only one relation that has to be guessed, notably also the crucial one for this rewrite to succeed. With this improvement, we take away valuable time of the proof search guessing irrelevant relations and provide only the necessary ones.

This only works for left-to-right identity rewrites due to the left-associativity of function application and the nature of function currying @schonfinkel1924bausteine @curry.

== ProperProxy

This last improvement does not directly enhance the generated proofs but affects the proof search for identity rewrites. We mentioned that leading identity rewrites can only be optimized left-to-right and only if there is a consistent sequence of identity subterms. For functions where only the first and last parameter is a rewrite, we would not be able to apply that system. However, we can see that those proofs are trivial because the requirement for identity rewrites is only to find some relation $r_"id"$ that is reflexive and a proof that the given element is proper. We could tag such elements and use that tag during the proof search to find a respective proof more easily.

#definition("ProperProxy")[
  ```lean
  class ProperProxy (r : relation α) (m : α) where
    proxy : r m m
  ```
] <ProperProxyDef>

#definition("Reflexive")[
```lean
class Reflexive {α : Sort u} (rel : relation α) where
  rfl : ∀ x, rel x x
```
] <ReflexiveDef>

We adopted Coq's encoding for such tags in our Lean implementation by defining a second typeclass called `ProperProxy` (see @ProperProxyDef) which is identical to the `Proper` definition seen in @Introduction. The only difference is that we implement different theorems (or typeclass instances) that transform the `ProperProxy` constraint into a `Reflexive` element seen in @ReflexiveDef. Those theorems are selected first for all `ProperProxy` metavariables and help solve the easy constraints. Only if that fails, we transition it to `Proper` instances and proceed with the usual theorems that we would use to solve arbitrary `Proper` constraints.

While this does not change the type of our proofs, it avoids unnecessary backtracking for subterms that do not need to be rewritten but also cannot be optimised by the currying technique we saw for leading identity rewrites.