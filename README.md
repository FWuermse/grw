# grw

## Questions

+ Quick note: equivalence relations are not closed under the respectful morphism construction so we actually have to start at PERs. It's mostly the same, fortunately.
+ Reading the Coq source code, it also turns out that a fair amount of typeclass resolution is customized by using the fact that the typeclass resolution engine is a variant of eauto
+ By using hints that call into custom tactics, a number of instances are applied selectively and not put into the instance database, to avoid combinatorial explosions.
+ Unlike the standard synthesis algorithm, this will instantiate metavariables.
