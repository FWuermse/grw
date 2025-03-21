# grw

This library implements generalised rewriting based on the Coq approach and the paper "A New Look at Generalized Rewriting in TypeTheory" by Matthieu Sozeau.

## Roadmap

- [x] Constraint generation
    - [x] generate the same constraints coq does
    - [x] compare algorithm and constraints of the coq and the paper version
- [ ]
    - [x] recreate eauto efficiently to handle multiple related goals
    - [ ] support adding tactics and theorems dynamically
- [ ] solve real-world grw problems
    - [ ] idris port
