Require Import Setoid.

Set Debug "rewrite".

Parameter A : Type.
Parameter r : relation A.
Parameter P : A -> Prop.
Parameter a b : A.
Parameter H : r a b.

Goal P a.
rewrite H.
