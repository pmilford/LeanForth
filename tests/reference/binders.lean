theorem identity {P : Prop} (proof : P) : P := proof

theorem choose_outer {P Q : Prop} (first : P) (_second : Q) : P := first

theorem choose_inner {P Q : Prop} (_first : P) (second : Q) : Q := second
