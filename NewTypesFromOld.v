Inductive rgb : Type:=
|red
|green
|blue.

Inductive color:Type:=
|black
|white
|primary (p:rgb).

Definition monochrome (c: color): bool :=
    match c with
    |black => true
    |white => true
    |primary p => false
    end.
Definition isred(c:color): bool :=
    match c with
    |black => false
    |white => false
    |primary red => true
    |primary _ => false
    end.
