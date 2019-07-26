Module Type KeySig.
Parameter key : Set.
Parameter eqKey : key -> key -> bool.
Axiom eqKey_refl : forall k1 k2, eqKey k1 k2 = true <-> k1 = k2.
End KeySig.