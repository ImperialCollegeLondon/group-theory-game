import subgroup.definitions

/-
An API for subgroups

Mathematician-friendly

Let G be a group. The type of subgroups of G is `subgroup G`. 
In other words, if `H : subgroup G` then H is a subgroup of G. 
The three basic facts you need to know about H are:

H.one_mem : (1 : G) ∈ H
H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H
H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H

Subgroups of a group form what is known as a *lattice*. 
This is a partially ordered set with a sensible notion of
max and min (and even sup and inf). 
-/

-- This entire project takes place in the `mygroup` namespace
namespace mygroup

-- TODO: prove subgroups are a lattice/semilattice-sup-bot/complete lattice/ whatever

end mygroup