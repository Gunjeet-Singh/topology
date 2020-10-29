import tactic
import data.real.basic

universe u

open set


structure topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

structure topology (α : Type u) :=
(𝒟 : set (set α))
(has_univ : univ ∈ 𝒟)
(has_inter : ∀ s t, s ∈ 𝒟 → t ∈ 𝒟 → (s ∩ t) ∈ 𝒟)
(has_sUnion : ∀ S ⊆ 𝒟, ⋃₀ S ∈ 𝒟)

namespace topology

variable {α : Type u}
variable {T : topology α}

def is_open (x : set α) : Prop := x ∈ T.𝒟

def discrete : topology α :=
{ 𝒟 := univ,
  has_univ := by simp,
  has_inter := by finish,
  has_sUnion := by finish, }

def trivial : topology α :=
{
  𝒟 := {∅, univ},
  has_univ := begin
    simp,
  end,
  has_inter := begin
    intros s t hs ht,
    finish,
  end,
  has_sUnion := begin
    intros S hS,
    -- finish, -- fails
    sorry, -- go to zulip
  end,
}

def neighbourhood : topology ℝ :=
{ 𝒟 := {x | sorry},
  has_univ := sorry,
  has_inter := sorry,
  has_sUnion := sorry, }


end topology
