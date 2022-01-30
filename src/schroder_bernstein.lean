import tactic

import logic.function.basic
import init.data.setoid
import data.setoid.basic

import algebra.iterate_hom

universes u v

-- Things to mention in report:
-- - It's surprisingly easy to add unnecessary hypothesis to definitions for
-- example, but linting checks this and helps out.
-- (like requiring that f is injective in same_chain, when it is only required
-- for transitivity)
-- - Lean makes sense of things which "aren't well defined" by looking in
--   hypothesis and making sure they are reasonable
--   (when subtracting in the natural numbers, it will check the result
--   is non-negative)
-- - Lean keeps you honest when trying to use arguments like wlog?

def same_chain_rel {α : Type u} (f : α → α) : α → α → Prop :=
λ x y, (∃ n : ℕ, f^[n] x = y) ∨ (∃ n : ℕ, f^[n] y = x)

lemma same_chain_reflexive {α : Type u} (f : α → α) : reflexive (same_chain_rel f) :=
λ _, or.inl ⟨0, rfl⟩

lemma same_chain_symmetric {α : Type u} (f : α → α) : symmetric (same_chain_rel f) :=
λ x y, (or_comm (∃ n, f^[n] x = y) (∃ n, f^[n] y = x)).mp

lemma same_chain_transitive {α : Type u} {f : α → α} (hf : function.injective f)
  : transitive (same_chain_rel f) :=
begin
  intros x y z hxy hyz,
  rcases hxy with ⟨n, hn⟩ | ⟨n, hn⟩,
  { rcases hyz with ⟨m, hm⟩ | ⟨m, hm⟩,
    { left, use m + n,
      rw [←hm, ←hn, function.iterate_add] },
    { cases lt_or_le n m,
      { right, use m - n,
        apply function.injective.iterate hf n,
        rw [←function.iterate_add_apply, nat.add_sub_of_le (le_of_lt h), hn, hm] },
      { left, use n - m,
        apply function.injective.iterate hf m,
        rw [←function.iterate_add_apply, nat.add_sub_of_le h, hm, hn] }}},
  { rcases hyz with ⟨m, hm⟩ | ⟨m, hm⟩,
    { cases lt_or_le n m,
      { left, use m - n,
        rw [←hn, ←hm, ←function.iterate_add_apply, add_comm, nat.add_sub_of_le (le_of_lt h)] },
      { right, use n - m,
        rw [←hn, ←hm, ←function.iterate_add_apply, add_comm, nat.add_sub_of_le h] }},
    { right, use n + m,
      rw [←hn, ←hm,function.iterate_add] }},
end

lemma same_chain_equivalence {α : Type u} {f : α → α} (hf : function.injective f) : equivalence (same_chain_rel f) :=
⟨same_chain_reflexive f, same_chain_symmetric f, same_chain_transitive hf⟩

def same_chain_setoid {α : Type u} {f : α → α} (hf : function.injective f) : setoid α :=
{ r := same_chain_rel f, iseqv := same_chain_equivalence hf }

lemma iter_comp_assoc {α : Type u} {β : Type v} (f : α → β) (g : β → α) (n : ℕ)
  : ∀ a : α, f (g ∘ f^[n] a) = (f ∘ g^[n] (f a)) :=
begin
  induction n,
  { intro a,
    rw [function.iterate_zero_apply, function.iterate_zero_apply] },
  { intro a,
    rw [function.iterate_succ, function.iterate_succ, n_ih (g (f a))] }
end

def same_chain_quotient_map {α : Type u} {β : Type v} {f : α → β} {g : β → α}
  (hf : function.injective f) (hg : function.injective g)
  : quotient (same_chain_setoid (function.injective.comp hg hf))
    → quotient (same_chain_setoid (function.injective.comp hf hg)) :=
begin
  apply quotient.map' f,
  intros a b,
  rintros (⟨n, hn⟩ | ⟨n, hn⟩);
  rw [←hn, iter_comp_assoc f g n],
  { left, use n },
  { right, use n }
end

lemma same_chain_quotient_map_inverse {α : Type u} {β : Type v} {f : α → β} {g : β → α}
  (hf : function.injective f) (hg : function.injective g)
  : ∀ x, same_chain_quotient_map hg hf (same_chain_quotient_map hf hg x) = x :=
begin
  intro x,
  rw [←quotient.out_eq' x, same_chain_quotient_map, same_chain_quotient_map,
      quotient.map'_mk', quotient.map'_mk'],
  apply quotient.sound',
  right, use 1,
  refl,
end

def same_chain_quotient_equiv {α : Type u} {β : Type v} {f : α → β} {g : β → α}
  (hf : function.injective f) (hg : function.injective g)
  : quotient (same_chain_setoid (function.injective.comp hg hf))
    ≃ quotient (same_chain_setoid (function.injective.comp hf hg)) :=
{ to_fun    := same_chain_quotient_map hf hg,
  inv_fun   := same_chain_quotient_map hg hf,
  left_inv  := same_chain_quotient_map_inverse hf hg,
  right_inv := same_chain_quotient_map_inverse hg hf,
}

theorem schroder_bernstein {α : Type u} {β : Type v} {f : α → β} {g : β → α}
  (hf : function.injective f) (hg : function.injective g)
  : ∃ (h : α → β), function.bijective h :=
begin
  sorry,
end
