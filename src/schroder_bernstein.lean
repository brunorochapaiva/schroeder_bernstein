import tactic

import logic.function.basic

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

def same_chain {α : Type u} (f : α → α) : α → α → Prop :=
λ x y, (∃ n : ℕ, f^[n] x = y) ∨ (∃ n : ℕ, f^[n] y = x)

lemma same_chain_reflexive {α : Type u} (f : α → α) : reflexive (same_chain f) :=
λ _, or.inl ⟨0, rfl⟩

lemma same_chain_symmetric {α : Type u} (f : α → α) : symmetric (same_chain f) :=
λ x y, (or_comm (∃ n, f^[n] x = y) (∃ n, f^[n] y = x)).mp

lemma same_chain_transitive {α : Type u} {f : α → α} (hf : function.injective f)
  : transitive (same_chain f) :=
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

lemma same_chain_equivalence {α : Type u} {f : α → α} (hf : function.injective f) : equivalence (same_chain f) :=
⟨same_chain_reflexive f, same_chain_symmetric f, same_chain_transitive hf⟩

theorem schroder_bernstein {α : Type u} {β : Type v} {f : α → β} {g : β → α}
  (hf : function.injective f) (hg : function.injective g)
  : ∃ (h : α → β), function.bijective h :=
begin
  have hfg : function.injective (f ∘ g) := function.injective.comp hf hg,
  have hgf : function.injective (g ∘ f) := function.injective.comp hg hf,
  sorry,
end
