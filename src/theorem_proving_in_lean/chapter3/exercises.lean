/-
Prove the following identities, replacing 
the “sorry” placeholders with actual proofs.
-/

section ex1
  variables p q r : Prop

  -- commutativity of ∧
  example : p ∧ q ↔ q ∧ p :=
  iff.intro 
    (assume h : p ∧ q,
      show q ∧ p, from and.intro (and.right h) (and.left h))
    (assume h : q ∧ p,
      show p ∧ q, from and.intro (and.right h) (and.left h))


  -- commutativity of ∨
  example : p ∨ q ↔ q ∨ p :=
  iff.intro 
  (assume h : p ∨ q, 
    or.elim h
    (assume hp : p,
      show q ∨ p, from or.intro_right q hp)
    (assume hq : q,
      show q ∨ p, from or.intro_left p hq))
  (assume h: q ∨ p, 
    or.elim h 
    (assume hq : q, 
      show p ∨ q, from or.intro_right p hq)
    (assume hp : p,
      show p ∨ q, from or.intro_left q hp))


  -- associativity of ∧
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
  (assume h : (p ∧ q) ∧ r, 
      ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
  (assume h : p ∧ (q ∧ r), 
      ⟨⟨h.left, h.right.left⟩, h.right.right⟩)


  -- associativity of ∨
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    iff.intro 
    (assume h : (p ∨ q) ∨ r,
    or.elim h 
    (assume hpq : p ∨ q, show p ∨ (q ∨ r), from
      or.elim hpq 
      (assume hp : p, show p ∨ q ∨ r, from or.intro_left (q ∨ r) hp ) 
      (assume hq : q, show p ∨ q ∨ r, from or.intro_right p (or.intro_left r hq)))
    (assume hr : r, show p ∨ q ∨ r, from or.intro_right p (or.intro_right q hr)))
    (assume h : p ∨ (q ∨ r),
    or.elim h
    (assume hp : p, show (p ∨ q) ∨ r, from or.intro_left r (or.intro_left q hp))
    (assume hqr : q ∨ r, show (p ∨ q) ∨ r, from 
      or.elim hqr
      (assume hq : q, show (p ∨ q) ∨ r, from or.intro_left r (or.intro_right p hq))
      (assume hr : r, show (p ∨ q) ∨ r, from or.intro_right (p ∨ q) hr)))


  -- distributivity ∧ over ∨
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  iff.intro
    (assume h : p ∧ (q ∨ r),
      have hp : p, from h.left,
      or.elim (h.right)
        (assume hq : q,
          show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
        (assume hr : r,
          show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩))
    (assume h : (p ∧ q) ∨ (p ∧ r),
      or.elim h
        (assume hpq : p ∧ q,
          have hp : p, from hpq.left,
          have hq : q, from hpq.right,
          show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩)
        (assume hpr : p ∧ r,
          have hp : p, from hpr.left,
          have hr : r, from hpr.right,
          show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩))


  -- distributivity ∨ over ∧ 
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (assume h : p ∨ (q ∧ r), 
      or.elim h
      (assume hp : p, ⟨or.inl hp, or.inl hp⟩)
      (assume hqr : q ∧ r, ⟨or.inr hqr.left, or.inr hqr.right⟩))
    (assume h : (p ∨ q) ∧ (p ∨ r), 
      have hpr : (p ∨ r), from h.right,
      have hpq : (p ∨ q), from h.left,
      or.elim hpr 
      (assume hp : p, show p ∨ q ∧ r, from or.intro_left (q ∧ r) hp)
      (assume hr : r, show p ∨ q ∧ r, from 
        or.elim hpq 
        (assume hp : p, or.intro_left (q ∧ r) hp)
        (assume hq : q, or.intro_right p ⟨hq, hr⟩)))


  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := 
  iff.intro
  (assume (hp : p → q → r), 
  assume (hpq : p ∧ q),
  show r, from (hp hpq.left) hpq.right)
  (assume (hpqr : p ∧ q → r),
  assume (hp : p),
  assume (hq : q),
  show r, from hpqr ⟨hp, hq⟩)


  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  iff.intro
  (assume (hpqr : (p ∨ q) → r), 
  and.intro 
    (assume (hp : p), show r, from hpqr (or.intro_left q hp)) 
    (assume (hq : q), show r, from hpqr (or.intro_right p hq))) 
  (assume (hprqr: (p → r) ∧ (q → r)), 
  assume (hpq : p ∨ q),
  or.elim hpq
  (assume (hp : p), show r, from hprqr.left hp)
  (assume (hq : q), show r, from hprqr.right hq))


  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro 
  (assume (hnpq : ¬(p ∨ q)), 
  and.intro
  (assume (hp : p), show false, from hnpq (or.inl hp) )
  (assume (hq : q), show false, from hnpq (or.inr hq)))
  (assume (hnpnq : ¬p ∧ ¬q),
  assume (hpq : p ∨ q),
  or.elim hpq
  (assume (hp : p), hnpnq.left hp)
  (assume (hq : q), hnpnq.right hq))


  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (assume (hnpnq : ¬p ∨ ¬q),
  assume (hpq: p ∧ q), 
  or.elim hnpnq 
  (assume (hnp: ¬p), hnp hpq.left)
  (assume (hnq: ¬q), hnq hpq.right))


  example : ¬(p ∧ ¬p) :=
  (assume (hpnp : p ∧ ¬p),
  hpnp.right hpnp.left)


  example : p ∧ ¬q → ¬(p → q) := 
  (assume (hpnq : p ∧ ¬q), 
  assume (hpq : p → q),
  hpnq.right (hpq hpnq.left))


  example : ¬p → (p → q) :=
  (assume (hnp : ¬p),
  assume (hp : p),
  absurd hp hnp)


  example : (¬p ∨ q) → (p → q) := 
  (assume (hnpq : ¬p ∨ q),
  assume (hp : p),
  or.elim hnpq 
  (assume (hnp : ¬p), absurd hp hnp)
  (assume (hq : q), hq))


  example : p ∨ false ↔ p :=
  iff.intro
  (assume (hpf : p ∨ false),
  or.elim hpf 
  (assume (hp : p), hp)
  (assume (hf : false), false.elim hf))
  (assume (hp : p), or.inl hp)


  example : p ∧ false ↔ false :=
  iff.intro
  (assume (hpf : p ∧ false), hpf.right)
  (assume (hf : false), false.elim hf)


  example : (p → q) → (¬q → ¬p) :=
  (assume (hpq : p → q),
  assume (hnq : ¬q),
  assume (hp : p), hnq (hpq hp))

end ex1


section ex2
  open classical

  variables (p q r s : Prop)

  example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  (assume (h : p → r ∨ s),
   or.elim (em p)
   (assume (hp : p),
    or.elim (h hp)
    (assume (hr : r), or.inl (assume (hp : p), hr) )
    (assume (hs : s), or.inr (assume (hp : p), hs)))
   (assume (hnp : ¬p), or.inl (assume (hp : p), (show r, from sorry))))

  example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  (assume (h : ¬(p ∧ q)),  
  or.elim (em p)
  (assume (hp : p), or.inr (show ¬q, 
    from assume hq : q, h ⟨hp, hq⟩)) 
  (assume (hnp : ¬p), or.inl hnp))

  example : ¬(p → q) → p ∧ ¬q :=
  (assume h : ¬(p → q), 
   or.elim (em q)
   (assume hq : q, false.elim (h (assume hp : p, hq)))
   (assume hnq : ¬q,
     and.intro
     (sorry) 
     hnq))

  example : (p → q) → (¬p ∨ q) :=
  (assume h : p → q,   
    or.elim (em p)
    (assume hp : p, or.inr (h hp))
    (assume hnp : ¬p, or.inl hnp))

  example : (¬q → ¬p) → (p → q) := 
  (assume h : (¬q → ¬p), 
  (assume hp : p, 
  or.elim (em q)
    (assume hq : q, hq)
    (assume hnq : ¬q, absurd hp (h hnq))))

  example : p ∨ ¬p :=
  or.elim (em p)
    (assume hp : p, or.inl hp)
    (assume hnp : ¬p, or.inr hnp)

  example : (((p → q) → p) → p) := 
  (assume h : ((p → q) → p), 
   or.elim (em q)
     (assume hq : q, h (assume hp : p, hq))
     (assume hnq : ¬q, absurd hnq sorry))
end ex2