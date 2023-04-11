-- {a, b} |- a /\ b

lemma ejemplo1 (a b : Prop) : a → b → a ∧ b :=

begin
  intros ha hb,
  apply (and.intro ha hb) 
end


lemma Ejemplo2 (a b : Prop) : a ∧ ¬b → ¬b ∧ a :=

begin
  intros h,
  apply and.intro,
    apply (and.right h),
    apply (and.left h)
end
