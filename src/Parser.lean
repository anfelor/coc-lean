import data.list
import data.pfun

-- A simple parser combinator library
-- Similar to http://dev.stephendiehl.com/fun/002_parsers.html

universes u v

structure Parser (a : Type u) :=
  mk :: (parse : string -> list (a × string))

def runParser {a} (m : Parser a) (s : string) : a ⊕ string :=
match m.parse s with
| [(res, "")] := sum.inl res
| [(_, rs)] := sum.inr "Parser did not consume entire stream."
| [] := sum.inr "No matches."
| _ := sum.inr "Ambiguous."
end

instance parser_has_pure : has_pure Parser :=
  { pure := λ α a, Parser.mk (λ s, [(a, s)]) }

instance parser_has_bind : has_bind Parser :=
  { bind := λ α β p f, Parser.mk (λ s, (p.parse s) >>= λ ⟨a, s'⟩, (f a).parse s') }

instance parser_functor : functor Parser :=
  { map := λ α β f p, p >>= (pure ∘ f) }

instance parser_has_seq : has_seq Parser :=
  { seq := λ α β p q, p >>= λ f, f <$> q }

instance parser_applicative : applicative Parser := {}
instance parser_monad : monad Parser := {}

def mplus {a} (p : Parser a) (q : Parser a) : Parser a :=
  Parser.mk $ λ s, p.parse s ++ q.parse s

instance parser_has_orelse : has_orelse Parser := 
  { orelse := λ _ p q,
      Parser.mk $ λ s, match p.parse s with
        | [] := q.parse s
        | res := res
        end }

instance parser_alternative : alternative Parser := 
  { failure := λ _, Parser.mk $ λ _, [] }

/-- Some higher order parsers like many, many1, .. only terminate 
    for some argument parsers. Therefore we factor the termination
    out into a type class. -/
def parser_rel {a} (p : Parser a) : string -> string -> Prop :=
  λ s1 s2, s1 ∈ (λ x : (a × string), x.2) <$> (p.parse s2)

class productive {a} (p : Parser a) := 
  (produces : well_founded (parser_rel p))

def list_bind_contains {a b} : Π (ls : list a) (f : Π x, x ∈ ls -> list b), list b
| [] f := []
| (l::ls) f := f l (by simp) ++ list_bind_contains ls (λ x h, f x (by simp [h]))

--  (::) <$> v <*> (many1 v <|> pure [])
def many1_rec {a} (v : Parser a)
  : Π s, (Π y, parser_rel v y s -> list (list a × string)) -> list (list a × string) :=
  λ s, λ rec, list_bind_contains (v.parse s) $ λ ⟨a', s'⟩ h, 
    let h2 : parser_rel v s' s := by { simp [parser_rel], exact ⟨a', h⟩, }
    in match (rec s' h2) with
    | [] := [⟨[a'], s'⟩]
    | res := (λ x : (list a × string), ⟨a' :: x.1, x.2⟩) <$> res
    end

def many1 {a} (v : Parser a) [d : productive v] : Parser (list a) :=
  Parser.mk $ λ s, @well_founded.fix _ _ _ d.produces (many1_rec v) s

def many {a} (v : Parser a) [productive v] : Parser (list a) := 
  many1 v <|> pure []

def item : Parser char :=
  Parser.mk $ λ s, match string.to_list s with
    | [] := []
    | (c::cs) := [(c, list.as_string cs)]
    end

lemma list_string_id {x} : list.as_string (string.to_list x) = x :=
begin
  cases x, rw [string.to_list, list.as_string],
end

lemma string_list_id {x} : string.to_list (list.as_string x) = x :=
begin
  cases x, repeat { simp [list.as_string, string.to_list], },
end

lemma item_productive_acc : ∀ l, acc (parser_rel item) (list.as_string l)
| [] := acc.intro _ (λ y h, 
  begin 
    simp [parser_rel, item, (<$>), string_list_id] at h,
    from false.elim h
  end)
| (l::ls) := acc.intro _ (λ y h,
  begin
    simp [parser_rel, item, string_list_id, (<$>)] at h,
    let h2 := item_productive_acc ls,
    rwa [h.symm] at h2,
  end)

instance item_productive : productive item :=
  { produces := 
    begin
      apply well_founded.intro, intro s,
      from eq.mp (by simp [list_string_id]) (item_productive_acc (string.to_list s))
    end }

def transform {a} (p : char -> option a) : Parser a :=
  item >>= λ c, match p c with
    | some r := pure r
    | none := Parser.mk (λ _, []) 
    end

lemma transform_productive_acc {a f} 
  : ∀ l, acc (parser_rel (@transform a f)) (list.as_string l)
| [] := acc.intro _ (λ y h, 
  begin
    simp [parser_rel, transform, (>>=), item, string_list_id, (<$>)] at h,
    from false.elim h
  end)
| (l::ls) := acc.intro _ (λ y h,
  begin
    simp [parser_rel, transform, (>>=), item, string_list_id, parser_has_bind] at h,
    cases f l, { simp [transform] at h, from false.elim h },
    simp [transform, pure] at h,
    let h2 := transform_productive_acc ls,
    rwa [h.symm] at h2,
  end)

instance transform_productive {a f} : productive (@transform a f) :=
  { produces :=
    begin
      apply well_founded.intro, intro s,
      from eq.mp (by simp [list_string_id]) (transform_productive_acc (string.to_list s))
    end }

def satisfy (p : char -> bool) : Parser char :=
  transform (λ c, if p c then some c else none)

instance satisfy_productive {f} : productive (satisfy f) :=
  { produces := begin simp [satisfy], from transform_productive.produces, end }

def oneOf (ls : list char) : Parser char := satisfy (λ c, c ∈ ls)

instance oneOf_productive {ls} : productive (oneOf ls) :=
  { produces := begin simp [oneOf], from satisfy_productive.produces, end }

def spaces : Parser (list char) := many (oneOf [' ', '\t', '\n'])

/-- The 'char' parser. -/
def character (c : char) : Parser char := satisfy (λ d, c = d)

def asDigit : char -> option nat
| '0' := some 0 | '1' := some 1 | '2' := some 2 | '3' := some 3 | '4' := some 4
| '5' := some 5 | '6' := some 6 | '7' := some 7 | '8' := some 8 | '9' := some 9
| _ := none

def isDigit (c : char) : bool := option.is_some (asDigit c)

def digit : Parser char := satisfy isDigit

def token {a} (p : Parser a) : Parser a :=
  p >>= λ a, spaces >> pure a

/-- The 'string' parser. -/
def charlist : list char -> Parser (list char)
| [] := pure []
| (c::cs) := character c >> charlist cs >> pure (c :: cs)

def reserved (s : string) : Parser string :=
  token (charlist (string.to_list s)) >> pure s

def parens {a} (p : Parser a) : Parser a :=
  reserved "(" >> p >>= λ r, reserved ")" >> pure r

def combineNum : Π (ls : list nat), nat
| [] := 0
| (l::ls) := l * (10 ^ ls.length) + combineNum ls

def natural : Parser nat :=
   combineNum <$> many1 (transform asDigit)

def integer : Parser int :=
  (character '-' <|> pure '+') >>= λ c,
  (λ n : nat, if c = '-' then -n else n) <$> natural

-- chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
-- chainl p op a = (p `chainl1` op) <|> return a

-- chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
-- p `chainl1` op = do {a <- p; rest a}
  -- where rest a = (do f <- op
                     -- b <- p
                     -- rest (f a b))
                 -- <|> return a