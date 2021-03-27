use tutor_ml_modules::*;

fn elaborate_string(s: &str) -> anyhow::Result<(String, String)> {
    let m = parse_string(&s)?;
    let (exsig, e) = elaborate(&mut Default::default(), m)?;
    Ok((
        format!("{}", il::tycon::DisplayTableWrapper(exsig)),
        format!("{}", e),
    ))
}

#[test]
fn elaboration_test() {
    assert_eq!(
        elaborate_string("").ok(),
        Some(("{}".into(), "let in {}".into()))
    );

    assert_eq!(
        elaborate_string("val x = λy => y").ok(),
        Some((
            "{x : ∀!v0. !v0 -> !v0, }".into(),
            "let x = λy => y in {x = x}".into()
        ))
    );

    assert_eq!(
        elaborate_string("type t = λ'a => 'a -> 'a").ok(),
        Some((
            "{t = λ!v0 => !v0 -> !v0 : Type -> Type, }".into(),
            "let in {}".into()
        ))
    );

    assert_eq!(
        elaborate_string("module M = {signature S = sig end} :> sig signature S = sig end end")
            .ok(),
        Some((
            "{M : {S = {}, }, }".into(),
            "let M = let in {} in {M = M}".into()
        ))
    );

    assert_eq!(
        elaborate_string("signature S_1 = sig type t type u 'a end").ok(),
        Some((
            "{S_1 = λ!v0 !v1 => {t = !v0 : Type, u = λ!v2 => !v1 !v2 : Type -> Type, }, }".into(),
            "let in {}".into()
        ))
    );

    assert_eq!(
        elaborate_string("val x = λy => y val y = λx => x").ok(),
        Some((
            "{x : ∀!v0. !v0 -> !v0, y : ∀!v1. !v1 -> !v1, }".into(),
            "let x = λy => y; y = λx => x in {x = x, y = y}".into()
        ))
    );

    assert_eq!(
        elaborate_string("
signature List = sig
  type t 'a

  val empty 'a : t 'a
  val cons 'a : 'a -> t 'a -> t 'a

  val foldl 'a 'b : ('b -> 'a -> 'b) -> 'b -> t 'a -> 'b
end")
        .ok(),
        Some((
            "{List = λ!v0 => {cons : ∀!v1. !v1 -> !v0 !v1 -> !v0 !v1, empty : ∀!v2. !v0 !v2, foldl : ∀!v3 !v4. (!v4 -> !v3 -> !v4) -> !v4 -> !v0 !v3 -> !v4, t = λ!v5 => !v0 !v5 : Type -> Type, }, }".into(),
            "let in {}".into()
        ))
    );

    assert_eq!(
        elaborate_string("signature T = sig type t 'b end where type t 'a = 'a -> 'a").ok(),
        Some((
            "{T = {t = λ!v0 => !v0 -> !v0 : Type -> Type, }, }".into(),
            "let in {}".into()
        ))
    );

    assert_eq!(
        elaborate_string("signature T = sig type t 'b type u = t end where type u 'a = 'a -> 'a")
            .ok(),
        Some((
            "{T = {t = λ!v0 => !v0 -> !v0 : Type -> Type, u = λ!v1 => !v1 -> !v1 : Type -> Type, }, }".into(),
            "let in {}".into()
        ))
    );

    assert_eq!(
        elaborate_string("signature T = sig type t 'b type u 'a = t 'a end where type u 'a = 'a -> 'a")
            .ok(),
        Some((
            "{T = {t = λ!v0 => !v0 -> !v0 : Type -> Type, u = λ!v1 => !v1 -> !v1 : Type -> Type, }, }".into(),
            "let in {}".into()
        ))
    );

    assert_eq!(
        elaborate_string("
signature S = sig
  type t
  type u = t
end

signature T = sig
  type u
  type t = u
end

type r 'a =
{
  module M = {
    type t = 'a
    type u = 'a
  } :> S :> T :> S

  type q = 'a
}.q")
            .ok(),
        Some((
            "{S = λ!v0 => {t = !v0 : Type, u = !v0 : Type, }, T = λ!v1 => {t = !v1 : Type, u = !v1 : Type, }, r = λ!v2 => !v2 : Type -> Type, }".into(),
            "let in {}".into()
        ))
    );

    assert_eq!(
        elaborate_string(
            "
module M = {
  type t 'a = ('a -> 'a) -> 'a -> 'a
} : sig
  type t 'a
end"
        )
        .ok(),
        Some((
            "{M : {t = λ!v0 => (!v0 -> !v0) -> !v0 -> !v0 : Type -> Type, }, }".into(),
            "let M = let in {} in {M = M}".into()
        ))
    );

    assert_eq!(
        elaborate_string("
include {
  val id = λx => x
  val f = id
}"
        )
        .ok(),
        Some((
            "{f : ∀!v0. !v0 -> !v0, id : ∀!v1. !v1 -> !v1, }".into(),
            "let {f = f, id = id} = let id = λx => x; f = id in {f = f, id = id} in {f = f, id = id}".into()
        ))
    );
}
