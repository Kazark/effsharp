namespace FSharp.Control

[<Struct>]
type Reader<'e,'a> = | Reader of ('e -> 'a)

[<Struct>]
type Cont<'r,'a> = | Cont of (('a -> 'r) -> 'r)

module Reader =
  let wrap (x : 'a) : Reader<'e,'a> =
    Reader (fun _ -> x)

  let run (env : 'e) (Reader f : Reader<'e,'a>) : 'a =
    f env

  let map (f : 'a -> 'b) (Reader g : Reader<'e, 'a>) : Reader<'e, 'b> =
    Reader (g >> f)

  let contramap (f : 'd -> 'e) (Reader g : Reader<'e,'a>) : Reader<'d,'a> =
    Reader (f >> g)

  let join (f: Reader<'e,Reader<'e,'a>>) : Reader<'e,'a> =
    Reader (fun e -> run e (run e f))

  let bind (f : 'a -> Reader<'e,'b>) (x : Reader<'e,'a>) : Reader<'e,'b> =
    join (map f x)

  let dimap (f : 'a -> 'b) (g : 's -> 'r) : Reader<'r,'a> -> Reader<'s,'b> =
    contramap g << map f

  let cont (f : 's -> 'r) (Reader g : Reader<'a->'r,'s>) : Cont<'r,'a> =
    Cont (g >> f)

  let ask<'a> : Reader<'a,'a> = Reader id

module Cont =
  let wrap (x : 'a) : Cont<'r,'a> =
    Cont (fun (f : 'a -> 'r) -> f x)

  let run (f : 'a -> 'r) (Cont k : Cont<'r,'a>) : 'r =
    k f

  let map (f : 'a -> 'b) (Cont k : Cont<'r, 'a>) : Cont<'r, 'b> =
    Cont (fun (g : 'b -> 'r) -> k (f >> g))

  let isomap (f : 'r -> 's) (g: 's -> 'r) (Cont k : Cont<'r,'a>) : Cont<'s,'a> =
    Cont (fun (h : 'a -> 's) -> f (k (h >> g)))

  let halfmap (f : 'r -> 's) (Cont k : Cont<'r,'a>) : Reader<'a->'r,'s> =
    Reader (k >> f)

  let join (Cont k: Cont<'r,Cont<'r,'a>>) : Cont<'r,'a> =
    Cont (fun (f : 'a -> 'r) ->
      k (fun (k' : Cont<'r,'a>) -> run f k')
    )

  let bind (f : 'a -> Cont<'r,'b>) (x : Cont<'r,'a>) : Cont<'r,'b> =
    join (map f x)

  let collapse<'r> : Cont<'r,'r> -> 'r =
    run id

[<Struct>]
type Eff<'r,'i,'o,'a> = | Eff of Reader<'i->Cont<'r,'o>,Cont<'r,'a>>

module Eff =
  let wrap (x : 'a) : Eff<'r,'i,'o,'a> =
    Eff (Reader.wrap (Cont.wrap x))

  let map (f : 'a -> 'b) (Eff k : Eff<'e,'i,'o,'a>) : Eff<'e,'i,'o,'b> =
    Eff (Reader.map (Cont.map f) k)

  let handleK (h : 'i -> Cont<'r,'o>) (Eff eff: Eff<'r,'i,'o,'a>) : Cont<'r,'a> =
    Reader.run h eff

  let handle (handler : 'i -> 'o) : Eff<'r,'i,'o,'a> -> Cont<'r,'a> =
    handleK (handler >> Cont.wrap)

  let join (eff: Eff<'e,'i,'o,Eff<'e,'i,'o,'a>>) : Eff<'e,'i,'o,'a> =
    Eff (
      Reader (fun (env: 'i -> Cont<'e,'o>) ->
        Cont.bind (handleK env) (handleK env eff)
      )
    )

  let bind (f : 'a -> Eff<'e,'i,'o,'b>) (x : Eff<'e,'i,'o,'a>) : Eff<'e,'i,'o,'b> =
    join (map f x)

  module Out =
    let contramap (f : 'p -> 'o) (Eff eff: Eff<'r,'i,'o,'a>) : Eff<'r,'i,'p,'a> =
      Eff (Reader.contramap (fun g -> g >> Cont.map f) eff)

    let contramapK (f : 'p -> Cont<'r,'o>) (Eff eff: Eff<'r,'i,'o,'a>)
        : Eff<'r,'i,'p,'a> =
      Eff (Reader.contramap (fun g -> g >> Cont.bind f) eff)

  module In =
    let map (f : 'i -> 'j) (Eff eff: Eff<'r,'i,'o,'a>) : Eff<'r,'j,'o,'a> =
      Eff (Reader.contramap (fun g -> f >> g) eff)

    let mapK (f : 'i -> Cont<'r,'j>) (Eff eff: Eff<'r,'i,'o,'a>)
        : Eff<'r,'j,'o,'a> =
      Eff (Reader.contramap (fun g -> f >> Cont.bind g) eff)

  module Result =
    let isomap (f : 'r -> 's) (g : 's -> 'r) (Eff eff : Eff<'r,'i,'o,'a>)
        : Eff<'s,'i,'o,'a> =
      Eff (Reader.dimap (Cont.isomap f g) (fun h -> h >> Cont.isomap g f) eff)

  let reinterpret
      (intrptr : 'i -> Eff<'r,'j,'p,'o>)
      (eff : Eff<'r,'i,'o,'a>)
      : Eff<'r,'j,'p,'a> =
    Eff (
      Reader (fun (f : 'j -> Cont<'r,'p>) ->
        handleK (intrptr >> handleK f) eff
      )
    )
