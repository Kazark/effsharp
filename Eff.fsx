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

  let konst (x : 'r) : Cont<'r,'a> =
    Cont (fun _ -> x)

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
type Eff<'r,'e,'a> = | Eff of Reader<'e,Cont<'r,'a>>

module Eff =
  let wrap (x : 'a) : Eff<'r,'e,'a> =
    Eff (Reader.wrap (Cont.wrap x))

  let map (f : 'a -> 'b) (Eff k : Eff<'r,'e,'a>) : Eff<'r,'e,'b> =
    Eff (Reader.map (Cont.map f) k)

  let handle (handlers : 'e) (Eff eff : Eff<'r,'e,'a>) : Cont<'r,'a> =
    Reader.run handlers eff

  let run (handlers : 'e) (f : 'a -> 'r) : Eff<'r,'e,'a> -> 'r =
    Cont.run f << handle handlers

  let collapse (handlers : 'e) : Eff<'a,'e,'a> -> 'a =
    run handlers id

  let join (eff: Eff<'r,'e,Eff<'r,'e,'a>>) : Eff<'r,'e,'a> =
    Eff (
      Reader (fun (handlers: 'e) ->
        Cont.bind (handle handlers) (handle handlers eff)
      )
    )

  let bind (f : 'a -> Eff<'r,'e,'b>) (x : Eff<'r,'e,'a>) : Eff<'r,'e,'b> =
    join (map f x)

  let isomap (f : 'r -> 's) (g : 's -> 'r) (Eff eff : Eff<'r,'e,'a>)
      : Eff<'s,'e,'a> =
    Eff (Reader.map (Cont.isomap f g) eff)

  let lift (f : 'e -> Cont<'r,'a>) : Eff<'r,'e,'a> =
    Eff (Reader f)

[<AutoOpen>]
module WorkflowBuilders =
  type EffWB() =
    member __.Return (x : 'a) : Eff<'r,'e,'a> = Eff.wrap x
    member __.Bind (x : Eff<'r,'e,'a>, f : 'a -> Eff<'r,'e,'b>) : Eff<'r,'e,'b> =
      Eff.bind f x
    member __.ReturnFrom (x : Eff<'r,'e,'a>) : Eff<'r,'e,'a> = x

  let eff = EffWB ()

type Fallible<'t,'r> =
  abstract member throw : 't -> Cont<'r,'a>

module Fallible =
  let throw<'t,'r,'e,'a when 'e :> Fallible<'t,'r>> (exc: 't) : Eff<'r,'e,'a> =
    Eff.lift (fun e -> e.throw exc)

type ChoiceFailure<'t,'r>() =
  member self.run (eff : Eff<Choice<'t,'r>,ChoiceFailure<'t,'r>,'r>)
      : Choice<'t,'r> =
    Eff.run self Choice2Of2 eff

  interface Fallible<'t,Choice<'t,'r>> with
    override __.throw (x : 't) : Cont<Choice<'t,'r>,'a> =
      Cont.konst (Choice1Of2 x)

module ChoiceExample =
  type DivByZero = DivByZero

  let div<'r,'e when 'e :> Fallible<DivByZero,'r>>
      (num : int) (denom : int) : Eff<'r,'e,int> =
    if denom = 0
    then Fallible.throw DivByZero
    else Eff.wrap (num / denom)

  let prettyPrint (choice: Choice<'a,'b>) : unit =
    match choice with
    | Choice1Of2 x -> printfn "Left %O" x
    | Choice2Of2 x -> printfn "Right %O" x

  let example () =
    printfn "Exception-throwing example: pure interpretation"
    printf "div 13 0 => "
    prettyPrint <| ChoiceFailure().run (div 13 0)
    printf "div 13 1 => "
    prettyPrint <| ChoiceFailure().run (div 13 7)

type NonDet<'a,'r> =
  abstract member between : 'a -> 'a -> Cont<'r,'a>

module NonDet =
  let between<'r,'e,'a when 'e :> NonDet<'a,'r>> (lower : 'a) (upper: 'a)
      : Eff<'r,'e,'a> =
    Eff.lift (fun e -> e.between lower upper)

type ImpureNonDet<'r>() =
  let rand = System.Random()

  member self.run (eff : Eff<'r,ImpureNonDet<'r>,'r>) : 'r =
    Eff.collapse self eff

  interface NonDet<int32,'r> with
    override __.between (lower: int32) (upper: int32) : Cont<'r,int32> =
      Cont.wrap (rand.Next(lower, upper))

type PureNonDet<'r>() =
  member self.run (eff : Eff<list<'r>,PureNonDet<'r>,'r>) : list<'r> =
    Eff.run self List.singleton eff

  interface NonDet<int32,list<'r>> with
    override __.between (lower: int32) (upper: int32) : Cont<list<'r>,int32> =
      Cont (fun f -> List.collect f [lower..upper])

module NonDetExample =
  let fizzbuzz<'r,'e when 'e :> NonDet<int32,'r>> : Eff<'r,'e,string> = eff {
    let! x = NonDet.between 0 100
    return match (x % 3 = 0, x % 5 = 0) with
           | (true, true) -> "fizzbuzz"
           | (true, false) -> "fizz"
           | (false, true) -> "buzz"
           | (false, false) -> string x
  }

  let example () =
    printfn "Non-determinism example"
    printfn "Impure: %O" <| ImpureNonDet().run fizzbuzz
    printfn "Pure: %O" <| PureNonDet().run fizzbuzz

module Main =
  [<EntryPoint>]
  let main(_: string[]): int =
    ChoiceExample.example ()
    NonDetExample.example ()
    0
