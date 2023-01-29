open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

[@deriving (sexp, compare)]
type htyp =
  | Arrow(htyp, htyp)
  | Num
  | Hole;

[@deriving (sexp, compare)]
type hexp =
  | Var(string)
  | Lam(string, hexp)
  | Ap(hexp, hexp)
  | Lit(int)
  | Plus(hexp, hexp)
  | Asc(hexp, htyp)
  | EHole
  | NEHole(hexp);

[@deriving (sexp, compare)]
type ztyp =
  | Cursor(htyp)
  | LArrow(ztyp, htyp)
  | RArrow(htyp, ztyp);

[@deriving (sexp, compare)]
type zexp =
  | Cursor(hexp)
  | Lam(string, zexp)
  | LAp(zexp, hexp)
  | RAp(hexp, zexp)
  | LPlus(zexp, hexp)
  | RPlus(hexp, zexp)
  | LAsc(zexp, htyp)
  | RAsc(hexp, ztyp)
  | NEHole(zexp);

[@deriving (sexp, compare)]
type child =
  | One
  | Two;

[@deriving (sexp, compare)]
type dir =
  | Child(child)
  | Parent;

[@deriving (sexp, compare)]
type shape =
  | Arrow
  | Num
  | Asc
  | Var(string)
  | Lam(string)
  | Ap
  | Lit(int)
  | Plus
  | NEHole;

[@deriving (sexp, compare)]
type action =
  | Move(dir)
  | Construct(shape)
  | Del
  | Finish;

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(htyp);

exception Unimplemented;

let rec erase_exp = (e: zexp): hexp => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (e) {
  | Cursor(he) => he
  | Lam(str, ze) => Lam(str, erase_exp(ze))
  | LAp(ze, he) => Ap(erase_exp(ze), he)
  | RAp(he, ze) => Ap(he, erase_exp(ze))
  | LPlus(ze, he) => Plus(erase_exp(ze), he)
  | RPlus(he, ze) => Plus(he, erase_exp(ze))
  | LAsc(ze, ht) => Asc(erase_exp(ze), ht)
  | RAsc(he, zt) => Asc(he, erase_typ(zt))
  | NEHole(ze) => NEHole(erase_exp(ze))
  };
}

and erase_typ = (zt: ztyp): htyp => {
  switch (zt) {
  | Cursor(ht) => ht
  | LArrow(zt, ht) => Arrow(erase_typ(zt), ht)
  | RArrow(ht, zt) => Arrow(ht, erase_typ(zt))
  };
};

let rec consistent = (t1: htyp, t2: htyp): bool => {
  switch (t1) {
  | Arrow(t1_1, t1_2) =>
    switch (t2) {
    | Arrow(t2_1, t2_2) =>
      if (consistent(t1_1, t2_1) && consistent(t1_2, t2_2)) {
        true;
      } else {
        false;
      }
    | Num => false
    | Hole => true
    }
  | Num =>
    switch (t2) {
    | Arrow(_, _) => false
    | Num => true
    | Hole => true
    }
  | Hole => true
  };
};

let match_arrow = (t: htyp): option(htyp) => {
  switch (t) {
  | Arrow(_, _) => Some(t)
  | Num => None
  | Hole => Some(Arrow(Hole, Hole))
  };
};

let rec syn = (ctx: typctx, e: hexp): option(htyp) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (e) {
  | Var(str) =>
    if (TypCtx.mem(str, ctx)) {
      Some(TypCtx.find(str, ctx));
    } else {
      None;
    }
  | Lam(_, _) => None
  | Ap(he1, he2) =>
    let t1 = syn(ctx, he1);
    switch (t1) {
    | Some(t2_arrow_t) =>
      switch (t2_arrow_t) {
      | Arrow(_, _)
      | Hole =>
        let arrow = match_arrow(t2_arrow_t);
        switch (arrow) {
        | Some(Arrow(t2, t)) =>
          if (ana(ctx, he2, t2)) {
            Some(t);
          } else {
            None;
          }
        | _ => None
        };
      | Num => None
      }
    | None => None
    };
  | Lit(_) => Some(Num)
  | Plus(he1, he2) =>
    if (ana(ctx, he1, Num) && ana(ctx, he2, Num)) {
      Some(Num);
    } else {
      None;
    }
  | Asc(he, ht) =>
    if (ana(ctx, he, ht)) {
      Some(ht);
    } else {
      None;
    }
  | EHole => Some(Hole)
  | NEHole(he) =>
    let syn_result = syn(ctx, he);
    switch (syn_result) {
    | Some(_) => Some(Hole)
    | None => None
    };
  };
}

and ana = (ctx: typctx, e: hexp, t: htyp): bool => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (e) {
  | Lam(str, he) =>
    switch (t) {
    | Arrow(_, _)
    | Hole =>
      let arrow = match_arrow(t);
      switch (arrow) {
      | Some(Arrow(t1, t2)) =>
        let ctx_new = TypCtx.add(str, t1, ctx);
        if (ana(ctx_new, he, t2)) {
          true;
        } else {
          false;
        };
      | _ => false
      };
    | Num => false
    }
  | _ =>
    let syn_result = syn(ctx, e);
    switch (syn_result) {
    | Some(t_) =>
      if (consistent(t, t_)) {
        true;
      } else {
        false;
      }
    | None => false
    };
  };
};

let syn_action =
    (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;
  let _ = a;

  raise(Unimplemented);
}

and ana_action = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};
