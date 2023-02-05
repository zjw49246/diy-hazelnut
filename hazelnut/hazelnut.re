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

let rec typ_action = (t: ztyp, a: action): option(ztyp) => {
  switch (a) {
  | Move(dr) =>
    switch (dr) {
    | Child(ch) =>
      switch (t) {
      | Cursor(Arrow(t1, t2)) =>
        switch (ch) {
        | One => Some(LArrow(Cursor(t1), t2))
        | Two => Some(RArrow(t1, Cursor(t2)))
        }
      | _ => zipper_typ_action(t, a)
      }
    | Parent =>
      switch (t) {
      | LArrow(Cursor(t1), t2)
      | RArrow(t1, Cursor(t2)) => Some(Cursor(Arrow(t1, t2)))
      | _ => zipper_typ_action(t, a)
      }
    }
  | Construct(sp) =>
    switch (sp) {
    | Arrow =>
      switch (t) {
      | Cursor(t1) => Some(RArrow(t1, Cursor(Hole)))
      | _ => zipper_typ_action(t, a)
      }
    | Num =>
      switch (t) {
      | Cursor(Hole) => Some(Cursor(Num))
      | _ => zipper_typ_action(t, a)
      }
    | _ => None
    }
  | Del =>
    switch (t) {
    | Cursor(_) => Some(Cursor(Hole))
    | _ => zipper_typ_action(t, a)
    }
  | _ => None
  };
}

and zipper_typ_action = (t: ztyp, a: action): option(ztyp) => {
  switch (t) {
  | LArrow(zt, ht) =>
    switch (typ_action(zt, a)) {
    | Some(zt_new) => Some(LArrow(zt_new, ht))
    | _ => None
    }
  | RArrow(ht, zt) =>
    switch (typ_action(zt, a)) {
    | Some(zt_new) => Some(RArrow(ht, zt_new))
    | _ => None
    }
  | _ => None
  };
};

let rec syn_action =
        (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (a) {
  | Move(_) =>
    switch (move_action(e, a)) {
    | Some(ze_new) => Some((ze_new, t))
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | Del =>
    switch (e) {
    | Cursor(_) => Some((Cursor(EHole), Hole))
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | Construct(Asc) =>
    switch (e) {
    | Cursor(he) => Some((RAsc(he, Cursor(t)), t))
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | Construct(Var(st)) =>
    if (TypCtx.mem(st, ctx)) {
      switch (e) {
      | Cursor(EHole) =>
        switch (t) {
        | Hole => Some((Cursor(Var(st)), TypCtx.find(st, ctx)))
        | _ => zipper_syn_action(ctx, (e, t), a)
        }
      | _ => zipper_syn_action(ctx, (e, t), a)
      };
    } else {
      zipper_syn_action(ctx, (e, t), a);
    }
  | Construct(Lam(st)) =>
    switch (e) {
    | Cursor(EHole) =>
      switch (t) {
      | Hole =>
        Some((
          RAsc(Lam(st, EHole), LArrow(Cursor(Hole), Hole)),
          Arrow(Hole, Hole),
        ))
      | _ => zipper_syn_action(ctx, (e, t), a)
      }
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | Construct(Ap) =>
    switch (e) {
    | Cursor(he) =>
      switch (match_arrow(t)) {
      | Some(Arrow(_, t2)) => Some((RAp(he, Cursor(EHole)), t2))
      | _ =>
        // equavalent to t inconsistent with (Hole arrow Hole), i.e. t is Num
        Some((RAp(NEHole(he), Cursor(EHole)), Hole))
      }
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | Construct(Lit(i)) =>
    switch (e) {
    | Cursor(EHole) =>
      switch (t) {
      | Hole => Some((Cursor(Lit(i)), Num))
      | _ => zipper_syn_action(ctx, (e, t), a)
      }
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | Construct(Plus) =>
    switch (e) {
    | Cursor(he) =>
      if (consistent(t, Num)) {
        Some((RPlus(he, Cursor(EHole)), Num));
      } else {
        Some((RPlus(NEHole(he), Cursor(EHole)), Num));
      }
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | Construct(NEHole) =>
    switch (e) {
    | Cursor(he) => Some((NEHole(Cursor(he)), Hole))
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | Finish =>
    switch (e) {
    | Cursor(NEHole(he)) =>
      switch (t) {
      | Hole =>
        switch (syn(ctx, he)) {
        | Some(t_new) => Some((Cursor(he), t_new))
        | _ => zipper_syn_action(ctx, (e, t), a)
        }
      | _ => zipper_syn_action(ctx, (e, t), a)
      }
    | _ => zipper_syn_action(ctx, (e, t), a)
    }
  | _ => zipper_syn_action(ctx, (e, t), a)
  };
}

and zipper_syn_action =
    (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  switch (e) {
  | LAsc(ze, ht) =>
    if (ht == t) {
      switch (ana_action(ctx, ze, a, ht)) {
      | Some(ze_new) => Some((LAsc(ze_new, ht), ht))
      | _ => None
      };
    } else {
      None;
    }
  | RAsc(he, zt) =>
    if (erase_typ(zt) == t) {
      switch (typ_action(zt, a)) {
      | Some(zt_new) =>
        let zt_new_erase = erase_typ(zt_new);
        if (ana(ctx, he, zt_new_erase)) {
          Some((RAsc(he, zt_new), zt_new_erase));
        } else {
          None;
        };
      | _ => None
      };
    } else {
      None;
    }
  | LAp(ze, he) =>
    switch (syn(ctx, erase_exp(ze))) {
    | Some(t2) =>
      switch (syn_action(ctx, (ze, t2), a)) {
      | Some((ze_new, t3)) =>
        switch (match_arrow(t3)) {
        | Some(Arrow(t4, t5)) =>
          if (ana(ctx, he, t4)) {
            Some((LAp(ze_new, he), t5));
          } else {
            None;
          }
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | RAp(he, ze) =>
    switch (syn(ctx, he)) {
    | Some(t2) =>
      switch (match_arrow(t2)) {
      | Some(Arrow(t3, t4)) =>
        switch (ana_action(ctx, ze, a, t3)) {
        | Some(ze_new) => Some((RAp(he, ze_new), t4))
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | LPlus(ze, he) =>
    switch (t) {
    | Num =>
      switch (ana_action(ctx, ze, a, Num)) {
      | Some(ze_new) => Some((LPlus(ze_new, he), Num))
      | _ => None
      }
    | _ => None
    }
  | RPlus(he, ze) =>
    switch (t) {
    | Num =>
      switch (ana_action(ctx, ze, a, Num)) {
      | Some(ze_new) => Some((RPlus(he, ze_new), Num))
      | _ => None
      }
    | _ => None
    }
  | NEHole(ze) =>
    switch (t) {
    | Hole =>
      switch (syn(ctx, erase_exp(ze))) {
      | Some(t1) =>
        switch (syn_action(ctx, (ze, t1), a)) {
        | Some((ze_new, _)) => Some((NEHole(ze_new), Hole))
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | _ => None
  };
}

and move_action = (e: zexp, a: action): option(zexp) => {
  switch (a) {
  | Move(Child(One)) =>
    switch (e) {
    | Cursor(Asc(he, ht)) => Some(LAsc(Cursor(he), ht))
    | Cursor(Lam(st, he)) => Some(Lam(st, Cursor(he)))
    | Cursor(Plus(he1, he2)) => Some(LPlus(Cursor(he1), he2))
    | Cursor(Ap(he1, he2)) => Some(LAp(Cursor(he1), he2))
    | Cursor(NEHole(he)) => Some(NEHole(Cursor(he)))
    | _ => None
    }
  | Move(Child(Two)) =>
    switch (e) {
    | Cursor(Asc(he, ht)) => Some(RAsc(he, Cursor(ht)))
    | Cursor(Plus(he1, he2)) => Some(RPlus(he1, Cursor(he2)))
    | Cursor(Ap(he1, he2)) => Some(RAp(he1, Cursor(he2)))
    | _ => None
    }
  | Move(Parent) =>
    switch (e) {
    | LAsc(Cursor(he), ht)
    | RAsc(he, Cursor(ht)) => Some(Cursor(Asc(he, ht)))
    | Lam(st, Cursor(he)) => Some(Cursor(Lam(st, he)))
    | LPlus(Cursor(he1), he2)
    | RPlus(he1, Cursor(he2)) => Some(Cursor(Plus(he1, he2)))
    | LAp(Cursor(he1), he2)
    | RAp(he1, Cursor(he2)) => Some(Cursor(Ap(he1, he2)))
    | NEHole(Cursor(he)) => Some(Cursor(NEHole(he)))
    | _ => None
    }
  | _ => None
  };
}

and ana_action = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (a) {
  | Move(_) =>
    switch (move_action(e, a)) {
    | Some(e_new) => Some(e_new)
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Del =>
    switch (e) {
    | Cursor(_) => Some(Cursor(EHole))
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Construct(Asc) =>
    switch (e) {
    | Cursor(he) => Some(RAsc(he, Cursor(t)))
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Construct(Var(st)) =>
    switch (e) {
    | Cursor(EHole) =>
      if (TypCtx.mem(st, ctx)) {
        if (!consistent(TypCtx.find(st, ctx), t)) {
          Some(NEHole(Cursor(Var(st))));
        } else {
          zipper_ana_action(ctx, e, a, t);
        };
      } else {
        zipper_ana_action(ctx, e, a, t);
      }
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Construct(Lam(st)) =>
    switch (e) {
    | Cursor(EHole) =>
      switch (match_arrow(t)) {
      | Some(Arrow(_, _)) => Some(Lam(st, Cursor(EHole)))
      | _ =>
        Some(NEHole(RAsc(Lam(st, EHole), LArrow(Cursor(Hole), Hole))))
      }
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Construct(Lit(i)) =>
    switch (e) {
    | Cursor(EHole) =>
      if (!consistent(t, Num)) {
        Some(NEHole(Cursor(Lit(i))));
      } else {
        zipper_ana_action(ctx, e, a, t);
      }
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | Finish =>
    switch (e) {
    | Cursor(NEHole(he)) =>
      if (ana(ctx, he, t)) {
        Some(Cursor(he));
      } else {
        zipper_ana_action(ctx, e, a, t);
      }
    | _ => zipper_ana_action(ctx, e, a, t)
    }
  | _ => zipper_ana_action(ctx, e, a, t)
  };
}

and zipper_ana_action =
    (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  switch (e) {
  | Lam(st, ze) =>
    switch (match_arrow(t)) {
    | Some(Arrow(t1, t2)) =>
      let ctx_new = TypCtx.add(st, t1, ctx);
      switch (ana_action(ctx_new, ze, a, t2)) {
      | Some(ze_new) => Some(Lam(st, ze_new))
      | _ => subsumption(ctx, e, a, t)
      };
    | _ => subsumption(ctx, e, a, t)
    }
  | _ => subsumption(ctx, e, a, t)
  };
}

and subsumption = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  switch (syn(ctx, erase_exp(e))) {
  | Some(t_new) =>
    switch (syn_action(ctx, (e, t_new), a)) {
    | Some((ze_new, t_new2)) =>
      if (consistent(t, t_new2)) {
        Some(ze_new);
      } else {
        None;
      }
    | _ => None
    }
  | _ => None
  };
};
