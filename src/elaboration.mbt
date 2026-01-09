///|
using @list {cons, empty}

///|
pub type Env = @list.List[Value]

///|
pub suberror TypeError String

///|
pub fn v_free(n : Name) -> Value {
  VNeutral(NFree(n))
}

///|
pub fn v_app(e : Value, v : Value) -> Value {
  match e {
    VLam(f) => f(v)
    VNeutral(n) => VNeutral(NApp(n, v))
    _ => panic()
  }
}

///|
pub fn v_fst(v : Value) -> Value {
  match v {
    VPair(a, _) => a
    VNeutral(n) => VNeutral(NFst(n))
    _ => panic()
  }
}

///|
pub fn v_snd(v : Value) -> Value {
  match v {
    VPair(_, b) => b
    VNeutral(n) => VNeutral(NSnd(n))
    _ => panic()
  }
}

///|
pub fn v_j_elim(
  a : Value,
  x : Value,
  mot : Value,
  base : Value,
  y : Value,
  p : Value,
) -> Value {
  match p {
    VRfl(_) => base
    VNeutral(n) => VNeutral(NJElim(a, x, mot, base, y, n))
    _ => panic()
  }
}

///|
pub fn v_w_rec(
  a : Value,
  b : (Value) -> Value,
  mot : Value,
  step : Value,
  target : Value,
) -> Value {
  match target {
    VSup(s, f) => {
      let ih = VLam(fn(pos) { v_w_rec(a, b, mot, step, f(pos)) })
      v_app(v_app(v_app(step, s), VLam(f)), ih)
    }
    VNeutral(n) => VNeutral(NWRec(a, b, mot, step, n))
    _ => panic()
  }
}

///|
pub fn v_max_univ(v1 : Value, v2 : Value) -> Value {
  match (v1, v2) {
    (VUniverse(u1), VUniverse(u2)) => VUniverse(u1.max(u2))
    _ => panic()
  }
}

///|
fn ensure_inf(
  i : Int,
  g : Context,
  d : Env,
  t : TermChk,
) -> Value raise TypeError {
  guard t is Inf(t_inf) else { raise TypeError("Type must be Inf") }
  type_inf(i, g, d, t_inf)
}

///|
fn ensure_univ(v : Value) -> Int raise TypeError {
  match v {
    VUniverse(u) => u
    _ => raise TypeError("Expected a universe")
  }
}

///|
pub fn subtyping(i : Int, v1 : Value, v2 : Value) -> Bool {
  match (v1, v2) {
    (VUniverse(u1), VUniverse(u2)) => u1 <= u2
    (VPi(a1, b1), VPi(a2, b2)) => {
      if quote(i, a1) != quote(i, a2) {
        return false
      }
      let v = v_free(Quote(i))
      subtyping(i + 1, b1(v), b2(v))
    }
    (VSigma(a1, b1), VSigma(a2, b2)) => {
      if not(subtyping(i, a1, a2)) {
        return false
      }
      let v = v_free(Quote(i))
      subtyping(i + 1, b1(v), b2(v))
    }
    _ => quote(i, v1) == quote(i, v2)
  }
}

///|
pub fn eval_inf(t : TermInf, d : Env) -> Value {
  match t {
    Ann(e, _) => eval_chk(e, d)
    Universe(u) => VUniverse(u)
    Pi(a, b) => VPi(eval_chk(a, d), fn(x) { eval_chk(b, cons(x, d)) })
    Sigma(a, b) => VSigma(eval_chk(a, d), fn(x) { eval_chk(b, cons(x, d)) })
    Bound(i) => d.iter().nth(i).unwrap()
    Free(x) => v_free(x)
    App(f, e) => v_app(eval_inf(f, d), eval_chk(e, d))
    Fst(p) => v_fst(eval_inf(p, d))
    Snd(p) => v_snd(eval_inf(p, d))
    UnitType => VUnitType
    Id(a, x, y) => VId(eval_chk(a, d), eval_chk(x, d), eval_chk(y, d))
    JElim(a, x, mot, base, y, p) =>
      v_j_elim(
        eval_chk(a, d),
        eval_chk(x, d),
        eval_chk(mot, d),
        eval_chk(base, d),
        eval_chk(y, d),
        eval_inf(p, d),
      )
    W(a, b) => VW(eval_chk(a, d), fn(x) { eval_chk(b, cons(x, d)) })
    WRec(a, b, mot, step, target) => {
      let va = eval_chk(a, d)
      let vb_val = eval_chk(b, d)
      let vb = fn(v) { v_app(vb_val, v) }
      v_w_rec(va, vb, eval_chk(mot, d), eval_chk(step, d), eval_inf(target, d))
    }
  }
}

///|
pub fn eval_chk(t : TermChk, d : Env) -> Value {
  match t {
    Inf(i) => eval_inf(i, d)
    Lam(e) => VLam(fn(x) { eval_chk(e, cons(x, d)) })
    Pair(x, y) => VPair(eval_chk(x, d), eval_chk(y, d))
    UnitElement => VUnitElement
    Rfl(x) => VRfl(eval_chk(x, d))
    Sup(s, f) => {
      let vs = eval_chk(s, d)
      let vf = eval_chk(f, d)
      match vf {
        VLam(cl) => VSup(vs, cl)
        VNeutral(n) => VSup(vs, fn(v) { v_app(VNeutral(n), v) })
        _ => panic()
      }
    }
  }
}

///|
pub fn quote(i : Int, v : Value) -> TermChk {
  match v {
    VUniverse(u) => Inf(Universe(u))
    VPi(a, b) => Inf(Pi(quote(i, a), quote(i + 1, b(v_free(Quote(i))))))
    VSigma(a, b) => Inf(Sigma(quote(i, a), quote(i + 1, b(v_free(Quote(i))))))
    VLam(f) => Lam(quote(i + 1, f(v_free(Quote(i)))))
    VPair(a, b) => Pair(quote(i, a), quote(i, b))
    VUnitType => Inf(UnitType)
    VUnitElement => UnitElement
    VId(a, x, y) => Inf(Id(quote(i, a), quote(i, x), quote(i, y)))
    VRfl(x) => Rfl(quote(i, x))
    VW(a, b) => Inf(W(quote(i, a), quote(i + 1, b(v_free(Quote(i))))))
    VSup(s, f) => Sup(quote(i, s), Lam(quote(i + 1, f(v_free(Quote(i))))))
    VNeutral(n) => Inf(neutral_quote(i, n))
  }
}

///|
pub fn neutral_quote(i : Int, n : Neutral) -> TermInf {
  match n {
    NFree(x) =>
      match x {
        Quote(k) => Bound(i - k - 1)
        _ => Free(x)
      }
    NApp(n, v) => App(neutral_quote(i, n), quote(i, v))
    NFst(n) => Fst(neutral_quote(i, n))
    NSnd(n) => Snd(neutral_quote(i, n))
    NJElim(a, x, mot, base, y, p) =>
      JElim(
        quote(i, a),
        quote(i, x),
        quote(i, mot),
        quote(i, base),
        quote(i, y),
        neutral_quote(i, p),
      )
    NWRec(a, b, mot, step, n) =>
      WRec(
        quote(i, a),
        quote(i + 1, b(v_free(Quote(i)))),
        quote(i, mot),
        quote(i, step),
        neutral_quote(i, n),
      )
  }
}

///|
pub fn type_inf(
  i : Int,
  g : Context,
  d : Env,
  t : TermInf,
) -> Type raise TypeError {
  match t {
    Universe(u) => VUniverse(u + 1)
    UnitType => VUniverse(0)
    Ann(e, dt) => {
      guard dt is Inf(t_inf) else { raise TypeError("Type must be Inf") }
      let ti = type_inf(i, g, d, t_inf)
      match ti {
        VUniverse(_) => {
          let ty = eval_inf(t_inf, d)
          type_chk(i, g, d, e, ty)
          ty
        }
        _ => raise TypeError("The annotation's type is not a type")
      }
    }
    Pi(a, b) | Sigma(a, b) | W(a, b) => {
      let u1 = ensure_inf(i, g, d, a) |> ensure_univ()
      let va = eval_chk(a, d)
      let u2 = ensure_inf(
          i + 1,
          cons((Local(i), va), g),
          cons(v_free(Local(i)), d),
          b,
        )
        |> ensure_univ()
      VUniverse(u1.max(u2))
    }
    Bound(j) => {
      let val = d.iter().nth(j).unwrap()
      match val {
        VNeutral(NFree(n)) =>
          match g.iter().find_first(fn(pair) { pair.0 == n }) {
            Some((_, ty)) => ty
            None => raise TypeError("Unknown Identifier")
          }
        _ =>
          raise TypeError("Internal error: Bound variable not in environment")
      }
    }
    Free(x) =>
      match g.iter().find_first(fn(pair) { pair.0 == x }) {
        Some((_, ty)) => ty
        None => raise TypeError("Unknown Identifier: \{x}")
      }
    App(f, e) =>
      match type_inf(i, g, d, f) {
        VPi(a, b) => {
          type_chk(i, g, d, e, a)
          b(eval_chk(e, d))
        }
        _ => raise TypeError("Illegal Application")
      }
    Fst(p) =>
      match type_inf(i, g, d, p) {
        VSigma(a, _) => a
        _ => raise TypeError("Fst expects Sigma")
      }
    Snd(p) =>
      match type_inf(i, g, d, p) {
        VSigma(_, b) => b(v_fst(eval_inf(p, d)))
        _ => raise TypeError("Snd expects Sigma")
      }
    Id(a, x, y) => {
      let u = ensure_inf(i, g, d, a) |> ensure_univ()
      let va = eval_chk(a, d)
      type_chk(i, g, d, x, va)
      type_chk(i, g, d, y, va)
      VUniverse(u)
    }
    JElim(a, x, mot, base, y, p) => {
      ensure_inf(i, g, d, a) |> ensure_univ() |> ignore
      let va = eval_chk(a, d)
      type_chk(i, g, d, x, va)
      let vx = eval_chk(x, d)
      type_chk(i, g, d, y, va)
      let vy = eval_chk(y, d)
      type_chk(i, g, d, Inf(p), VId(va, vx, vy))
      let mot_ty = ensure_inf(i, g, d, mot)
      match mot_ty {
        VPi(_, f1) =>
          match f1(v_free(Quote(i))) {
            VPi(_, f2) => {
              let co_domain = f2(v_free(Quote(i + 1)))
              ensure_univ(co_domain) |> ignore
            }
            _ => raise TypeError("Motive must be a binary function")
          }
        _ => raise TypeError("Motive must be a function")
      }
      let v_mot = eval_chk(mot, d)
      type_chk(i, g, d, base, v_app(v_app(v_mot, vx), VRfl(vx)))
      v_app(v_app(v_mot, vy), eval_inf(p, d))
    }
    WRec(a, b, mot, step, target) => {
      ensure_inf(i, g, d, a) |> ensure_univ() |> ignore
      let va = eval_chk(a, d)
      let b_ty = ensure_inf(i, g, d, b)
      match b_ty {
        VPi(dom, cod) => {
          if quote(i, dom) != quote(i, va) {
            raise TypeError("W-type: B domain mismatch")
          }
          let _ = ensure_univ(cod(v_free(Quote(i))))

        }
        _ => raise TypeError("WRec: B must be a function")
      }
      let vb_val = eval_chk(b, d)
      let vb = fn(v) { v_app(vb_val, v) }
      let v_w = VW(va, vb)
      type_chk(i, g, d, Inf(target), v_w)
      let mot_ty = ensure_inf(i, g, d, mot)
      match mot_ty {
        VPi(dom, cod) => {
          if quote(i, dom) != quote(i, v_w) {
            raise TypeError("WRec: motive domain mismatch")
          }
          ensure_univ(cod(v_free(Quote(i)))) |> ignore
        }
        _ => raise TypeError("WRec: motive must be a function")
      }
      let v_mot = eval_chk(mot, d)
      let step_ty = VPi(va, fn(s) {
        let v_bs = vb(s)
        VPi(VPi(v_bs, fn(_) { v_w }), fn(f) {
          VPi(VPi(v_bs, fn(p) { v_app(v_mot, v_app(f, p)) }), fn(_) {
            v_app(v_mot, VSup(s, fn(pos) { v_app(f, pos) }))
          })
        })
      })
      type_chk(i, g, d, step, step_ty)
      v_app(v_mot, eval_inf(target, d))
    }
  }
}

///|
pub fn type_chk(
  i : Int,
  g : Context,
  d : Env,
  t : TermChk,
  v : Type,
) -> Unit raise TypeError {
  match t {
    Inf(e) => {
      let vn = type_inf(i, g, d, e)
      if not(subtyping(i, vn, v)) {
        raise TypeError(
          "Type Mismatch: inferred type is not a subtype of expected type",
        )
      }
    }
    Lam(e) =>
      match v {
        VPi(a, b) =>
          type_chk(
            i + 1,
            cons((Local(i), a), g),
            cons(v_free(Local(i)), d),
            e,
            b(v_free(Local(i))),
          )
        _ => raise TypeError("Expected Pi type for Lambda")
      }
    Pair(e1, e2) =>
      match v {
        VSigma(a, b) => {
          type_chk(i, g, d, e1, a)
          type_chk(i, g, d, e2, b(eval_chk(e1, d)))
        }
        _ => raise TypeError("Expected Sigma type for Pair")
      }
    UnitElement =>
      match v {
        VUnitType => ()
        _ => raise TypeError("Expected UnitType")
      }
    Rfl(x) =>
      match v {
        VId(va, vx, vy) => {
          type_chk(i, g, d, x, va)
          let vx_val = eval_chk(x, d)
          if quote(i, vx_val) != quote(i, vx) ||
            quote(i, vx_val) != quote(i, vy) {
            raise TypeError("Rfl endpoints mismatch")
          }
        }
        _ => raise TypeError("Expected Id type for Rfl")
      }
    Sup(s, f) =>
      match v {
        VW(va, vb) => {
          type_chk(i, g, d, s, va)
          let vs = eval_chk(s, d)
          type_chk(i, g, d, f, VPi(vb(vs), fn(_) { VW(va, vb) }))
        }
        _ => raise TypeError("Expected W type for Sup")
      }
  }
}

///|
pub fn type_inf_0(g : Context, t : TermInf) -> Type raise TypeError {
  type_inf(0, g, empty(), t)
}
