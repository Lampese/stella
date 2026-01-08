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

// J-Eliminator 归约: J(..., Rfl x) -> method

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
pub fn eval_inf(t : TermInf, d : Env) -> Value {
  match t {
    Ann(e, _) => eval_chk(e, d)
    Star => VStar
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
      let vb = match vb_val {
        VPi(_, f) => f
        _ => panic()
      }
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
    VStar => Inf(Star)
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
    Star | UnitType => VStar
    Ann(e, dt) => {
      type_chk(i, g, d, dt, VStar)
      let ty = eval_chk(dt, d)
      type_chk(i, g, d, e, ty)
      ty
    }
    Pi(a, b) | Sigma(a, b) | W(a, b) => {
      type_chk(i, g, d, a, VStar)
      let va = eval_chk(a, d)
      type_chk(
        i + 1,
        cons((Local(i), va), g),
        cons(v_free(Local(i)), d),
        b,
        VStar,
      )
      VStar
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
      type_chk(i, g, d, a, VStar)
      let va = eval_chk(a, d)
      type_chk(i, g, d, x, va)
      type_chk(i, g, d, y, va)
      VStar
    }
    JElim(a, x, mot, base, y, p) => {
      type_chk(i, g, d, a, VStar)
      let va = eval_chk(a, d)
      type_chk(i, g, d, x, va)
      let vx = eval_chk(x, d)
      type_chk(i, g, d, y, va)
      let vy = eval_chk(y, d)
      type_chk(i, g, d, Inf(p), VId(va, vx, vy))
      let mot_ty = VPi(va, fn(y_p) { VPi(VId(va, vx, y_p), fn(_) { VStar }) })
      type_chk(i, g, d, mot, mot_ty)
      let v_mot = eval_chk(mot, d)
      type_chk(i, g, d, base, v_app(v_app(v_mot, vx), VRfl(vx)))
      v_app(v_app(v_mot, vy), eval_inf(p, d))
    }
    WRec(a, b, mot, step, target) => {
      type_chk(i, g, d, a, VStar)
      let va = eval_chk(a, d)
      type_chk(i, g, d, b, VPi(va, fn(_) { VStar }))
      let vb_val = eval_chk(b, d)
      let vb = match vb_val {
        VPi(_, f) => f
        _ => panic()
      }
      let v_w = VW(va, vb)
      type_chk(i, g, d, Inf(target), v_w)
      type_chk(i, g, d, mot, VPi(v_w, fn(_) { VStar }))
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
      if quote(i, v) != quote(i, vn) {
        raise TypeError("Type Mismatch")
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
