use std::collections::{BTreeMap, HashMap};

pub enum Crouton<'decl: 'route, 'route: 'ret, 'ret> {
  End(Box<&'decl str>),
  Slurp(Box<&'decl str>),
  Literal(Box<&'decl str>, Box<Crouton<'decl, 'route, 'ret>>),
  Bind(Box<&'decl str>, Box<Crouton<'decl, 'route, 'ret>>),
  Cond(fn(&'route str)-> bool, Box<Crouton<'decl, 'route, 'ret>>),
  BindCond(Box<&'decl str>, fn(&'route str)-> bool, Box<Crouton<'decl, 'route, 'ret>>),
  OrElse(Box<Crouton<'decl, 'route, 'ret>>, Box<Crouton<'decl, 'route, 'ret>>),
  LiteralVec(Vec<(&'decl str, Box<Crouton<'decl, 'route, 'ret>>)>),
  LiteralSlice(&'ret [(&'decl str, Box<Crouton<'decl, 'route, 'ret>>)]),
  LiteralHashMap(HashMap<&'decl str, Box<Crouton<'decl, 'route, 'ret>>>),
  LiteralBTreeMap(BTreeMap<&'decl str, Box<Crouton<'decl, 'route, 'ret>>>),
}

#[macro_export] macro_rules! end      { ($name:expr) => (Crouton::End(Box::new($name))) }
#[macro_export] macro_rules! slurp    { ($name:expr) => (Crouton::Slurp(Box::new($name))) }
#[macro_export] macro_rules! literal  { ($lit:expr,  $next:expr) => (Crouton::Literal(Box::new($lit), Box::new($next))) }
#[macro_export] macro_rules! bind     { ($name:expr, $next:expr) => (Crouton::Bind(Box::new($name), Box::new($next))) }
#[macro_export] macro_rules! cond     { ($cond:expr, $next:expr) => (Crouton::Cond($cond, Box::new($next))) }
#[macro_export] macro_rules! bindcond { ($bind:expr, $cond:expr, $next:expr) => (Crouton::BindCond(Box::new($bind), $cond, Box::new($next))) }
#[macro_export] macro_rules! orelse   { ($l:expr, $r:expr) => (Crouton::OrElse(Box::new($l), Box::new($r))) }
#[macro_export] macro_rules! literalvec      { ($items:expr) => (Crouton::LiteralVec($items)) }
#[macro_export] macro_rules! literalslice    { ($items:expr) => (Crouton::LiteralSlice($items)) }
#[macro_export] macro_rules! literalhashmap  { ($items:expr) => (Crouton::LiteralHashMap($items)) }
#[macro_export] macro_rules! literalbtreemap { ($items:expr) => (Crouton::LiteralBTreeMap($items)) }

#[derive(Debug)]
pub struct Routing<'decl: 'route, 'route: 'ret, 'ret> {
  pub pieces: &'ret [&'route str],
  pub matches: Vec<(&'decl str, &'route str)>,
}

impl<'decl: 'route, 'route: 'ret, 'ret> Routing<'decl, 'route, 'ret> {
  pub fn new(pieces: &'ret [&'route str], matches: Vec<(&'decl str, &'route str)>)
    -> Routing<'decl, 'route, 'ret> {
    Routing { pieces: pieces, matches: matches }
  }
}

pub type RouteResult<'decl: 'route, 'route: 'ret, 'ret> = Result<Route<'decl, 'route>, Routing<'decl, 'route, 'ret>>;
pub type RoutingResult<'decl: 'route, 'route: 'ret, 'ret> = Result<Routing<'decl, 'route, 'ret>, Routing<'decl, 'route, 'ret>>;

#[derive(Debug)]
pub struct Route<'decl: 'route, 'route> {
  pub name: &'decl str,
  pub matches: Vec<(&'decl str, &'route str)>,
}

fn skip<'decl: 'route, 'route: 'ret, 'ret>(routing: Routing<'decl, 'route, 'ret>) -> RoutingResult<'decl, 'route, 'ret> {
  routing.pieces.get(1..)
    .map(|ps| Routing { pieces: ps, matches: routing.matches.clone() }).ok_or(routing)
}
fn skip_bind<'decl: 'route, 'route: 'ret, 'ret>(routing: Routing<'decl, 'route, 'ret>, name: &'decl str) -> RoutingResult<'decl, 'route, 'ret> {
  match routing.pieces.get(1..) {
    Some(ps) => {
      let mut ms = routing.matches.clone();
      ms.push((name, routing.pieces[0]));
      Ok(Routing { pieces: ps, matches: ms })
    },
    None => Err(routing),
  }
}

fn deconstruct(path: &str) -> Vec<&str> {
  let mut rest = path;
  let mut pieces = vec!();
  loop {
    if rest.is_empty() { return pieces; }
    match rest.find('/') {
      Some(0) => match rest.get(1..) {
        Some(s) => rest = s,
        None => return pieces,
      },
      Some(n) => {
        pieces.push(&rest[..n]);
        match rest.get(n..) {
          Some(s) => rest = s,
          None =>  return pieces,
        }
      },
      None => {
        pieces.push(rest);
        return pieces;
      }
    }
  }
}

impl<'decl: 'route, 'route: 'ret, 'ret> Crouton<'decl, 'route, 'ret> {
  fn route(&self, state: Routing<'decl, 'route, 'ret>) -> RouteResult<'decl, 'route, 'ret> {
    match self {
      &Crouton::End(ref name) => {
        if state.pieces.is_empty() { Ok(Route { name: &name, matches: state.matches }) }
        else { Err(state) }
      },
      &Crouton::Slurp(ref name) => {
        let mut ms = state.matches.clone();
        for p in state.pieces { ms.push((&*name, p)) }
        Ok(Route { name: &*name, matches: ms })
      },
      &Crouton::Literal(ref val, ref next) => {
        if state.pieces.is_empty() || &*state.pieces[0] != **val { Err(state) }
        else { skip(state).and_then(|st| next.route(st)) }
      },
      &Crouton::Bind(ref name, ref next) => {
        if state.pieces.is_empty() { Err(state) }
        else { skip_bind(state, &*name).and_then(|st| next.route(st)) }
      },
      &Crouton::Cond(ref pred, ref next) => {
        if state.pieces.is_empty() || !pred(&*state.pieces[0]) { Err(state) }
        else { skip(state).and_then(|st| next.route(st)) }
      },
      &Crouton::BindCond(ref name, ref pred, ref next) => {
        if state.pieces.is_empty() || !pred(&*state.pieces[0]) { Err(state) }
        else { skip_bind(state, &*name).and_then(|st| next.route(st)) }
      },
      &Crouton::OrElse(ref l, ref r) => {
        match l.route(state) {
          Ok(v) => Ok(v),
          Err(st) => r.route(st),
        }
      },
      &Crouton::LiteralVec(ref ls) => {
        if state.pieces.is_empty() { Err(state) }
        else {
          let mut st = state;
          for kv in ls.iter() {
            let (ref k,ref v) = *kv;
            if st.pieces[0] == *k {
              match skip(st).and_then(|st2| v.route(st2)) {
                Ok(v) => return Ok(v),
                Err(s) => { st = s; }
              }
            }
          }
          Err(st)
        }
      },
      &Crouton::LiteralSlice(ref ls) => {
        if state.pieces.is_empty() { Err(state) }
        else {
          let mut st = state;
          for kv in ls.iter() {
            let (ref k,ref v) = *kv;
            if st.pieces[0] == *k {
              match skip(st).and_then(|st2| v.route(st2)) {
                Ok(v) => return Ok(v),
                Err(s) => { st = s; }
              }
            }
          }
          Err(st)
        }
      },
      &Crouton::LiteralHashMap(ref ls) => {
        if state.pieces.is_empty() { Err(state) }
        else {
          match ls.get(state.pieces[0]) {
            Some(v) => skip(state).and_then(|st| v.route(st)),
            None => Err(state),
          }
        }
      },
      &Crouton::LiteralBTreeMap(ref ls) => {
        if state.pieces.is_empty() { Err(state) }
        else {
          match ls.get(state.pieces[0]) {
            Some(v) => skip(state).and_then(|st| v.route(st)),
            None => Err(state),
          }
        }
      },
    }
  }
}

pub struct Router<'decl: 'route, 'route: 'ret, 'ret> {
  pub crouton: Crouton<'decl, 'route, 'ret>
}
impl<'decl: 'route, 'route: 'ret, 'ret> Router<'decl, 'route, 'ret> {
  pub fn new(crouton: Crouton<'decl, 'route, 'ret>) -> Router<'decl, 'route, 'ret> { Router { crouton: crouton } }
  pub fn route(&self, path: &'route str) -> Option<Route<'decl, 'route>> {
    let pieces = deconstruct(path);
    let r = Routing { pieces: &pieces, matches: vec!() };
    self.crouton.route(r).ok()
  }
}

#[cfg(test)]
mod tests {

  use ::Crouton;
  use std::collections::{BTreeMap, HashMap};

  #[test]
  fn skip() {
    let v1 = vec!("hello","world");
    let v2 = vec!("hello");
    let v3 = vec!();
    let r1 = ::skip(::Routing::new(v1.as_slice(), vec!() )).unwrap();
    let r2 = ::skip(::Routing::new(v2.as_slice(), vec!() )).unwrap();
    let r3 = ::skip(::Routing::new(v3.as_slice(), vec!() ));
    let r4 = ::skip(::Routing::new(v1.as_slice(), vec!(("hello","world")) )).unwrap();
    let r5 = ::skip(::Routing::new(v2.as_slice(), vec!(("hello","world")) )).unwrap();
    assert_eq!(r1.pieces.len(),1);
    assert_eq!(r1.matches.len(),0);
    assert_eq!(r1.pieces[0],"world");
    assert_eq!(r2.pieces.is_empty(),true);
    assert_eq!(r2.matches.len(),0);
    assert_eq!(r3.is_err(),true);
    assert_eq!(r4.matches.len(),1);
    assert_eq!(r4.pieces.len(),1);
    let (k4,v4) = r4.matches[0];
    assert_eq!(k4, "hello");
    assert_eq!(v4, "world");
    assert_eq!(r5.matches.len(),1);
    assert_eq!(r5.pieces.is_empty(),true);
    let (k5,v5) = r5.matches[0];
    assert_eq!(k5, "hello");
    assert_eq!(v5, "world");
  }
  #[test]
  fn skip_bind() {
    let v1 = vec!("hello","world");
    let v2 = vec!("hello");
    let v3 = vec!();
    let r1 = ::skip_bind(::Routing::new(v1.as_slice(), vec!()), "world").unwrap();
    let r2 = ::skip_bind(::Routing::new(v2.as_slice(), vec!()), "world").unwrap();
    let r3 = ::skip_bind(::Routing::new(v3.as_slice(), vec!()), "world");
    let r4 = ::skip_bind(::Routing::new(v1.as_slice(), vec!(("hello","world"))), "world").unwrap();
    let r5 = ::skip_bind(::Routing::new(v2.as_slice(), vec!(("hello","world"))), "world").unwrap();
    assert_eq!(r1.pieces.len(),1);
    assert_eq!(r1.matches.len(),1);
    let (k1,v1) = r1.matches[0];
    assert_eq!(k1, "world");
    assert_eq!(v1, "hello");
    assert_eq!(r2.pieces.is_empty(),true);
    assert_eq!(r2.matches.len(),1);
    let (k2,v2) = r2.matches[0];
    assert_eq!(k2, "world");
    assert_eq!(v2, "hello");
    assert_eq!(r3.is_err(),true);
    assert_eq!(r4.matches.len(),2);
    assert_eq!(r4.pieces.len(),1);
    let (k41,v41) = r4.matches[0];
    assert_eq!(k41, "hello");
    assert_eq!(v41, "world");
    let (k42,v42) = r4.matches[1];
    assert_eq!(k42, "world");
    assert_eq!(v42, "hello");
    assert_eq!(r5.matches.len(),2);
    assert_eq!(r5.pieces.is_empty(),true);
    let (k51,v51) = r5.matches[0];
    assert_eq!(k51, "hello");
    assert_eq!(v51, "world");
    let (k52,v52) = r5.matches[1];
    assert_eq!(k52, "world");
    assert_eq!(v52, "hello");
  }
  #[test]
  fn deconstruct() {
    let t1 = "///hello///world//";
    let t2 = "";
    let t3 = "///";
    let t4 = "/hello/world";
    let r1 = ::deconstruct(t1);
    let r2 = ::deconstruct(t2);
    let r3 = ::deconstruct(t3);
    let r4 = ::deconstruct(t4);
    assert_eq!(r1.len(),2);
    assert_eq!(r2.len(),0);
    assert_eq!(r3.len(),0);
    assert_eq!(r1[0], "hello");
    assert_eq!(r1[1], "world");
    assert_eq!(r4.len(),2);
    assert_eq!(r4[0], "hello");
    assert_eq!(r4[1], "world");
  }
  #[test]
  fn route_end() {
    let r = end!("hello").route(::Routing::new(vec!().as_slice(), vec!())).unwrap();
    assert_eq!(r.name, "hello");
    assert_eq!(r.matches.is_empty(), true);
  }
  #[test]
  fn route_slurp() {
    let r1 = slurp!("hello")
      .route(::Routing::new(vec!().as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = slurp!("hello")
      .route(::Routing::new(vec!("world").as_slice(), vec!())).unwrap();
    assert_eq!(r2.name, "hello");
    assert_eq!(r2.matches.len(), 1);
    let (k2,v2) = r2.matches[0];
    assert_eq!(k2, "hello");
    assert_eq!(v2, "world");
    let r3 = slurp!("hello")
      .route(::Routing::new(vec!("hello", "world").as_slice(), vec!())).unwrap();
    assert_eq!(r3.matches.len(), 2);
    let (k30,v30) = r3.matches[0];
    assert_eq!(k30, "hello");
    assert_eq!(v30, "hello");
    let (k31,v31) = r3.matches[1];
    assert_eq!(k31, "hello");
    assert_eq!(v31, "world");
    let r4 = slurp!("hello")
      .route(::Routing::new(vec!("world").as_slice(), vec!(("world", "hello")))).unwrap();
    assert_eq!(r4.name, "hello");
    assert_eq!(r3.matches.len(), 2);
    let (k40,v40) = r4.matches[0];
    let (k41,v41) = r4.matches[1];
    assert_eq!(k40, "world");
    assert_eq!(v40, "hello");
    assert_eq!(k41, "hello");
    assert_eq!(v41, "world");
  }  
  #[test]
  fn route_literal() {
    let e = vec!();
    let w = vec!("world");
    let h = vec!("hello");
    let r1 = literal!("world", end!("hello"))
      .route(::Routing::new(w.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = literal!("world", end!("hello"))
      .route(::Routing::new(w.as_slice(), vec!(("world","hello")))).unwrap();
    assert_eq!(r2.name, "hello");
    assert_eq!(r2.matches.len(), 1);
    let (k,v) = r2.matches[0];
    assert_eq!(k, "world");
    assert_eq!(v, "hello");
    let r3 = literal!("world", end!("hello"))
      .route(::Routing::new(e.as_slice(), vec!()));
    assert_eq!(r3.is_err(), true);
    let r4 = literal!("world", end!("hello"))
      .route(::Routing::new(h.as_slice(), vec!()));
    assert_eq!(r4.is_err(), true);
  }  
  #[test]
  fn route_bind() {
    let e = vec!();
    let w = vec!("world");
    let r1 = bind!("hello", end!("hello"))
      .route(::Routing::new(w.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.len(), 1);
    let (k10,v10) = r1.matches[0];
    assert_eq!(k10, "hello");
    assert_eq!(v10, "world");
    let r2 = bind!("hello", end!("hello"))
      .route(::Routing::new(w.as_slice(), vec!(("world", "hello")))).unwrap();
    assert_eq!(r2.name, "hello");
    assert_eq!(r2.matches.len(), 2);
    let (k20,v20) = r2.matches[0];
    let (k21,v21) = r2.matches[1];
    assert_eq!(k20, "world");
    assert_eq!(v20, "hello");
    assert_eq!(k21, "hello");
    assert_eq!(v21, "world");
    let r3 = bind!("world", end!("hello"))
      .route(::Routing::new(e.as_slice(), vec!()));
    assert_eq!(r3.is_err(), true);
  }

  fn cond_hello(val: &str) -> bool { val == "hello" }
  fn cond_five(val: &str) -> bool { val.len() == 5 }

  #[test]
  fn route_cond() {
    let e = vec!();
    let w = vec!("world");
    let h = vec!("hello");
    let r1 = cond!(cond_hello, end!("hello"))
      .route(::Routing::new(h.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = cond!(cond_hello, end!("hello"))
      .route(::Routing::new(h.as_slice(), vec!(("world","hello")))).unwrap();
    assert_eq!(r2.name, "hello");
    assert_eq!(r2.matches.len(), 1);
    let (k,v) = r2.matches[0];
    assert_eq!(k, "world");
    assert_eq!(v, "hello");
    let r3 = cond!(cond_hello, end!("hello"))
      .route(::Routing::new(e.as_slice(), vec!()));
    assert_eq!(r3.is_err(), true);
    let r4 = cond!(cond_hello, end!("hello"))
      .route(::Routing::new(w.as_slice(), vec!()));
    assert_eq!(r4.is_err(), true);
  }  
  #[test]
  fn route_bindcond() {
    let e = vec!();
    let w = vec!("world");
    let h = vec!("hello");
    let f = vec!("foo");
    let r1 = bindcond!("hello", cond_five, end!("hello"))
      .route(::Routing::new(h.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.len(), 1);
    let (k10,v10) = r1.matches[0];
    assert_eq!(k10, "hello");
    assert_eq!(v10, "hello");
    let r2 = bindcond!("hello", cond_five, end!("hello"))
      .route(::Routing::new(w.as_slice(), vec!(("world","hello")))).unwrap();
    assert_eq!(r2.name, "hello");
    assert_eq!(r2.matches.len(), 2);
    let (k20,v20) = r2.matches[0];
    assert_eq!(k20, "world");
    assert_eq!(v20, "hello");
    let (k21,v21) = r2.matches[1];
    assert_eq!(k21, "hello");
    assert_eq!(v21, "world");
    let r3 = bindcond!("hello", cond_five, end!("hello"))
      .route(::Routing::new(e.as_slice(), vec!()));
    assert_eq!(r3.is_err(), true);
    let r4 = bindcond!("hello", cond_five, end!("hello"))
      .route(::Routing::new(f.as_slice(), vec!()));
    assert_eq!(r4.is_err(), true);
  }  
  #[test]
  fn route_orelse() {
    let e = vec!();
    let h = vec!("hello");
    let w = vec!("world");
    let route = orelse!(literal!("hello", end!("hello")), end!("world"));
    let r1 = route.route(::Routing::new(h.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = route.route(::Routing::new(e.as_slice(), vec!())).unwrap();
    assert_eq!(r2.name, "world");
    assert_eq!(r2.matches.is_empty(), true);
    let r3 = route.route(::Routing::new(h.as_slice(), vec!(("hello", "world")))).unwrap();
    assert_eq!(r3.name, "hello");
    assert_eq!(r3.matches.len(), 1);
    let (k3,v3) = r3.matches[0];
    assert_eq!(k3,"hello");
    assert_eq!(v3,"world");
    let r4 = route.route(::Routing::new(e.as_slice(), vec!(("hello", "world")))).unwrap();
    assert_eq!(r4.name, "world");
    assert_eq!(r4.matches.len(), 1);
    let (k4,v4) = r4.matches[0];
    assert_eq!(k4,"hello");
    assert_eq!(v4,"world");
    let r5 = route.route(::Routing::new(w.as_slice(), vec!()));
    assert_eq!(r5.is_err(), true);
  }  
  #[test]
  fn route_literalvec() {
    let e = vec!();
    let h = vec!("hello");
    let w = vec!("world");
    let e1 = end!("hello");
    let e2 = end!("world");
    let v = vec!(("hello",Box::new(e1)),("world",Box::new(e2)));
    let route = literalvec!(v);
    let r1 = route.route(::Routing::new(h.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = route.route(::Routing::new(w.as_slice(), vec!())).unwrap();
    assert_eq!(r2.name, "world");
    assert_eq!(r2.matches.is_empty(), true);
    let r3 = route.route(::Routing::new(h.as_slice(), vec!(("hello","world")))).unwrap();
    assert_eq!(r3.name, "hello");
    assert_eq!(r3.matches.len(), 1);
    let (k3,v3) = r3.matches[0];
    assert_eq!(k3, "hello");
    assert_eq!(v3, "world");
    let r4 = route.route(::Routing::new(w.as_slice(), vec!(("hello","world")))).unwrap();
    assert_eq!(r4.name, "world");
    assert_eq!(r4.matches.len(), 1);
    let (k4,v4) = r4.matches[0];
    assert_eq!(k4, "hello");
    assert_eq!(v4, "world");
    let r5 = route.route(::Routing::new(e.as_slice(), vec!()));
    assert_eq!(r5.is_err(), true);
  }  
  #[test]
  fn route_literalslice() {
    let e = vec!();
    let h = vec!("hello");
    let w = vec!("world");
    let e1 = end!("hello");
    let e2 = end!("world");
    let v = vec!(("hello",Box::new(e1)),("world",Box::new(e2)));
    let route = literalslice!(v.as_slice());
    let r1 = route.route(::Routing::new(h.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = route.route(::Routing::new(w.as_slice(), vec!())).unwrap();
    assert_eq!(r2.name, "world");
    assert_eq!(r2.matches.is_empty(), true);
    let r3 = route.route(::Routing::new(h.as_slice(), vec!(("hello","world")))).unwrap();
    assert_eq!(r3.name, "hello");
    assert_eq!(r3.matches.len(), 1);
    let (k3,v3) = r3.matches[0];
    assert_eq!(k3, "hello");
    assert_eq!(v3, "world");
    let r4 = route.route(::Routing::new(w.as_slice(), vec!(("hello","world")))).unwrap();
    assert_eq!(r4.name, "world");
    assert_eq!(r4.matches.len(), 1);
    let (k4,v4) = r4.matches[0];
    assert_eq!(k4, "hello");
    assert_eq!(v4, "world");
    let r5 = route.route(::Routing::new(e.as_slice(), vec!()));
    assert_eq!(r5.is_err(), true);
  }  
  #[test]
  fn route_literalhashmap() {
    let e = vec!();
    let h = vec!("hello");
    let w = vec!("world");
    let e1 = end!("hello");
    let e2 = end!("world");
    let mut m = HashMap::new();
    m.insert("hello", Box::new(e1));
    m.insert("world", Box::new(e2));
    let route = literalhashmap!(m);
    let r1 = route.route(::Routing::new(h.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = route.route(::Routing::new(w.as_slice(), vec!())).unwrap();
    assert_eq!(r2.name, "world");
    assert_eq!(r2.matches.is_empty(), true);
    let r3 = route.route(::Routing::new(h.as_slice(), vec!(("hello","world")))).unwrap();
    assert_eq!(r3.name, "hello");
    assert_eq!(r3.matches.len(), 1);
    let (k3,v3) = r3.matches[0];
    assert_eq!(k3, "hello");
    assert_eq!(v3, "world");
    let r4 = route.route(::Routing::new(w.as_slice(), vec!(("hello","world")))).unwrap();
    assert_eq!(r4.name, "world");
    assert_eq!(r4.matches.len(), 1);
    let (k4,v4) = r4.matches[0];
    assert_eq!(k4, "hello");
    assert_eq!(v4, "world");
    let r5 = route.route(::Routing::new(e.as_slice(), vec!()));
    assert_eq!(r5.is_err(), true);
  }  
  #[test]
  fn route_literalbtreemap() {
    let e = vec!();
    let h = vec!("hello");
    let w = vec!("world");
    let e1 = end!("hello");
    let e2 = end!("world");
    let mut m = BTreeMap::new();
    m.insert("hello", Box::new(e1));
    m.insert("world", Box::new(e2));
    let route = literalbtreemap!(m);
    let r1 = route.route(::Routing::new(h.as_slice(), vec!())).unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = route.route(::Routing::new(w.as_slice(), vec!())).unwrap();
    assert_eq!(r2.name, "world");
    assert_eq!(r2.matches.is_empty(), true);
    let r3 = route.route(::Routing::new(h.as_slice(), vec!(("hello","world")))).unwrap();
    assert_eq!(r3.name, "hello");
    assert_eq!(r3.matches.len(), 1);
    let (k3,v3) = r3.matches[0];
    assert_eq!(k3, "hello");
    assert_eq!(v3, "world");
    let r4 = route.route(::Routing::new(w.as_slice(), vec!(("hello","world")))).unwrap();
    assert_eq!(r4.name, "world");
    assert_eq!(r4.matches.len(), 1);
    let (k4,v4) = r4.matches[0];
    assert_eq!(k4, "hello");
    assert_eq!(v4, "world");
    let r5 = route.route(::Routing::new(e.as_slice(), vec!()));
    assert_eq!(r5.is_err(), true);
  }  
  #[test]
  fn router() {
    let e1 = end!("hello");
    let e2 = end!("world");
    let mut m = HashMap::new();
    m.insert("hello", Box::new(e1));
    m.insert("world", Box::new(e2));
    let route = literalhashmap!(m);
    let router = ::Router::new(route);
    let r1 = router.route("/hello").unwrap();
    assert_eq!(r1.name, "hello");
    assert_eq!(r1.matches.is_empty(), true);
    let r2 = router.route("/world").unwrap();
    assert_eq!(r2.name, "world");
    assert_eq!(r2.matches.is_empty(), true);
    let r3 = router.route("");
    assert_eq!(r3.is_none(), true);
  }
}
