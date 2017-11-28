The irresponsible software guild presents...

# Crouton - Path Routing to the overkill

A high-performance hierarchical path router

## Features

1. Describe your routes flexibily as a simple tree of data.
2. Easily compose multiple applications together at different prefixes.
3. Simple and small (under 200 loc!), pure, safe, optimised rust code.

## Usage

```
#[macro_use] extern crate crouton;

use crouton::{Crouton,Router};

fn main() {
  // Define our routes as a data structure with the handy macro api
  let routes = literalvec!(
    vec!(
      ("login",  end!("login")),
      ("logout", end!("logout")),
      ("user", orelse!(
        end!("user-list"),
        bindcond!(
          "user-id",
          |id| id.parse::<u64>().is_some(),
          end!("user"))))))
  // Instantiate a router from the routes
  let router = Router::new(routes);
  // Feed it paths from the command line
  for arg in env::args().skip(1).collect() {
    match router.route(arg) {
      Some(r) => println!("Path {} matches route {}", arg, r.name),
      None => println!("Path {} does not match a route", arg),
    }
  }
}
```

## What's in a path?

Crouton treats a path as a series of `/`-delimited segments.

The path `/hello/world` is treated as the segments `hello` and `world`.

The `Crouton` enum is the specification of how matches should occur, segment by segment.

Here is a rust specification of a route that would match `/hello/world`

```rust
literal!("hello", literal!("world", end!("helloworld")))
```

The two things to notice about this are:

1. `literal!` takes a literal segment and another matcher for if that succeeds
2. We assign a name (`helloworld`) to a successful match with `end!`

Here's how it matches:

1. The path `/hello/world` is split into `hello` and `world` segments.
2. We match `hello` against the literal `hello`, which succeeds.
3. We match `world` against the literal `world`, which succeeds.
4. We match no more segments against the endpoint `helloworld` which succeeds.
5. Match succeeds as `helloworld`.

## Branching

Here is a route that matches either `/hello` as `hello` or `/` as `world`:

```rust
orelse!(literal!("hello", end!("hello")), end!("world"))
```

`orelse!` takes two matchers and tries them in order. Let's match with it:

`/hello` matches as follows:

1. The path `/hello` is split into one segment, `hello`.
2. We match `hello` against the literal `hello` which succeeds.
3. We match no more segments against the endpoint `hello` which succeeds.
4. Match succeeds as `hello`.

`/` matches as follows:

1. The path `/` is split into no segments.
2. We match no segments against the literal `hello` which fails.
3. We match no segments against the endpoint `world` which succeeds.
4. Match succeeds as `world`.

The return value of matching is an `Option`. When a match fails, you get a `None` back.

Because a route will not succeed until the entire length of it has succeeded, backtracking
is naturally provided by the conditional facilities.

## Macro index

There are 11 macros corresponding to 11 constructors of the `Crouton` enum:

* `end!(name: String)`   - Matches as name when there are no more segments remaining.
* `slurp!(name: String)` - Matches as name, binding any remaining segments under name.
* `literal!(value: String, next: Crouton)` - Matches a literal value against the next segment and continues matching with next.
* `bind!(name: String, next: Crouton)` - Matches any single segment unconditionally, storing the name in matches.
* `cond!(pred: fn(&str) -> bool, next: Crouton)` - Matches a single segment if `pred(segment)` returns true.
* `bindcond!(name: String, pred: fn(&str) -> bool, next: Crouton)` - Conditional bind.
* `orelse!(first: Crouton, second: Crouton)` - Try in order, return first matching
* `literalvec!(items: Vec<(&str, Box<Crouton>)>)` - Tries a list of literals, forwarding to the first success
* `literalslice!(items: &[(&str, Box<Crouton>)])` - As literalvec, but backed by a slice of string slices
* `literalhashmap!(items: HashMap<&str, Box<Crouton>>)` - As literalvec, but backed by a hash map
* `literalbtreemap!(items: BTreeMap<&str, Box<Crouton>>)` - As literalvec, but backed by a btree map

These eliminate much of the boilerplate involved in building routes, but don't worry they're all quite simple!

Here's a route from earlier:

```rust
literal!("hello", literal!("world", end!("helloworld")))
```

Here is what that looks like after macroexpansion:


```rust
Crouton::Literal(
  Box::new("hello"),
  Box::new(Crouton::Literal(
    Box::new("world"),
    Box::new(Crouton::End("helloworld"))
  ))
)
```

As you can see, we're not doing anything too clever, just boilerplating for you.

## Routing under the hood

The `Router` struct provides the simplest API where you don't have to worry much about lifetimes.
It performs three functions:

1. Deconstructs the given path to a vector
2. Calls the internal routing API.
3. Converts the result to `Option<Route>`

The internal routing API is the `Crouton::route` method, which maps a `Crouton` and a `Routing`
to a `Result<Route,Routing>`.

`Route` is the structure describing a successful match (without lifetimes):

```rust
pub struct Route {
  pub name: & str,
  pub matches: Vec<(& str, & str)>,
}
```

`Routing` is the structure which holds the working state of a match (without lifetimes):

```rust
pub struct Routing {
  pub pieces: & [& str],
  pub matches: Vec<(& str, & str)>,
}
```

We use the `Err` constructor to feed the lifetimes of `Routing` back when a match fails.
This allows us to minimise copying in the event of fallback.

## Lifetimes

Most of Crouton is parameterised by three lifetimes, ordered longest first:

* `decl`  - Declaration time
* `route` - Data valid while the original route string is valid
* `ret`   - A working 'return' lifetime

## FAQ

Q. Why do endpoints have names instead of just code?
A. Because we're planning to build a reverse router soon.

Q. Why do you have four options for matching a list of literals?:
A. So you can pick the one that performs best in your situation:

* When you have only a few options (as is typical), you can use `LiteralVec` or `LiteralSlice` depending on whether you want it to own the data
* When you have more (like 100+), you can use `LiteralHashMap` or `LiteralBTreeMap`. Don't forget to benchmark!

Q. You've clearly put work into making it efficient. Why?
A. URL Routing typically happens on every request, so we can save power and behave better under load.

## Copyright and License

Copyright (c) 2017 James Laver

Licensed under the Apache License, Version 2.0

