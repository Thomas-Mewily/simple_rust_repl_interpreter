### A simple interpreter in Rust.

This project is a simple virtual machine for executing expression, and a tiny programming langage using the Lisp S-expression syntax style that can be parsed and used into the virtual machine.

You can use it like an REPL for the moment (Read–eval–print loop) by typing expression in the terminal :

```rust
42
=> 42
```

```rust
(+ 1 2)
=> 3
```

```rust
(+ 1 (* 2 (+ 3 4))) 
=> 15
```

```rust
(& true false)
=> false
```

```rust
(if (== 1 2) 10 20)
=> 20
```


### Strongly typed :

```rust
(& true 42)    
Expected `bool` instead of `42` for the 2 arg
> fn(bool, bool) -> bool
```

Currently support :
- Integer,
- Boolean,
- If Else, 
- and user build in function from the source language

### Adding new function from Rust into the virtual machine is easy :

```rust
self.add("true", true);
self.add("false", false);

self.add("void", ());
self.add("bool", Kind::Bool);
self.add("i32", Kind::I32);
self.add("type", Kind::Kind);

self.add("+", |x: i32, y: i32| x + y);
self.add("*", |x: i32, y: i32| x * y);

self.add("&", |x: bool, y: bool| x & y);
self.add("|", |x: bool, y: bool| x | y);

self.add("!", |x: bool| !x);
```

